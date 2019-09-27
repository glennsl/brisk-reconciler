module type OutputTree = {
  type node;

  let markAsStale: unit => unit;

  let insertNode: (~parent: node, ~child: node, ~position: int) => node;
  let deleteNode: (~parent: node, ~child: node, ~position: int) => node;
  let moveNode: (~parent: node, ~child: node, ~from: int, ~to_: int) => node;
};

module Make = (OutputTree: OutputTree) => {
  module GlobalState = {
    let debug = ref(true);
    let componentKeyCounter = ref(0);
    let reset = () => {
      debug := true;
      componentKeyCounter := 0;
    };

    /**
     * Use physical equality to recognize that an element was added to the list
     * of children.
     * Note: this currently does not check for pending updates on components in
     * the list.
     */
    let useTailHack = ref(false);
  };

  module Key = {
    type t = int;

    let equal = (==);
    let none = (-1);
    let dynamicKeyMagicNumber = 0;
    let create = () => {
      incr(GlobalState.componentKeyCounter);
      GlobalState.componentKeyCounter^;
    };
  };
  type internalOutputNode =
    | Node(OutputTree.node)
    | UpdatedNode(OutputTree.node, OutputTree.node);
  type outputNodeContainer = Lazy.t(internalOutputNode);
  type outputNodeGroup = list(outputNodeContainer);
  type id('a) = ..;
  type instance('hooks, 'initialHooks, 'elementType, 'outputNode, 'render) = {
    hooks: Hooks.state('hooks, unit),
    component:
      component('hooks, 'initialHooks, 'elementType, 'outputNode, 'render),
    element,
    instanceSubForest: instanceForest,
    subElements: 'elementType,
    hostInstance: 'outputNode,
  }
  and renderFunction('hooks, 'initialHooks, 'render) =
    (~hooks: Hooks.t('hooks, unit, 'initialHooks, 'initialHooks)) => 'render
  and elementFunction('hooks, 'initialHooks, 'elementType) =
    (~hooks: Hooks.t('hooks, unit, 'initialHooks, 'initialHooks)) =>
    (Hooks.t(unit, unit, 'hooks, unit), 'elementType)
  and element =
    | Element(
        elementFunction('hooks, 'initialHooks, 'elementType),
        component('hooks, 'initialHooks, 'elementType, 'outputNode, 'render),
        Key.t,
      )
      : element
  and syntheticElement =
    | Flat(element)
    | Nested(list(syntheticElement))
  and outputTreeElement = {
    make: unit => OutputTree.node,
    configureInstance:
      (~isFirstRender: bool, OutputTree.node) => OutputTree.node,
    children: syntheticElement,
  }
  and elementType('elementType, 'outputNode) =
    | Host: elementType(outputTreeElement, outputNodeContainer)
    | React: elementType(syntheticElement, outputNodeGroup)
  and component('hooks, 'initialHooks, 'elementType, 'outputNode, 'render) = {
    render:
      (~hooks: Hooks.t('hooks, unit, 'initialHooks, 'initialHooks)) => 'render,
    elementType: elementType('elementType, 'outputNode),
    id:
      id(
        instance('hooks, 'initialHooks, 'elementType, 'outputNode, 'render),
      ),
    debugName: string,
    useDynamicKey: bool,
    eq:
      'a.
      (
        'a,
        id('a),
        id(
          instance('hooks, 'initialHooks, 'elementType, 'outputNode, 'render),
        )
      ) =>
      option(
        instance('hooks, 'initialHooks, 'elementType, 'outputNode, 'render),
      ),

  }
  and instanceForest =
    | IFlat(opaqueInstance)
    | INested(list(instanceForest), int /*subtree size*/)
  and opaqueInstance =
    | Instance(
        instance('hooks, 'initialHooks, 'elementType, 'outputNode, 'render),
      )
      : opaqueInstance;

  type polymorphicRender = {
    render:
      'hooks 'initialHooks 'elementType.
      elementFunction('hooks, 'initialHooks, 'elementType),

  };

  type renderedElement = {
    nearestHostOutputNode: outputNodeContainer,
    instanceForest,
    enqueuedEffects: EffectSequence.t,
  };

  type opaqueInstanceUpdate = {
    nearestHostOutputNode: outputNodeContainer,
    opaqueInstance,
    enqueuedEffects: EffectSequence.t,
  };

  module InstanceForest = {
    let getSubtreeSize =
      fun
      | INested(_, x) => x
      | IFlat(Instance({hostInstance, component: {elementType}})) =>
        switch (elementType) {
        | React => List.length(hostInstance)
        | Host => 1
        };

    let rec fold = (f, acc, instanceForest) => {
      switch (instanceForest) {
      | IFlat(opaqueInstance) => f(acc, opaqueInstance)
      | INested(l, _) =>
        List.fold_left(
          (acc, instanceForest) => fold(f, acc, instanceForest),
          acc,
          l,
        )
      };
    };

    let rec flatten =
      fun
      | IFlat(l) => [l]
      | INested(l, _) => ListTR.concat(ListTR.map(flatten, l));
    let outputTreeNodes = subtree =>
      flatten(subtree)
      |> List.fold_left(
           (
             acc: list(outputNodeContainer),
             Instance({component: {elementType}, hostInstance}),
           ) =>
             switch (elementType) {
             | React => List.append(hostInstance, acc)
             | Host => [hostInstance, ...acc]
             },
           [],
         )
      |> List.rev;

    let pendingEffects = (~lifecycle, acc, instanceForest) => {
      fold(
        (acc, Instance({hooks})) =>
          EffectSequence.chain(Hooks.pendingEffects(~lifecycle, hooks), acc),
        acc,
        instanceForest,
      );
    };
  };

  module SyntheticElement = {
    let rec map = (f, syntheticElement): (instanceForest, EffectSequence.t) =>
      switch (syntheticElement) {
      | Flat(l) =>
        let (opaqueInstance, enqueuedMountEffects) = f(l);
        (IFlat(opaqueInstance), enqueuedMountEffects);
      | Nested(l) =>
        let instanceSubForestAndEffects = ListTR.map(map(f), l);
        let subForest = ListTR.map(fst, instanceSubForestAndEffects);
        let effects = ListTR.map(snd, instanceSubForestAndEffects);
        (
          INested(
            subForest,
            subForest
            |> List.map(InstanceForest.getSubtreeSize)
            |> List.fold_left((+), 0),
          ),
          List.fold_left(EffectSequence.chain, EffectSequence.noop, effects),
        );
      };
    let rec fold =
            (f, renderedElement, nearestHostOutputNode: outputNodeContainer) =>
      switch (renderedElement) {
      | Flat(e) =>
        let {nearestHostOutputNode, opaqueInstance, enqueuedEffects} =
          f(~nearestHostOutputNode, e);
        {
          nearestHostOutputNode,
          instanceForest: IFlat(opaqueInstance),
          enqueuedEffects,
        };
      | Nested(l) =>
        let (nextL, nearestHostOutputNode, enqueuedEffects) =
          List.fold_left(
            ((acc, nearestHostOutputNode, enqueuedEffects), element) => {
              let {
                nearestHostOutputNode,
                instanceForest,
                enqueuedEffects: nextEffects,
              } =
                fold(f, element, nearestHostOutputNode);
              (
                [instanceForest, ...acc],
                nearestHostOutputNode,
                EffectSequence.chain(enqueuedEffects, nextEffects),
              );
            },
            ([], nearestHostOutputNode, EffectSequence.noop),
            List.rev(l),
          );
        {
          nearestHostOutputNode,
          instanceForest:
            INested(
              nextL,
              List.map(InstanceForest.getSubtreeSize, nextL)
              |> List.fold_left((+), 0),
            ),
          enqueuedEffects,
        };
      };
  };

  module Node = {
    let make:
      type elementType_ outputNode.
        (
          elementType(elementType_, outputNode),
          elementType_,
          instanceForest
        ) =>
        outputNode =
      (elementType, subElements, instanceSubTree) =>
        switch (elementType) {
        | Host =>
          lazy {
            let instance =
              subElements.make()
              |> subElements.configureInstance(~isFirstRender=true);
            Node(
              List.fold_left(
                ((position, parent), child) =>
                  (
                    position + 1,
                    {
                      let Node(child) | UpdatedNode(_, child) =
                        Lazy.force(child);
                      OutputTree.insertNode(~parent, ~child, ~position);
                    },
                  ),
                (0, instance),
                InstanceForest.outputTreeNodes(instanceSubTree),
              )
              |> snd,
            );
          }
        | React => InstanceForest.outputTreeNodes(instanceSubTree)
        };
  };

  module SubtreeChange = {
    let insertNodes =
        (
          ~parent as parentWrapper: internalOutputNode,
          ~children: outputNodeGroup,
          ~position as initialPosition: int,
        ) => {
      let Node(oldParent) | UpdatedNode(_, oldParent) = parentWrapper;
      let newParent =
        List.fold_left(
          ((position, parent), child) =>
            (
              position + 1,
              {
                let Node(child) | UpdatedNode(_, child) = Lazy.force(child);
                OutputTree.insertNode(~parent, ~child, ~position);
              },
            ),
          (initialPosition, oldParent),
          children,
        )
        |> snd;
      newParent === oldParent
        ? parentWrapper : UpdatedNode(oldParent, newParent);
    };
    let deleteNodes =
        (
          ~parent as parentWrapper: internalOutputNode,
          ~children: outputNodeGroup,
          ~position as initialPosition: int,
        ) => {
      let Node(oldParent) | UpdatedNode(_, oldParent) = parentWrapper;
      let newParent =
        List.fold_left(
          ((position, parent), child) =>
            (
              position + 1,
              {
                let Node(child) | UpdatedNode(_, child) = Lazy.force(child);
                OutputTree.deleteNode(~parent, ~child, ~position);
              },
            ),
          (initialPosition, oldParent),
          children,
        )
        |> snd;
      newParent === oldParent
        ? parentWrapper : UpdatedNode(oldParent, newParent);
    };

    let prependElement =
        (~parent: outputNodeContainer, ~children: outputNodeGroup)
        : outputNodeContainer =>
      lazy (insertNodes(~parent=Lazy.force(parent), ~children, ~position=0));

    let replaceSubtree =
        (
          ~parent: outputNodeContainer,
          ~prevChildren: outputNodeGroup,
          ~nextChildren: outputNodeGroup,
          ~absoluteSubtreeIndex: int,
        )
        : outputNodeContainer =>
      lazy {
        insertNodes(
          ~parent=
            deleteNodes(
              ~parent=Lazy.force(parent),
              ~children=prevChildren,
              ~position=absoluteSubtreeIndex,
            ),
          ~children=nextChildren,
          ~position=absoluteSubtreeIndex,
        );
      };

    let reorderNode =
        (
          ~child: outputNodeContainer,
          ~parent: OutputTree.node,
          ~indexShift: int,
          ~from: int,
          ~to_: int,
        ) => {
      let isVal = Lazy.is_val(child);
      switch (Lazy.force(child)) {
      | Node(child) =>
        from === to_ - indexShift
          ? parent : OutputTree.moveNode(~parent, ~child, ~from, ~to_)
      | UpdatedNode(prevChild, child) when !isVal =>
        OutputTree.insertNode(
          ~parent=
            OutputTree.deleteNode(~parent, ~child=prevChild, ~position=from),
          ~child,
          ~position=to_,
        )
      | UpdatedNode(_prevChild, child) =>
        from === to_ - indexShift
          ? parent : OutputTree.moveNode(~parent, ~child, ~from, ~to_)
      };
    };

    let reorder =
        (
          ~parent,
          ~instance as Instance({hostInstance, component: {elementType}}),
          ~indexShift,
          ~from,
          ~to_,
        )
        : outputNodeContainer =>
      switch (elementType) {
      | Host =>
        lazy {
          let parentWrapper = Lazy.force(parent);
          let Node(oldParent) | UpdatedNode(_, oldParent) = parentWrapper;
          let newParent =
            reorderNode(
              ~parent=oldParent,
              ~child=hostInstance,
              ~indexShift,
              ~from,
              ~to_,
            );
          newParent === oldParent
            ? parentWrapper : UpdatedNode(oldParent, newParent);
        }
      | React =>
        lazy {
          let parentWrapper = Lazy.force(parent);
          let Node(oldParent) | UpdatedNode(_, oldParent) = parentWrapper;
          let newParent =
            List.fold_left(
              ((index, parent), child) =>
                (
                  index + 1,
                  reorderNode(
                    ~parent,
                    ~child,
                    ~indexShift,
                    ~from=from + index,
                    ~to_=to_ + index,
                  ),
                ),
              (0, oldParent),
              hostInstance,
            )
            |> snd;
          newParent === oldParent
            ? parentWrapper : UpdatedNode(oldParent, newParent);
        }
      };

    let updateNodes =
        (
          ~parent,
          ~instanceForest: instanceForest,
          ~position as initialPosition,
        ) =>
      lazy {
        let parentWrapper = Lazy.force(parent);
        let Node(oldParent) | UpdatedNode(_, oldParent) = parentWrapper;
        let newParent =
          List.fold_left(
            ((position, instance), x) =>
              (
                position + 1,
                switch (Lazy.force(x)) {
                | Node(_child) => instance
                | UpdatedNode(oldNode, newNode) =>
                  OutputTree.insertNode(
                    ~parent=
                      OutputTree.deleteNode(
                        ~parent=instance,
                        ~child=oldNode,
                        ~position,
                      ),
                    ~child=newNode,
                    ~position,
                  )
                },
              ),
            (initialPosition, oldParent),
            InstanceForest.outputTreeNodes(instanceForest),
          )
          |> snd;
        newParent === oldParent
          ? parentWrapper : UpdatedNode(oldParent, newParent);
      };
  };

  module OpaqueInstanceHash = {
    type t = lazy_t(Hashtbl.t(int, (opaqueInstance, int)));
    let addOpaqueInstance = (idTable, index, opaqueInstance) => {
      let Instance({element: Element(_, _, key)}) = opaqueInstance;
      key == Key.none
        ? () : Hashtbl.add(idTable, key, (opaqueInstance, index));
    };
    let addRenderedElement = (idTable, renderedElement, index) => {
      let rec aux = index =>
        fun
        | IFlat(l) => addOpaqueInstance(idTable, index, l)
        | INested(l, _) => List.iteri((i, x) => aux(i, x), l);
      aux(index, renderedElement);
    };
    let createKeyTable = renderedElement =>
      lazy {
        let keyTable = Hashtbl.create(1);
        addRenderedElement(keyTable, renderedElement, 0);
        keyTable;
      };
    let lookupKey = (table, key) => {
      let keyTable = Lazy.force(table);
      try (Some(Hashtbl.find(keyTable, key))) {
      | Not_found => None
      };
    };
  };

  module Instance = {
    let rec ofElement =
            (Element(render, component, _) as element)
            : (opaqueInstance, EffectSequence.t) => {
      let (hooks, subElements) =
        render(
          ~hooks=
            Hooks.ofState(
              Hooks.createState(),
              ~onStateDidChange=OutputTree.markAsStale,
            ),
        );
      let hooks = Hooks.toState(hooks);
      let (instanceSubForest, mountEffects) =
        (
          switch (component.elementType) {
          | React => (subElements: syntheticElement)
          | Host => subElements.children
          }
        )
        |> ofList;
      (
        Instance({
          hooks,
          element,
          subElements,
          instanceSubForest,
          hostInstance:
            Node.make(component.elementType, subElements, instanceSubForest),
          component,
        }),
        EffectSequence.chain(
          Hooks.pendingEffects(~lifecycle=Hooks.Effect.Mount, hooks),
          mountEffects,
        ),
      );
    }
    and ofList = (syntheticElement): (instanceForest, EffectSequence.t) =>
      SyntheticElement.map(ofElement, syntheticElement);

    let pendingEffects =
        (~lifecycle, ~nextEffects, ~instance as {instanceSubForest, hooks}) => {
      InstanceForest.pendingEffects(
        ~lifecycle,
        EffectSequence.chain(
          Hooks.pendingEffects(~lifecycle, hooks),
          nextEffects,
        ),
        instanceSubForest,
      );
    };
  };

  module Render = {
    let getOpaqueInstance = (~useKeyTable, Element(_, _, key)) =>
      switch (useKeyTable) {
      | None => None
      | Some(keyTable) => OpaqueInstanceHash.lookupKey(keyTable, key)
      };

    type childElementUpdate = {
      updatedRenderedElement: renderedElement,
      /* This represents the way previously rendered elements have been shifted due to moves */
      indexShift: int,
    };

    module UpdateContext = {
      type t = {
        shouldExecutePendingUpdates: bool,
        useKeyTable: option(OpaqueInstanceHash.t),
        /* This is a unique index of an element within a subtree,
          * thanks to tracking it we can efficiently manage moves of within a subtree
         */
        nearestHostOutputNode: outputNodeContainer,
        absoluteSubtreeIndex: int,
      };
    };

    /**
     * Initial render of an Element. Recurses to produce the entire tree of
     * instances.
     */
    let rec renderElement =
            (~useKeyTable=?, ~nearestHostOutputNode, element)
            : opaqueInstanceUpdate =>
      switch (getOpaqueInstance(~useKeyTable, element)) {
      | Some((opaqueInstance, _)) =>
        updateOpaqueInstance(
          ~updateContext=
            UpdateContext.{
              nearestHostOutputNode,
              absoluteSubtreeIndex: 0,
              useKeyTable,
              shouldExecutePendingUpdates: false,
            },
          opaqueInstance,
          element,
        )
      | None =>
        let (opaqueInstance, enqueuedEffects) = Instance.ofElement(element);

        {nearestHostOutputNode, opaqueInstance, enqueuedEffects};
      }
    and renderReactElement =
        (~useKeyTable=?, nearestHostOutputNode, syntheticElement)
        : renderedElement =>
      SyntheticElement.fold(
        renderElement(~useKeyTable?),
        syntheticElement,
        nearestHostOutputNode,
      )
    /**
     * Update a previously rendered instance tree according to a new Element.
     *
     * Here's where the magic happens:
     * -------------------------------
     *
     * We perform a dynamic check that two types are statically equal by way of
     * mutation! We have a value of type `Instance` and another of type
     * `Element`, where we each has their own `component 'x` for potentially
     * different 'x. We need to see if the 'x are the same and if so safely "cast"
     * one's `component` to the others. We do this by handing off state safely into
     * one of their `component`s, and then seeing if we can observe it in the
     * other, and if so, we simply treat the old component as the new one's.
     *
     * This approach is as sound as our confidence in our ability to repair the
     * mutations accurately.
     *
     * There are more elegant ways to do this using first class modules, combined
     * with extensible variants. That is how we should do this if we want to turn
     * this implementation into something serious - it would avoid hitting the
     * write barrier.
     *
     * The UpdateLog:
     * ---------------------
     * The updates happen depth first and so the update log contains the deepes
     * changes first.
     * A change at depth N in the tree, causes all nodes from 0 to N generate an
     * update. It's because the render tree is an immutable data structure.
     * A change deep within a tree, means that the subtree of its parent has
     * changed and it propagates to the root of a tree.
     */
    and updateOpaqueInstance =
        (
          ~updateContext: UpdateContext.t,
          Instance(instance) as originalOpaqueInstance,
          Element(renderNextElement, nextComponent, _) as nextElement,
        )
        : opaqueInstanceUpdate => {
      let nextState =
        updateContext.shouldExecutePendingUpdates
          ? Hooks.flushPendingStateUpdates(instance.hooks) : instance.hooks;
      let stateChanged = nextState !== instance.hooks;

      let bailOut = !stateChanged && instance.element === nextElement;

      if (bailOut && !updateContext.shouldExecutePendingUpdates) {
        {
          nearestHostOutputNode: updateContext.nearestHostOutputNode,
          opaqueInstance: originalOpaqueInstance,
          enqueuedEffects: EffectSequence.noop,
        };
      } else {
        let {component: {id}} = instance;

        switch (
          nextComponent.eq(
            {...instance, hooks: nextState},
            id,
            nextComponent.id,
          )
        ) {
        /*
         * Case A: The next element *is* of the same component class.
         */
        | Some(handedInstance) =>
          let {
                nearestHostOutputNode,
                opaqueInstance: newOpaqueInstance,
                enqueuedEffects,
              } as ret =
            updateInstance(
              ~originalOpaqueInstance,
              ~updateContext,
              ~nextComponent,
              ~renderNextElement,
              ~nextElement,
              ~stateChanged,
              handedInstance,
            );
          newOpaqueInstance === originalOpaqueInstance
            ? ret
            : {
              nearestHostOutputNode:
                SubtreeChange.updateNodes(
                  ~parent=nearestHostOutputNode,
                  ~instanceForest=IFlat(newOpaqueInstance),
                  ~position=updateContext.absoluteSubtreeIndex,
                ),
              opaqueInstance: newOpaqueInstance,
              enqueuedEffects,
            };
        /*
         * Case B: The next element is *not* of the same component class. We know
         * because otherwise we would have observed the mutation on
         * `nextComponentClass`.
         */
        | None =>
          /**
           * ** Switching component type **
           */
          let (opaqueInstance, mountEffects) =
            Instance.ofElement(nextElement);
          let enqueuedEffects =
            Instance.pendingEffects(
              ~lifecycle=Hooks.Effect.Unmount,
              ~nextEffects=mountEffects,
              ~instance,
            );
          {
            nearestHostOutputNode:
              SubtreeChange.replaceSubtree(
                ~parent=updateContext.nearestHostOutputNode,
                ~prevChildren=
                  InstanceForest.outputTreeNodes(
                    IFlat(originalOpaqueInstance),
                  ),
                ~nextChildren=
                  InstanceForest.outputTreeNodes(IFlat(opaqueInstance)),
                ~absoluteSubtreeIndex=updateContext.absoluteSubtreeIndex,
              ),
            opaqueInstance,
            enqueuedEffects,
          };
        };
      };
    }
    and updateInstance:
      type hooks initialHooks elementType outputNodeType ret.
        (
          ~originalOpaqueInstance: opaqueInstance,
          ~updateContext: UpdateContext.t,
          ~nextComponent: component(
                            hooks,
                            initialHooks,
                            elementType,
                            outputNodeType,
                            ret,
                          ),
          ~renderNextElement: elementFunction(
                                hooks,
                                initialHooks,
                                elementType,
                              ),
          ~nextElement: element,
          ~stateChanged: bool,
          instance(hooks, initialHooks, elementType, outputNodeType, ret)
        ) =>
        opaqueInstanceUpdate =
      (
        ~originalOpaqueInstance,
        ~updateContext,
        ~nextComponent,
        ~renderNextElement,
        ~nextElement,
        ~stateChanged,
        instance,
      ) => {
        let updatedInstanceWithNewElement = {
          ...instance,
          element: nextElement,
        };

        let shouldRerender = stateChanged || nextElement !== instance.element;

        let (initialHooks, nextSubElements) =
          if (shouldRerender) {
            let (initialHooks, nextElement) =
              renderNextElement(
                ~hooks=
                  Hooks.ofState(
                    updatedInstanceWithNewElement.hooks,
                    ~onStateDidChange=OutputTree.markAsStale,
                  ),
              );
            (Hooks.toState(initialHooks), nextElement);
          } else {
            (instance.hooks, instance.subElements);
          };

        let updatedInstanceWithNewState = {
          ...updatedInstanceWithNewElement,
          hooks: initialHooks,
        };

        let {subElements, instanceSubForest} = updatedInstanceWithNewState;
        let (
          nearestHostOutputNode,
          updatedInstanceWithNewSubtree,
          enqueuedEffects,
        ) =
          switch (nextComponent.elementType) {
          | React =>
            let {
              nearestHostOutputNode,
              instanceForest: nextInstanceSubForest,
              enqueuedEffects,
            } =
              updateInstanceSubtree(
                ~updateContext,
                ~oldInstanceForest=instanceSubForest,
                ~oldReactElement=subElements: syntheticElement,
                ~nextReactElement=nextSubElements: syntheticElement,
                (),
              );
            nextInstanceSubForest !== instanceSubForest
              ? (
                nearestHostOutputNode,
                {
                  ...updatedInstanceWithNewState,
                  subElements: nextSubElements,
                  instanceSubForest: nextInstanceSubForest,
                },
                enqueuedEffects,
              )
              : (
                nearestHostOutputNode,
                updatedInstanceWithNewState,
                enqueuedEffects,
              );
          | Host =>
            let instanceWithNewHostView =
              shouldRerender
                ? {
                  ...updatedInstanceWithNewState,
                  hostInstance:
                    lazy {
                      let instance =
                        Lazy.force(updatedInstanceWithNewState.hostInstance);
                      let Node(beforeUpdate) | UpdatedNode(_, beforeUpdate) = instance;
                      let afterUpdate =
                        nextSubElements.configureInstance(
                          ~isFirstRender=false,
                          beforeUpdate,
                        );
                      afterUpdate === beforeUpdate
                        ? instance : UpdatedNode(beforeUpdate, afterUpdate);
                    },
                }
                : updatedInstanceWithNewState;

            let {
              nearestHostOutputNode: hostInstance,
              instanceForest: nextInstanceSubForest,
              enqueuedEffects,
            } =
              updateInstanceSubtree(
                ~updateContext={
                  ...updateContext,
                  absoluteSubtreeIndex: 0,
                  nearestHostOutputNode: (
                    instanceWithNewHostView.hostInstance: outputNodeContainer
                  ),
                },
                ~oldInstanceForest=instanceSubForest,
                ~oldReactElement=subElements.children,
                ~nextReactElement=nextSubElements.children,
                (),
              );
            if (nextInstanceSubForest
                !== instanceWithNewHostView.instanceSubForest) {
              (
                updateContext.nearestHostOutputNode,
                {
                  ...instanceWithNewHostView,
                  instanceSubForest: nextInstanceSubForest,
                  subElements: nextSubElements,
                  hostInstance,
                }:
                  instance(
                    hooks,
                    initialHooks,
                    elementType,
                    outputNodeType,
                    ret,
                  ),
                enqueuedEffects,
              );
            } else {
              (
                updateContext.nearestHostOutputNode,
                instanceWithNewHostView,
                enqueuedEffects,
              );
            };
          };
        if (updatedInstanceWithNewSubtree === updatedInstanceWithNewElement
            && !stateChanged) {
          {
            nearestHostOutputNode,
            opaqueInstance: originalOpaqueInstance,
            enqueuedEffects,
          };
        } else {
          {
            nearestHostOutputNode,
            opaqueInstance: Instance(updatedInstanceWithNewSubtree),
            enqueuedEffects:
              EffectSequence.chain(
                Hooks.pendingEffects(
                  ~lifecycle=Hooks.Effect.Update,
                  updatedInstanceWithNewSubtree.hooks,
                ),
                enqueuedEffects,
              ),
          };
        };
      }

    /**
     * updateRenderedElement recurses through the syntheticElement tree as long as
     * the oldReactElement and nextReactElement have the same shape.
     *
     * The base case is either an empty list - Nested([]) or a Flat element.
     *
     * syntheticElement is a recursive tree like data structure. The tree doesn't
     * contain children of the syntheticElements returned from children, it only
     * contains the "immediate" children so to speak including all nested lists.
     *
     * `keyTable` is a hash table containing all keys in the syntheticElement tree.
     */
    and updateInstanceSubtree =
        (
          ~updateContext,
          ~oldInstanceForest,
          ~oldReactElement,
          ~nextReactElement,
          (),
        )
        : renderedElement =>
      switch (oldInstanceForest, oldReactElement, nextReactElement) {
      | (
          INested(instanceSubTrees, subtreeSize),
          Nested(oldReactElements),
          Nested([nextReactElement, ...nextReactElements]),
        )
          when
            nextReactElements === oldReactElements && GlobalState.useTailHack^ =>
        /* Detected that nextReactElement was obtained by adding one element */
        let {
          nearestHostOutputNode,
          instanceForest: addedElement,
          enqueuedEffects,
        } =
          renderReactElement(
            updateContext.nearestHostOutputNode,
            nextReactElement,
          );
        {
          nearestHostOutputNode:
            SubtreeChange.prependElement(
              ~parent=nearestHostOutputNode,
              ~children=InstanceForest.outputTreeNodes(addedElement),
            ),
          /*** Prepend element */
          instanceForest:
            INested(
              [addedElement, ...instanceSubTrees],
              subtreeSize + InstanceForest.getSubtreeSize(addedElement),
            ),
          enqueuedEffects,
        };
      | (
          INested(oldInstanceForests, _),
          Nested(oldReactElements),
          Nested(nextReactElements),
        )
          when
            List.length(nextReactElements)
            === List.length(oldInstanceForests) =>
        let keyTable =
          switch (updateContext.useKeyTable) {
          | None => OpaqueInstanceHash.createKeyTable(oldInstanceForest)
          | Some(keyTable) => keyTable
          };
        let (
          nearestHostOutputNode,
          newInstanceForests,
          subtreeSize,
          _indexShift,
          enqueuedEffects,
        ) =
          ListTR.fold3(
            (
              (
                nearestHostOutputNode,
                renderedElements,
                prevSubtreeSize,
                indexShift,
                enqueuedEffectsAcc,
              ),
              oldInstanceForest,
              oldReactElement,
              nextReactElement,
            ) => {
              let {
                indexShift,
                updatedRenderedElement: {
                  nearestHostOutputNode,
                  instanceForest,
                  enqueuedEffects,
                },
              } =
                updateChildRenderedElement(
                  ~updateContext={
                    ...updateContext,
                    nearestHostOutputNode,
                    useKeyTable: Some(keyTable),
                    absoluteSubtreeIndex: prevSubtreeSize,
                  },
                  ~indexShift,
                  ~oldInstanceForest,
                  ~oldReactElement,
                  ~nextReactElement,
                  (),
                );
              (
                nearestHostOutputNode,
                [instanceForest, ...renderedElements],
                prevSubtreeSize
                + InstanceForest.getSubtreeSize(instanceForest),
                indexShift,
                EffectSequence.chain(enqueuedEffects, enqueuedEffectsAcc),
              );
            },
            oldInstanceForests,
            oldReactElements,
            nextReactElements,
            (
              updateContext.nearestHostOutputNode,
              [],
              updateContext.absoluteSubtreeIndex,
              0,
              EffectSequence.noop,
            ),
          );
        let newInstanceForests = List.rev(newInstanceForests);
        {
          nearestHostOutputNode,
          instanceForest: INested(newInstanceForests, subtreeSize),
          enqueuedEffects,
        };
      /*
       * Key Policy for syntheticElement.
       * Nested elements determine shape: if the shape is not identical, re-render.
       * Flat elements use a positional match by default, where components at
       * the same position (from left) are matched for updates.
       * If the component has an explicit key, match the instance with the same key.
       * Note: components are matched for key across the entire syntheticElement structure.
       */
      | (
          IFlat(Instance(oldInstance) as oldOpaqueInstance),
          Flat(Element(_, _, oldKey)),
          Flat(Element(_, _, nextKey) as nextReactElement),
        ) =>
        if (nextKey !== oldKey) {
          /* Not found: render a new instance */
          let {
            nearestHostOutputNode,
            opaqueInstance: newOpaqueInstance,
            enqueuedEffects: mountEffects,
          } =
            renderElement(
              nextReactElement,
              ~nearestHostOutputNode=updateContext.nearestHostOutputNode,
            );
          let enqueuedEffects =
            Instance.pendingEffects(
              ~lifecycle=Unmount,
              ~nextEffects=mountEffects,
              ~instance=oldInstance,
            );
          let newInstanceForest = IFlat(newOpaqueInstance);
          {
            nearestHostOutputNode:
              SubtreeChange.replaceSubtree(
                ~parent=nearestHostOutputNode,
                ~prevChildren=
                  InstanceForest.outputTreeNodes(oldInstanceForest),
                ~nextChildren=
                  InstanceForest.outputTreeNodes(newInstanceForest),
                /* hard-coded zero since we will only ever have one child */
                ~absoluteSubtreeIndex=0,
              ),
            instanceForest: newInstanceForest,
            enqueuedEffects,
          };
        } else {
          let {
            nearestHostOutputNode,
            opaqueInstance: newOpaqueInstance,
            enqueuedEffects,
          } =
            updateOpaqueInstance(
              ~updateContext={...updateContext, useKeyTable: None},
              oldOpaqueInstance,
              nextReactElement,
            );
          {
            nearestHostOutputNode,
            instanceForest:
              oldOpaqueInstance !== newOpaqueInstance
                ? IFlat(newOpaqueInstance) : oldInstanceForest,
            enqueuedEffects,
          };
        }
      | (oldInstanceForest, _, _) =>
        /* Notice that all elements which are queried successfully
         *  from the hash table must have been here in the previous render
         * No, it's not true. What if the key is the same but element type changes
         * Wtf, stop thinking
         */
        let keyTable =
          switch (updateContext.useKeyTable) {
          | None => OpaqueInstanceHash.createKeyTable(oldInstanceForest)
          | Some(keyTable) => keyTable
          };
        let {
          nearestHostOutputNode,
          instanceForest: newInstanceForest,
          enqueuedEffects: mountEffects,
        } =
          renderReactElement(
            ~useKeyTable=keyTable,
            updateContext.nearestHostOutputNode,
            nextReactElement,
          );

        let enqueuedEffects =
          InstanceForest.pendingEffects(
            ~lifecycle=Hooks.Effect.Unmount,
            mountEffects,
            oldInstanceForest,
          );
        {
          nearestHostOutputNode:
            SubtreeChange.replaceSubtree(
              ~parent=nearestHostOutputNode,
              ~prevChildren=InstanceForest.outputTreeNodes(oldInstanceForest),
              ~nextChildren=InstanceForest.outputTreeNodes(newInstanceForest),
              ~absoluteSubtreeIndex=updateContext.absoluteSubtreeIndex,
            ),
          instanceForest: newInstanceForest,
          enqueuedEffects,
        };
      }
    and updateChildRenderedElement =
        (
          ~updateContext as {
            UpdateContext.shouldExecutePendingUpdates,
            useKeyTable,
            nearestHostOutputNode,
            absoluteSubtreeIndex,
          },
          ~indexShift,
          ~oldInstanceForest,
          ~oldReactElement,
          ~nextReactElement,
          (),
        )
        : childElementUpdate =>
      switch (oldInstanceForest, oldReactElement, nextReactElement) {
      /*
       * Key Policy for syntheticElement.
       * Nested elements determine shape: if the shape is not identical, re-render.
       * Flat elements use a positional match by default, where components at
       * the same position (from left) are matched for updates.
       * If the component has an explicit key, match the instance with the same key.
       * Note: components are matched for key across the entire syntheticElement structure.
       */
      | (
          IFlat(oldOpaqueInstance),
          Flat(Element(_, _, oldKey)),
          Flat(Element(_, _, nextKey) as nextReactElement),
        ) =>
        let keyTable =
          switch (useKeyTable) {
          | None =>
            OpaqueInstanceHash.createKeyTable(IFlat(oldOpaqueInstance))
          | Some(keyTable) => keyTable
          };
        let (
          nearestHostOutputNode,
          update,
          newOpaqueInstance,
          enqueuedEffects,
        ) =
          if (nextKey !== Key.none) {
            switch (OpaqueInstanceHash.lookupKey(keyTable, nextKey)) {
            | Some((subOpaqueInstance, previousIndex)) =>
              /* Instance tree with the same component key */
              let {
                nearestHostOutputNode,
                opaqueInstance: updatedOpaqueInstance,
                enqueuedEffects,
              } =
                updateOpaqueInstance(
                  ~updateContext=
                    UpdateContext.{
                      useKeyTable: None,
                      shouldExecutePendingUpdates,
                      nearestHostOutputNode,
                      absoluteSubtreeIndex: previousIndex + indexShift,
                    },
                  subOpaqueInstance,
                  nextReactElement,
                );
              (
                nearestHostOutputNode,
                `NoChangeOrNested(previousIndex),
                updatedOpaqueInstance,
                enqueuedEffects,
              );
            | None =>
              /* Not found: render a new instance */
              let {
                nearestHostOutputNode,
                opaqueInstance: newOpaqueInstance,
                enqueuedEffects,
              } =
                renderElement(~nearestHostOutputNode, nextReactElement);
              (
                nearestHostOutputNode,
                `NewElement,
                newOpaqueInstance,
                enqueuedEffects,
              );
            };
          } else {
            let {
              nearestHostOutputNode,
              opaqueInstance: updatedOpaqueInstance,
              enqueuedEffects,
            } =
              updateOpaqueInstance(
                ~updateContext=
                  UpdateContext.{
                    shouldExecutePendingUpdates,
                    nearestHostOutputNode,
                    absoluteSubtreeIndex,
                    useKeyTable: None,
                  },
                oldOpaqueInstance,
                nextReactElement,
              );
            (
              nearestHostOutputNode,
              `NoChangeOrNested(absoluteSubtreeIndex),
              updatedOpaqueInstance,
              enqueuedEffects,
            );
          };
        switch (update) {
        | `NewElement =>
          let newInstanceForest = IFlat(newOpaqueInstance);
          {
            updatedRenderedElement: {
              nearestHostOutputNode:
                SubtreeChange.replaceSubtree(
                  ~parent=nearestHostOutputNode,
                  ~prevChildren=
                    InstanceForest.outputTreeNodes(oldInstanceForest),
                  ~nextChildren=
                    InstanceForest.outputTreeNodes(newInstanceForest),
                  ~absoluteSubtreeIndex,
                ),
              instanceForest: newInstanceForest,
              enqueuedEffects,
            },
            indexShift: 0,
          };
        | `NoChangeOrNested(previousIndex) =>
          let changed = oldOpaqueInstance !== newOpaqueInstance;
          let element =
            changed ? IFlat(newOpaqueInstance) : oldInstanceForest;
          if (oldKey != nextKey) {
            {
              updatedRenderedElement: {
                nearestHostOutputNode:
                  SubtreeChange.reorder(
                    ~parent=nearestHostOutputNode,
                    ~instance=newOpaqueInstance,
                    ~indexShift,
                    ~from=previousIndex,
                    ~to_=absoluteSubtreeIndex,
                  ),
                instanceForest: element,
                enqueuedEffects,
              },
              indexShift: InstanceForest.getSubtreeSize(element),
            };
          } else {
            {
              updatedRenderedElement: {
                nearestHostOutputNode,

                instanceForest: element,
                enqueuedEffects,
              },
              indexShift: 0,
            };
          };
        };
      | (_, _, _) => {
          updatedRenderedElement:
            updateInstanceSubtree(
              ~updateContext={
                UpdateContext.absoluteSubtreeIndex,
                shouldExecutePendingUpdates,
                nearestHostOutputNode,
                /* Not sure about this */
                useKeyTable,
              },
              ~oldInstanceForest,
              ~oldReactElement,
              ~nextReactElement,
              (),
            ),
          indexShift: 0,
        }
      };

    /**
     * Execute the pending updates at the top level of an instance tree.
     * If no state change is performed, the argument is returned unchanged.
     */
    let flushPendingUpdates = (opaqueInstance, nearestHostOutputNode) => {
      let Instance({element}) = opaqueInstance;
      updateOpaqueInstance(
        ~updateContext=
          UpdateContext.{
            useKeyTable: None,
            shouldExecutePendingUpdates: true,
            nearestHostOutputNode,
            absoluteSubtreeIndex: 0,
          },
        opaqueInstance,
        element,
      );
    };
  };

  module RenderedElement = {
    /**
     * Rendering produces a list of instance trees.
     */
    type t = renderedElement;

    let listToRenderedElement = renderedElements =>
      INested(
        renderedElements,
        renderedElements
        |> List.fold_left(
             (acc, e) => acc + InstanceForest.getSubtreeSize(e),
             0,
           ),
      );
    let render = (nearestHostOutputNode: OutputTree.node, syntheticElement): t => {
      let (instanceForest, mountEffects) = Instance.ofList(syntheticElement);
      {
        instanceForest,
        nearestHostOutputNode:
          lazy (
            Node(
              InstanceForest.outputTreeNodes(instanceForest)
              |> List.fold_left(
                   ((position, parent), child) =>
                     (
                       position + 1,
                       {
                         let Node(child) | UpdatedNode(_, child) =
                           Lazy.force(child);
                         let parent =
                           OutputTree.insertNode(~parent, ~child, ~position);
                         parent;
                       },
                     ),
                   (0, nearestHostOutputNode),
                 )
              |> snd,
            )
          ),
        enqueuedEffects: mountEffects,
      };
    };
    let update =
        (
          ~previousElement,
          ~renderedElement as {instanceForest, nearestHostOutputNode}: t,
          nextReactElement,
        )
        : t =>
      Render.updateInstanceSubtree(
        ~updateContext=
          Render.UpdateContext.{
            nearestHostOutputNode,
            absoluteSubtreeIndex: 0,
            useKeyTable: None,
            shouldExecutePendingUpdates: false,
          },
        ~oldInstanceForest=instanceForest,
        ~oldReactElement=previousElement,
        ~nextReactElement,
        (),
      );

    let rec map =
            (f, renderedElement, nearestHostOutputNode: outputNodeContainer) =>
      switch (renderedElement) {
      | IFlat(e) =>
        let {nearestHostOutputNode, opaqueInstance, enqueuedEffects} =
          f(e, nearestHostOutputNode);
        let unchanged = e === opaqueInstance;

        {
          nearestHostOutputNode,
          instanceForest: unchanged ? renderedElement : IFlat(opaqueInstance),
          enqueuedEffects,
        };
      | INested(l, _) =>
        let (nextL, nearestHostOutputNode, effects) =
          List.fold_left(
            (
              (acc, nearestHostOutputNode: outputNodeContainer, effectsAcc),
              renderedElement,
            ) => {
              let {
                nearestHostOutputNode,
                instanceForest: next,
                enqueuedEffects,
              } =
                map(f, renderedElement, nearestHostOutputNode);
              (
                [next, ...acc],
                nearestHostOutputNode,
                EffectSequence.chain(effectsAcc, enqueuedEffects),
              );
            },
            ([], nearestHostOutputNode, EffectSequence.noop),
            List.rev(l): list(instanceForest),
          );
        let unchanged = List.for_all2((===), l, nextL);
        {
          nearestHostOutputNode,
          instanceForest:
            unchanged
              ? renderedElement
              : INested(
                  nextL,
                  List.fold_left(
                    (acc, elem) => InstanceForest.getSubtreeSize(elem) + acc,
                    0,
                    nextL,
                  ),
                ),
          enqueuedEffects: effects,
        };
      };

    /**
     * Flush the pending updates in an instance tree.
     */
    let flushPendingUpdates =
        ({instanceForest, nearestHostOutputNode, enqueuedEffects}: t): t => {
      let {
        nearestHostOutputNode,
        instanceForest: newInstanceForest,
        enqueuedEffects: nextEnqueuedEffects,
      } =
        map(
          Render.flushPendingUpdates,
          instanceForest,
          nearestHostOutputNode,
        );
      {
        instanceForest: newInstanceForest,
        nearestHostOutputNode,
        enqueuedEffects:
          EffectSequence.chain(nextEnqueuedEffects, enqueuedEffects),
      };
    };

    let executeHostViewUpdates = ({nearestHostOutputNode}: t) => {
      let Node(hostView) | UpdatedNode(_, hostView) =
        Lazy.force(nearestHostOutputNode);
      hostView;
    };

    let executePendingEffects = ({enqueuedEffects} as renderedElement: t) => {
      enqueuedEffects();
      {...renderedElement, enqueuedEffects: EffectSequence.noop};
    };
  };

  let listToElement = l => Nested(l);
  let empty = Nested([]);

  module Hooks = Hooks;
  module RemoteAction = RemoteAction;

  let component:
    type hooks initialHooks renderFunctionImpl.
      (
        ~useDynamicKey: bool=?,
        renderFunction(hooks, initialHooks, renderFunctionImpl)
      ) =>
      component(
        hooks,
        initialHooks,
        syntheticElement,
        outputNodeGroup,
        renderFunctionImpl,
      ) =
    (~useDynamicKey=false, f) => {
      module Component = {
        type id('a) +=
          | Id: id(
                  instance(
                    hooks,
                    initialHooks,
                    syntheticElement,
                    outputNodeGroup,
                    renderFunctionImpl,
                  ),
                );

        let eq:
          type c.
            (
              c,
              id(c),
              id(
                instance(
                  hooks,
                  initialHooks,
                  syntheticElement,
                  outputNodeGroup,
                  renderFunctionImpl,
                ),
              )
            ) =>
            option(
              instance(
                hooks,
                initialHooks,
                syntheticElement,
                outputNodeGroup,
                renderFunctionImpl,
              ),
            ) =
          (instance, id1, id2) => {
            switch (id1, id2) {
            | (Id, Id) => Some(instance)
            | (_, _) => None
            };
          };
      };
      {
        render: f,
        id: Component.Id,
        elementType: React,
        debugName: "",
        eq: Component.eq,
        useDynamicKey,
      };
    };

  let nativeComponent:
    type hooks initialHooks renderFunctionImpl.
      (
        ~useDynamicKey: bool=?,
        renderFunction(hooks, initialHooks, renderFunctionImpl)
      ) =>
      component(
        hooks,
        initialHooks,
        outputTreeElement,
        outputNodeContainer,
        renderFunctionImpl,
      ) =
    (~useDynamicKey=false, f) => {
      module Component = {
        type id('a) +=
          | Id: id(
                  instance(
                    hooks,
                    initialHooks,
                    outputTreeElement,
                    outputNodeContainer,
                    renderFunctionImpl,
                  ),
                );

        let eq:
          type c.
            (
              c,
              id(c),
              id(
                instance(
                  hooks,
                  initialHooks,
                  outputTreeElement,
                  outputNodeContainer,
                  renderFunctionImpl,
                ),
              )
            ) =>
            option(
              instance(
                hooks,
                initialHooks,
                outputTreeElement,
                outputNodeContainer,
                renderFunctionImpl,
              ),
            ) =
          (instance, id1, id2) => {
            switch (id1, id2) {
            | (Id, Id) => Some(instance)
            | (_, _) => None
            };
          };
      };
      {
        render: f,
        id: Component.Id,
        elementType: Host,
        debugName: "",
        eq: Component.eq,
        useDynamicKey,
      };
    };

  let element = (~key=Key.none, ~debugName, render, component) => {
    let key =
      key != Key.none
        ? key
        : {
          component.useDynamicKey ? Key.create() : Key.none;
        };

    Flat(Element(render, {...component, debugName}, key));
  };
};

module Hooks = Hooks;
module RemoteAction = RemoteAction;
