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

type nodeUpdate('host) =
  | Node('host)
  | UpdatedNode('host, 'host);

type outputNodeContainer('node) = Lazy.t(nodeUpdate('node));

type outputNodeGroup('node) = list(outputNodeContainer('node));

type id('a) = ..;

type instance('hooks, 'elementType, 'outputNode, 'node, 'childNode) = {
  hooks: Hooks.state('hooks),
  component: component('hooks, 'elementType, 'outputNode, 'node, 'childNode),
  element: element('node),
  instanceSubForest: instanceForest('childNode),
  subElements: 'elementType,
  hostInstance: 'outputNode,
}
and element('node) =
  | Element(component('hooks, 'elementType, 'outputNode, 'node, 'childNode))
    : element('node)
and syntheticElement('node) =
  | Flat(element('node))
  | Nested(list(syntheticElement('node)))
and outputTreeElement('node, 'childNode) = {
  make: unit => 'node,
  configureInstance: (~isFirstRender: bool, 'node) => 'node,
  children: syntheticElement('childNode),
  insertNode: (~parent: 'node, ~child: 'childNode, ~position: int) => 'node,
}
and elementType('elementType, 'outputNode, 'node, 'childNode) =
  | Host: elementType(
            outputTreeElement('node, 'childNode),
            outputNodeContainer('node),
            'node,
            'childNode,
          )
  | React: elementType(
             syntheticElement('node),
             outputNodeGroup('node),
             'node,
             'childNode,
           )
and instanceForest('node) =
  | IFlat(opaqueInstance('node))
  | INested(list(instanceForest('node)), int /*subtree size*/)
and component('hooks, 'elementType, 'outputNode, 'node, 'childNode) = {
  debugName: string,
  key: int,
  elementType: elementType('elementType, 'outputNode, 'node, 'childNode),
  id: id(instance('hooks, 'elementType, 'outputNode, 'node, 'childNode)),
  eq:
    'a.
    (
      'a,
      id('a),
      id(instance('hooks, 'elementType, 'outputNode, 'node, 'childNode))
    ) =>
    option(instance('hooks, 'elementType, 'outputNode, 'node, 'childNode)),

  render:
    Hooks.t('hooks, 'hooks) => ('elementType, Hooks.t(Hooks.nil, 'hooks)),
}
and opaqueInstance('node) =
  | Instance(instance('hooks, 'elementType, 'outputNode, 'node, 'childNode))
    : opaqueInstance('node);

type renderedElement('node) = {
  nearestHostOutputNode: outputNodeContainer('node),
  instanceForest: instanceForest('node),
  enqueuedEffects: EffectSequence.t,
};

type opaqueInstanceUpdate('node) = {
  nearestHostOutputNode: outputNodeContainer('node),
  opaqueInstance: opaqueInstance('node),
  enqueuedEffects: EffectSequence.t,
};

module InstanceForest = {
  let getSubtreeSize: type node. instanceForest(node) => int =
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

  let outputTreeNodes:
    type node. instanceForest(node) => outputNodeGroup(node) =
    subtree =>
      flatten(subtree)
      |> List.fold_left(
           (
             acc: outputNodeGroup(node),
             Instance({component: {elementType}, hostInstance}):
               opaqueInstance(node),
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
        EffectSequence.chain(
          Hooks.pendingEffects(~lifecycle, Some(hooks)),
          acc,
        ),
      acc,
      instanceForest,
    );
  };
};

module SyntheticElement = {
  let rec map = (f, syntheticElement) =>
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
  let rec fold = (f, renderedElement, nearestHostOutputNode) =>
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
  let make =
      (
        type elementType_,
        type outputNode,
        type node_,
        type childNode,
        elementType: elementType(elementType_, outputNode, node_, childNode),
        subElements: elementType_,
        instanceSubTree: instanceForest(childNode),
      ) =>
    switch (elementType) {
    | Host =>
      lazy({
        let instance =
          subElements.make()
          |> subElements.configureInstance(~isFirstRender=true);
        (
          Node(
            List.fold_left(
              ((position, parent), child) =>
                (
                  position + 1,
                  {
                    let Node(child) | UpdatedNode(_, child) =
                      Lazy.force(child);
                    subElements.insertNode(~parent, ~child, ~position);
                  },
                ),
              (0, instance),
              InstanceForest.outputTreeNodes(instanceSubTree),
            )
            |> snd,
          ):
            internalOutputNode(node_)
        );
      })
    | React => InstanceForest.outputTreeNodes(instanceSubTree)
    };
};

module SubtreeChange = {
  let insertNodes =
      (
        ~insertNode,
        ~parent as parentWrapper,
        ~children,
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
              insertNode(~parent, ~child, ~position);
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
        ~deleteNode,
        ~parent as parentWrapper,
        ~children,
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
              deleteNode(~parent, ~child, ~position);
            },
          ),
        (initialPosition, oldParent),
        children,
      )
      |> snd;
    newParent === oldParent
      ? parentWrapper : UpdatedNode(oldParent, newParent);
  };

  let prependElement = (~insertNode, ~parent, ~children) =>
    lazy(
      insertNodes(
        ~insertNode,
        ~parent=Lazy.force(parent),
        ~children,
        ~position=0,
      )
    );

  let replaceSubtree =
      (
        ~insertNode,
        ~deleteNode,
        ~parent,
        ~prevChildren,
        ~nextChildren,
        ~absoluteSubtreeIndex: int,
      ) =>
    lazy(
      {
        insertNodes(
          ~insertNode,
          ~parent=
            deleteNodes(
              ~deleteNode,
              ~parent=Lazy.force(parent),
              ~children=prevChildren,
              ~position=absoluteSubtreeIndex,
            ),
          ~children=nextChildren,
          ~position=absoluteSubtreeIndex,
        );
      }
    );

  let reorderNode =
      (
        ~moveNode,
        ~insertNode,
        ~deleteNode,
        ~child,
        ~parent,
        ~indexShift: int,
        ~from: int,
        ~to_: int,
      ) => {
    let isVal = Lazy.is_val(child);
    switch (Lazy.force(child)) {
    | Node(child) =>
      from === to_ - indexShift
        ? parent : moveNode(~parent, ~child, ~from, ~to_)
    | UpdatedNode(prevChild, child) when !isVal =>
      insertNode(
        ~parent=deleteNode(~parent, ~child=prevChild, ~position=from),
        ~child,
        ~position=to_,
      )
    | UpdatedNode(_prevChild, child) =>
      from === to_ - indexShift
        ? parent : moveNode(~parent, ~child, ~from, ~to_)
    };
  };

  let reorder =
      (
        type node,
        type child,
        ~moveNode:
           (~parent: node, ~child: child, ~from: int, ~to_: int) => node,
        ~insertNode: (~parent: node, ~child: child, ~position: int) => node,
        ~deleteNode: (~parent: node, ~child: child, ~position: int) => node,
        ~parent: outputNodeContainer(node),
        ~instance as
          Instance({hostInstance, component: {elementType}}):
            opaqueInstance(child),
        ~indexShift,
        ~from,
        ~to_,
      ) =>
    switch (elementType) {
    | Host =>
      lazy({
        let parentWrapper = Lazy.force(parent);
        let Node(oldParent) | UpdatedNode(_, oldParent) = parentWrapper;
        let newParent =
          reorderNode(
            ~insertNode,
            ~deleteNode,
            ~moveNode,
            ~parent=oldParent,
            ~child=hostInstance,
            ~indexShift,
            ~from,
            ~to_,
          );
        newParent === oldParent
          ? parentWrapper : UpdatedNode(oldParent, newParent);
      })
    | React =>
      lazy({
        let parentWrapper = Lazy.force(parent);
        let Node(oldParent) | UpdatedNode(_, oldParent) = parentWrapper;
        let newParent =
          List.fold_left(
            ((index, parent), child) =>
              (
                index + 1,
                reorderNode(
                  ~insertNode,
                  ~deleteNode,
                  ~moveNode,
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
      })
    };

  let updateNodes =
      (
        ~insertNode,
        ~deleteNode,
        ~parent,
        ~instanceForest,
        ~position as initialPosition,
      ) =>
    lazy({
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
                insertNode(
                  ~parent=
                    deleteNode(~parent=instance, ~child=oldNode, ~position),
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
    });
};

module OpaqueInstanceHash = {
  type t('node) = lazy_t(Hashtbl.t(int, (opaqueInstance('node), int)));
  let addOpaqueInstance = (idTable, index, opaqueInstance) => {
    let Instance({component: {key}}) = opaqueInstance;
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
    lazy({
      let keyTable = Hashtbl.create(1);
      addRenderedElement(keyTable, renderedElement, 0);
      keyTable;
    });
  let lookupKey = (table, key) => {
    let keyTable = Lazy.force(table);
    try(Some(Hashtbl.find(keyTable, key))) {
    | Not_found => None
    };
  };
};

module Instance = {
  let rec ofComponent =
          (
            type node,
            type childNode,
            component: component(_, _, _, node, childNode),
          ) => {
    let (subElements, hooks) =
      component.render(
        Hooks.ofState(None, ~onStateDidChange=() => {
          /* OutputTree.markAsStale */
          ()
        }),
      );
    let hooks = Hooks.toState(hooks);
    let children: syntheticElement(node) =
      switch (component.elementType) {
      | React => subElements
      | Host => subElements.children
      };
    let (instanceSubForest, mountEffects) = ofList(children);
    (
      Instance({
        hooks,
        element,
        component,
        subElements,
        instanceSubForest,
        hostInstance:
          Node.make(component.elementType, subElements, instanceSubForest),
      }),
      EffectSequence.chain(
        Hooks.pendingEffects(~lifecycle=Hooks.Effect.Mount, Some(hooks)),
        mountEffects,
      ),
    );
  }
  and ofElement:
    type node. element(node) => (opaqueInstance(node), EffectSequence.t) =
    (Element(component) as element) => {
      let (subElements, hooks) =
        component.render(
          Hooks.ofState(None, ~onStateDidChange=() => {
            /* OutputTree.markAsStale */
            ()
          }),
        );
      let hooks = Hooks.toState(hooks);
      let children: syntheticElement(node) =
        switch (component.elementType) {
        | React => subElements
        | Host => subElements.children
        };
      let (instanceSubForest, mountEffects) = ofList(children);
      (
        Instance({
          hooks,
          element,
          component,
          subElements,
          instanceSubForest,
          hostInstance:
            Node.make(component.elementType, subElements, instanceSubForest),
        }),
        EffectSequence.chain(
          Hooks.pendingEffects(~lifecycle=Hooks.Effect.Mount, Some(hooks)),
          mountEffects,
        ),
      );
    }

  and ofList:
    type node.
      syntheticElement(node) => (instanceForest(node), EffectSequence.t) =
    syntheticElement => SyntheticElement.map(ofElement, syntheticElement);

  let pendingEffects =
      (~lifecycle, ~nextEffects, ~instance as {instanceSubForest, hooks}) => {
    InstanceForest.pendingEffects(
      ~lifecycle,
      EffectSequence.chain(
        Hooks.pendingEffects(~lifecycle, Some(hooks)),
        nextEffects,
      ),
      instanceSubForest,
    );
  };
};

module Render = {
  let getOpaqueInstance = (~useKeyTable, Element({key})) =>
    switch (useKeyTable) {
    | None => None
    | Some(keyTable) => OpaqueInstanceHash.lookupKey(keyTable, key)
    };

  type childElementUpdate('node) = {
    updatedRenderedElement: renderedElement('node),
    /* This represents the way previously rendered elements have been shifted due to moves */
    indexShift: int,
  };

  module UpdateContext = {
    type t('node) = {
      shouldExecutePendingUpdates: bool,
      useKeyTable: option(OpaqueInstanceHash.t('node)),
      /* This is a unique index of an element within a subtree,
        * thanks to tracking it we can efficiently manage moves of within a subtree
       */
      nearestHostOutputNode: outputNodeContainer('node),
      absoluteSubtreeIndex: int,
    };
  };

  /**
     * Initial render of an Element. Recurses to produce the entire tree of
     * instances.
     */
  let rec renderElement = (~useKeyTable=?, ~nearestHostOutputNode, element) =>
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
      (~useKeyTable=?, nearestHostOutputNode, syntheticElement) =>
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
        ~updateContext,
        Instance(instance) as originalOpaqueInstance,
        Element(nextComponent) as nextElement,
      ) => {
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
      let {component} = instance;
      switch (
        nextComponent.eq(
          {...instance, hooks: nextState},
          component.id,
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
        let (opaqueInstance, mountEffects) = Instance.ofElement(nextElement);
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
  and updateInstance =
      (
        ~originalOpaqueInstance,
        ~updateContext,
        ~nextComponent,
        ~nextElement,
        ~stateChanged,
        instance,
      ) => {
    let updatedInstanceWithNewElement = {
      ...instance,
      component: nextComponent,
      element: nextElement,
    };

    let shouldRerender = stateChanged || nextElement !== instance.element;

    let (nextSubElements, initialHooks) =
      if (shouldRerender) {
        let (nextElement, initialHooks) =
          nextComponent.render(
            Hooks.ofState(
              Some(updatedInstanceWithNewElement.hooks),
              ~onStateDidChange=OutputTree.markAsStale,
            ),
          );
        (nextElement, Hooks.toState(initialHooks));
      } else {
        (instance.subElements, instance.hooks);
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
                lazy({
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
                }),
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
        if (nextInstanceSubForest !== instanceWithNewHostView.instanceSubForest) {
          (
            updateContext.nearestHostOutputNode,
            {
              ...instanceWithNewHostView,
              instanceSubForest: nextInstanceSubForest,
              subElements: nextSubElements,
              hostInstance,
            }:
              instance(hooks, elementType, outputNodeType),
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
              Some(updatedInstanceWithNewSubtree.hooks),
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
        when nextReactElements === oldReactElements && GlobalState.useTailHack^ =>
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
          List.length(nextReactElements) === List.length(oldInstanceForests) =>
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
              prevSubtreeSize + InstanceForest.getSubtreeSize(instanceForest),
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
        Flat(Element({key: oldKey})),
        Flat(Element({key: nextKey}) as nextReactElement),
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
              ~prevChildren=InstanceForest.outputTreeNodes(oldInstanceForest),
              ~nextChildren=InstanceForest.outputTreeNodes(newInstanceForest),
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
        Flat(Element({key: oldKey})),
        Flat(Element({key: nextKey}) as nextReactElement),
      ) =>
      let keyTable =
        switch (useKeyTable) {
        | None => OpaqueInstanceHash.createKeyTable(IFlat(oldOpaqueInstance))
        | Some(keyTable) => keyTable
        };
      let (nearestHostOutputNode, update, newOpaqueInstance, enqueuedEffects) = {
        let Element(component) = nextReactElement;
        if (component.key !== Key.none) {
          switch (OpaqueInstanceHash.lookupKey(keyTable, component.key)) {
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
        let element = changed ? IFlat(newOpaqueInstance) : oldInstanceForest;
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
        lazy(
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
            let {nearestHostOutputNode, instanceForest: next, enqueuedEffects} =
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
      map(Render.flushPendingUpdates, instanceForest, nearestHostOutputNode);
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

let element = (~key as argumentKey=Key.none, component) => {
  let key =
    argumentKey != Key.none
      ? argumentKey
      : {
        let isDynamicKey = component.key == Key.dynamicKeyMagicNumber;
        isDynamicKey ? Key.create() : Key.none;
      };
  let componentWithKey =
    key != component.key ? {...component, key} : component;
  Flat(Element(componentWithKey));
};

let listToElement = l => Nested(l);
let empty = Nested([]);

module Hooks = Hooks;
module RemoteAction = RemoteAction;

module Expert = {
  let jsx_list = listToElement;
  let component:
    type a.
      (
        ~useDynamicKey: bool=?,
        string,
        ~key: Key.t=?,
        Hooks.t(a, a) => (syntheticElement, Hooks.t(Hooks.nil, a))
      ) =>
      syntheticElement =
    (~useDynamicKey=false, debugName) => {
      module Component = {
        type id('a) +=
          | Id: id(instance(a, syntheticElement, outputNodeGroup));

        let eq:
          type c.
            (
              c,
              id(c),
              id(instance(a, syntheticElement, outputNodeGroup))
            ) =>
            option(instance(a, syntheticElement, outputNodeGroup)) =
          (instance, id1, id2) => {
            switch (id1, id2) {
            | (Id, Id) => Some(instance)
            | (_, _) => None
            };
          };
      };
      (~key=?, render) =>
        element(
          ~key?,
          {
            debugName,
            elementType: React,
            key: useDynamicKey ? Key.dynamicKeyMagicNumber : Key.none,
            id: Component.Id,
            eq: Component.eq,
            render,
          },
        );
    };

  let nativeComponent:
    type a.
      (
        ~useDynamicKey: bool=?,
        string,
        ~key: Key.t=?,
        Hooks.t(a, a) => (outputTreeElement, Hooks.t(Hooks.nil, a))
      ) =>
      syntheticElement =
    (~useDynamicKey=false, debugName) => {
      module Component = {
        type id('a) +=
          | Id: id(instance(a, outputTreeElement, outputNodeContainer));

        let eq:
          type c.
            (
              c,
              id(c),
              id(instance(a, outputTreeElement, outputNodeContainer))
            ) =>
            option(instance(a, outputTreeElement, outputNodeContainer)) =
          (instance, id1, id2) => {
            switch (id1, id2) {
            | (Id, Id) => Some(instance)
            | (_, _) => None
            };
          };
      };
      (~key=?, render) =>
        element(
          ~key?,
          {
            debugName,
            elementType: Host,
            key: useDynamicKey ? Key.dynamicKeyMagicNumber : Key.none,
            id: Component.Id,
            eq: Component.eq,
            render,
          },
        );
    };
};
let component = (~useDynamicKey=?, debugName) => {
  let c = Expert.component(~useDynamicKey?, debugName);
  (~key=?, render) => {
    c(
      ~key?,
      hooks => {
        let (hooks, e) = render(hooks);
        (e, hooks);
      },
    );
  };
};
let nativeComponent = (~useDynamicKey=?, debugName) => {
  let c = Expert.nativeComponent(~useDynamicKey?, debugName);
  (~key=?, render) => {
    c(
      ~key?,
      hooks => {
        let (hooks, e) = render(hooks);
        (e, hooks);
      },
    );
  };
};

module Hooks = Hooks;
module RemoteAction = RemoteAction;
