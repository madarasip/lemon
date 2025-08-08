// Copyright (c) 2025 Peter Madarasi
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to
// deal in the Software without restriction, including without limitation the
// rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
// sell copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
// FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS
// IN THE SOFTWARE.

#ifndef LEMON_SPARSITY_H
#define LEMON_SPARSITY_H

/// \file
/// \brief Algorithms for finding uniformly sparse subgraphs.

#include <lemon/bin_heap.h>
#include <lemon/bucket_heap.h>
#include <lemon/connectivity.h>
#include <lemon/lgf_writer.h>
#include <lemon/list_graph.h>
#include <lemon/maps.h>
#include <lemon/unionfind.h>

#include <limits>
#include <type_traits>
#include <vector>


namespace lemon {
  namespace unisparse_bits {

    // Fill a map with a given value
    template<typename GR, typename Key, class... Args,
             template<typename, typename...> class Map>
    void smartMapFill(const GR& g, Map<Key, Args...>& map,
                      const typename Map<Key, Args...>::Value& v)
    {
      mapFill(g, map, v);
    }

    // For a NullMap, fill should do nothing
    template<typename GR, typename Key, class... Args>
    void smartMapFill(const GR&, NullMap<Key, Args...>&,
                      typename NullMap<Key, Args...>::Value)
    {}

    // Test in compile time whether T is a specialization of Templ
    template<typename T, template<typename...> class Templ>
    struct isSpecialization : std::false_type {};

    template<template<typename...> class Templ, typename... Args>
    struct isSpecialization<Templ<Args...>, Templ> : std::true_type {};

    template<typename M>
    constexpr bool isNullMap()
    {
      return isSpecialization<M, NullMap>::value;
    }

    template<typename M>
    constexpr bool isConstMap()
    {
      return isSpecialization<M, ConstMap>::value;
    }

    /// \brief A simplified, efficient implementation of the BFS algorithm.
    ///
    /// This class provides an implementation of the BFS algorithm tailored to
    /// the needs of the \ref UniSparse class. Only the predecessor and the
    /// reached maps are maintained. Furthermore, the re-initialization is also
    /// more efficient.
    template<class Digraph>
    class Bfs {
    protected:
      TEMPLATE_DIGRAPH_TYPEDEFS(Digraph);

    public:
      using PredMap = typename Digraph::template NodeMap<Arc>;
      using ReachedMap = typename Digraph::template NodeMap<bool>;

    protected:
      const Digraph& _dg;
      PredMap _pred;
      ReachedMap _reached;

      std::vector<Node> _queue;
      int _queue_head, _queue_tail;
      const int _numNodes;

    public:
      Bfs(const Digraph& dg, const int numNodes)
        : _dg(dg), _pred(_dg), _reached(_dg), _queue_head(0), _queue_tail(0),
          _numNodes(numNodes)
      {}

    private:
      Bfs(const Digraph& dg) : Bfs(dg, countNodes(dg))
      {}

    public:
      void init()
      {
        LEMON_ASSERT(_numNodes == countNodes(_dg), "Bad number of nodes!");
        _queue.resize(_numNodes);
        if(_queue_head < static_cast<int>(_queue.size()) / 2) {
          for(int i = 0; i < _queue_head; ++i) {
            _reached.set(_queue[i], false);
          }
        }
        else {
          for(NodeIt n(_dg); n != INVALID; ++n) {
            _reached.set(n, false);
          }
        }
        _queue_head = _queue_tail = 0;
      }

      void addSource(const Node s)
      {
        if(!_reached[s]) {
          _reached.set(s, true);
          _pred.set(s, INVALID);
          _queue[_queue_head++] = s;
        }
      }

      Node processNextNode()
      {
        const Node u = _queue[_queue_tail++];
        Node v;
        for(OutArcIt e(_dg, u); e != INVALID; ++e) {
          if(!_reached[v = _dg.target(e)]) {
            _queue[_queue_head++] = v;
            _reached.set(v, true);
            _pred.set(v, e);
          }
        }
        return u;
      }

      bool emptyQueue() const
      {
        return _queue_tail == _queue_head;
      }

      void start()
      {
        while(!emptyQueue()) {
          processNextNode();
        }
      }

      // returns whether at least k nodes can be reached
      bool isAtLeastKNodesReachable(const int k)
      {
        if(_queue_head >= k) {
          return true;
        }
        while(!emptyQueue()) {
          const Node u = _queue[_queue_tail++];
          for(OutArcIt e(_dg, u); e != INVALID; ++e) {
            const Node t = _dg.target(e);
            if(!_reached[t]) {
              _queue[_queue_head] = t;
              if(++_queue_head == k) {
                return true;
              }
              _reached.set(t, true);
              _pred.set(t, e);
            }
          }
        }
        return false;
      }

      // finds a node other than the sources with degree smaller than k
      template<typename DegMap>
      Node findNodeWithDegLeqK(const DegMap& deg, const int k)
      {
        while(!emptyQueue()) {
          const Node u = _queue[_queue_tail++];
          for(OutArcIt e(_dg, u); e != INVALID; ++e) {
            const Node t = _dg.target(e);
            if(!_reached[t]) {
              _queue[_queue_head++] = t;
              _reached.set(t, true);
              _pred.set(t, e);
              if(deg[t] < k) {
                return t;
              }
            }
          }
        }
        return INVALID;
      }

      // finds a node other than the sources with degree smaller than k
      bool anyReachable(const Node t1, const Node t2)
      {
        while(!emptyQueue()) {
          const Node u = _queue[_queue_tail++];
          for(OutArcIt e(_dg, u); e != INVALID; ++e) {
            const Node t = _dg.target(e);
            if(!_reached[t]) {
              _queue[_queue_head++] = t;
              _reached.set(t, true);
              _pred.set(t, e);
              if(t == t1 || t == t2) {
                return true;
              }
            }
          }
        }
        return false;
      }

      Arc predArc(const Node n) const
      {
        return _pred[n];
      }

      bool reached(const Node n) const
      {
        return _reached[n];
      }

      const ReachedMap& reachedMap() const
      {
        return _reached;
      }
    };

    /// \brief Template to make STL iterators from (UniSparse) iterators.
    ///
    /// This class template makes an STL iterator from iterators with given
    /// ctor args.
    ///
    /// \tparam IT The type of the iterator.
    /// \tparam CTOR The iterator constructor type.
    template<typename IT, typename... CTOR>
    struct IterWrapper
      : public IT, public std::iterator<std::input_iterator_tag, IT> {
      IterWrapper(const CTOR&... ctor) : IT(ctor...)
      {}

      IterWrapper(Invalid) : IT(INVALID)
      {}

      const IT& operator*() const
      {
        return static_cast<const IT&>(*this);
      }

      using IT::operator++;
    };

    // C++11 implementation of index_sequence (introduced in C++14)
    template<std::size_t... Is>
    struct index_sequence {};

    template<std::size_t N, std::size_t... Is>
    struct make_index_sequence : make_index_sequence<N - 1, N - 1, Is...> {};

    template<std::size_t... Is>
    struct make_index_sequence<0, Is...> : index_sequence<Is...> {};

    template<typename... Ts>
    using index_sequence_for = make_index_sequence<sizeof...(Ts)>;

    /// \brief A generic wrapper for range-based for loops.
    ///
    /// This template wraps an iterator and provides begin() and end() to make
    /// range-based for loops and STL algorithms work.
    ///
    /// \tparam IT The type of the UniSparse iterator.
    /// \tparam CTOR The iterator constructor type.
    template<typename USI, typename... CTOR>
    class RangeWrapperMoveOnly {
      using It = IterWrapper<USI, CTOR...>;
      const std::tuple<const CTOR&...> _ctor_args;

    public:
      RangeWrapperMoveOnly(const CTOR&... ctor) : _ctor_args(ctor...)
      {}

      template<std::size_t... Is>
      It createIterator(index_sequence<Is...>) const
      {
        return It(std::get<Is>(_ctor_args)...); // move or rvo
      }

      It begin() const
      {
        return createIterator(index_sequence_for<CTOR...>{}); // move or rvo
      }

      It end() const
      {
        return It(INVALID);
      }
    };

    // Creates an indicator map from the values written to this map.
    template<typename IndMap, typename Edge>
    class IndMapSetter {
      IndMap& _im;
    public:
      IndMapSetter(IndMap& im) : _im(im)
      {}

      template<typename T>
      void set(const T&, const Edge e)
      {
        _im.set(e, true);
      }
    };

    // assigns value to unordered pairs of nodes, edges or arcs
    template<typename GR,                  // the type of the graph
             typename KeyToIndexMap,       // maps nodes/edges/arcs to indices
             typename Value>               // what to assign to item pairs
    class UnorderedPairMap {
      using Graph = GR;
      using Key = typename KeyToIndexMap::Key;
      using Index = typename KeyToIndexMap::Value;

      KeyToIndexMap keyToInd;
      std::vector<Value> data;

      // assumes j <= i
      Index toOneDim(const Index i, const Index j) const
      {
        LEMON_ASSERT(j <= i, "Bad lower triangle index!");
        return i*(i+1)/2 + j;   // lower triangular, row-major representation
      }

    public:
      UnorderedPairMap(const Graph& g, const int numNodes)
        : keyToInd(g), data(toOneDim(numNodes, 0))
      {
        typedef typename ItemSetTraits<Graph, Key>::ItemIt KeyIt;
        Index i = 0;
        for(KeyIt it(g); it != INVALID; ++it) {
          keyToInd.set(it, i++);
        }
      }

      Value get(const Key u, const Key v) const
      {
        const Index i = keyToInd[u];
        const Index j = keyToInd[v];
        return data[i <= j ? toOneDim(j, i) : toOneDim(i, j)];
      }

      void set(const Key u, const Key v, const Value val)
      {
        const Index i = keyToInd[u];
        const Index j = keyToInd[v];
        data[i <= j ? toOneDim(j, i) : toOneDim(i, j)] = val;
      }
    };

    class LowerRange;
    class UpperRange;
    class UnknownRange;
  } // namespace unisparse_bits


  /// \brief Default traits class of \c UniSparse class.
  ///
  /// Default traits class of \c UniSparse class.
  /// \tparam GR The type of the undirected graph.
  template<typename GR>
  struct UniSparseDefaultTraits {
    /// \brief The type of the undirected graph the algorithm runs on.
    ///
    /// The type of the undirected graph the algorithm runs on.
    using Graph = GR;

    /// \brief The type of the inner digraph.
    ///
    /// The type of the inner digraph.
    /// It must provide \p addNode(), \p addArc(), \p reverseArc()
    /// and \p clear() member functions.
    using Digraph = ListDigraph;

    /// \brief Instantiates a \c Digraph.
    ///
    /// This function instantiates a \c Digraph.
    static Digraph* createInnerDigraph()
    {
      return new Digraph;
    }

    /// \brief The type of the container that list the edges from best to
    /// worst.
    ///
    /// This container either provides the order in which the edges are to be
    /// processed or serves as the container in which the edges will be sorted
    /// by their weights if the weight map is set.
    ///
    /// It must provide \p size(), \p resize(), \p operator[], \p begin() and
    /// \p end() member functions.
    using ProcessingOrderContainer = std::vector<typename Graph::Edge>;

    /// \brief Instantiates a \c ProcessingOrderContainer.
    ///
    /// This function instantiates a \ref ProcessingOrderContainer.
    static ProcessingOrderContainer* createProcessingOrderContainer()
    {
      return new ProcessingOrderContainer;
    }

    /// \brief The type of the node map that converts the nodes of the inner
    /// digraph to those of the input graph.
    ///
    /// The type of the node map that converts the nodes of the inner
    /// digraph to the input graph.
    /// It must conform to the \ref concepts::ReadWriteMap "ReadWriteMap"
    /// concept. This map will be written exactly once for each node.
    /// \warning The iterators
    /// \ref UniSparse::LastBlockingTightNodeIt "LastBlockingTightNodeIt",
    /// \ref UniSparseComp::CompNodeIt "CompNodeIt", and the functions
    /// \ref UniSparse::nodesOfLastBlockingTight()
    /// "nodesOfLastBlockingTight()", \ref UniSparseComp::CompIt::nodes()
    /// "nodes()" read this node map, hence it must not be \c NullMap if any
    /// of them is used.
    using ToInputNodeMap = typename Digraph::NodeMap<typename Graph::Node>;

    /// \brief Instantiates a \c ToInputNodeMap.
    ///
    /// This function instantiates a \ref ToInputNodeMap.
    /// \param dg The inner digraph for which \ref ToInputNodeMap is defined.
    static ToInputNodeMap* createToInputNodeMap(const Digraph& dg)
    {
      return new ToInputNodeMap(dg, INVALID);
    }

    /// \brief The type of the node map that converts the nodes of the input
    /// graph to those of the inner digraph.
    ///
    /// The type of the node map that converts the nodes of the input
    /// graph to those of the inner digraph. It must conform to the
    /// \ref concepts::ReadWriteMap "ReadWriteMap" concept. This map will
    /// be written exactly once for each node.
    /// \warning This node map must never be \c NullMap since it is written in
    /// \ref UniSparseSpec::init() and read during processing the edges.
    using ToInnerNodeMap = typename Graph::template NodeMap<typename Digraph
                                                            ::Node>;

    /// \brief Instantiates a \c ToInnerNodeMap.
    ///
    /// This function instantiates a \ref ToInnerNodeMap.
    /// \param g The input graph for which \ref ToInnerNodeMap is defined.
    static ToInnerNodeMap* createToInnerNodeMap(const Graph& g)
    {
      return new ToInnerNodeMap(g, INVALID);
    }

    /// \brief The type of the arc map that converts the arcs of the inner
    /// digraph to the edges of the input graph.
    ///
    /// The type of the arc map that converts the arcs of the inner digraph
    /// to the edges of the input graph. It must conform to the
    /// \ref concepts::ReadWriteMap "ReadWriteMap" concept. This map will be
    /// written exactly once for each arc.
    /// \warning The iterators
    /// \ref UniSparse::LastBlockingTightEdgeIt "LastBlockingTightEdgeIt",
    /// \ref UniSparseComp::CompEdgeIt "CompEdgeIt", and the functions
    /// \ref UniSparse::edgesOfLastBlockingTight()
    /// "edgesOfLastBlockingTight()", \ref UniSparseComp::CompIt::edges()
    /// "edges()" read this arc map, hence it must not be \c NullMap if any
    /// of them is used.
    using ToInputEdgeMap = typename Digraph::ArcMap<typename Graph::Edge>;

    /// \brief Instantiates a \c ToInputEdgeMap.
    ///
    /// This function instantiates a \ref ToInputEdgeMap.
    /// \param dg The inner digraph for which \ref ToInputEdgeMap is defined.
    static ToInputEdgeMap* createToInputEdgeMap(const Digraph& dg)
    {
      return new ToInputEdgeMap(dg, INVALID);
    }

    /// \brief The type of the edge map that converts the edges of the input
    /// graph to the arcs of the inner digraph.
    ///
    /// The type of the edge map that converts the edges of the input
    /// graph to the arcs of the inner digraph. It must conform to the
    /// \ref concepts::ReadWriteMap "ReadWriteMap" concept. This map will be
    /// written exactly once for each accepted edge, and never for any other
    /// edges. This is a \c NullMap by default.
    /// \warning This edge map must not be \c NullMap if the function
    /// \ref UniSparseSpec::isInduced() "isInduced" is used. For example, use
    /// \ref Graph::EdgeMap<typename Digraph::Arc>.
    using ToInnerArcMap = NullMap<typename Graph::Edge, typename Digraph::Arc>;

    /// \brief Instantiates a \c ToInnerArcMap.
    ///
    /// This function instantiates a \ref ToInnerArcMap.
    /// \param g The input graph for which \ref ToInnerArcMap is defined.
#ifdef DOXYGEN
    static ToInnerArcMap* createToInnerArcMap(const Graph& g)
#else
    static ToInnerArcMap* createToInnerArcMap(const Graph&)
#endif
    {
      return new ToInnerArcMap;
    }

    /// \brief Compile time promise for the range.
    ///
    /// Supported types are unisparse_bits::LowerRange,
    /// unisparse_bits::UpperRange and unisparse_bits::UnknownRange.
    using RangeSelector = unisparse_bits::UnknownRange;

    /// \brief Set the constant 1 weight function.
    ///
    /// Set the constant 1 weight function. This is equivalent to setting
    /// \res ConstMap<typename Graph::Edge, int>(1)
    /// "ConstMap<Edge, int>(1)" as the WeightMap.
    using AllOneWeights = std::false_type;

    using IsSet_ToInputNodeMap = std::false_type;
    using IsSet_ToInnerNodeMap = std::false_type;
    using IsSet_ToInputEdgeMap = std::false_type;
    using IsSet_ToInnerArcMap = std::false_type;
  };


  /// \brief Algorithms for \f$ (k,2k) \f$-sparsity.
  ///
  /// An undirected graph \f$ G=(V,E) \f$ is called \f$ (k,2k) \f$-sparse if
  /// \f$ i(X) \leq k|X|-2k \f$ for every \f$ X \subseteq V \f$ of size at
  /// least 3, where \f$ i(X) \f$ is the number of edges induced by the nodes
  /// in \f$ X \f$. A graph is called \f$ (k,2k) \f$-tight if it is
  /// \f$ (k,2k) \f$-sparse and
  /// \f$ |E| = k|V| - 2k \f$.
  ///
  /// This class provides an efficient implementation for extracting an
  /// inclusion-wise maximal \f$ (k,2k) \f$-sparse subgraph of an undirected
  /// simple graph in time \f$ O(k^2mn) \f$.
  ///
  /// There is also a \ref uniSparseSpec() "function-type interface" called
  /// \ref uniSparseSpec(), which is convenient in simpler use cases.
  ///
  /// \tparam GR The type of the undirected graph the algorithm runs on.
  /// The default type is \ref ListGraph.
  /// \tparam TR The traits class that defines various types used in the
  /// algorithm. By default, it is \ref UniSparseDefaultTraits. In most cases,
  /// this parameter should not be set directly, consider to use the named
  /// template parameters instead.
  ///
  /// \warning The algorithm works for simple graphs only, i.e. neither
  /// parallel edges nor loops are allowed.
#ifdef DOXYGEN
  template<typename GR, typename TR>
#else
  template<typename GR = ListGraph, typename TR = UniSparseDefaultTraits<GR>>
#endif
  class UniSparseSpec {
  public:
    /// The type of the undirected graph the algorithm runs on.
    using Graph = GR;
    /// \brief The type of the inner digraph.
    using Digraph = typename TR::Digraph;
    /// \brief The type of the node map that converts the nodes of the inner
    /// digraph to those of the input graph.
    using ToInputNodeMap = typename TR::ToInputNodeMap;
    /// \brief The type of the node map that converts the nodes of the input
    /// graph to those of the inner digraph.
    using ToInnerNodeMap = typename TR::ToInnerNodeMap;
    /// \brief The type of the arc map that converts the arcs of the inner
    /// digraph to the edges of the input graph.
    using ToInputEdgeMap = typename TR::ToInputEdgeMap;
    /// \brief The type of the edge map that converts the edges of the input
    /// graph to the arcs of the inner digraph.
    using ToInnerArcMap = typename TR::ToInnerArcMap;
    /// \brief The \ref UniSparseDefaultTraits "traits class" of the algorithm.
    using Traits = TR;

  protected:
    // The type of the node map that stores the number of outgoing arcs.
    using OutDegMap = typename Digraph::template NodeMap<int>;
    // The type of the reversed (inner) digraph.
    using RevDigraph = ReverseDigraph<Digraph>;

  private:
    using Edge = typename GR::Edge;
    using Node = typename GR::Node;
    using EdgeIt = typename GR::EdgeIt;
    using NodeIt = typename GR::NodeIt;
    using Arc = typename Digraph::Arc;
    using ArcIt = typename Digraph::ArcIt;
    using OutArcIt = typename Digraph::OutArcIt;
    using DNode = typename Digraph::Node;
    using DNodeIt = typename Digraph::NodeIt;

  protected:
    // The undirected simple graph the algorithm runs on.
    const Graph& _inputGraph;
    // The parameters of (k,2k)-sparsity.
    const int _k;

    // The edge iterator of the next edge to be processed.
    EdgeIt _nextEdgeIt;
    // The latest edge that has been processed.
    Edge _previousEdge;

    // The total number of nodes and edges in the input graph.
    const int _numEdges, _numNodes;
    // The number of inserted edges (increased as edges are inserted).
    int _numInserted;

    // The inner digraph constructed by the algorithm.
    Digraph* _innerDigraph;
    // Indicates whether _innerDigraph is locally allocated.
    bool _local_innerDigraph;

    // The node map converting the inner digraph nodes to input nodes,
    // initialized in the \ref init() function.
    ToInputNodeMap* _toInputNode;
    // Indicates whether _toInputNode is locally allocated.
    bool _local_toInputNode;

    // The node map converting the input nodes to inner digraph nodes,
    // initialized in the \ref init() function.
    ToInnerNodeMap* _toInnerNode;
    // Indicates whether _toInnerNode is locally allocated.
    bool _local_toInnerNode;

    // The arc map converting the arcs of the inner digraph to the edges of the
    // input graph. Once an edge \c e is accepted and the arc \c a is inserted
    // to the inner digraph, they are registered in this map.
    ToInputEdgeMap* _toInputEdge;
    // Indicates whether _toInputEdge is locally allocated.
    bool _local_toInputEdge;

    // The edge map converting the edges of the input graph to the arcs of the
    // inner digraph. Once an edge \c e is accepted and the arc \c a is
    // inserted to the inner digraph, they are registered in this map. If it
    // maps INVALID to an edge, then the edge has not been accepted (so far).
    ToInnerArcMap* _toInnerArc;
    // Indicates whether _toInnerArc is locally allocated.
    bool _local_toInnerArc;

    // Used for path reversals in the inner digraph built by the algorithm.
    unisparse_bits::Bfs<Digraph>* _bfs;

    // The reverse of the inner digraph.
    RevDigraph* _revDigraph;
    // Used for searching in the reverse of the inner digraph.
    unisparse_bits::Bfs<RevDigraph>* _revBfs;

    // The node map that stores the out-degrees in the inner digraph.
    OutDegMap* _outDeg;

    // Largest number of edges in a (k,l)-sparse graph on _numNodes nodes.
    const int _fullRank;

  public:
    using Create = UniSparseSpec;

    /// \name Named Template Parameters

    /// @{

    template<typename DGR>
    struct SetInnerDigraphTraits : public Traits {
      using Digraph = DGR;
      using DNode = typename Digraph::Node;
      using Arc = typename Digraph::Arc;
      using IsSet_ToInputNodeMap = typename Traits::IsSet_ToInputNodeMap;
      using IsSet_ToInnerNodeMap = typename Traits::IsSet_ToInnerNodeMap;
      using IsSet_ToInputEdgeMap = typename Traits::IsSet_ToInputEdgeMap;
      using IsSet_ToInnerArcMap = typename Traits::IsSet_ToInnerArcMap;

      using ToInputNodeMap = typename // resort to default if not already set
        std::conditional<std::is_same<IsSet_ToInputNodeMap,
                                      std::true_type>::value,
                         typename Traits::ToInputNodeMap,
                         typename Digraph::template NodeMap<Node>>::type;
      using ToInnerNodeMap = typename // resort to default if not already set
        std::conditional<std::is_same<IsSet_ToInnerNodeMap,
                                      std::true_type>::value,
                         typename Traits::ToInnerNodeMap,
                         typename Graph::template NodeMap<DNode>>::type;
      using ToInputEdgeMap = typename // resort to default if not already set
        std::conditional<std::is_same<IsSet_ToInputEdgeMap,
                                      std::true_type>::value,
                         typename Traits::ToInputEdgeMap,
                         typename Digraph::template ArcMap<Edge>>::type;
      using ToInnerArcMap = typename // resort to default if not already set
        std::conditional<std::is_same<IsSet_ToInnerArcMap,
                                      std::true_type>::value,
                         typename Traits::ToInnerArcMap,
                         NullMap<Edge, Arc>>::type;

      using OutDegMap = typename Digraph::template NodeMap<int>;

      static Digraph* createInnerDigraph()
      {
        LEMON_ASSERT(false, "Digraph is not initialized!");
        return nullptr;
      }

      // update Parent::createToInputNodeMap if ToInputNodeMap is not set
      template<typename T = IsSet_ToInputNodeMap>
      static typename std::enable_if<std::is_same<T, std::false_type>::value,
                                     ToInputNodeMap*>::type
      createToInputNodeMap(const Digraph& dg)
      {
        return new ToInputNodeMap(dg, INVALID); // the owner is UniSparseSpec
      }
      // do nothing if already set
      template<typename T = IsSet_ToInputNodeMap>
      static typename std::enable_if<std::is_same<T, std::true_type>::value,
                                     ToInputNodeMap*>::type
      createToInputNodeMap(const Digraph&)
      {
        LEMON_ASSERT(false, "ToInputNodeMap is not initialized!");
        return nullptr;
      }

      // update Parent::createToInnerNodeMap if ToInnerNodeMap is not set
      template<typename T = IsSet_ToInnerNodeMap>
      static typename std::enable_if<std::is_same<T, std::false_type>::value,
                                     ToInnerNodeMap*>::type
      createToInnerNodeMap(const Graph& g)
      {
        return new ToInnerNodeMap(g, INVALID); // the owner is UniSparseSpec
      }
      // do nothing if already set
      template<typename T = IsSet_ToInnerNodeMap>
      static typename std::enable_if<std::is_same<T, std::true_type>::value,
                                     ToInnerNodeMap*>::type
      createToInnerNodeMap(const Graph&)
      {
        LEMON_ASSERT(false, "ToInnerNodeMap is not initialized!");
        return nullptr;
      }

      // update Parent::createToInputEdgeMap if ToInputEdgeMap is not set
      template<typename T = IsSet_ToInputEdgeMap>
      static typename std::enable_if<std::is_same<T, std::false_type>::value,
                                     ToInputEdgeMap*>::type
      createToInputEdgeMap(const Digraph& dg)
      {
        return new ToInputEdgeMap(dg, INVALID); // the owner is UniSparseSpec
      }
      // do nothing if already set
      template<typename T = IsSet_ToInputEdgeMap>
      static typename std::enable_if<std::is_same<T, std::true_type>::value,
                                     ToInputEdgeMap*>::type
      createToInputEdgeMap(const Digraph&)
      {
        LEMON_ASSERT(false, "ToInputEdgeMap is not initialized!");
        return nullptr;
      }

      // update Parent::createToInnerArcMap if ToInnerArcMap is not set
      template<typename T = IsSet_ToInnerArcMap>
      static typename std::enable_if<std::is_same<T, std::false_type>::value,
                                     ToInnerArcMap*>::type
      createToInnerArcMap(const Graph&)
      {
        return new ToInnerArcMap; // the owner is UniSparseSpec
      }
      // do nothing if already set
      template<typename T = IsSet_ToInnerArcMap>
      static typename std::enable_if<std::is_same<T, std::true_type>::value,
                                     ToInnerArcMap*>::type
      createToInnerArcMap(const Graph&)
      {
        LEMON_ASSERT(false, "ToInnerArcMap is not initialized!");
        return nullptr;
      }
    };

    /// \brief \ref named-templ-param "Named parameter" for setting
    /// \c InnerDigraph type.
    ///
    /// \ref named-templ-param "Named parameter" for setting
    /// \c InnerDigraph type.
    ///
    /// It must provide \p addNode(), \p addArc(), \p reverseArc()
    /// and \p clear() member functions.
    template<typename DGR>
    struct SetInnerDigraph
      : public UniSparseSpec<Graph, SetInnerDigraphTraits<DGR>> {
      using Create = UniSparseSpec<Graph, SetInnerDigraphTraits<DGR>>;
    };

    template<typename NM>
    struct SetToInputNodeMapTraits : public Traits {
      using ToInputNodeMap = NM;
      using IsSet_ToInputNodeMap = std::true_type;

#ifdef DOXYGEN
      static ToInputNodeMap* createToInputNodeMap(const Digraph& dg)
#else
      static ToInputNodeMap* createToInputNodeMap(const Digraph&)
#endif
      {
        LEMON_ASSERT(false, "ToInputNodeMap is not initialized!");
        return nullptr;
      }
    };

    /// \brief \ref named-templ-param "Named parameter" for setting
    /// \c ToInputNodeMap type.
    ///
    /// \ref named-templ-param "Named parameter" for setting
    /// \c ToInputNodeMap type.
    ///
    /// It must conform to the \ref concepts::ReadWriteMap
    /// "ReadWriteMap" concept.
    ///
    /// \warning The iterators
    /// \ref UniSparse::LastBlockingTightNodeIt "LastBlockingTightNodeIt",
    /// \ref UniSparse::nodesOfLastBlockingTight()
    /// "nodesOfLastBlockingTight()", hence it must not be \c NullMap if any
    /// of them is used.
    template<typename NM>
    struct SetToInputNodeMap
      : public UniSparseSpec<Graph, SetToInputNodeMapTraits<NM>> {
      using Create = UniSparseSpec<Graph, SetToInputNodeMapTraits<NM>>;
    };

    template<typename NM>
    struct SetToInnerNodeMapTraits : public Traits {
      using ToInnerNodeMap = NM;
      using IsSet_ToInnerNodeMap = std::true_type;

#ifdef DOXYGEN
      static ToInnerNodeMap* createToInnerNodeMap(const Graph& g)
#else
      static ToInnerNodeMap* createToInnerNodeMap(const Graph&)
#endif
      {
        LEMON_ASSERT(false, "ToInnerNodeMap is not initialized!");
        return nullptr;
      }
    };

    /// \brief \ref named-templ-param "Named parameter" for setting
    /// \c ToInnerNodeMap type.
    ///
    /// \ref named-templ-param "Named parameter" for setting
    /// \c ToInnerNodeMap type.
    ///
    /// It must conform to the \ref concepts::ReadWriteMap
    /// "ReadWriteMap" concept.
    /// \warning This node map must never be \c NullMap since it is written in
    /// \ref UniSparseComp::init() and read during processing the edges.
    template<typename NM>
    struct SetToInnerNodeMap
      : public UniSparseSpec<Graph, SetToInnerNodeMapTraits<NM>> {
      using Create = UniSparseSpec<Graph, SetToInnerNodeMapTraits<NM>>;
    };

    template<typename AM>
    struct SetToInputEdgeMapTraits : public Traits {
      using ToInputEdgeMap = AM;
      using IsSet_ToInputEdgeMap = std::true_type;

#ifdef DOXYGEN
      static ToInputEdgeMap* createToInputEdgeMap(const Digraph& dg)
#else
      static ToInputEdgeMap* createToInputEdgeMap(const Digraph&)
#endif
      {
        LEMON_ASSERT(false, "ToInputEdgeMap is not initialized!");
        return nullptr;
      }
    };

    /// \brief \ref named-templ-param "Named parameter" for setting
    /// \c ToInputEdgeMap type.
    ///
    /// \ref named-templ-param "Named parameter" for setting
    /// \c ToInputEdgeMap type.
    ///
    /// It must conform to the \ref concepts::ReadWriteMap
    /// "ReadWriteMap" concept.
    ///
    /// \warning The iterators
    /// \ref UniSparse::LastBlockingTightEdgeIt "LastBlockingTightEdgeIt" and
    /// \ref UniSparse::edgesOfLastBlockingTight()
    /// "edgesOfLastBlockingTight()", read this arc map, hence it must not be
    /// \c NullMap if any of them is used.
    template<typename AM>
    struct SetToInputEdgeMap
      : public UniSparseSpec<Graph, SetToInputEdgeMapTraits<AM>> {
      using Create = UniSparseSpec<Graph, SetToInputEdgeMapTraits<AM>>;
    };

    template<typename EM>
    struct SetToInnerArcMapTraits : public Traits {
      using ToInnerArcMap = EM;
      using IsSet_ToInnerArcMap = std::true_type;

#ifdef DOXYGEN
      static ToInnerArcMap* createToInnerArcMap(const Graph& g)
#else
      static ToInnerArcMap* createToInnerArcMap(const Graph&)
#endif
      {
        LEMON_ASSERT(false, "ToInnerArcMap is not initialized!");
        return nullptr;
      }
    };

    /// \brief \ref named-templ-param "Named parameter" for setting
    /// \c ToInnerArcMap type.
    ///
    /// \ref named-templ-param "Named parameter" for setting
    /// \c ToInnerArcMap type.
    ///
    /// It must conform to the \ref concepts::ReadWriteMap
    /// "ReadWriteMap" concept. This is a \c NullMap by default.
    /// \warning This edge map must not be \c NullMap if the function
    /// \ref UniSparseSpec::isInduced() "isInduced" is used. For example, use
    /// \ref Graph::EdgeMap<typename Digraph::Arc>.
    template<typename EM>
    struct SetToInnerArcMap
      : public UniSparseSpec<Graph, SetToInnerArcMapTraits<EM>> {
      using Create = UniSparseSpec<Graph, SetToInnerArcMapTraits<EM>>;
    };

#ifndef DOXYGEN
  protected:
    UniSparseSpec(const Graph& g, const int k, const int l) // protected!
      : _inputGraph(g), _k(k), _nextEdgeIt(_inputGraph),
        _previousEdge(INVALID), _numEdges(countEdges(_inputGraph)),
        _numNodes(countNodes(_inputGraph)), _numInserted(0),
        _innerDigraph(nullptr), _local_innerDigraph(false),
        _toInputNode(nullptr), _local_toInputNode(false),
        _toInnerNode(nullptr), _local_toInnerNode(false),
        _toInputEdge(nullptr), _local_toInputEdge(false),
        _toInnerArc(nullptr), _local_toInnerArc(false),
        _bfs(nullptr), _revDigraph(nullptr), _revBfs(nullptr),
        _outDeg(nullptr), _fullRank(std::max(0, k * _numNodes - l))
    {
      LEMON_ASSERT(k > 0, "Parameter k must be positive!");
    }
#endif

  public:
    /// \brief Constructor.
    ///
    /// Constructor.
    /// \param g The undirected simple graph the algorithm runs on.
    /// \param k The parameter \f$ k \f$ of \f$ (k,2k) \f$-sparsity.
    UniSparseSpec(const Graph& g, const int k)
      : _inputGraph(g), _k(k), _nextEdgeIt(_inputGraph),
        _previousEdge(INVALID), _numEdges(countEdges(_inputGraph)),
        _numNodes(countNodes(_inputGraph)), _numInserted(0),
        _innerDigraph(nullptr), _local_innerDigraph(false),
        _toInputNode(nullptr), _local_toInputNode(false),
        _toInnerNode(nullptr), _local_toInnerNode(false),
        _toInputEdge(nullptr), _local_toInputEdge(false),
        _toInnerArc(nullptr), _local_toInnerArc(false),
        _bfs(nullptr), _revDigraph(nullptr), _revBfs(nullptr),
        _outDeg(nullptr), _fullRank(_numNodes > 2 ? _k * (_numNodes - 2)
                                    : std::numeric_limits<int>::max())
    {
      LEMON_ASSERT(simpleGraph(g), "Only for simple graphs!"); // TODO
      LEMON_ASSERT(k > 0, "Parameter k must be positive!");
    }

    /// \brief Destructor.
    ///
    /// Destructor.
    ~UniSparseSpec()
    {
      delete _outDeg;
      delete _revBfs;
      delete _revDigraph;
      delete _bfs;
      if(_local_toInnerArc) {
        delete _toInnerArc;
      }
      if(_local_toInputEdge) {
        delete _toInputEdge;
      }
      if(_local_toInnerNode) {
        delete _toInnerNode;
      }
      if(_local_toInputNode) {
        delete _toInputNode;
      }
      if(_local_innerDigraph) {
        delete _innerDigraph;
      }
    }

    /// \brief Sets the \c Digraph.
    ///
    /// Sets the inner \c Digraph to be built by the algorithm.
    ///
    /// \param dg The inner \c Digraph built by the algorithm.
    ///
    /// If you don't use this function before calling \ref checkSparse(),
    /// \ref run() or \ref init(), then an instance will be allocated
    /// automatically. The destructor deallocates this automatically allocated
    /// graph, of course.
    ///
    /// \return <tt> (*this) </tt>
    UniSparseSpec& innerDigraph(Digraph& dg)
    {
      if(_local_innerDigraph) {
        _local_innerDigraph = false;
        delete _innerDigraph;
      }
      _innerDigraph = &dg;
      return *this;
    }

    /// \brief Sets the \c ToInputNodeMap.
    ///
    /// Sets the \c ToInputNodeMap.
    ///
    /// \param m The \c ToInputNodeMap of the inner digraph.
    ///
    /// If you don't use this function before calling \ref checkSparse(),
    /// \ref run() or \ref init(), then an instance will be allocated
    /// automatically. The destructor deallocates this automatically allocated
    /// map, of course.
    ///
    /// \return <tt> (*this) </tt>
    UniSparseSpec& toInputNodeMap(ToInputNodeMap& m)
    {
      if(_local_toInputNode) {
        _local_toInputNode = false;
        delete _toInputNode;
      }
      _toInputNode = &m;
      return *this;
    }

    /// \brief Sets the \c ToInnerNodeMap.
    ///
    /// Sets the \c ToInnerNodeMap.
    ///
    /// \param m The \c ToInnerNodeMap of the input graph.
    ///
    /// If you don't use this function before calling \ref checkSparse(),
    /// \ref run() or \ref init(), then an instance will be allocated
    /// automatically. The destructor deallocates this automatically allocated
    /// map, of course.
    ///
    /// \return <tt> (*this) </tt>
    UniSparseSpec& toInnerNodeMap(ToInnerNodeMap& m)
    {
      if(_local_toInnerNode) {
        _local_toInnerNode = false;
        delete _toInnerNode;
      }
      _toInnerNode = &m;
      return *this;
    }

    /// \brief Sets the \c ToInputEdgeMap.
    ///
    /// Sets the \c ToInputEdgeMap.
    ///
    /// \param m The \c ToInputEdgeMap of the inner digraph.
    ///
    /// If you don't use this function before calling \ref checkSparse(),
    /// \ref run() or \ref init(), then an instance will be allocated
    /// automatically. The destructor deallocates this automatically allocated
    /// map, of course.
    ///
    /// \return <tt> (*this) </tt>
    UniSparseSpec& toInputEdgeMap(ToInputEdgeMap& m)
    {
      if(_local_toInputEdge) {
        _local_toInputEdge = false;
        delete _toInputEdge;
      }
      _toInputEdge = &m;
      return *this;
    }

    /// \brief Sets the \c ToInnerArcMap.
    ///
    /// Sets the \c ToInnerArcMap.
    ///
    /// \param m The \c ToInnerArcMap of the input graph.
    ///
    /// If you don't use this function before calling \ref checkSparse(),
    /// \ref run() or \ref init(), then an instance will be allocated
    /// automatically. The destructor deallocates this automatically allocated
    /// map, of course.
    ///
    /// \return <tt> (*this) </tt>
    UniSparseSpec& toInnerArcMap(ToInnerArcMap& m)
    {
      if(_local_toInnerArc) {
        _local_toInnerArc = false;
        delete _toInnerArc;
      }
      _toInnerArc = &m;
      return *this;
    }

  public:
    /// \name Execution Control
    /// The simplest way to use UniSparseSpec is to call either the
    /// member function \ref checkSparse() or \ref run().
    /// If you need better control on the execution, you have to call \ref
    /// init() first, then you can process the edges with \ref
    /// processNextEdge() until \ref isAllDone() (or \ref isAllProcessed())
    /// returns \c true, as shown by the following code snippet.
    ///
    /// \code
    ///   uss.init();
    ///   while(!uss.isAllDone()) {
    ///     uss.processNextEdge();
    ///   }
    /// \endcode
    ///
    ///
    /// If you want to choose the edge to be processed next, then
    /// use \ref processEdge(const Edge&) "processEdge(e)",
    /// as follows.
    ///
    /// \code
    ///   uss.init();
    ///   for(const auto& e : g.edges()) {
    ///     uss.processEdge(e);
    ///   }
    /// \endcode

    /// @{

    /// \brief Initializes the internal data structures.
    ///
    /// Initializes the internal data structures.
    void init()
    {
      _nextEdgeIt = EdgeIt(_inputGraph);
      _previousEdge = INVALID;
      _numInserted = 0;
      if(!_innerDigraph) {
        _local_innerDigraph = true;
        _innerDigraph = Traits::createInnerDigraph();
        LEMON_ASSERT(_innerDigraph, "InnerDigraph is not initialized!");
      }
      else {
        _innerDigraph->clear();
      }
      if(!_toInputNode) {
        _local_toInputNode = true;
        _toInputNode = Traits::createToInputNodeMap(*_innerDigraph);
        LEMON_ASSERT(_toInputNode, "ToInputNode is not initialized!");
      }
      if(!_toInnerNode) {
        _local_toInnerNode = true;
        _toInnerNode = Traits::createToInnerNodeMap(_inputGraph);
        LEMON_ASSERT(_toInnerNode, "ToInnerNode is not initialized!");
      }
      if(!_toInputEdge) {
        _local_toInputEdge = true;
        _toInputEdge = Traits::createToInputEdgeMap(*_innerDigraph);
        LEMON_ASSERT(_toInputEdge, "ToInputEdge is not initialized!");
      }
      if(!_toInnerArc) {
        _local_toInnerArc = true;
        _toInnerArc = Traits::createToInnerArcMap(_inputGraph);
        LEMON_ASSERT(_toInnerArc, "ToInnerArc is not initialized!");
      }
      else {
        unisparse_bits::smartMapFill(_inputGraph, *_toInnerArc, INVALID);
      }

      delete _bfs;
      _bfs = new unisparse_bits::Bfs<Digraph>(*_innerDigraph, _numNodes);

      delete _revDigraph;
      _revDigraph = new RevDigraph(*_innerDigraph);

      delete _revBfs;
      _revBfs = new unisparse_bits::Bfs<RevDigraph>(*_revDigraph, _numNodes);

      for(NodeIt u(_inputGraph); u != INVALID; ++u) {
        const DNode v = _innerDigraph->addNode();
        _toInputNode->set(v, u);
        _toInnerNode->set(u, v);
      }

      delete _outDeg;
      _outDeg = new OutDegMap(*_innerDigraph, 0);
    }

    /// \brief The next edge to be processed.
    ///
    /// \return The next edge to be processed.
    Edge nextEdge() const
    {
      return _nextEdgeIt;
    }

    /// \brief The latest processed edge.
    ///
    /// \return The latest processed edge.
    Edge previousEdge() const
    {
      return _previousEdge;
    }

    /// \brief Returns \c true if all edges are processed.
    ///
    /// \return \c true if all edges are processed.
    ///
    /// \pre This function works correctly only if edges are processed by
    /// \ref checkSparse(), \ref run() or \ref processNextEdge(), but not by
    /// \ref processEdge(const Edge&) "processEdge(e)".
    /// \note Consider using the function \ref isAllDone() instead, which
    /// also detects if no more edges may be accepted.
    bool isAllProcessed() const
    {
      return _nextEdgeIt == INVALID;
    }

    /// \brief Returns \c true if all edges are processed or no other edge
    /// may be accepted.
    ///
    /// \return \c true if all edges are processed or no other edge may be
    /// accepted.
    ///
    /// This function is just a shortcut of
    ///
    /// \code
    ///   sparseSize() >= fullRank() || isAllProcessed()
    /// \endcode
    ///
    /// \pre This function works correctly only if edges are processed by
    /// \ref checkSparse(), \ref run() or \ref processNextEdge(), but not by
    /// \ref processEdge(const Edge&) "processEdge(e)".
    bool isAllDone() const
    {
      return sparseSize() >= fullRank() || isAllProcessed();
    }

    /// \brief Returns the upper bound for the total number of edges in a
    /// \f$ (k,2k) \f$-sparse graph.
    ///
    /// \return The upper bound for the total number of edges in a
    /// \f$ (k,2k) \f$-sparse graph, that is, \f$ k|V|-2k \f$ if the graph has
    /// at least three nodes, otherwise, \c INT_MAX.
    int fullRank() const
    {
      return _fullRank;
    }

    /// \brief Processes the given edge.
    ///
    /// Processes the given edge.
    ///
    /// \param e The edge to be processed.
    ///
    /// The following code snippet shows how this function can be used for
    /// better control on the execution.
    ///
    /// \code
    ///   uss.init();
    ///   for(const auto& e : g.edges()) {
    ///     uss.processEdge(e);
    ///   }
    /// \endcode
    ///
    /// \return The resulting \c Arc if the edge has been accepted, otherwise
    /// \c INVALID.
    ///
    /// \pre Function \ref init() must be called before using this function.
    /// \warning It is the caller's responsibility to process each edge only
    /// once. If an edge is processed multiple times, then it may get accepted
    /// several times and/or the algorithm may run slower.
    Arc processEdge(const Edge& e)
    {
      LEMON_ASSERT(e != INVALID, "Processing INVALID edge!");
      return processEdge(e, _inputGraph.u(e), _inputGraph.v(e));
    }

    /// \brief Processes the given edge.
    ///
    /// Processes the given edge.
    ///
    /// \param e The edge to be processed.
    /// \param from The incident node from which the arc should be oriented
    /// (if possible) in case \c e is accepted.
    ///
    /// The following code snippet shows how this function can be used for
    /// better control on the execution.
    ///
    /// \code
    ///   uss.init();
    ///   for(const auto& u : g.nodes()) {
    ///     for(const auto& e : g.trueIncEdges(u)) {
    ///       if(u < g.oppositeNode(u, e)) {
    ///         uss.processEdge(e, u);
    ///       }
    ///     }
    ///   }
    /// \endcode
    ///
    /// \return The resulting \c Arc if the edge has been accepted, otherwise
    /// \c INVALID.
    ///
    /// \pre Function \ref init() must be called before using this function.
    /// \warning The arc will be oriented from the node \c from only if its
    /// outdegree is smaller than \f$ k \f$, otherwise, the desired direction
    /// will be ignored.
    /// \warning It is the caller's responsibility to process each edge only
    /// once. If an edge is processed multiple times, then it may get accepted
    /// several times and/or the algorithm may run slower.
    Arc processEdge(const Edge& e, const Node from)
    {
      LEMON_ASSERT(e != INVALID, "Processing INVALID edge!");
      return processEdge(e, from, _inputGraph.oppositeNode(e, from));
    }

    /// \brief Processes the given edge.
    ///
    /// Processes the given edge.
    ///
    /// \param e The edge to be processed.
    /// \param from The incident node from which the arc should be oriented
    /// (if possible) in case \c e is accepted.
    /// \param to The incident node to which the arc should be oriented
    /// (if possible) in case \c e is accepted.
    ///
    /// The following code snippet shows how this function can be used for
    /// better control on the execution.
    ///
    /// \code
    ///   uss.init();
    ///   for(const auto& u : g.nodes()) {
    ///     for(const auto& e : g.trueIncEdges(u)) {
    ///       if(u < g.oppositeNode(u, e)) {
    ///         uss.processEdge(e, u, g.oppositeNode(u, e));
    ///       }
    ///     }
    ///   }
    /// \endcode
    ///
    /// \return The resulting \c Arc if the edge has been accepted, otherwise
    /// \c INVALID.
    ///
    /// \pre Function \ref init() must be called before using this function.
    /// \warning It is the caller's responsibility to process each edge only
    /// once. If an edge is processed multiple times, then it may get accepted
    /// several times and/or the algorithm may run slower.
    Arc processEdge(const Edge& e, const Node from, const Node to)
    {
      LEMON_ASSERT(e != INVALID, "Processing INVALID edge!");
      LEMON_ASSERT(_inputGraph.u(e) != _inputGraph.v(e),
                   "No loops are allowed in UniSparseSpec!");

      _previousEdge = e;

      const DNode innerU = (*_toInnerNode)[from];
      const DNode innerV = (*_toInnerNode)[to];

      reversePaths(innerU, innerV);

      LEMON_ASSERT((*_outDeg)[innerU] == 0 && (*_outDeg)[innerV] == 0,
                   "Unexpected outdeg!");

      if(!isSmallDegNodeReachableFromAll(innerU, innerV)) {
        return INVALID;
      }

      const Arc a = insertArc(innerU, innerV);
      registerAcceptance(e, a);

      return a;
    }

    /// \brief Processes the next edge.
    ///
    /// Processes the current edge with \ref processEdge(const Edge&)
    /// "processEdge(e)" and steps the iterator to the next edge.
    /// The following code snippet shows how this function can be used for
    /// better control on the execution. To query the edge to be processed,
    /// call \ref nextEdge() before using this function.
    ///
    /// \code
    ///   uss.init();
    ///   while(!uss.isAllDone()) {
    ///     uss.processNextEdge();
    ///   }
    /// \endcode
    ///
    /// \return The resulting \c Arc if the edge has been accepted, otherwise
    /// \c INVALID.
    ///
    /// \pre Function \ref init() must be called before using this function.
    Arc processNextEdge()
    {
      LEMON_ASSERT(_nextEdgeIt != INVALID,
                   "Called processNextEdge(), but no more edges are left!");
      const Arc ret = processEdge(_nextEdgeIt);
      ++_nextEdgeIt;
      return ret;
    }

    /// \brief Runs the algorithm to check \f$ (k,2k) \f$-sparsity.
    ///
    /// This function runs the \ref UniSparseSpec algorithm to check
    /// \f$ (k,2k) \f$-sparsity.
    ///
    /// \return \c true if the graph is \f$ (k,2k) \f$-sparse.
    bool checkSparse()
    {
      init();
      while(!isAllDone()) {
        if(processNextEdge() == INVALID) {
          return false;
        }
      }
      return isSparse();
    }

    /// \brief Runs the algorithm to find the inclusion-wise maximal
    /// \f$ (k,2k) \f$-sparse subgraph.
    ///
    /// This function runs the algorithm to determine the inclusion-wise
    /// maximal \f$ (k,2k) \f$-sparse subgraph.
    ///
    /// \return \c true if the graph is \f$ (k,2k) \f$-sparse.
    bool run()
    {
      init();
      while(!isAllDone()) {
        processNextEdge();
      }
      return isSparse();
    }

    /// @}

  private:
    // make isAllDone return true
    void forceAllProcessed()
    {
      _nextEdgeIt = INVALID;
    }

    // init node if applicable
    void conditionallyInitNode(const Node)
    {}

    // Inserts the arc uv or vu into _innerDigraph.
    template<bool runAssert>
    Arc _insertArc(const DNode u, const DNode v)
    {
      ++_numInserted;
      auto& outDegU = (*_outDeg)[u];
      if(outDegU < _k) {
        ++outDegU;
        return _innerDigraph->addArc(u, v);
      }
      // could not orient from u, so orient it from v
      LEMON_ASSERT(!runAssert || (*_outDeg)[v] < _k,
                   "No suitable orientation found for an accepted edge!");
      ++(*_outDeg)[v];
      return _innerDigraph->addArc(v, u);
    }

  protected:
    // Inserts the uv or vu arc into _innerDigraph even if outDeg > k.
    Arc insertArcNoAssert(const DNode u, const DNode v)
    {
      return _insertArc<false>(u, v);
    }

    // Inserts the uv or vu arc into _innerDigraph.
    Arc insertArc(const DNode u, const DNode v)
    {
      return _insertArc<true>(u, v);
    }

    // Reverse paths from the nodes u or v to a node of small out-degree.
    bool reversePaths(const DNode u, const DNode v)
    {
      while((*_outDeg)[u] > 0 || (*_outDeg)[v] > 0) {
        _bfs->init();
        _bfs->addSource(u);
        _bfs->addSource(v);

        DNode n = _bfs->findNodeWithDegLeqK(*_outDeg, _k);

        if(n == INVALID) {
          return false;
        }

        ++(*_outDeg)[n];
        do {
          const Arc& a = _bfs->predArc(n);
          n = _innerDigraph->source(a);
          _innerDigraph->reverseArc(a);
        } while(n != u && n != v);
        --(*_outDeg)[n];        // n == u or n == v
      }
      return true;
    }

    // Updates the variables and maps after an arc is inserted.
    void registerAcceptance(const Edge& e, const Arc& a)
    {
      this->_toInputEdge->set(a, e);
      this->_toInnerArc->set(e, a);
    }

  private:
    // Returns true iff every node other than u and v reaches a vertex of
    // degree smaller than k (assumes that u and v have no out-going arcs)
    bool isSmallDegNodeReachableFromAll(const DNode u, const DNode v)
    {
      LEMON_ASSERT((*_outDeg)[u] == 0 && (*_outDeg)[v] == 0,
                   "Unexpected outdeg!");

      _revBfs->init();
      for(DNodeIt n(*_innerDigraph); n != INVALID; ++n) {
        if((*_outDeg)[n] < _k && n != u && n != v) {
          _revBfs->addSource(n);
        }
      }

      return _revBfs->isAtLeastKNodesReachable(_numNodes - 2);
    }

  public:
    /// \name Query Functions
    /// The result of the algorithm can be obtained using the following
    /// functions.
    /// \pre The algorithm should be run before using these functions.

    /// @{

    /// \brief Returns \c true if the graph is \f$ (k,2k) \f$-sparse.
    ///
    /// \return \c true if the graph is \f$ (k,2k) \f$-sparse.
    ///
    /// \pre One of \ref checkSparse() or \ref run() should be called, or, if
    /// the edges are processed by \ref processNextEdge()
    /// or \ref processEdge(const Edge&) "processEdge(e)", then at least one
    /// edge must be rejected or all edges must be processed before using this
    /// function.
    bool isSparse() const
    {
      return _numInserted == _numEdges; // true if _numNodes < 3
    }

    /// \brief Returns \c true if the graph is \f$ (k,2k) \f$-tight.
    ///
    /// \return \c true if the graph is \f$ (k,2k) \f$-tight, that is, it is
    /// \f$ (k,2k) \f$-sparse and \f$ |E| = k|V| - 2k \f$.
    ///
    /// \pre One of \ref checkSparse() or \ref run() should be called, or, if
    /// the edges are processed by \ref processNextEdge()
    /// or \ref processEdge(const Edge&) "processEdge(e)", then at least one
    /// edge must be rejected or all edges must be processed before using this
    /// function.
    bool isTight() const
    {
      return isSparse() && _numEdges == _k * (_numNodes - 2);
    }

    /// \brief Returns \c true if the given edge belongs to the maximal
    /// sparse subgraph.
    ///
    /// \param e The edge to be checked.
    ///
    /// \return \c true if the given edge belongs to the maximal
    /// sparse subgraph.
    ///
    /// \pre Either \ref run() should be called or all edges must be processed
    /// by \ref processNextEdge() or \ref processEdge(const Edge&)
    /// "processEdge(e)" before using this function.
    ///
    /// \pre The edge map \ref UniSparseDefaultTraits::ToInnerArcMap
    /// "ToInnerArcMap" must not be \c NullMap if this function is used.
    bool isInduced(const Edge& e) const
    {
      LEMON_ASSERT(!unisparse_bits::isNullMap<ToInnerArcMap>(),
                   "ToInnerArcMap must not be NullMap!");
      LEMON_ASSERT(_toInnerArc, "ToInnerArcMap is not allocated!");
      return (*_toInnerArc)[e] != INVALID;
    }

    /// \brief Returns the number of accepted edges.
    ///
    /// \return The number of accepted edges, i.e. the number of the edges in
    /// the (current) sparse subgraph.
    int sparseSize() const
    {
      return _numInserted;
    }

    /// \brief Returns \c true if the given node is reached during the latest
    /// path reversal.
    ///
    /// \param n the node to be checked.
    ///
    /// \return \c true if the given node is reached during the latest path
    /// reversal.
    bool reached(const DNode n) const
    {
      return _bfs->reached(n);
    }

    /// @}

    /// \name Traits Query and Setter Functions
    /// The variables and maps of the \ref UniSparseDefaultTraits "Traits"
    /// class can be accessed and set using the following member functions.
    /// \pre One of \ref checkSparse(), \ref run() or \ref init() must be
    /// called before using them.

    /// @{

    /// \brief Returns a const reference to the \c Digraph build by the
    /// algorithm.
    ///
    /// \return Const reference to the \ref UniSparseDefaultTraits::Digraph
    /// "Digraph" built by the algorithm.
    ///
    /// \pre One of \ref checkSparse(), \ref run() or \ref init() must be
    /// called before using this function.
    const Digraph& innerDigraph() const
    {
      return *_innerDigraph;
    }

    /// \brief Returns a const reference to the \c ToInputNodeMap.
    ///
    /// \return Const reference to the \ref
    /// UniSparseDefaultTraits::ToInputNodeMap "ToInputNodeMap".
    ///
    /// \pre One of \ref checkSparse(), \ref run() or \ref init() must be
    /// called before using this function.
    const ToInputNodeMap& toInputNodeMap() const
    {
      return *_toInputNode;
    }

    /// \brief Returns a const reference to the \c ToInnerNodeMap.
    ///
    /// \return Const reference to the \ref
    /// UniSparseDefaultTraits::ToInnerNodeMap "ToInnerNodeMap".
    ///
    /// \pre One of \ref checkSparse(), \ref run() or \ref init() must be
    /// called before using this function.
    const ToInnerNodeMap& toInnerNodeMap() const
    {
      return *_toInnerNode;
    }

    /// \brief Returns a const reference to the \c ToInputEdgeMap.
    ///
    /// \return Const reference to the \ref
    /// UniSparseDefaultTraits::ToInputEdgeMap "ToInputEdgeMap".
    ///
    /// \pre One of \ref checkSparse(), \ref run() or \ref init() must be
    /// called before using this function.
    const ToInputEdgeMap& toInputEdgeMap() const
    {
      return *_toInputEdge;
    }

    /// \brief Returns a const reference to the \c ToInnerArcMap.
    ///
    /// \return Const reference to the
    /// \ref UniSparseDefaultTraits::ToInnerArcMap "ToInnerArcMap".
    ///
    /// \pre One of \ref checkSparse(), \ref run() or \ref init() must be
    /// called before using this function.
    const ToInnerArcMap& toInnerArcMap() const
    {
      return *_toInnerArc;
    }

    /// @}

    /// \name Iterators
    /// After or during the execution of the algorithm, one can access the
    /// accepted edges using \ref edgesOfSparse() or \ref SparseEdgeIt.
    /// For example, the following code snippet prints the id of each
    /// accepted edge.
    ///
    /// \code
    ///   uss.run()
    ///   for(const auto& e : uss.edgesOfSparse()) {
    ///     std::cout << g.id(e) << std::endl;
    ///   }
    /// \endcode
    ///
    /// In case the latest edge was rejected (i.e. the functions \ref
    /// processNextEdge(), \ref processEdge(const Edge&) "processEdge(e)"
    /// return \c INVALID, or \ref checkSparse() return \c false), one can
    /// query an inclusion-wise minimal tight subgraph blocking the insertion
    /// of the edge using \ref nodesOfLastBlockingTight() and
    /// \ref edgesOfLastBlockingTight(), or alternatively, the \ref
    /// LastBlockingTightNodeIt and \ref LastBlockingTightEdgeIt iterators. The
    /// code snippet below shows an example.
    /// \warning If the latest edge has been accepted, then the behavior is
    /// undefined!
    ///
    /// \code
    ///   using BNodeIt = UniSparseSpec<ListGraph>::LastBlockingTightNodeIt;
    ///   using BEdgeIt = UniSparseSpec<ListGraph>::LastBlockingTightEdgeIt;
    ///
    ///   UniSparseSpec<ListGraph> uss(g, k);
    ///   if(!uss.checkSparse()) {
    ///     // Nodes
    ///     for(const auto& n : uss.nodesOfLastBlockingTight()) {
    ///       std::cout << g.id(n) << std::endl;
    ///     }
    ///     // Same as above
    ///     for(BNodeIt n(uss); n != INVALID; ++n) {
    ///       std::cout << g.id(n) << std::endl;
    ///     }
    ///     // Edges
    ///     for(const auto& e : uss.edgesOfLastBlockingTight()) {
    ///       std::cout << g.id(e) << std::endl;
    ///     }
    ///     // Same as above
    ///     for(BEdgeIt e(uss); e != INVALID; ++e) {
    ///       std::cout << g.id(e) << std::endl;
    ///     }
    ///   }
    /// \endcode

    /// @{

  public:
    /// \brief Iterator class for the edges of the sparse graph.
    ///
    /// Iterator class for the edges of the sparse graph. The acceptance
    /// of an edge invalidates this iterator.
    ///
    /// The following snippet uses \ref edgesOfSparse() to access the
    /// accepted edges.
    ///
    /// \code
    ///   UniSparseSpec<ListGraph> uss(g, k);
    ///   uss.run()
    ///   for(const auto& e : uss.edgesOfSparse()) {
    ///     std::cout << g.id(e) << std::endl;
    ///   }
    /// \endcode
    ///
    /// Alternatively, \ref SparseEdgeIt can be used for the same purpose
    /// as follows.
    ///
    /// \code
    ///   using SEdgeIt = UniSparseSpec<ListGraph>::SparseEdgeIt;
    ///   UniSparseSpec<ListGraph> uss(g, k);
    ///   uss.run();
    ///   for(SEdgeIt e(uss); e != INVALID; ++e) {
    ///     std::cout << g.id(e) << std::endl;
    ///   }
    /// \endcode
    ///
    /// \pre The type of the node map \ref
    /// UniSparseDefaultTraits::ToInputEdgeMap "ToInputEdgeMap" of the
    /// underlying \ref UniSparseSpec class must not be \c NullMap.
    class SparseEdgeIt {
      using USS = UniSparseSpec<GR, TR>;
      using ArcIt = typename USS::ArcIt;

      const USS* const _uss;
      ArcIt _arcIt;

    public:
      /// \brief Constructor.
      ///
      /// Constructor. Sets the iterator to the first edge.
      SparseEdgeIt(const USS& uss) : _uss(&uss), _arcIt(_uss->innerDigraph())
      {}

      /// \brief Initializes the iterator to be invalid.
      ///
      /// Initializes the iterator to be invalid.
      /// \sa Invalid for more details.
      SparseEdgeIt(Invalid) : _uss(nullptr), _arcIt(INVALID)
      {}

      /// \brief Edge conversion.
      ///
      /// Edge conversion.
      operator Edge() const
      {
        return _arcIt != INVALID ? (*_uss->_toInputEdge)[_arcIt] : INVALID;
      }

      /// \brief Steps the iterator to the next edge.
      ///
      /// Steps the iterator to the next edge.
      SparseEdgeIt& operator++()
      {
        ++_arcIt;
        return *this;
      }

      /// \brief Inequality operator.
      ///
      /// Inequality operator.
      /// \pre The compared iterators belong to the same instance of
      /// \ref UniSparseSpec.
      bool operator!=(const SparseEdgeIt& rhs) const
      {
        return _arcIt != rhs._arcIt;
      }
    };

    /// \brief Returns the collection of the accepted edges.
    ///
    /// This function can be used for iterating on the accepted edges. It
    /// returns a wrapped SparseEdgeIt, which behaves as an STL container and
    /// can be used in range-based for loops and STL algorithms. The acceptance
    /// of an edge invalidates this iterator.
    ///
    /// The following code demonstrates the usage of the wrapped iterator.
    ///
    /// \code
    ///   uss.run();
    ///   for(const auto& e : uss.edgesOfSparse()) {
    ///     std::cout << g.id(e) << std::endl;
    ///   }
    /// \endcode
    ///
    /// \pre The type of the node map \ref
    /// UniSparseDefaultTraits::ToInputEdgeMap "ToInputEdgeMap" of the
    /// underlying \ref UniSparseSpec class must not be \c NullMap.
    LemonRangeWrapper1<SparseEdgeIt, UniSparseSpec<GR, TR>>
    edgesOfSparse() const
    {
      return LemonRangeWrapper1<SparseEdgeIt, UniSparseSpec<GR, TR>>(*this);
    }

    /// \brief Iterator class for the nodes of the blocking tight subgraph.
    ///
    /// In case the latest edge was rejected (i.e. the functions
    /// \ref processNextEdge(), \ref processEdge(const Edge&) "processEdge(e)"
    /// return \c INVALID, or \ref checkSparse() return \c false), one can
    /// iterate on the node set of an inclusion-wise minimal tight subgraph
    /// blocking the insertion. Processing any edge invalidates this iterator.
    ///
    /// The following snippet uses \ref nodesOfLastBlockingTight() to access
    /// the node set of the blocking tight subgraph whenever
    /// \ref processNextEdge() returns \c false, i.e. rejects an edge.
    ///
    /// \code
    ///   UniSparseSpec<ListGraph> uss(g, k);
    ///   if(!uss.checkSparse()) {
    ///     for(const auto& n : uss.nodesOfLastBlockingTight()) {
    ///       std::cout << g.id(n) << std::endl;
    ///     }
    ///   }
    /// \endcode
    ///
    /// Alternatively, \ref LastBlockingTightNodeIt can be used for the same
    /// purpose as follows.
    ///
    /// \code
    ///   using BNodeIt = UniSparseSpec<ListGraph>::LastBlockingTightNodeIt;
    ///   UniSparseSpec<ListGraph> uss(g, k);
    ///   if(!uss.checkSparse()) {
    ///     for(BNodeIt n(uss); n != INVALID; ++n) {
    ///       std::cout << g.id(n) << std::endl;
    ///     }
    ///   }
    /// \endcode
    ///
    /// \pre The type of the edge map \ref
    /// UniSparseDefaultTraits::ToInputEdgeMap "ToInputEdgeMap" of the
    /// underlying \ref UniSparseSpec class must not be \c NullMap.
    /// \warning If the latest edge has been accepted, then the blocking tight
    /// subgraph and hence the behavior is undefined!
    class LastBlockingTightNodeIt {
      const UniSparseSpec* const _uss;
      DNodeIt _dNodeIt;

    public:
      // prevent accidental down casting and any other conversion
      template<typename T>
      LastBlockingTightNodeIt(const T&) = delete;

      /// \brief Constructor.
      ///
      /// Constructor. Sets the iterator to the first node.
      LastBlockingTightNodeIt(const UniSparseSpec& uss)
        : _uss(&uss), _dNodeIt(*_uss->_innerDigraph)
      {
        stepItToNextValid();
      }

      /// \brief Initializes the iterator to be invalid.
      ///
      /// Initializes the iterator to be invalid.
      /// \sa Invalid for more details.
      LastBlockingTightNodeIt(Invalid) : _uss(nullptr), _dNodeIt(INVALID)
      {}

      /// \brief Node conversion.
      ///
      /// Node conversion.
      operator Node() const
      {
        return _dNodeIt != INVALID ? (*_uss->_toInputNode)[_dNodeIt] : INVALID;
      }

      /// \brief Steps the iterator to the next node.
      ///
      /// Steps the iterator to the next node.
      LastBlockingTightNodeIt& operator++()
      {
        ++_dNodeIt;
        stepItToNextValid();
        return *this;
      }

      /// \brief Inequality operator.
      ///
      /// Inequality operator.
      /// \pre The compared iterators belong to the same instance of
      /// \ref UniSparseSpec.
      bool operator!=(const LastBlockingTightNodeIt& rhs) const
      {
        return _dNodeIt != rhs._dNodeIt;
      }

    private:
      void stepItToNextValid()
      {
        while(_dNodeIt != INVALID && _uss->_revBfs->reached(_dNodeIt)) {
          ++_dNodeIt;
        }
      }
    };

    /// \brief Returns the collection of the nodes of the blocking tight
    /// subgraph.
    ///
    /// This function can be used for iterating on the nodes of the blocking
    /// tight subgraph. It returns a wrapped LastBlockingTightNodeIt, which
    /// behaves as an STL container and can be used in range-based for loops
    /// and STL algorithms. Processing any edge invalidates this iterator.
    ///
    /// The following code demonstrates the usage of the wrapped iterator.
    ///
    /// \code
    ///   for(const auto& n : uss.nodesOfLastBlockingTight()) {
    ///     std::cout << g.id(n) << std::endl;
    ///   }
    /// \endcode
    ///
    /// \pre The type of the edge map \ref
    /// UniSparseDefaultTraits::ToInputEdgeMap "ToInputEdgeMap" of the
    /// underlying \ref UniSparseSpec class must not be \c NullMap.
    /// \warning If the latest edge has been accepted, then the blocking tight
    /// subgraph and hence the behavior is undefined!
    LemonRangeWrapper1<LastBlockingTightNodeIt, UniSparseSpec<GR, TR>>
    nodesOfLastBlockingTight() const
    {
      return LemonRangeWrapper1<LastBlockingTightNodeIt,
                                UniSparseSpec<GR, TR>>(*this);
    }

    /// \brief Iterator class for the edges of the blocking tight subgraph.
    ///
    /// In case the latest edge was rejected (i.e. the functions
    /// \ref processNextEdge(), \ref processEdge(const Edge&) "processEdge(e)"
    /// return \c INVALID, or \ref checkSparse() return \c false), one can
    /// iterate on the edge set of an inclusion-wise minimal tight subgraph
    /// blocking the insertion. Processing any edge invalidates this iterator.
    ///
    /// The following snippet uses \ref edgesOfLastBlockingTight() to access
    /// the edge set of the blocking tight subgraph after \ref checkSparse()
    /// returns \c false.
    ///
    /// \code
    ///   UniSparseSpec<ListGraph> uss(g, k);
    ///   if(!uss.checkSparse()) {
    ///     for(const auto& n : uss.edgesOfLastBlockingTight()) {
    ///       std::cout << g.id(n) << std::endl;
    ///     }
    ///   }
    /// \endcode
    ///
    /// Alternatively, \ref LastBlockingTightEdgeIt can be used for the same
    /// purpose as follows.
    ///
    /// \code
    ///   using BEdgeIt = UniSparseSpec<ListGraph>::LastBlockingTightEdgeIt;
    ///   UniSparseSpec<ListGraph> uss(g, k);
    ///   if(!uss.checkSparse()) {
    ///     for(BEdgeIt e(uss); e != INVALID; ++e) {
    ///       std::cout << g.id(e) << std::endl;
    ///     }
    ///   }
    /// \endcode
    ///
    /// \pre The latest edge must be rejected, otherwise the blocking tight
    /// subgraph and hence the behavior is undefined!
    /// \pre The type of the edge map \ref
    /// UniSparseDefaultTraits::ToInputEdgeMap "ToInputEdgeMap" of the
    /// underlying \ref UniSparseSpec class must not be \c NullMap.
    class LastBlockingTightEdgeIt {
      const UniSparseSpec* const _uss;
      DNodeIt _dNodeIt;
      OutArcIt _outArcIt;

    public:
      // prevent accidental down casting and any other conversion
      template<typename T>
      LastBlockingTightEdgeIt(const T&) = delete;

      /// \brief Constructor.
      ///
      /// Constructor. Sets the iterator to the first node.
      LastBlockingTightEdgeIt(const UniSparseSpec& uss)
        : _uss(&uss), _dNodeIt(*_uss->_innerDigraph)
      {
        if(_dNodeIt != INVALID) {
          _outArcIt = OutArcIt(*_uss->_innerDigraph, _dNodeIt);
          stepOutArcToNextValid();
        }
      }

      /// \brief Initializes the iterator to be invalid.
      ///
      /// Initializes the iterator to be invalid.
      /// \sa Invalid for more details.
      LastBlockingTightEdgeIt(Invalid)
        : _uss(nullptr), _dNodeIt(INVALID), _outArcIt(INVALID)
      {}

      /// \brief Edge conversion.
      ///
      /// Edge conversion.
      operator Edge() const
      {
        return _outArcIt != INVALID ? (*_uss->_toInputEdge)[_outArcIt]
          : INVALID;
      }

      /// \brief Steps the iterator to the next edge.
      ///
      /// Steps the iterator to the next edge.
      LastBlockingTightEdgeIt& operator++()
      {
        ++_outArcIt;
        stepOutArcToNextValid();
        return *this;
      }

      /// \brief Inequality operator.
      ///
      /// Inequality operator.
      /// \pre The compared iterators belong to the same instance of
      /// \ref UniSparseSpec.
      bool operator!=(const LastBlockingTightEdgeIt& rhs) const
      {
        return _dNodeIt != rhs._dNodeIt || _outArcIt != rhs._outArcIt;
      }

    private:
      void stepOutArcToNextValid()
      {
        const auto& dg = _uss->innerDigraph();
        while(true) {
          if(_outArcIt == INVALID) {
            // step to the next node
            if(++_dNodeIt != INVALID) {
              _outArcIt = OutArcIt(dg, _dNodeIt);
            }
            else {
              // no more edges left
              return;
            }
          }
          else if(!_uss->_revBfs->reached(dg.target(_outArcIt))) {
            // found the next arc
            return;
          }
          else {
            // arc is not in tight, take the next arc
            ++_outArcIt;
          }
        }
      }
    };

    /// \brief Returns the collection of the edges of the blocking tight
    /// subgraph.
    ///
    /// This function can be used for iterating on the edges of the last
    /// blocking tight subgraph. It returns a wrapped LastBlockingTightEdgeIt,
    /// which behaves as an STL container and can be used in range-based for
    /// loops and STL algorithms.
    /// Processing any edge invalidates this iterator.
    ///
    /// The following code demonstrates the usage of the wrapped iterator.
    ///
    /// \code
    ///   for(const auto& e : uss.edgesOfLastBlockingTight()) {
    ///     std::cout << g.id(e) << std::endl;
    ///   }
    /// \endcode
    ///
    /// \pre The type of the edge map \ref
    /// UniSparseDefaultTraits::ToInputEdgeMap "ToInputEdgeMap" of the
    /// underlying \ref UniSparseSpec class must not be \c NullMap.
    /// \warning If the latest edge has been accepted, then the blocking tight
    /// subgraph and hence the behavior is undefined!
    LemonRangeWrapper1<LastBlockingTightEdgeIt, UniSparseSpec<GR, TR>>
    edgesOfLastBlockingTight() const
    {
      return LemonRangeWrapper1<LastBlockingTightEdgeIt,
                                UniSparseSpec<GR, TR>>(*this);
    }
  };

  /// \brief Algorithms for \f$ (k,l) \f$-sparsity.
  ///
  /// An undirected graph \f$ G=(V,E) \f$ is called \f$ (k,l) \f$-sparse if
  /// \f$ i(X) \leq \max \{0,k|X|-l\} \f$ for every \f$ X \subseteq V \f$,
  /// where \f$ i(X) \f$ is the number of edges induced by the set \f$ X \f$ of
  /// nodes and \f$ 0 \leq l < 2k \f$. A graph is called \f$ (k,l) \f$-tight if
  /// it is \f$ (k,l) \f$-sparse and \f$ |E| = \max \{0,k|V|-l\} \f$. It is
  /// \f$ (k,l) \f$-spanning if it contains a \f$ (k,l) \f$-tight subgraph that
  /// spans the entire vertex set.
  ///
  /// This class provides an efficient implementation for extracting a
  /// maximum-size \f$ (k,l) \f$-sparse subgraph (that has maximum or minimum
  /// weight) of an undirected graph in time \f$ O(klmn) \f$, provided that
  /// \f$ 0 \leq l < 2k \f$. The space complexity is \f$ O(|V|) \f$. For the
  /// case \f$ l = 2k \f$, see the class \ref UniSparseSpec.
  ///
  /// There is also a \ref uniSparse() "function-type interface" called
  /// \ref uniSparse(), which is convenient in simpler use cases.
  ///
  /// \tparam GR The type of the undirected graph the algorithm runs on.
  /// The default type is \ref ListGraph.
  /// \tparam WM The type of the edge map that specifies the weights of the
  /// edges. It must conform to the \ref concepts::ReadMap "ReadMap" concept.
  /// The default map type is \ref NullMap "NullMap<GR::Edge, int>", which
  /// means that the problem is unweighted.
  /// \tparam TR The traits class that defines various types used in the
  /// algorithm. By default, it is \ref UniSparseDefaultTraits. In most cases,
  /// this parameter should not be set directly, consider to use the named
  /// template parameters instead.
#ifdef DOXYGEN
  template<typename GR, typename WM, typename TR>
#else
  template<typename GR = ListGraph,
           typename WM = NullMap<typename GR::Edge, int>,
           typename TR = UniSparseDefaultTraits<GR>>
#endif
  class UniSparse : public UniSparseSpec<GR, TR> {
  protected:
    using Parent = UniSparseSpec<GR, TR>;

    using Parent::_bfs;
    using Parent::_innerDigraph;
    using Parent::_inputGraph;
    using Parent::_k;
    using Parent::_nextEdgeIt;
    using Parent::_numEdges;
    using Parent::_numInserted;
    using Parent::_numNodes;
    using Parent::_outDeg;
    using Parent::_previousEdge;
    using Parent::_toInnerNode;

    using Parent::insertArc;
    using Parent::insertArcNoAssert;
    using Parent::reversePaths;

    friend class UniSparseBits; // TODO-ryiC: Remove this.

  public:
    using Parent::sparseSize;

    /// \brief The type of the graph the algorithm runs on.
    using Graph = GR;
    /// \brief The type of the map storing the edge weights.
    using WeightMap = WM;
    /// \brief The type of the inner digraph.
    using Digraph = typename TR::Digraph;
    /// \brief The type of the edge order container.
    using ProcessingOrderContainer = typename TR::ProcessingOrderContainer;
    /// \brief The type of the node map that converts the nodes of the inner
    /// digraph to those of the input graph.
    using ToInputNodeMap = typename TR::ToInputNodeMap;
    /// \brief The type of the node map that converts the nodes of the input
    /// graph to those of the inner digraph.
    using ToInnerNodeMap = typename TR::ToInnerNodeMap;
    /// \brief The type of the arc map that converts the arcs of the inner
    /// digraph to the edges of the input graph.
    using ToInputEdgeMap = typename TR::ToInputEdgeMap;
    /// \brief The type of the edge map that converts the edges of the input
    /// graph to the arcs of the inner digraph.
    using ToInnerArcMap = typename TR::ToInnerArcMap;
    /// \brief The promised range for l and k.
    using RangeSelector = typename TR::RangeSelector;
    /// \brief The \ref UniSparseDefaultTraits "traits class" of the algorithm.
    using Traits = TR;
    // The type of the weights.
    using Weight = typename WeightMap::Value;
    // The node map that stores the out-degrees in the inner digraph.
    using OutDegMap = typename Digraph::template NodeMap<int>;

  private:
    using Edge = typename GR::Edge;
    using Node = typename GR::Node;
    using EdgeIt = typename GR::EdgeIt;
    using NodeIt = typename GR::NodeIt;
    using Arc = typename Digraph::Arc;
    using ArcIt = typename Digraph::ArcIt;
    using OutArcIt = typename Digraph::OutArcIt;
    using DNode = typename Digraph::Node;
    using DNodeIt = typename Digraph::NodeIt;

  protected:
    // The parameters of \f$ (k,l) \f$-sparsity.
    const int _l;

    // The total weight of the accepted edges.
    Weight _sumWeights;
    // Indicates whether the weight is to be maximized.
    bool _maximize;
    // The current index in the _processingOrderContainer.
    int _currPOCIndex;

    // The edge map storing the weights of the edges.
    const WeightMap* _weights;
    // The container storing the edges in the order given by the weights.
    ProcessingOrderContainer* _processingOrderContainer;
    // Indicates whether _processingOrderContainer is locally allocated.
    bool _local_processingOrderContainer;

  public:
    /// \brief Constants for selecting the heuristic.
    ///
    /// Enum type containing constants for selecting the heuristic for the \ref
    /// run function in the unweighted case. \UniSparse provides 9 different
    /// heuristics for the processing order of the edges. These can only be
    /// used in the unweighted case, except for BASIC.
    enum Heuristic {

      /// In the unweighted case, \ref TRANSP is called, in the weighted case,
      /// the \ref BASIC heuristic is called.
      AUTO,

      /// The edges are processed in the order given by the EdgeIt.
      BASIC,

      /// Cyclically iterates over the nodes and selects the next unprocessed
      /// edge incident to the current node, and then moves to the next node.
      /// The accepted edges are oriented towards the current node.
      /// This heuristic tends to work best when the number of edges is
      /// significantly larger than the number of nodes. The space requirement
      /// is linear in the number of the edges of the input graph.
      TRANSP,

      /// A memory-optimized variant of the \c TRANSP heuristic. The
      /// processing order of the edges strongly depends of the id's of the
      /// nodes. The space requirement is linear in the number of the nodes of
      /// the input graph, but it tends to be slower than \c TRANSP.
      TRANSP_MEM,

      /// Cyclically iterates over the nodes and selects the next unprocessed
      /// edge incident to the current node as long as an edge is accepted at
      /// each node (or no more incident edges exist), before moving to the
      /// next node. The accepted edges are oriented towards the current node.
      /// The space requirement is linear in the number of the edges of the
      /// input graph.
      TRANSP_ONE_OUT,

      /// A memory-optimized variant of the \c TRANSP_ONE_OUT heuristic. The
      /// processing order of the edges strongly depends of the id's of the
      /// nodes. The space requirement is linear in the number of the nodes of
      /// the input graph, and it is only slightly slower than
      /// \c TRANSP_ONE_OUT.
      TRANSP_ONE_OUT_MEM,

      /// Finds \f$ \min \{l, 2k-l\} + (k-\ell)^+ \f$ spanning forests using
      /// BFS, then processes the rest of the edges according to the \ref BASIC
      /// heuristic. The space requirement is linear in the number of the edges
      /// of the input graph.
      FORESTS_BFS,

      /// Finds \f$ \min \{l, 2k-l\} + (k-\ell)^+ \f$ spanning forests using
      /// DFS, then processes the rest of the edges according to the \ref BASIC
      /// heuristic. The space requirement is linear in the number of the edges
      /// of the input graph.
      FORESTS_DFS,

      /// Finds \f$ \min \{l, 2k-l\} \f$ spanning forests and
      /// \f$ (k-\ell)^+ \f$ pseudoforests using BFS, then processes the rest
      /// of the edges according to the \ref BASIC heuristic. The space
      /// requirement is linear in the number of the edges of the input graph.
      PFORESTS_BFS,

      /// Finds \f$ \min \{l, 2k-l\} \f$ spanning forests and
      /// \f$ (k-\ell)^+ \f$ pseudoforests using DFS, then processes the rest
      /// of the edges according to the \ref BASIC heuristic. The space
      /// requirement is linear in the number of the edges of the input graph.
      PFORESTS_DFS,

      /// Iterates over the nodes and processes all incident edges for each
      /// node. The space requirement is linear in the number of the edges of
      /// the input graph.
      NODE_BASIC,

      /// Selects a node with minimal degree in the input graph and processes
      /// all its incident edges, then takes the next node. The space
      /// requirement is linear in the number of the edges of the input graph.
      NODE_DEG_MIN,

      /// Selects a node with minimal number of incident processed edges and
      /// processes all incident edges, then takes the next node. The space
      /// requirement is linear in the number of the edges of the input graph.
      NODE_PROC_MIN,

      /// Selects a node with minimal outdegree in the inner digraph and
      /// processes all incident edges, then take the next node. The space
      /// requirement is linear in the number of the edges of the input graph.
      NODE_OUT_DEG_MIN
    };

  protected:
    // AUTO
    class Auto {
      UniSparse& _us;

    public:
      Auto(UniSparse& us) : _us(us)
      {}

      bool checkSparse()
      {
        if(_us.weightedCase()) {
          return Basic(_us).checkSparse();
        }
        else {
          return Transp(_us).checkSparse();
        }
      }

      bool run()
      {
        if(_us.weightedCase()) {
          return Basic(_us).run();
        }
        else {
          return Transp(_us).run();
        }
      }
    };

    // BASIC
    class Basic {
      UniSparse& _us;

      template<bool checkSparse>
      bool basic()
      {
        if(_us.weightedCase()) {
          while(!_us.isAllDone()) {
            if(_us.weightedProcessNextEdge() == INVALID && checkSparse) {
              return false;
            }
          }
        }
        else {
          while(!_us.isAllDone()) {
            if(_us.unweightedProcessNextEdge() == INVALID && checkSparse) {
              return false;
            }
          }
        }
        return _us.isSparse();
      }

    public:
      Basic(UniSparse& us) : _us(us)
      {}

      bool checkSparse()
      {
        return basic<true>();
      }

      bool run()
      {
        return basic<false>();
      }
    };

    // TRANSP
    class Transp {
      UniSparse& _us;

      template<bool checkSparse>
      bool transp()
      {
        LEMON_ASSERT(!_us.weightedCase(),
                     "Transp is for the unweighted case only!");
        TEMPLATE_GRAPH_TYPEDEFS(Graph);
        const Graph& g = _us._inputGraph;
        typename Graph::template NodeMap<IncEdgeIt> incEdgeIts(g, INVALID);
        BoolEdgeMap processed(g, false);
        std::vector<Node> nodes;
        for(NodeIt n(g); n != INVALID; ++n) {
          incEdgeIts[n] = IncEdgeIt(g, n);
          if(incEdgeIts[n] != INVALID) {
            nodes.push_back(n);
          }
        }

        while(!nodes.empty()) {
          for(size_t i = 0; i < nodes.size(); ) { // no incr
            Node& n = nodes[i];
            IncEdgeIt& eit = incEdgeIts[n];
            if(!processed[eit]) {
              processed[eit] = true;
              if(_us.processEdge(eit, n) == INVALID && checkSparse) {
                return false;
              }
              if(_us.isAllDone()) {
                return _us.isSparse();
              }
            }
            if(++eit != INVALID) {
              ++i;
            }
            else {
              n = nodes.back();
              nodes.pop_back();
            }
          }
        }
        _us.forceAllProcessed();
        return _us.isSparse();
      }

    public:
      Transp(UniSparse& us) : _us(us)
      {}

      bool checkSparse()
      {
        return transp<true>();
      }

      bool run()
      {
        return transp<false>();
      }
    };

    // TRANSP_MEM
    class TranspMem {
      UniSparse& _us;

      template<bool checkSparse>
      bool transpMem()
      {
        LEMON_ASSERT(!_us.weightedCase(),
                     "TranspMem is for the unweighted case only!");
        TEMPLATE_GRAPH_TYPEDEFS(Graph);
        const Graph& g = _us._inputGraph;
        typename Graph::template NodeMap<TrueIncEdgeIt> incEdgeIts(g, INVALID);
        std::vector<Node> nodes;
        for(NodeIt n(g); n != INVALID; ++n) {
          incEdgeIts[n] = TrueIncEdgeIt(g, n);
          if(incEdgeIts[n] != INVALID) {
            nodes.push_back(n);
          }
        }

        while(!nodes.empty()) {
          for(size_t i = 0; i < nodes.size(); ) { // no incr
            Node& n = nodes[i];
            TrueIncEdgeIt& eit = incEdgeIts[n];
            if(!(n < g.oppositeNode(n, eit))) {
              if(_us.processEdge(eit, n) == INVALID && checkSparse) {
                return false;
              }
              if(_us.isAllDone()) {
                return _us.isSparse();
              }
            }
            if(++eit != INVALID) {
              ++i;
            }
            else {
              n = nodes.back();
              nodes.pop_back();
            }
          }
        }
        _us.forceAllProcessed();
        return _us.isSparse();
      }

    public:
      TranspMem(UniSparse& us) : _us(us)
      {}

      bool checkSparse()
      {
        return transpMem<true>();
      }

      bool run()
      {
        return transpMem<false>();
      }
    };

    // TRANSP_ONE_OUT
    class TranspOneOut {
      UniSparse& _us;

      template<bool checkSparse>
      bool transpOneOut()
      {
        LEMON_ASSERT(!_us.weightedCase(),
                     "TranspOneOut is for the unweighted case only!");
        TEMPLATE_GRAPH_TYPEDEFS(Graph);
        const Graph& g = _us._inputGraph;
        typename Graph::template NodeMap<IncEdgeIt> incEdgeIts(g, INVALID);
        BoolEdgeMap processed(g, false);
        std::vector<Node> nodes;
        for(NodeIt n(g); n != INVALID; ++n) {
          incEdgeIts[n] = IncEdgeIt(g, n);
          if(incEdgeIts[n] != INVALID) {
            nodes.push_back(n);
          }
        }

        while(!nodes.empty()) {
          for(size_t i = 0; i < nodes.size(); ) { // no incr
            Node& n = nodes[i];
            IncEdgeIt& eit = incEdgeIts[n];
            while(eit != INVALID && processed[eit]) {
              ++eit;
            }
            if(eit != INVALID) {
              processed[eit] = true;
              const bool rejected = (_us.processEdge(eit, n) == INVALID);
              if(checkSparse && rejected) {
                return false;
              }
              if(_us.isAllDone()) {
                return _us.isSparse();
              }
              ++eit;
              i += !rejected;
            }
            else {
              n = nodes.back();
              nodes.pop_back();
            }
          }
        }
        _us.forceAllProcessed();
        return _us.isSparse();
      }

    public:
      TranspOneOut(UniSparse& us) : _us(us)
      {}

      bool checkSparse()
      {
        return transpOneOut<true>();
      }

      bool run()
      {
        return transpOneOut<false>();
      }
    };

    // TRANSP_ONE_OUT_MEM
    class TranspOneOutMem {
      UniSparse& _us;

      template<bool checkSparse>
      bool transpOneOutMem()
      {
        LEMON_ASSERT(!_us.weightedCase(),
                     "TranspOneOutMem is for the unweighted case only!");
        TEMPLATE_GRAPH_TYPEDEFS(Graph);
        const Graph& g = _us._inputGraph;
        typename Graph::template NodeMap<TrueIncEdgeIt> incEdgeIts(g, INVALID);
        std::vector<Node> nodes;
        for(NodeIt n(g); n != INVALID; ++n) {
          incEdgeIts[n] = TrueIncEdgeIt(g, n);
          if(incEdgeIts[n] != INVALID) {
            nodes.push_back(n);
          }
        }

        while(!nodes.empty()) {
          for(size_t i = 0; i < nodes.size(); ) { // no incr
            Node& n = nodes[i];
            TrueIncEdgeIt& eit = incEdgeIts[n];
            while(eit != INVALID && n < g.oppositeNode(n, eit)) {
              ++eit;
            }
            if(eit != INVALID) {
              const bool rejected = (_us.processEdge(eit, n) == INVALID);
              if(checkSparse && rejected) {
                return false;
              }
              if(_us.isAllDone()) {
                return _us.isSparse();
              }
              ++eit;
              i += !rejected;
            }
            else {
              n = nodes.back();
              nodes.pop_back();
            }
          }
        }
        _us.forceAllProcessed();
        return _us.isSparse();
      }

    public:
      TranspOneOutMem(UniSparse& us) : _us(us)
      {}

      bool checkSparse()
      {
        return transpOneOutMem<true>();
      }

      bool run()
      {
        return transpOneOutMem<false>();
      }

    };

    // Forced, dangerous processEdge. To be used in the forest heuristics only.
    void processEdgeUnchecked(const Edge& e, const Node from)
    {
      LEMON_ASSERT(_inputGraph.u(e) == from || _inputGraph.v(e) == from,
                   "Bad orientation request!");
      const DNode u = (*_toInnerNode)[from];
      const DNode v = (*_toInnerNode)[_inputGraph.oppositeNode(from, e)];
      registerAcceptance(e, insertArcNoAssert(u, v));
    }

    class ForestBase {
      template<typename DGR>
      int maxOutDeg(const DGR& digraph)
      {
        int maxDeg = 0;
        for(DNodeIt n(digraph); n != INVALID; ++n) {
          const int deg = countOutArcs(digraph, n);
          if(maxDeg < deg) {
            maxDeg = deg;
          }
        }
        return maxDeg;
      }

    public:
      template<typename DGR>
      bool checkInnerDigraph(const DGR& digraph, const int k, const int l)
      {
        LEMON_ASSERT(countNodes(digraph) == 0 || maxOutDeg(digraph) <= k,
                     "Bad orientation!");
        // Undirector<const DGR> undir(digraph);
        // uniSparse(undir, k, l).checkSparse();
        ignore_unused_variable_warning(digraph, k, l);
        return true;
      }

      template<typename SubGraph, typename ReachedMap, typename Queue>
      void findAndProcessForestBFS(UniSparse& us, SubGraph& subGraph,
                                   ReachedMap& reached, Queue& queue)
      {
        LEMON_ASSERT(us._numNodes == 0
                     || mapMaxValue(subGraph, reached) == 0,
                     "Bad reached resetting!");
        LEMON_ASSERT(queue.size() == 0, "Bad queue!");
        size_t qHead = 0;
        for(typename SubGraph::NodeIt r(subGraph); r != INVALID; ++r) {
          if(!reached[r]) {
            LEMON_ASSERT(qHead == queue.size(), "Bad start of a comp!");
            queue.push_back(r);
            reached[r] = true;
            while(qHead != queue.size()) {
              Node u = queue[qHead++];
              typedef typename SubGraph::IncEdgeIt SIncEdgeIt;
              for(SIncEdgeIt e(subGraph, u); e != INVALID; ++e) {
                const Node v = subGraph.oppositeNode(u, e);
                if(!reached[v]) {
                  us.processEdgeUnchecked(e, v);
                  reached[v] = true;
                  queue.push_back(v);
                  subGraph.disable(e);
                }
              }
            }
            LEMON_ASSERT(qHead == queue.size(), "Bad queue handling!");
          }
        }
      }

      template<typename SubGraph, typename ReachedMap, typename Stack>
      void findAndProcessForestDFS(UniSparse& us, SubGraph& subGraph,
                                   ReachedMap& reached, Stack& stack)
      {
        LEMON_ASSERT(us._numNodes == 0
                     || mapMaxValue(subGraph, reached) == 0,
                     "Bad reached resetting!");
        // run dfs from each unprocessed node
        for(typename SubGraph::NodeIt r(subGraph); r != INVALID; ++r) {
          if(!reached[r]) {
            reached[r] = true;
            stack.front() = typename SubGraph::IncEdgeIt(subGraph, r);
            int stackHead = 0;
            while(stackHead >= 0) {
              auto& edgeIt = stack[stackHead];
              if(edgeIt == INVALID) {
                --stackHead;
                continue;
              }
              LEMON_ASSERT(subGraph.status(edgeIt),
                           "Unprocessed hidden edge!");
              Node n;
              if(!reached[n = subGraph.runningNode(edgeIt)]) {
                subGraph.disable(edgeIt);
                us.processEdgeUnchecked(edgeIt, n);
                reached[n] = true;
                stack[++stackHead] = typename SubGraph::IncEdgeIt(subGraph, n);
              }
              ++edgeIt;
            }
          }
        }
      }
    };

    // FORESTS_BFS
    class ForestsBFS : private ForestBase {
      UniSparse& _us;

      using ForestBase::findAndProcessForestBFS;
      using ForestBase::checkInnerDigraph;

      template<bool checkSparse>
      bool forestsBFS()
      {
        TEMPLATE_GRAPH_TYPEDEFS(Graph);
        using FE = FilterEdges<const Graph>;

        const Graph& g = _us._inputGraph;
        const int k = _us._k;
        const int l = _us._l;
        const int numOfForests = (l <= k) ? k : (2 * k - l);
        BoolEdgeMap edgeFilter(g, true);
        FE subGraph(g, edgeFilter); // non-forest edges
        if(numOfForests) {
          BoolNodeMap reached(g, false);
          std::vector<Node> queue;
          queue.reserve(_us._numNodes);

          findAndProcessForestBFS(_us, subGraph, reached, queue);
          for(int i = 1; i < numOfForests; ++i) {
            // reset reached and queue
            for(const Node u : queue) {
              reached[u] = false;
            }
            queue.resize(0);

            findAndProcessForestBFS(_us, subGraph, reached, queue);
          }
          LEMON_ASSERT(checkInnerDigraph(_us.innerDigraph(), k, l),
                       "Union of forests is not sparse!");
        }
        typedef typename FE::EdgeIt FEdgeIt;
        for(FEdgeIt eit(subGraph); eit != INVALID && !_us.isAllDone(); ++eit) {
          if(_us.processEdge(eit) == INVALID && checkSparse) {
            return false;
          }
        }
        _us.forceAllProcessed();
        return _us.isSparse();
      }

    public:
      ForestsBFS(UniSparse& us) : _us(us)
      {}

      bool checkSparse()
      {
        return forestsBFS<true>();
      }

      bool run()
      {
        return forestsBFS<false>();
      }
    };

    // FOREST_DFS
    class ForestsDFS : private ForestBase {
      UniSparse& _us;

      using ForestBase::findAndProcessForestDFS;
      using ForestBase::checkInnerDigraph;

      template<bool checkSparse>
      bool forestsDFS()
      {
        TEMPLATE_GRAPH_TYPEDEFS(Graph);
        using FE = FilterEdges<const Graph>;

        const Graph& g = _us._inputGraph;
        const int k = _us._k;
        const int l = _us._l;
        const int numOfForests = (l <= k) ? k : (2 * k - l);

        BoolEdgeMap edgeFilter(g, true);
        FE subGraph(g, edgeFilter);

        if(numOfForests) {
          BoolNodeMap reached(g, false);
          // holds the next edge to process on each level
          std::vector<typename FE::IncEdgeIt> stack(_us._numNodes);
          findAndProcessForestDFS(_us, subGraph, reached, stack);
          for(int i = 1; i < numOfForests; ++i) {
            mapFill(g, reached, false);
            findAndProcessForestDFS(_us, subGraph, reached, stack);
          }
          LEMON_ASSERT(checkInnerDigraph(_us.innerDigraph(), k, l),
                       "Union of forests is not sparse!");
        }
        typedef typename FE::EdgeIt FEdgeIt;
        for(FEdgeIt eit(subGraph); eit != INVALID && !_us.isAllDone(); ++eit) {
          if(_us.processEdge(eit) == INVALID && checkSparse) {
            return false;
          }
        }
        _us.forceAllProcessed();
        return _us.isSparse();
      }

    public:
      ForestsDFS(UniSparse& us) : _us(us)
      {}

      bool checkSparse()
      {
        return forestsDFS<true>();
      }

      bool run()
      {
        return forestsDFS<false>();
      }
    };

    // PFORESTS_BFS
    class PForestsBFS : private ForestBase {
      UniSparse& _us;

      using ForestBase::findAndProcessForestBFS;
      using ForestBase::checkInnerDigraph;

      template<bool checkSparse>
      bool pForestsBFS()
      {
        TEMPLATE_GRAPH_TYPEDEFS(Graph);
        typedef FilterEdges<const Graph> FE;

        const Graph& g = _us._inputGraph;
        const int k = _us._k;
        const int l = _us._l;
        const int numOfForests = std::min(l, 2*k - l);
        const int numOfPForests = std::max(0, k - l);

        BoolEdgeMap edgeFilter(g, true);
        FE subGraph(g, edgeFilter);
        BoolNodeMap reached(g, false);

        std::vector<Node> queue;
        queue.reserve(_us._numNodes);
        // first, find numOfForests pseudo forests
        typename Graph::template NodeMap<Edge> pred(g, INVALID);
        for(int i = 0; i < numOfPForests; ++i) {
          // reset reached and queue
          for(const Node u : queue) {
            reached[u] = false;
          }
          queue.resize(0);

          LEMON_ASSERT(_us._numNodes == 0
                       || mapMaxValue(g, reached) == 0,
                       "Bad reached resetting!");
          // run bfs
          size_t qHead = 0;
          size_t qHeadPrev = 0;
          for(NodeIt r(g); r != INVALID; ++r) {
            if(!reached[r]) {
              LEMON_ASSERT(qHead == queue.size(), "Bad start of a comp!");
              Edge pseudoEdge = INVALID;
              queue.push_back(r);
              pred[r] = INVALID;
              reached[r] = true;
              qHeadPrev = qHead;
              while(qHead != queue.size()) {
                Node u = queue[qHead++];
                typedef typename FE::IncEdgeIt FIncEdgeIt;
                for(FIncEdgeIt e(subGraph, u); e != INVALID; ++e) {
                  const Node v = subGraph.oppositeNode(u, e);
                  if(!reached[v]) {
                    pred[v] = e;
                    reached[v] = true;
                    queue.push_back(v);
                    edgeFilter[e] = false;
                  }
                  else if(i < numOfPForests
                          && pseudoEdge == INVALID) {
                    pseudoEdge = e;
                    edgeFilter[pseudoEdge] = false;
                  }
                }
              }
              // A proper orientation: orient the path from an endpoint of
              // the pseudo edge to the root (this path includes the pseudo
              // edge), then orient the rest of the edges toward the root.
              // first, traverse and orient the path to the root r
              if(pseudoEdge != INVALID) {
                Node u = g.u(pseudoEdge);
                // process pseudo edge
                _us.processEdgeUnchecked(pseudoEdge, u);
                // process the path to the root, directed away from it
                while((pseudoEdge = pred[u]) != INVALID) {
                  pred[u] = INVALID;
                  u = subGraph.oppositeNode(u, pseudoEdge);
                  _us.processEdgeUnchecked(pseudoEdge, u);
                }
              }
              LEMON_ASSERT(qHead == queue.size(), "Bad queue handling!");
              // second, orient the rest of the edges toward the root
              for(size_t j = qHeadPrev + 1; j < qHead; ++j) {
                const Node u = queue[j];
                const Edge& e = pred[u];
                if(e != INVALID) {
                  _us.processEdgeUnchecked(e, u);
                }
              }
            }
          }
        }
        // second, find numOfForests forests
        for(int i = 0; i < numOfForests; ++i) {
          // reset reached and queue
          for(const Node u : queue) {
            reached[u] = false;
          }
          queue.resize(0);

          findAndProcessForestBFS(_us, subGraph, reached, queue);
        }
        LEMON_ASSERT(checkInnerDigraph(_us.innerDigraph(), k, l),
                     "Union of forests is not sparse!");
        typedef typename FE::EdgeIt FEdgeIt;
        for(FEdgeIt eit(subGraph); eit != INVALID && !_us.isAllDone(); ++eit) {
          if(_us.processEdge(eit) == INVALID && checkSparse) {
            return false;
          }
        }
        _us.forceAllProcessed();
        return _us.isSparse();
      }

    public:
      PForestsBFS(UniSparse& us) : _us(us)
      {}

      bool checkSparse()
      {
        return pForestsBFS<true>();
      }

      bool run()
      {
        return pForestsBFS<false>();
      }
    };

    // PFORESTS_DFS
    class PForestsDFS : private ForestBase {
      UniSparse& _us;

      using ForestBase::findAndProcessForestDFS;
      using ForestBase::checkInnerDigraph;

      template<bool checkSparse>
      bool pForestsDFS()
      {
        TEMPLATE_GRAPH_TYPEDEFS(Graph);
        typedef FilterEdges<const Graph> FE;

        const Graph& g = _us._inputGraph;
        const int k = _us._k;
        const int l = _us._l;
        const int numOfForests = std::min(l, 2*k - l);
        const int numOfPForests = std::max(0, k - l);

        BoolEdgeMap edgeFilter(g, true);
        FE subGraph(g, edgeFilter);
        BoolNodeMap reached(g, false);

        // holds the next edge to process on each level
        std::vector<typename FE::IncEdgeIt> stack(_us._numNodes);
        // first, find numOfForests pseudo forests
        typename Graph::template NodeMap<Edge> pred(g, INVALID);
        for(int i = 0; i < numOfPForests; ++i) {
          if(i > 0) {
            mapFill(g, reached, false);
          }
          LEMON_ASSERT(_us._numNodes == 0
                       || mapMaxValue(g, reached) == 0,
                       "Bad reached resetting!");
          // run dfs from each unprocessed node
          for(NodeIt r(g); r != INVALID; ++r) {
            if(!reached[r]) {
              bool pseudoEdgeFound = false;
              pred[r] = INVALID;
              reached[r] = true;
              stack.front() = typename FE::IncEdgeIt(subGraph, r);
              int stackHead = 0;
              while(stackHead >= 0) {
                auto& edgeIt = stack[stackHead];
                if(edgeIt == INVALID // all enabled inc. edges are processed
                   || (!edgeFilter[edgeIt] // the edge is hidden
                       && ++edgeIt == INVALID)) { // the rest are processed
                  --stackHead;
                  continue;
                }
                LEMON_ASSERT(edgeIt != INVALID, "Should have stepped back!");
                LEMON_ASSERT(edgeFilter[edgeIt],
                             "Two unprocessed hidden edges?!");
                Node n;
                if(!reached[n = subGraph.runningNode(edgeIt)]) {
                  edgeFilter[edgeIt] = false;
                  pred[n] = edgeIt;
                  reached[n] = true;
                  stack[++stackHead] = typename FE::IncEdgeIt(subGraph, n);
                }
                else if(i < numOfPForests && !pseudoEdgeFound) {
                  pseudoEdgeFound = true;
                  Edge pseudoEdge = edgeIt;
                  edgeFilter[edgeIt] = false;
                  Node u = g.u(pseudoEdge);
                  // process pseudo edge
                  _us.processEdgeUnchecked(pseudoEdge, u);
                  // process the path to the root, directed away from it
                  while((pseudoEdge = pred[u]) != INVALID) {
                    pred[u] = INVALID;
                    u = subGraph.oppositeNode(u, pseudoEdge);
                    _us.processEdgeUnchecked(pseudoEdge, u);
                  }
                }
                ++edgeIt;
              }
            }
          }
          for(NodeIt u(g); u != INVALID; ++u) {
            const Edge& e = pred[u];
            if(e != INVALID) {
              _us.processEdgeUnchecked(e, u);
            }
          }
        }
        // second, find numOfForests forests
        if(numOfForests) {
          if(numOfPForests) {
            mapFill(g, reached, false);
          }
          findAndProcessForestDFS(_us, subGraph, reached, stack);
        }
        for(int i = 1; i < numOfForests; ++i) {
          mapFill(g, reached, false);
          findAndProcessForestDFS(_us, subGraph, reached, stack);
        }
        LEMON_ASSERT(checkInnerDigraph(_us.innerDigraph(), k, l),
                     "Union of forests is not sparse!");
        typedef typename FE::EdgeIt FEdgeIt;
        for(FEdgeIt eit(subGraph); eit != INVALID && !_us.isAllDone(); ++eit) {
          if(_us.processEdge(eit) == INVALID && checkSparse) {
            return false;
          }
        }
        _us.forceAllProcessed();
        return _us.isSparse();
      }

    public:
      PForestsDFS(UniSparse& us) : _us(us)
      {}

      bool checkSparse()
      {
        return pForestsDFS<true>();
      }

      bool run()
      {
        return pForestsDFS<false>();
      }
    };

    // NODE_BASIC
    class NodeBasic {
      UniSparse& _us;

      template<bool checkSparse>
      bool nodeBasic()
      {
        const auto& g = _us._inputGraph;
        TEMPLATE_GRAPH_TYPEDEFS(Graph);

        typename Graph::template EdgeMap<bool> processed(g, false);
        for(NodeIt n(g); n != INVALID; ++n) {
          for(IncEdgeIt e(g, n); e != INVALID; ++e) {
            if(!processed[e]) {
              processed.set(e, true);
              if(_us.processEdge(e, n) == INVALID && checkSparse) {
                return false;
              }
              if(_us.isAllDone()) {
                return _us.isSparse();
              }
            }
          }
        }
        _us.forceAllProcessed();
        return _us.isSparse();
      }

    public:
      NodeBasic(UniSparse& us) : _us(us)
      {}

      bool checkSparse()
      {
        return nodeBasic<true>();
      }

      bool run()
      {
        return nodeBasic<false>();
      }
    };

    // NODE_DEG_MIN
    template<typename US,       // U is either UniSparse or UniSparseComp
             bool orientToMin>  // orient the edge towards the current node?
    class NodeDegMinBase {
      US& _us;

      template<bool checkSparse>
      bool nodeDegMinBase()
      {
        const auto& g = _us._inputGraph;
        TEMPLATE_GRAPH_TYPEDEFS(Graph);

        BoolEdgeMap processed(g, false);
        using BH = BucketHeap<IntNodeMap>;
        IntNodeMap hm(g, BH::PRE_HEAP);
        BH bh(hm);
        for(NodeIt n(g); n != INVALID; ++n) {
          bh.push(n, countTrueIncEdges(g, n));
        }

        while(!bh.empty()) {
          const Node minNode = bh.top();
          bh.pop();
          LEMON_ASSERT(minNode != INVALID, "");
          _us.conditionallyInitNode(minNode);
          for(IncEdgeIt e(g, minNode); e != INVALID; ++e) {
            if(!processed[e]) {
              const Node u = g.oppositeNode(minNode, e);
              if(u != minNode && bh.state(u) != BH::POST_HEAP) {
                bh.decrease(u, bh[u] - 1);
              }
              processed.set(e, true);
              const Node from = orientToMin ? u : minNode;
              if(_us.processEdge(e, from) == INVALID && checkSparse) {
                return false;
              }
              if(_us.isAllDone()) {
                return _us.isSparse();
              }
            }
          }
        }
        _us.forceAllProcessed();
        return _us.isSparse();
      }

    public:
      NodeDegMinBase(US& us) : _us(us)
      {}

      bool checkSparse()
      {
        return nodeDegMinBase<true>();
      }

      bool run()
      {
        return nodeDegMinBase<false>();
      }
    };

    using NodeDegMin = NodeDegMinBase<UniSparse, false>;

    // NODE_PROC_MIN
    template<typename US,       // U is either UniSparse or UniSparseComp
             bool orientToMin>  // orient the edge towards the current node?
    class NodeProcMinBase {
      US& _us;

      template<bool checkSparse>
      bool nodeProcMinBase()
      {
        const auto& g = _us._inputGraph;
        TEMPLATE_GRAPH_TYPEDEFS(Graph);

        BoolEdgeMap processed(g, false);
        using BH = BucketHeap<IntNodeMap>;
        IntNodeMap hm(g, BH::PRE_HEAP);
        BH bh(hm);
        for(NodeIt n(g); n != INVALID; ++n) {
          bh.push(n, 0);
        }

        for(int i = 0; i < _us._numNodes; ++i) {
          const Node minNode = bh.top();
          bh.pop();
          _us.conditionallyInitNode(minNode);
          for(IncEdgeIt e(g, minNode); e != INVALID; ++e) {
            if(!processed[e]) {
              const Node u = g.oppositeNode(minNode, e);
              processed.set(e, true);
              const Node from = orientToMin ? u : minNode;
              if(_us.processEdge(e, from) == INVALID && checkSparse) {
                return false;
              }
              if(_us.isAllDone()) {
                return _us.isSparse();
              }
              if(u != minNode) {
                bh.increase(u, bh[u] + 1);
              }
            }
          }
        }
        _us.forceAllProcessed();
        return _us.isSparse();
      }

    public:
      NodeProcMinBase(US& us) : _us(us)
      {}

      bool checkSparse()
      {
        return nodeProcMinBase<true>();
      }

      bool run()
      {
        return nodeProcMinBase<false>();
      }
    };

    using NodeProcMin = NodeProcMinBase<UniSparse, false>;

    // NODE_OUT_DEG_MIN
    template<typename US,       // U is either UniSparse or UniSparseComp
             bool orientToMin>  // orient the edge towards the current node?
    class NodeOutDegMinBase {
      US& _us;

      template<bool checkSparse>
      bool nodeOutDegMinBase()
      {
        const auto& g = _us._inputGraph;
        const auto& digraph = _us.innerDigraph();
        const auto& toInnerNode = _us.toInnerNodeMap();
        TEMPLATE_GRAPH_TYPEDEFS(Graph);

        BoolEdgeMap processed(g, false);
        using BH = BucketHeap<IntNodeMap>;
        IntNodeMap hm(g, BH::PRE_HEAP);
        BH bh(hm);
        for(NodeIt n(g); n != INVALID; ++n) {
          bh.push(n, 0);
        }

        for(int i = 0; i < _us._numNodes; ++i) {
          const Node minNode = bh.top();
          bh.pop();
          _us.conditionallyInitNode(minNode);
          for(IncEdgeIt e(g, minNode); e != INVALID; ++e) {
            if(!processed[e]) {
              const Node u = g.oppositeNode(minNode, e);
              processed.set(e, true);
              const Node from = orientToMin ? u : minNode;
              const auto a = _us.processEdge(e, from);
              if(a == INVALID && checkSparse) {
                return false;
              }
              if(_us.isAllDone()) {
                return _us.isSparse();
              }
              if(a != INVALID && minNode != u) {
                const Node inputNode = digraph.source(a) == toInnerNode[u]
                  ? u : minNode;
                if(bh.state(inputNode) != BH::POST_HEAP) {
                  bh.increase(inputNode, bh[inputNode] + 1);
                }
              }
            }
          }
        }
        _us.forceAllProcessed();
        return _us.isSparse();
      }

    public:
      NodeOutDegMinBase(US& us) : _us(us)
      {}

      bool checkSparse()
      {
        return nodeOutDegMinBase<true>();
      }

      bool run()
      {
        return nodeOutDegMinBase<false>();
      }
    };

    using NodeOutDegMin = NodeOutDegMinBase<UniSparse, false>;

    // make isAllDone return true
    void forceAllProcessed()
    {
      if(weightedCase()) {
        _currPOCIndex = _numEdges;
      }
      else {
        _nextEdgeIt = INVALID;
      }
    }

    // init node if applicable
    void conditionallyInitNode(const Node)
    {}

  public:
    using Create = UniSparse;

    /// \name Named Template Parameters

    /// @{

    /// \brief \ref named-templ-param "Named parameter" for setting
    /// \c InnerDigraph type.
    ///
    /// \ref named-templ-param "Named parameter" for setting
    /// \c InnerDigraph type.
    ///
    /// It must provide \p addNode(), \p addArc(), \p reverseArc() and
    /// \p clear() member functions.
    template<typename DGR>
    struct SetInnerDigraph
      : public UniSparse<GR, WM,
                         typename Parent
                         ::template SetInnerDigraphTraits<DGR>> {
      using Create = UniSparse<GR, WM,
                               typename Parent
                               ::template SetInnerDigraphTraits<DGR>>;
    };

    template<typename POC>
    struct SetProcessingOrderContainerTraits : public Traits {
      using ProcessingOrderContainer = POC;

      static ProcessingOrderContainer* createProcessingOrderContainer()
      {
        LEMON_ASSERT(false, "ProcessingOrderContainer is not initialized!");
        return nullptr;
      }
    };

    /// \brief \ref named-templ-param "Named parameter" for setting
    /// \c ProcessingOrderContainer type.
    ///
    /// \ref named-templ-param "Named parameter" for setting
    /// \c ProcessingOrderContainer type.
    ///
    /// It must provide \p size(), \p resize(), \p operator[], \p begin() and
    /// \p end() member functions.
    template<typename POC>
    struct SetProcessingOrderContainer
      : public UniSparse<GR, WM, SetProcessingOrderContainerTraits<POC>> {
      using Create = UniSparse<GR, WM, SetProcessingOrderContainerTraits<POC>>;
    };

    /// \brief \ref named-templ-param "Named parameter" for setting
    /// \c ToInputNodeMap type.
    ///
    /// \ref named-templ-param "Named parameter" for setting
    /// \c ToInputNodeMap type.
    ///
    /// It must conform to the \ref concepts::ReadWriteMap
    /// "ReadWriteMap" concept.
    ///
    /// \warning The class \ref LastBlockingTightNodeIt and the
    /// function \ref nodesOfLastBlockingTight() read this node map,
    /// hence it must not be \c NullMap if any of them is used.
    template<typename NM>
    struct SetToInputNodeMap
      : public UniSparse<GR, WM,
                         typename Parent
                         ::template SetToInputNodeMapTraits<NM>> {
      using Create = UniSparse<GR, WM,
                               typename Parent
                               ::template SetToInputNodeMapTraits<NM>>;
    };

    /// \brief \ref named-templ-param "Named parameter" for setting
    /// \c ToInnerNodeMap type.
    ///
    /// \ref named-templ-param "Named parameter" for setting
    /// \c ToInnerNodeMap type.
    ///
    /// It must conform to the \ref concepts::ReadWriteMap
    /// "ReadWriteMap" concept.
    /// \warning This node map must never be \c NullMap since we write it in
    /// \ref init() and then read it during processing the edges.
    template<typename NM>
    struct SetToInnerNodeMap
      : public UniSparse<GR, WM,
                         typename Parent
                         ::template SetToInnerNodeMapTraits<NM>> {
      using Create = UniSparse<GR, WM,
                               typename Parent
                               ::template SetToInnerNodeMapTraits<NM>>;
    };

    /// \brief \ref named-templ-param "Named parameter" for setting
    /// \c ToInputEdgeMap type.
    ///
    /// \ref named-templ-param "Named parameter" for setting
    /// \c ToInputEdgeMap type.
    ///
    /// It must conform to the \ref concepts::ReadWriteMap
    /// "ReadWriteMap" concept.
    ///
    /// \warning The class \ref LastBlockingTightEdgeIt and the
    /// function \ref edgesOfLastBlockingTight() read this edge map,
    /// hence it must not be \c NullMap if any of them is used.
    template<typename AM>
    struct SetToInputEdgeMap
      : public UniSparse<GR, WM,
                         typename Parent
                         ::template SetToInputEdgeMapTraits<AM>> {
      using Create = UniSparse<GR, WM,
                               typename Parent
                               ::template SetToInputEdgeMapTraits<AM>>;
    };

    /// \brief \ref named-templ-param "Named parameter" for setting
    /// \c ToInnerArcMap type.
    ///
    /// \ref named-templ-param "Named parameter" for setting
    /// \c ToInnerArcMap type.
    ///
    /// It must conform to the \ref concepts::ReadWriteMap
    /// "ReadWriteMap" concept.
    /// \warning This edge map must not be \c NullMap if the function
    /// \ref UniSparse::isInduced() "isInduced" is used. For example, use
    /// \ref Graph::EdgeMap<typename Digraph::Arc>.
    template<typename EM>
    struct SetToInnerArcMap
      : public UniSparse<GR, WM,
                         typename Parent
                         ::template SetToInnerArcMapTraits<EM>> {
      using Create = UniSparse<GR, WM,
                               typename Parent
                               ::template SetToInnerArcMapTraits<EM>>;
    };

    struct SetLowerRangeTraits : public Traits {
      using RangeSelector = unisparse_bits::LowerRange;
    };

    /// \brief \ref named-templ-param "Named parameter" for setting
    /// \c RangeSelector to \c LowerRange.
    ///
    /// \ref named-templ-param "Named parameter" for setting
    /// \c RangeSelector to \c LowerRange.
    struct SetLowerRange
      : public UniSparse<Graph, WM, SetLowerRangeTraits> {
      using Create = UniSparse<GR, WM, SetLowerRangeTraits>;
    };

    struct SetUpperRangeTraits : public Traits {
      using RangeSelector = unisparse_bits::UpperRange;
    };

    /// \brief \ref named-templ-param "Named parameter" for setting
    /// \c RangeSelector to \c UpperRange.
    ///
    /// \ref named-templ-param "Named parameter" for setting
    /// \c RangeSelector to \c UpperRange.
    struct SetUpperRange
      : public UniSparse<Graph, WM, SetUpperRangeTraits> {
      using Create = UniSparse<Graph, WM, SetUpperRangeTraits>;
    };

    /// @}

  protected:
    UniSparse(const Graph& g, const int k, const int l, const WeightMap* w)
      : Parent(g, k, l), _l(l), _sumWeights(0), _maximize(true),
        _currPOCIndex(0), _weights(w), _processingOrderContainer(nullptr),
        _local_processingOrderContainer(false)
    {
      LEMON_ASSERT(_l >= 0 && _l < 2 * _k,
                   "Parameter l must be in {0,...,2k-1}!");
      using namespace unisparse_bits;
      LEMON_ASSERT((std::is_same<RangeSelector, LowerRange>::value
                    <= (_l <= _k)), "Bad range! Broken promise l <= k.");
      LEMON_ASSERT((std::is_same<RangeSelector, UpperRange>::value
                    <= (_l > _k)), "Bad range! Broken promise l > k.");
    }

  public:
    /// \brief Constructor.
    ///
    /// Constructor.
    /// \param g The undirected graph the algorithm runs on.
    /// \param k The parameter \f$ k \f$ of \f$ (k,l) \f$-sparsity.
    /// \param l The parameter \f$ k \f$ of \f$ (k,l) \f$-sparsity.
    UniSparse(const Graph& g, const int k, const int l)
      : UniSparse(g, k, l, nullptr)
    {}

    /// \brief Constructor.
    ///
    /// Constructor.
    /// \param g The undirected graph the algorithm runs on.
    /// \param k The parameter \f$ k \f$ of \f$ (k,l) \f$-sparsity.
    /// \param l The parameter \f$ k \f$ of \f$ (k,l) \f$-sparsity.
    /// \param w The edge map of the input graph storing the weights.
    UniSparse(const Graph& g, const int k, const int l, const WeightMap& w)
      : UniSparse(g, k, l, &w)
    {}

    /// \brief Destructor.
    ///
    /// Destructor.
    ~UniSparse()
    {
      if(_local_processingOrderContainer) {
        delete _processingOrderContainer;
      }
    }

    /// \brief Sets the \c Digraph.
    ///
    /// Sets the inner \c Digraph to be built by the algorithm.
    ///
    /// \param dg The inner \c Digraph built by the algorithm.
    ///
    /// If you don't use this function before calling \ref checkSparse(),
    /// \ref run() or \ref init(), then an instance will be allocated
    /// automatically. The destructor deallocates this automatically allocated
    /// graph, of course.
    ///
    /// \return <tt> (*this) </tt>
    UniSparse& innerDigraph(Digraph& dg)
    {
      return static_cast<UniSparse&>(Parent::innerDigraph(dg));
    }

    /// \brief Sets the \c ProcessingOrderContainer.
    ///
    /// Sets the \c ProcessingOrderContainer. The edges will be inserted and
    /// sorted by their weights in this container.
    ///
    /// If you don't use this function before calling \ref checkSparse(),
    /// \ref run() or \ref init(), then an instance will be allocated
    /// automatically. The destructor deallocates this automatically allocated
    /// container, of course.
    ///
    /// \param v The \c ProcessingOrderContainer.
    ///
    /// \return <tt> (*this) </tt>
    UniSparse& processingOrderContainer(ProcessingOrderContainer& v)
    {
      if(_local_processingOrderContainer) {
        _local_processingOrderContainer = false;
        delete _processingOrderContainer;
      }
      _processingOrderContainer = &v;
      return *this;
    }

    /// \brief Sets the sense of optimization to maximization.
    ///
    /// Sets the sense of optimization to maximization. This is the default
    /// setting.
    ///
    /// \return <tt> (*this) </tt>
    UniSparse& maximize()
    {
      _maximize = true;
      return *this;
    }

    /// \brief Sets the sense of optimization to minimization.
    ///
    /// Sets the sense of optimization to minimization.
    ///
    /// \return <tt> (*this) </tt>
    UniSparse& minimize()
    {
      _maximize = false;
      return *this;
    }

    /// \brief Sets the \c ToInputNodeMap.
    ///
    /// Sets the \c ToInputNodeMap.
    ///
    /// \param m The \ref UniSparseDefaultTraits::ToInputNodeMap
    /// "ToInputNodeMap" of the inner digraph.
    ///
    /// If you don't use this function before calling \ref checkSparse(),
    /// \ref run() or \ref init(), then an instance will be allocated
    /// automatically. The destructor deallocates this automatically allocated
    /// map, of course.
    ///
    /// \return <tt> (*this) </tt>
    UniSparse& toInputNodeMap(ToInputNodeMap& m)
    {
      return static_cast<UniSparse&>(Parent::toInputNodeMap(m));
    }

    /// \brief Sets the \c ToInnerNodeMap.
    ///
    /// Sets the \c ToInnerNodeMap.
    ///
    /// \param m The \c ToInnerNodeMap of the input graph.
    ///
    /// If you don't use this function before calling \ref checkSparse(),
    /// \ref run() or \ref init(), then an instance will be allocated
    /// automatically. The destructor deallocates this automatically allocated
    /// map, of course.
    ///
    /// \return <tt> (*this) </tt>
    UniSparse& toInnerNodeMap(ToInnerNodeMap& m)
    {
      return static_cast<UniSparse&>(Parent::toInnerNodeMap(m));
    }

    /// \brief Sets the \c ToInputEdgeMap.
    ///
    /// Sets the \c ToInputEdgeMap.
    ///
    /// \param m The \c ToInputEdgeMap of the inner digraph.
    ///
    /// If you don't use this function before calling \ref checkSparse(),
    /// \ref run() or \ref init(), then an instance will be allocated
    /// automatically. The destructor deallocates this automatically allocated
    /// map, of course.
    ///
    /// \return <tt> (*this) </tt>
    UniSparse& toInputEdgeMap(ToInputEdgeMap& m)
    {
      return static_cast<UniSparse&>(Parent::toInputEdgeMap(m));
    }

    /// \brief Sets the \c ToInnerArcMap.
    ///
    /// Sets the \c ToInnerArcMap.
    ///
    /// \param m The \c ToInnerArcMap of the input graph.
    ///
    /// If you don't use this function before calling \ref checkSparse(),
    /// \ref run() or \ref init(), then an instance will be allocated
    /// automatically. The destructor deallocates this automatically allocated
    /// map, of course.
    ///
    /// \return <tt> (*this) </tt>
    UniSparse& toInnerArcMap(ToInnerArcMap& m)
    {
      return static_cast<UniSparse&>(Parent::toInnerArcMap(m));
    }

    /// \brief Returns \c true if weights are given, i.e. if the type of the
    /// WeightMap is not a NullMap.
    ///
    /// \return \c true if weights are given, i.e. if the type of the WeightMap
    /// is not a NullMap.
    constexpr bool weightedCase() const
    {
      using namespace unisparse_bits;
      LEMON_ASSERT(_weights || isNullMap<WeightMap>(),
                   "The WeightMap is not a NullMap but it was not set!");
      return !isNullMap<WeightMap>();
    }

    /// \brief Returns \c true if \f$ l \leq k \f$.
    ///
    /// \return \c true if \f$ l \leq k \f$.
    bool lowerRangeCase() const
    {
      using namespace unisparse_bits;
      return std::is_same<RangeSelector, LowerRange>::value
        || (!std::is_same<RangeSelector, UpperRange>::value && _l <= _k);
    }

    /// \brief Returns \c true if \f$ l > k \f$.
    ///
    /// \return \c true if \f$ l > k \f$.
    bool upperRangeCase() const
    {
      return !lowerRangeCase();
    }

    /// \name Execution Control
    ///
    /// The simplest way to use UniSparse is to call either the
    /// member function \ref checkSparse() or \ref run().
    /// If you need better control on the execution, you have to call \ref
    /// init(), then you can process the edges one by one with \ref
    /// processNextEdge() until \ref isAllDone() (or \ref isAllProcessed())
    /// returns \c true, see the following code snippet.
    ///
    /// \code
    ///   us.init();
    ///   while(!us.isAllDone()) {
    ///     us.processNextEdge();
    ///   }
    /// \endcode
    ///
    /// If you want to control which edge is processed next, then
    /// use \ref processEdge(const Edge&) "processEdge(e)":
    ///
    /// \code
    ///   us.init();
    ///   for(const auto& e : g.edges()) {
    ///     us.processEdge(e);
    ///   }
    /// \endcode

    /// @{

    /// \brief Initializes the internal data structures.
    ///
    /// Initializes the internal data structures.
    void init()
    {
      Parent::init();

      if(weightedCase()) {
        if(!_processingOrderContainer) {
          _local_processingOrderContainer = true;
          _processingOrderContainer = Traits::createProcessingOrderContainer();
          LEMON_ASSERT(_processingOrderContainer,
                       "ProcessingOrderContainer is not initialized!");
        }
        _processingOrderContainer->resize(_numEdges);
        unsigned i = 0;
        for(EdgeIt e(_inputGraph); e != INVALID; ++e) {
          (*_processingOrderContainer)[i++] = e;
        }
        if(!unisparse_bits::isConstMap<WeightMap>()) {
          sortProcessingOrderContainer();
        }

        _sumWeights = 0;
        _currPOCIndex = 0;
      }
    }

    /// \brief Returns the next edge to be processed.
    ///
    /// \return The next edge to be processed.
    ///
    /// \pre Function \ref init() must be called before using this function.
    Edge nextEdge() const
    {
      if(weightedCase()) {
        return _currPOCIndex < _numEdges
          ? (*_processingOrderContainer)[_currPOCIndex]
          : INVALID;
      }
      return _nextEdgeIt;
    }

    /// \brief Returns \c true if all edges are processed.
    ///
    /// \return \c true if all edges are processed.
    ///
    /// \pre This function works correctly only if edges are processed by
    /// \ref checkSparse(), \ref run() or \ref processNextEdge(), but not by
    /// \ref processEdge(const Edge&) "processEdge(e)".
    /// \note Consider using the function \ref isAllDone() instead, which
    /// also detects if no more edges may be accepted.
    bool isAllProcessed() const
    {
      return weightedCase() ? _currPOCIndex >= _numEdges
        : _nextEdgeIt == INVALID;
    }

    /// \brief Returns \c true if all edges are processed or no other edge
    /// may be accepted.
    ///
    /// \return \c true if all edges are processed or no other edge may be
    /// accepted.
    ///
    /// This function is just a shortcut of
    ///
    /// \code
    ///   sparseSize() >= fullRank() || isAllProcessed()
    /// \endcode
    ///
    /// \pre This function works correctly only if edges are processed by
    /// \ref checkSparse(), \ref run() or \ref processNextEdge(), but not by
    /// \ref processEdge(const Edge&) "processEdge(e)".
    bool isAllDone() const
    {
      return sparseSize() >= fullRank() || isAllProcessed();
    }

    /// \brief Returns the upper bound for the total number of edges in a
    /// \f$ (k,l) \f$-sparse graph.
    ///
    /// \return The upper bound for the total number of edges in a
    /// \f$ (k,l) \f$-sparse graph, that is, \f$ (k|V|-l)^+ \f$.
    int fullRank() const
    {
      return Parent::fullRank();
    }

    /// \brief Processes the given edge.
    ///
    /// Processes the given edge.
    ///
    /// \param e The edge to be processed.
    ///
    /// The following code snippet shows how this function can be used for
    /// better control on the execution.
    ///
    /// \code
    ///   us.init();
    ///   for(const auto& e : g.edges()) {
    ///     us.processEdge(e);
    ///   }
    /// \endcode
    ///
    /// \return The resulting \c Arc if the edge has been accepted, otherwise
    /// \c INVALID.
    ///
    /// \pre Function \ref init() must be called before using this function.
    /// \warning It is the caller's responsibility to process each edge only
    /// once. If an edge is processed multiple times, then it may get accepted
    /// several times and/or the algorithm may run slower.
    Arc processEdge(const Edge& e)
    {
      LEMON_ASSERT(e != INVALID, "Processing INVALID edge!");
      return processEdge(e, _inputGraph.u(e), _inputGraph.v(e));
    }

    /// \brief Processes the given edge.
    ///
    /// Processes the given edge.
    ///
    /// \param e The edge to be processed.
    /// \param from The incident node from which the arc should be oriented
    /// (if possible) in case \c e is accepted.
    ///
    /// The following code snippet shows how this function can be used for
    /// better control on the execution.
    ///
    /// \code
    ///   us.init();
    ///   for(const auto& u : g.nodes()) {
    ///     for(const auto& e : g.trueIncEdges(u)) {
    ///       if(u < g.oppositeNode(u, e)) {
    ///         us.processEdge(e, u);
    ///       }
    ///     }
    ///   }
    /// \endcode
    ///
    /// \return The resulting \c Arc if the edge has been accepted, otherwise
    /// \c INVALID.
    ///
    /// \pre Function \ref init() must be called before using this function.
    /// \warning The arc will be oriented from the node \c from only if its
    /// outdegree is smaller than \f$ k \f$, otherwise, the desired direction
    /// will be ignored.
    /// \warning It is the caller's responsibility to process each edge only
    /// once. If an edge is processed multiple times, then it may get accepted
    /// several times and/or the algorithm may run slower.
    Arc processEdge(const Edge& e, const Node from)
    {
      LEMON_ASSERT(e != INVALID, "Processing INVALID edge!");
      LEMON_ASSERT(_inputGraph.u(e) == from || _inputGraph.v(e) == from,
                   "Bad orientation request!");
      return processEdge(e, from, _inputGraph.oppositeNode(from, e));
    }


    /// \brief Processes the given edge.
    ///
    /// Processes the given edge.
    ///
    /// \param e The edge to be processed.
    /// \param from The incident node from which the arc should be oriented
    /// (if possible) in case \c e is accepted.
    /// \param to The incident node to which the arc should be oriented
    /// (if possible) in case \c e is accepted.
    ///
    /// The following code snippet shows how this function can be used for
    /// better control on the execution.
    ///
    /// \code
    ///   us.init();
    ///   for(const auto& u : g.nodes()) {
    ///     for(const auto& e : g.trueIncEdges(u)) {
    ///       if(u < g.oppositeNode(u, e)) {
    ///         us.processEdge(e, u, g.oppositeNode(u, e));
    ///       }
    ///     }
    ///   }
    /// \endcode
    ///
    /// \return The resulting \c Arc if the edge has been accepted, otherwise
    /// \c INVALID.
    ///
    /// \pre Function \ref init() must be called before using this function.
    /// \warning The arc will be oriented from the node \c from only if its
    /// outdegree is smaller than \f$ k \f$, otherwise, the desired direction
    /// will be ignored.
    /// \warning It is the caller's responsibility to process each edge only
    /// once. If an edge is processed multiple times, then it may get accepted
    /// several times and/or the algorithm may run slower.
    Arc processEdge(const Edge& e, const Node from, const Node to)
    {
      LEMON_ASSERT(e != INVALID, "Processing INVALID edge!");
      LEMON_ASSERT((_inputGraph.u(e) == from && _inputGraph.v(e) == to)
                   || (_inputGraph.u(e) == to && _inputGraph.v(e) == from),
                   "Bad orientation request!");

      _previousEdge = e;

      const DNode innerU = (*_toInnerNode)[from];
      const DNode innerV = (*_toInnerNode)[to];

      if(!reversePaths(innerU, innerV)) {
        return INVALID;
      }

      const Arc a = insertArc(innerU, innerV);
      registerAcceptance(e, a);

      return a;
    }

    /// \brief Processes the next edge.
    ///
    /// Processes the next edge and steps the iterator to the next edge.
    /// The following code snippet shows how this function can be used for
    /// better control on the execution.
    ///
    /// \code
    ///   us.init();
    ///   while(!us.isAllDone()) {
    ///     us.processNextEdge();
    ///   }
    /// \endcode
    ///
    /// \return The resulting \c Arc if the edge has been accepted, otherwise
    /// \c INVALID.
    ///
    /// \pre Function \ref init() must be called before using this function.
    Arc processNextEdge()
    {
      return weightedCase() ? weightedProcessNextEdge()
        : unweightedProcessNextEdge();
    }

    /// \brief Runs the algorithm to check \f$ (k,l) \f$-sparsity.
    ///
    /// This function runs the \c UniSparse algorithm to check
    /// \f$ (k,l) \f$-sparsity.
    ///
    /// \tparam HeuristicImpl The class containing the implementation of the
    /// member function \c checkSparse to check the sparsity.
    ///
    /// \return \c true if the graph is \f$ (k,l) \f$-sparse.
    template<typename HeuristicImpl = Auto>
    bool checkSparse()
    {
      init();
      return HeuristicImpl(*this).checkSparse();
    }

    /// \brief Runs the algorithm to check \f$ (k,l) \f$-sparsity.
    ///
    /// This function runs the \c UniSparse algorithm to check
    /// \f$ (k,l) \f$-sparsity.
    ///
    /// \param heuristic The type of \c Heuristic.
    ///
    /// \return \c true if the graph is \f$ (k,l) \f$-sparse.
    bool checkSparse(const Heuristic heuristic)
    {
      LEMON_ASSERT(heuristic == BASIC || heuristic == AUTO || !weightedCase(),
                   "Only BASIC and AUTO are available in the weighted case!");
      switch(heuristic) {
      case AUTO:
        return checkSparse<Auto>();
      case BASIC:
        return checkSparse<Basic>();
      case TRANSP:
        return checkSparse<Transp>();
      case TRANSP_MEM:
        return checkSparse<TranspMem>();
      case TRANSP_ONE_OUT:
        return checkSparse<TranspOneOut>();
      case TRANSP_ONE_OUT_MEM:
        return checkSparse<TranspOneOutMem>();
      case FORESTS_BFS:
        return checkSparse<ForestsBFS>();
      case FORESTS_DFS:
        return checkSparse<ForestsDFS>();
      case PFORESTS_BFS:
        return checkSparse<PForestsBFS>();
      case PFORESTS_DFS:
        return checkSparse<PForestsDFS>();
      case NODE_BASIC:
        return checkSparse<NodeBasic>();
      case NODE_DEG_MIN:
        return checkSparse<NodeDegMin>();
      case NODE_PROC_MIN:
        return checkSparse<NodeProcMin>();
      case NODE_OUT_DEG_MIN:
        return checkSparse<NodeOutDegMin>();
      default:
        LEMON_ASSERT(0, "Unknown heuristic!");
        return false; // avoid warning
      }
    }

    /// \brief Runs the algorithm to find a(n optimal) largest
    /// \f$ (k,l) \f$-sparse subgraph.
    ///
    /// This function runs the \c UniSparse algorithm to find a(n optimal)
    /// \f$ (k,l) \f$-sparse subgraph.
    ///
    /// The algorithm finds a largest sparse subgraph or, if edge weights
    /// were given, a maximum- or minimum-weight largest sparse subgraph.
    ///
    /// \tparam HeuristicImpl The class containing the implementation of the
    /// member function \c run to run the algorithm.
    ///
    /// \return \c true if the graph is \f$ (k,l) \f$-sparse.
    template<typename HeuristicImpl = Auto>
    bool run()
    {
      init();
      return HeuristicImpl(*this).run();
    }

    /// \brief Runs the algorithm to find a(n optimal) largest
    /// \f$ (k,l) \f$-sparse subgraph.
    ///
    /// This function runs the \c UniSparse algorithm to find a(n optimal)
    /// \f$ (k,l) \f$-sparse subgraph.
    ///
    /// The algorithm finds a largest sparse subgraph or, if edge weights
    /// were given, a maximum- or minimum-weight largest sparse subgraph.
    ///
    /// \param heuristic The type of \c Heuristic. In the weighted case, either
    /// \ref AUTO or \ref BASIC must be used.
    ///
    /// \return \c true if the graph is \f$ (k,l) \f$-sparse.
    bool run(const Heuristic heuristic)
    {
      LEMON_ASSERT(heuristic == BASIC || heuristic == AUTO || !weightedCase(),
                   "Only BASIC and AUTO are available in the weighted case!");
      switch(heuristic) {
      case AUTO:
        return run<Auto>();
      case BASIC:
        return run<Basic>();
      case TRANSP:
        return run<Transp>();
      case TRANSP_MEM:
        return run<TranspMem>();
      case TRANSP_ONE_OUT:
        return run<TranspOneOut>();
      case TRANSP_ONE_OUT_MEM:
        return run<TranspOneOutMem>();
      case FORESTS_BFS:
        return run<ForestsBFS>();
      case FORESTS_DFS:
        return run<ForestsDFS>();
      case PFORESTS_BFS:
        return run<PForestsBFS>();
      case PFORESTS_DFS:
        return run<PForestsDFS>();
      case NODE_BASIC:
        return run<NodeBasic>();
      case NODE_DEG_MIN:
        return run<NodeDegMin>();
      case NODE_PROC_MIN:
        return run<NodeProcMin>();
      case NODE_OUT_DEG_MIN:
        return run<NodeOutDegMin>();
      default:
        LEMON_ASSERT(0, "Unknown heuristic!");
        return false; // avoid warning
      }
    }

    /// @}

  private:
    Arc weightedProcessNextEdge()
    {
      LEMON_ASSERT(weightedCase(),
                   "Called weightedProcessNextEdge in unweighted case!");
      return processEdge((*_processingOrderContainer)[_currPOCIndex++]);
    }

    Arc unweightedProcessNextEdge()
    {
      LEMON_ASSERT(!weightedCase(),
                   "Called unweightedProcessNextEdge in weighted case!");
      const Arc ret = processEdge(_nextEdgeIt);
      ++_nextEdgeIt;
      return ret;
    }

  protected:
    // Reverse paths from the nodes u or v to a node of small out-degree.
    bool reversePaths(const DNode u, const DNode v)
    {
      while(!isInsertable(u, v)) {
        _bfs->init();
        _bfs->addSource(u);
        _bfs->addSource(v);

        DNode n = _bfs->findNodeWithDegLeqK(*_outDeg, _k);

        if(n == INVALID) {
          return false;
        }

        ++(*_outDeg)[n];
        do {
          const Arc& a = _bfs->predArc(n);
          n = _innerDigraph->source(a);
          _innerDigraph->reverseArc(a);
        } while(n != u && n != v);
        --(*_outDeg)[n];        // n == u or n == v
      }
      return true;
    }

    // Updates the variables and maps after an arc is inserted.
    void registerAcceptance(const Edge& e, const Arc& a)
    {
      if(weightedCase()) {
        _sumWeights += (*_weights)[e];
      }
      Parent::registerAcceptance(e, a);
    }

    // Checks whether an edge is insertable without reversing any paths.
    bool isInsertable(const DNode u, const DNode v) const
    {
      const auto outDegU = (*_outDeg)[u];
      return u != v ? 2*_k - _l > outDegU + (*_outDeg)[v] : _k - _l > outDegU;
    }

    // Sorts the edges by weights.
    void sortProcessingOrderContainer()
    {
      if(_maximize) {
        std::sort(std::begin(*_processingOrderContainer),
                  std::end(*_processingOrderContainer),
                  [this](const Edge& e, const Edge& f) {
                    return (*_weights)[e] > (*_weights)[f];
                  });
      }
      else {
        std::sort(std::begin(*_processingOrderContainer),
                  std::end(*_processingOrderContainer),
                  [this](const Edge& e, const Edge& f) {
                    return (*_weights)[e] < (*_weights)[f];
                  });
      }
    }

  public:
    /// \name Query Functions
    /// The result of the algorithm can be obtained using the following
    /// functions.
    /// \pre The algorithm should be run before using these functions.
    /// \note If you need to determine the components, that is, the
    /// maximum-size \f$ (k,l) \f$-sparse subgraphs, then use the
    /// \ref UniSparseComp class.

    /// @{

    /// \brief Returns \c true if the graph is \f$ (k,l) \f$-sparse.
    ///
    /// \return \c true if the graph is \f$ (k,l) \f$-sparse.
    ///
    /// \pre One of \ref checkSparse() or \ref run() should be called, or, if
    /// the edges are processed by \ref processNextEdge()
    /// or \ref processEdge(const Edge&) "processEdge(e)", then at least one
    /// edge must be rejected or all edges must be processed before using this
    /// function.
    bool isSparse() const
    {
      return Parent::isSparse();
    }

    /// \brief Returns \c true if the graph is \f$ (k,l) \f$-spanning.
    ///
    /// \return \c true if the graph is spanning.
    ///
    /// \pre Either \ref run() should be called or all edges must be processed
    /// by \ref processNextEdge() or \ref processEdge(const Edge&)
    /// "processEdge(e)" before using this function.
    bool isSpanning() const
    {
      return _numInserted == fullRank();
    }

    /// \brief Returns \c true if the graph is \f$ (k,l) \f$-tight.
    ///
    /// \return \c true if the graph is tight, that is, it is
    /// \f$ (k,l) \f$-sparse and \f$ |E| = \max \{0,k|V|-l\} \f$.
    ///
    /// \pre One of \ref checkSparse() or \ref run() should be called, or, if
    /// the edges are processed by \ref processNextEdge()
    /// or \ref processEdge(const Edge&) "processEdge(e)", then at least one
    /// edge must be rejected or all edges must be processed before using this
    /// function.
    bool isTight() const
    {
      return isSparse() && _numEdges == fullRank();
    }

    /// \brief Returns the total weight of the accepted edges.
    ///
    /// \return The total weight of the accepted edges, i.e. the total weight
    /// of the edges in the (current) sparse subgraph.
    Weight sparseWeight() const
    {
      return _sumWeights;
    }

    /// @}

    /// \name Traits Query and Setter Functions
    /// The variables and maps of the \ref UniSparseDefaultTraits "Traits"
    /// class can be accessed and set using the following member functions.
    /// \pre One of \ref checkSparse(), \ref run() or \ref init() must be
    /// called before using them.

    /// @{

    using Parent::innerDigraph;
    using Parent::toInnerArcMap;
    using Parent::toInnerNodeMap;
    using Parent::toInputEdgeMap;
    using Parent::toInputNodeMap;

    /// \brief Returns a const reference to the \c ProcessingOrderContainer.
    ///
    /// \return Const reference to the \ref
    /// UniSparseDefaultTraits::ProcessingOrderContainer
    /// "ProcessingOrderContainer".
    ///
    /// \pre One of \ref checkSparse(), \ref run() or \ref init() must be
    /// called before using this function, or a container must be passed using
    /// \ref processingOrderContainer(ProcessingOrderContainer&)
    /// "processingOrderContainer()".
    const ProcessingOrderContainer& processingOrderContainer() const
    {
      return *_processingOrderContainer;
    }

    /// @}

    /// \name Iterators
    /// In case the latest edge was rejected (i.e. the functions \ref
    /// processNextEdge(), \ref processEdge(const Edge&) "processEdge(e)"
    /// return \c INVALID, or \ref checkSparse() return \c false), one can
    /// query an inclusion-wise minimal tight subgraph blocking the insertion
    /// of the edge using \ref nodesOfLastBlockingTight() and
    /// \ref edgesOfLastBlockingTight(), or alternatively, the \ref
    /// LastBlockingTightNodeIt and \ref LastBlockingTightEdgeIt iterators. The
    /// code snippet below shows an example.
    /// \warning If the latest edge has been accepted, then the behavior is
    /// undefined!
    ///
    /// \code
    ///   using BNodeIt = UniSparse<ListGraph>::LastBlockingTightNodeIt;
    ///   using BEdgeIt = UniSparse<ListGraph>::LastBlockingTightEdgeIt;
    ///   UniSparse<ListGraph> us(g, k, l);
    ///   us.init();
    ///   while(!us.isAllDone()) {
    ///     if(us.processNextEdge() == INVALID) { // could not accept the edge?
    ///       // Nodes
    ///       for(const auto& n : us.nodesOfLastBlockingTight()) {
    ///         std::cout << g.id(n) << std::endl;
    ///       }
    ///       // Same as above
    ///       for(BNodeIt n(us); n != INVALID; ++n) {
    ///         std::cout << g.id(n) << std::endl;
    ///       }
    ///       // Edges
    ///       for(const auto& e : us.edgesOfLastBlockingTight()) {
    ///         std::cout << g.id(e) << std::endl;
    ///       }
    ///       // Same as above
    ///       for(BEdgeIt e(us); e != INVALID; ++e) {
    ///         std::cout << g.id(e) << std::endl;
    ///       }
    ///     }
    ///   }
    /// \endcode

    /// @{

  public:
    /// \brief Iterator class for the nodes of the last blocking tight
    /// subgraph.
    ///
    /// In case the latest edge was rejected (i.e. the functions
    /// \ref processNextEdge(), \ref processEdge(const Edge&) "processEdge(e)"
    /// return \c INVALID, or \ref checkSparse() return \c false), one can
    /// iterate on the node set of an inclusion-wise minimal tight subgraph
    /// blocking the insertion. Processing any edge invalidates this iterator.
    ///
    /// The following snippet uses \ref LastBlockingTightNodeIt to access
    /// the node set of the blocking tight subgraph after \ref checkSparse()
    /// returns \c false.
    ///
    /// \code
    ///   UniSparse<ListGraph> us(g, k, l);
    ///   if(!us.checkSparse()) {
    ///     for(const auto& n : us.nodesOfLastBlockingTight()) {
    ///       std::cout << g.id(n) << std::endl;
    ///     }
    ///   }
    /// \endcode
    ///
    /// Alternatively, \ref nodesOfLastBlockingTight() can be used for the same
    /// purpose as follows.
    ///
    /// \code
    ///   using BNodeIt = UniSparse<ListGraph>::LastBlockingTightNodeIt;
    ///   UniSparse<ListGraph> us(g, k, l);
    ///   if(!us.checkSparse()) {
    ///     for(BNodeIt n(us); n != INVALID; ++n) {
    ///       std::cout << g.id(n) << std::endl;
    ///     }
    ///   }
    /// \endcode
    ///
    /// \pre The latest edge must be rejected.
    /// \pre The type of the node map \ref
    /// UniSparseDefaultTraits::ToInputNodeMap "ToInputNodeMap" of the
    /// underlying \c UniSparse class must not be \c NullMap.
    class LastBlockingTightNodeIt {
      const UniSparse* const _us;
      DNodeIt _dNodeIt;

    public:
      // prevent accidental down casting and any other conversion
      template<typename T>
      LastBlockingTightNodeIt(const T&) = delete;

      /// \brief Constructor.
      ///
      /// Constructor. Sets the iterator to the first node.
      LastBlockingTightNodeIt(const UniSparse& us)
        : _us(&us), _dNodeIt(*_us->_innerDigraph)
      {
        stepItToNextValid();
      }

      /// \brief Initializes the iterator to be invalid.
      ///
      /// Initializes the iterator to be invalid.
      /// \sa Invalid for more details.
      LastBlockingTightNodeIt(Invalid) : _us(nullptr), _dNodeIt(INVALID)
      {}

      /// \brief Node conversion.
      ///
      /// Node conversion.
      operator Node() const
      {
        return _dNodeIt != INVALID ? (*_us->_toInputNode)[_dNodeIt] : INVALID;
      }

      /// \brief Steps the iterator to the next node.
      ///
      /// Steps the iterator to the next node.
      LastBlockingTightNodeIt& operator++()
      {
        ++_dNodeIt;
        stepItToNextValid();
        return *this;
      }

      /// \brief Inequality operator.
      ///
      /// Inequality operator.
      /// \pre The compared iterators belong to the same instance of
      /// \ref UniSparse.
      bool operator!=(const LastBlockingTightNodeIt& rhs) const
      {
        return _dNodeIt != rhs._dNodeIt;
      }

    private:
      void stepItToNextValid()
      {
        while(_dNodeIt != INVALID && !_us->_bfs->reached(_dNodeIt)) {
          ++_dNodeIt;
        }
      }
    };

    /// \brief Returns the collection of the nodes of the last blocking tight
    /// subgraph.
    ///
    /// This function can be used for iterating on the nodes of the last
    /// blocking tight subgraph. It returns a wrapped LastBlockingTightNodeIt,
    /// which behaves as an STL container and can be used in range-based for
    /// loops and STL algorithms.
    /// Processing any edge invalidates this iterator.
    ///
    /// The following code demonstrates the usage of the wrapped iterator.
    ///
    /// \code
    ///   for(const auto& n : us.nodesOfLastBlockingTight()) {
    ///     std::cout << g.id(n) << std::endl;
    ///   }
    /// \endcode
    ///
    /// \pre The latest edge must be rejected, otherwise the blocking tight
    /// subgraph and hence the behavior is undefined!
    /// \pre The type of the node map \ref
    /// UniSparseDefaultTraits::ToInputNodeMap "ToInputNodeMap" of the
    /// underlying \c UniSparse class must not be \c NullMap.
    LemonRangeWrapper1<LastBlockingTightNodeIt, UniSparse<GR, WM, TR>>
    nodesOfLastBlockingTight() const
    {
      return LemonRangeWrapper1<LastBlockingTightNodeIt,
                                UniSparse<GR, WM, TR>>(*this);
    }

    /// \brief Iterator class for the edges of the blocking tight subgraph.
    ///
    /// In case the latest edge was rejected (i.e. the functions
    /// \ref processNextEdge(), \ref processEdge(const Edge&) "processEdge(e)"
    /// return \c INVALID, or \ref checkSparse() return \c false), one can
    /// iterate on the edge set of an inclusion-wise minimal tight subgraph
    /// blocking the insertion. Processing any edge invalidates this iterator.
    ///
    /// The following snippet uses \ref edgesOfLastBlockingTight() to access
    /// the edge set of the blocking tight subgraph after \ref checkSparse()
    /// returns \c false.
    ///
    /// \code
    ///   UniSparse<ListGraph> us(g, k, l);
    ///   if(!us.checkSparse()) {
    ///     for(const auto& e : us.edgesOfLastBlockingTight()) {
    ///       std::cout << g.id(e) << std::endl;
    ///     }
    ///   }
    /// \endcode
    ///
    /// Alternatively, \ref LastBlockingTightEdgeIt can be used for the same
    /// purpose as follows.
    ///
    /// \code
    ///   using EdgeIt = UniSparse<ListGraph>::LastBlockingTightEdgeIt;
    ///   UniSparse<ListGraph> us(g, k, l);
    ///   if(!us.checkSparse()) {
    ///     for(EdgeIt e(us); e != INVALID; ++e) {
    ///       std::cout << g.id(e) << std::endl;
    ///     }
    ///   }
    /// \endcode
    ///
    /// \pre The latest edge must be rejected, otherwise the blocking tight
    /// subgraph and hence the behavior is undefined!
    /// \pre The type of the edge map \ref
    /// UniSparseDefaultTraits::ToInputEdgeMap "ToInputEdgeMap" of the
    /// underlying \c UniSparse class must not be \c NullMap.
    class LastBlockingTightEdgeIt {
      const UniSparse* const _us;
      DNodeIt _dNodeIt;
      OutArcIt _outArcIt;

    public:
      // prevent accidental down casting and any other conversion
      template<typename T>
      LastBlockingTightEdgeIt(const T&) = delete;

      /// \brief Constructor.
      ///
      /// Constructor. Sets the iterator to the first node.
      LastBlockingTightEdgeIt(const UniSparse& us)
        : _us(&us), _dNodeIt(*_us->_innerDigraph)
      {
        if(_dNodeIt != INVALID) {
          _outArcIt = OutArcIt(*_us->_innerDigraph, _dNodeIt);
          stepOutArcToNextValid();
        }
      }

      /// \brief Initializes the iterator to be invalid.
      ///
      /// Initializes the iterator to be invalid.
      /// \sa Invalid for more details.
      LastBlockingTightEdgeIt(Invalid)
        : _us(nullptr), _dNodeIt(INVALID), _outArcIt(INVALID)
      {}

      /// \brief Edge conversion.
      ///
      /// Edge conversion.
      operator Edge() const
      {
        return _outArcIt != INVALID ? (*_us->_toInputEdge)[_outArcIt]
          : INVALID;
      }

      /// \brief Steps the iterator to the next edge.
      ///
      /// Steps the iterator to the next edge.
      LastBlockingTightEdgeIt& operator++()
      {
        ++_outArcIt;
        stepOutArcToNextValid();
        return *this;
      }

      /// \brief Inequality operator.
      ///
      /// Inequality operator.
      /// \pre The compared iterators belong to the same instance of
      /// \ref UniSparse.
      bool operator!=(const LastBlockingTightEdgeIt& rhs) const
      {
        return _dNodeIt != rhs._dNodeIt || _outArcIt != rhs._outArcIt;
      }

    private:
      void stepOutArcToNextValid()
      {
        const auto& dg = _us->innerDigraph();
        while(true) {
          if(_outArcIt == INVALID) {
            // step to the next node
            if(++_dNodeIt != INVALID) {
              _outArcIt = OutArcIt(dg, _dNodeIt);
            }
            else {
              // no more edges left
              return;
            }
          }
          else if(_us->_bfs->reached(dg.target(_outArcIt))) {
            // found the next arc
            return;
          }
          else {
            // arc is not in tight, take the next arc
            ++_outArcIt;
          }
        }
      }
    };

    /// \brief Returns the collection of the edges of the last blocking tight
    /// subgraph.
    ///
    /// This function can be used for iterating on the edges of the last
    /// blocking tight subgraph. It returns a wrapped LastBlockingTightEdgeIt,
    /// which behaves as an STL container and can be used in range-based for
    /// loops and STL algorithms.
    /// Processing any edge invalidates this iterator.
    ///
    /// The following code demonstrates the usage of the wrapped iterator.
    ///
    /// \code
    ///   for(const auto& e : us.edgesOfLastBlockingTight()) {
    ///     std::cout << g.id(e) << std::endl;
    ///   }
    /// \endcode
    ///
    /// \pre The type of the edge map \ref
    /// UniSparseDefaultTraits::ToInputEdgeMap "ToInputEdgeMap" of the
    /// underlying \c UniSparse class must not be \c NullMap.
    /// \pre The latest edge must be rejected, otherwise the blocking tight
    /// subgraph and hence the behavior is undefined!
    LemonRangeWrapper1<LastBlockingTightEdgeIt, UniSparse<GR, WM, TR>>
    edgesOfLastBlockingTight() const
    {
      return LemonRangeWrapper1<LastBlockingTightEdgeIt,
                                UniSparse<GR, WM, TR>>(*this);
    }

    /// @}
  };


  /// \brief Algorithms for \f$ (k,l) \f$-sparsity.
  ///
  /// An undirected graph \f$ G=(V,E) \f$ is called \f$ (k,l) \f$-sparse if
  /// \f$ i(X) \leq \max \{0,k|X|-l\} \f$ for every \f$ X\subseteq V \f$, where
  /// \f$ i(X) \f$ is the number of edges induced by the set \f$ X \f$ of
  /// nodes and \f$ 0 \leq l < 2k \f$. A graph is called \f$ (k,l) \f$-tight
  /// if it is \f$ (k,l) \f$-sparse and \f$ |E| = \max \{0,k|V|-l\} \f$. It is
  /// \f$ (k,l) \f$-spanning if it contains a \f$ (k,l) \f$-tight subgraph that
  /// spans the entire vertex set.
  ///
  /// This class provides an efficient implementation for extracting a
  /// maximum-size \f$ (k,l) \f$-sparse subgraph (that has maximum or minimum
  /// weight) of an undirected graph in time \f$ O(kln^2) \f$, provided that
  /// \f$ 0 \leq l < 2k \f$. In the unweighted case, the space complexity is
  /// \f$ O(|V|) \f$; in the weighted case, \f$ O(|V|) \f$ if
  /// \f$ 0 \leq l \leq k \f$, and \f$ O(|V|^2) \f$ if \f$ k < l < 2k \f$.
  /// For the case \f$ l = 2k \f$, see the class \ref UniSparseSpec.
  ///
  /// There is also a \ref uniSparseComp() "function-type interface" called
  /// \ref uniSparseComp(), which is convenient in simpler use cases.
  ///
  /// \tparam GR The type of the undirected graph the algorithm runs on.
  /// The default type is \ref ListGraph.
  /// \tparam WM The type of the edge map that specifies the weights of the
  /// edges. It must conform to the \ref concepts::ReadMap "ReadMap" concept.
  /// The default map type is \ref NullMap "NullMap<GR::Edge, int>", which
  /// means that the problem is unweighted.
  /// \tparam TR The traits class that defines various types used in the
  /// algorithm. By default, it is \ref UniSparseDefaultTraits. In most cases,
  /// this parameter should not be set directly, consider to use the named
  /// template parameters instead.
#ifdef DOXYGEN
  template<typename GR, typename WM, typename TR>
#else
  template<typename GR = ListGraph,
           typename WM = NullMap<typename GR::Edge, int>,
           typename TR = UniSparseDefaultTraits<GR>>
#endif
  class UniSparseComp : public UniSparse<GR, WM, TR> {
    using Parent = UniSparse<GR, WM, TR>;

    using Parent::_currPOCIndex;
    using Parent::_innerDigraph;
    using Parent::_inputGraph;
    using Parent::_nextEdgeIt;
    using Parent::_numEdges;
    using Parent::_numInserted;
    using Parent::_numNodes;
    using Parent::_outDeg;
    using Parent::_previousEdge;
    using Parent::_processingOrderContainer;
    using Parent::_toInnerNode;
    using Parent::_revBfs;

    using Parent::_k;
    using Parent::_l;

    using Parent::registerAcceptance;
    using Parent::insertArc;
    using Parent::reversePaths;

  public:
    using Parent::fullRank;
    using Parent::sparseSize;
    using Parent::lowerRangeCase;
    using Parent::upperRangeCase;
    using Parent::weightedCase;

    /// \brief The type of the graph the algorithm runs on.
    using Graph = GR;
    /// \brief The type of the map storing the edge weights.
    using WeightMap = WM;
    /// \brief The type of the inner digraph.
    using Digraph = typename TR::Digraph;
    /// \brief The type of the node map that converts the nodes of the inner
    /// digraph to those of the input graph.
    using ToInputNodeMap = typename TR::ToInputNodeMap;
    /// \brief The type of the node map that converts the nodes of the input
    /// graph to those of the inner digraph.
    using ToInnerNodeMap = typename TR::ToInnerNodeMap;
    /// \brief The type of the arc map that converts the arcs of the inner
    /// digraph to the edges of the input graph.
    using ToInputEdgeMap = typename TR::ToInputEdgeMap;
    /// \brief The type of the edge map that converts the edges of the input
    /// graph to the arcs of the inner digraph.
    using ToInnerArcMap = typename TR::ToInnerArcMap;
    /// \brief The promised range for l and k.
    using RangeSelector = typename TR::RangeSelector;
    /// \brief Set the constant 1 weight function.
    using AllOneWeights = typename TR::AllOneWeights;

    /// \brief The \ref UniSparseDefaultTraits "traits class" of the algorithm.
    using Traits = TR;

  private:
    using Edge = typename GR::Edge;
    using Node = typename GR::Node;
    using EdgeIt = typename GR::EdgeIt;
    using NodeIt = typename GR::NodeIt;
    using TrueIncEdgeIt = typename GR::TrueIncEdgeIt;
    using Arc = typename Digraph::Arc;
    using ArcIt = typename Digraph::ArcIt;
    using OutArcIt = typename Digraph::OutArcIt;
    using DNode = typename Digraph::Node;
    using DNodeIt = typename Digraph::NodeIt;

    template<typename V>
    using DigraphNodeMap = typename Digraph::template NodeMap<V>;

  public:
    /// \brief The type of the node map storing the index of the component
    /// containing the given node, used in the lower range.
    using LowerCompMap = DigraphNodeMap<int>;

    /// \brief The type of the container storing a component, used in the
    /// upper range.
    using Comp = std::vector<DNode>;
    /// \brief The type of the container storing the components, used in the
    /// upper range.
    using Comps = std::vector<Comp>;
    /// \brief The indicator map of the union of the nodes of the components
    /// containing the node being processed, used in the upper range.
    using UpperCompUnionMap = DigraphNodeMap<bool>;
    /// \brief The matrix indicating whether two nodes are contained in one
    /// component.
    using UpperCompMtx = unisparse_bits::UnorderedPairMap<Digraph,
                                                          DigraphNodeMap<int>,
                                                          bool>;

  private:
    // The container storing the components.
    Comps _comps;

    // Lower Range
    // The node map storing the index of the component containing the given
    // node.
    LowerCompMap* _lowerComp;

    // Upper Range
    // The indicator map of the union of the nodes of the components containing
    // the node being processed (i.e. _nodeIt).
    UpperCompUnionMap* _upperCompUnionCV;
    // Char.vector of a component (weighted case only)
    UpperCompUnionMap* _upperCompCV;
    // Unweighted.
    NodeIt _nodeIt;
    TrueIncEdgeIt _incEdgeIt;
    // Weighted.
    UpperCompMtx* _upperCompMtx;

  public:
    /// \brief Constants for selecting the heuristic.
    ///
    /// Enum type containing constants for selecting the heuristic for the \ref
    /// run function in the unweighted case. \UniSparse provides 9 different
    /// heuristics for the processing order of the edges. These can only be
    /// used in the unweighted case, except for \ref BASIC.
    enum Heuristic {

      /// In the unweighted case, \ref NODE_OUT_DEG_MIN is called, in the
      /// weighted case, the \ref BASIC heuristic is called.
      AUTO,

      /// The edges are processed in the order given by NodeIt and
      /// TrueIncEdgeIt.
      NODE_BASIC,

      /// Selects a node with minimal degree in the input graph and processes
      /// all its incident edges, then takes the next node. The space
      /// requirement is linear in the number of the edges of the input graph.
      NODE_DEG_MIN,

      /// Selects a node with minimal number of incident processed edges and
      /// processes all incident edges, then takes the next node. The space
      /// requirement is linear in the number of the edges of the input graph.
      NODE_PROC_MIN,

      /// Selects a node with minimal outdegree in the inner digraph and
      /// processes all incident edges, then take the next node. The space
      /// requirement is linear in the number of the edges of the input graph.
      NODE_OUT_DEG_MIN
    };

  private:
    // AUTO
    class Auto {
      UniSparseComp& _usc;

    public:
      Auto(UniSparseComp& usc) : _usc(usc)
      {}

      bool checkSparse()
      {
        if(_usc.weightedCase()) {
          return NodeBasic(_usc).checkSparse();
        }
        else {
          return NodeOutDegMin(_usc).checkSparse();
        }
      }

      bool run()
      {
        if(_usc.weightedCase()) {
          return NodeBasic(_usc).run();
        }
        else {
          return NodeOutDegMin(_usc).run();
        }
      }
    };

    // BASIC
    class NodeBasic {
      UniSparseComp& _usc;

      template<bool checkSparse>
      bool basic()
      {
        if(_usc.lowerRangeCase()) {
          if(_usc.weightedCase()) {
            while(!_usc.isAllDone()) {
              if(_usc.lowerWeightedProcessNextEdge() == INVALID
                 && checkSparse) {
                return false;
              }
            }
          }
          else {
            while(!_usc.isAllDone()) {
              if(_usc.lowerUnweightedProcessNextEdge() == INVALID
                 && checkSparse) {
                return false;
              }
            }
          }
        }
        else {
          if(_usc.weightedCase()) {
            while(!_usc.isAllDone()) {
              if(_usc.upperWeightedProcessNextEdge() == INVALID
                 && checkSparse) {
                return false;
              }
            }
          }
          else {
            while(!_usc.isAllDone()) {
              if(_usc.upperUnweightedProcessNextEdge() == INVALID
                 && checkSparse) {
                return false;
              }
            }
          }
        }
        _usc.forceAllProcessed();
        return _usc.isSparse();
      }

    public:
      NodeBasic(UniSparseComp& usc) : _usc(usc)
      {}

      bool checkSparse()
      {
        return basic<true>();
      }

      bool run()
      {
        return basic<false>();
      }
    };

    // NODE_DEG_MIN
    using NodeDegMin = typename Parent::template
      NodeDegMinBase<UniSparseComp, true>;
    friend NodeDegMin;

    // NODE_PROC_MIN
    using NodeProcMin = typename Parent::template
      NodeProcMinBase<UniSparseComp, true>;
    friend NodeProcMin;

    // NODE_OUT_DEG_MIN
    using NodeOutDegMin = typename Parent::template
      NodeOutDegMinBase<UniSparseComp, true>;
    friend NodeOutDegMin;

    // make isAllDone return true
    void forceAllProcessed()
    {
      if(lowerRangeCase()) {
        if(weightedCase()) {
          _currPOCIndex = _numEdges;
        }
        else {
          _nextEdgeIt = INVALID;
        }
      }
      else {
        if(weightedCase()) {
          _currPOCIndex = _numEdges;
        }
        else {
          _nodeIt = INVALID;
        }
      }
    }

    // init node if applicable
    void conditionallyInitNode(const Node n)
    {
      if(!weightedCase() && upperRangeCase()) {
        initNode(n);
      }
    }

  public:
    using Create = UniSparseComp;

    /// \name Named Template Parameters

    /// @{

    /// \brief \ref named-templ-param "Named parameter" for setting
    /// \c InnerDigraph type.
    ///
    /// \ref named-templ-param "Named parameter" for setting
    /// \c InnerDigraph type.
    ///
    /// It must provide \p addNode(), \p addArc(), \p reverseArc()
    /// and \p clear() member functions.
    template<typename DGR>
    struct SetInnerDigraph
      : public UniSparseComp<
      GR, WM, typename Parent::template SetInnerDigraphTraits<DGR>> {
      using Create = UniSparseComp<GR, WM,
                                   typename Parent
                                   ::template SetInnerDigraphTraits<DGR>>;
    };

    /// \brief \ref named-templ-param "Named parameter" for setting
    /// \c ToInputNodeMap type.
    ///
    /// \ref named-templ-param "Named parameter" for setting
    /// \c ToInputNodeMap type.
    ///
    /// It must conform to the \ref concepts::ReadWriteMap
    /// "ReadWriteMap" concept.
    ///
    /// \warning The iterators
    /// \ref UniSparseComp::LastBlockingTightNodeIt "LastBlockingTightNodeIt",
    /// \ref UniSparseComp::CompNodeIt "CompNodeIt", and the functions
    /// \ref UniSparseComp::nodesOfLastBlockingTight()
    /// "nodesOfLastBlockingTight()",
    /// \ref UniSparseComp::CompIt::nodes() "nodes()" read this node map,
    /// hence it must not be \c NullMap if any of them is used.
    template<typename NM>
    struct SetToInputNodeMap
      : public UniSparseComp<GR, WM,
                             typename Parent
                             ::template SetToInputNodeMapTraits<NM>> {
      using Create = UniSparseComp<GR, WM,
                                   typename Parent
                                   ::template SetToInputNodeMapTraits<NM>>;
    };

    /// \brief \ref named-templ-param "Named parameter" for setting
    /// \c ToInnerNodeMap type.
    ///
    /// \ref named-templ-param "Named parameter" for setting
    /// \c ToInnerNodeMap type.
    /// It must conform to the \ref concepts::ReadWriteMap
    /// "ReadWriteMap" concept.
    /// \warning This node map must never be \c NullMap since it is written in
    /// \ref init() and read during processing the edges.
    template<typename NM>
    struct SetToInnerNodeMap
      : public UniSparseComp<GR, WM,
                             typename Parent
                             ::template SetToInnerNodeMapTraits<NM>> {
      using Create = UniSparseComp<GR, WM,
                                   typename Parent
                                   ::template SetToInnerNodeMapTraits<NM>>;
    };

    /// \brief \ref named-templ-param "Named parameter" for setting
    /// \c ToInputEdgeMap type.
    ///
    /// \ref named-templ-param "Named parameter" for setting
    /// \c ToInputEdgeMap type.
    ///
    /// It must conform to the \ref concepts::ReadWriteMap
    /// "ReadWriteMap" concept.
    ///
    /// \warning The iterators
    /// \ref UniSparseComp::LastBlockingTightEdgeIt "LastBlockingTightEdgeIt",
    /// \ref UniSparseComp::edgesOfLastBlockingTight()
    /// "edgesOfLastBlockingTight()",
    /// \ref UniSparseComp::CompEdgeIt "CompEdgeIt", and the functions
    /// \ref UniSparseComp::CompIt::edges() "edges()" read this arc map,
    /// hence it must not be \c NullMap if any of them is used.
    template<typename AM>
    struct SetToInputEdgeMap
      : public UniSparseComp<GR, WM,
                             typename Parent
                             ::template SetToInputEdgeMapTraits<AM>> {
      using Create = UniSparseComp<GR, WM,
                                   typename Parent
                                   ::template SetToInputEdgeMapTraits<AM>>;
    };

    /// \brief \ref named-templ-param "Named parameter" for setting
    /// \c ToInnerArcMap type.
    ///
    /// \ref named-templ-param "Named parameter" for setting
    /// \c ToInnerArcMap type.
    ///
    /// It must conform to the \ref concepts::ReadWriteMap
    /// "ReadWriteMap" concept.
    /// \warning This edge map must not be \c NullMap if the function
    /// \ref UniSparseComp::isInduced() "isInduced" is used. For example, use
    /// \ref Graph::EdgeMap<typename Digraph::Arc>.
    template<typename EM>
    struct SetToInnerArcMap
      : public UniSparseComp<GR, WM,
                             typename Parent
                             ::template SetToInnerArcMapTraits<EM>> {
      using Create = UniSparseComp<GR, WM,
                                   typename Parent
                                   ::template SetToInnerArcMapTraits<EM>>;
    };

    struct SetAllOneWeightsTraits : public Traits {
      using AllOneWeights = std::true_type;
    };

    /// \brief \ref named-templ-param "Named parameter" for setting
    /// \c AllOneWeights to \c std::true_type.
    ///
    /// \ref named-templ-param "Named parameter" for setting
    /// \c AllOneWeights to \c std::true_type.
    struct SetAllOneWeights
      : public UniSparseComp<Graph, ConstMap<Edge, int>, TR> {
      using Create = UniSparseComp<Graph, ConstMap<Edge, int>,
                                   SetAllOneWeightsTraits>;
    };

    struct SetLowerRangeTraits : public Traits {
      using RangeSelector = unisparse_bits::LowerRange;
    };

    /// \brief \ref named-templ-param "Named parameter" for setting
    /// \c RangeSelector to \c LowerRange.
    ///
    /// \ref named-templ-param "Named parameter" for setting
    /// \c RangeSelector to \c LowerRange.
    struct SetLowerRange
      : public UniSparseComp<Graph, WM, SetLowerRangeTraits> {
      using Create = UniSparseComp<GR, WM, SetLowerRangeTraits>;
    };

    struct SetUpperRangeTraits : public Traits {
      using RangeSelector = unisparse_bits::UpperRange;
    };

    /// \brief \ref named-templ-param "Named parameter" for setting
    /// \c RangeSelector to \c UpperRange.
    ///
    /// \ref named-templ-param "Named parameter" for setting
    /// \c RangeSelector to \c UpperRange.
    struct SetUpperRange
      : public UniSparseComp<Graph, WM, SetUpperRangeTraits> {
      using Create = UniSparseComp<Graph, WM, SetUpperRangeTraits>;
    };

    /// @}

    template<typename T>
    typename std::enable_if<std::is_same<T, std::true_type>::value,
                            const ConstMap<Edge, int>*>::type
    allocateAllOneWeightsMap()
    {
      return new ConstMap<Edge, int>(1);
    }

    template<typename T>
    typename std::enable_if<std::is_same<T, std::false_type>::value,
                            const WeightMap*>::type
    allocateAllOneWeightsMap()
    {
      return nullptr;
    }

    template<typename T>
    typename std::enable_if<std::is_same<T, std::true_type>::value, void>::type
    deleteAllOneWeightsMap()
    {
      delete Parent::_weights;
    }

    template<typename T>
    typename std::enable_if<std::is_same<T, std::false_type>::value,
                            void>::type
    deleteAllOneWeightsMap()
    {}

  protected:
    UniSparseComp(const Graph& g, const int k, const int l, const WeightMap* w)
      : Parent(g, k, l, w), _comps(), _lowerComp(nullptr),
        _upperCompUnionCV(nullptr), _upperCompCV(nullptr), _nodeIt(INVALID),
        _incEdgeIt(INVALID), _upperCompMtx(nullptr)
    {}

  public:
    /// \brief Constructor.
    ///
    /// Constructor.
    /// \param g The undirected graph the algorithm runs on.
    /// \param k The parameter \f$ k \f$ of \f$ (k,l) \f$-sparsity.
    /// \param l The parameter \f$ l \f$ of \f$ (k,l) \f$-sparsity.
    UniSparseComp(const Graph& g, const int k, const int l)
      : UniSparseComp(g, k, l, allocateAllOneWeightsMap<AllOneWeights>())
    {}

    /// \brief Constructor.
    ///
    /// Constructor.
    /// \param g The undirected graph the algorithm runs on.
    /// \param k The parameter \f$ k \f$ of \f$ (k,l) \f$-sparsity.
    /// \param l The parameter \f$ l \f$ of \f$ (k,l) \f$-sparsity.
    UniSparseComp(const Graph& g, const int k, const int l, const WeightMap& w)
      : UniSparseComp(g, k, l, &w)
    {}

    /// \brief Destructor.
    ///
    /// Destructor.
    ~UniSparseComp()
    {
      delete _upperCompMtx;
      delete _upperCompCV;
      delete _upperCompUnionCV;
      delete _lowerComp;
      deleteAllOneWeightsMap<AllOneWeights>();
    }

    /// \brief Sets the \c Digraph.
    ///
    /// Sets the inner \c Digraph to be built by the algorithm.
    ///
    /// \param dg The inner \c Digraph built by the algorithm.
    ///
    /// If you don't use this function before calling \ref checkSparse(),
    /// \ref run() or \ref init(), then an instance will be allocated
    /// automatically. The destructor deallocates this automatically allocated
    /// graph, of course.
    ///
    /// \return <tt> (*this) </tt>
    UniSparseComp& innerDigraph(Digraph& dg)
    {
      return static_cast<UniSparseComp&>(Parent::innerDigraph(dg));
    }

    /// \brief Sets the sense of optimization to maximization.
    ///
    /// Sets the sense of optimization to maximization. This is the default
    /// setting.
    ///
    /// \return <tt> (*this) </tt>
    UniSparseComp& maximize()
    {
      return static_cast<UniSparseComp&>(Parent::maximize());
    }

    /// \brief Sets the sense of optimization to minimization.
    ///
    /// Sets the sense of optimization to minimization.
    ///
    /// \return <tt> (*this) </tt>
    UniSparseComp& minimize()
    {
      return static_cast<UniSparseComp&>(Parent::minimize());
    }

    /// \brief Sets the \c ToInputNodeMap.
    ///
    /// Sets the \c ToInputNodeMap.
    ///
    /// \param m The \c ToInputNodeMap of the inner digraph.
    ///
    /// If you don't use this function before calling \ref checkSparse(),
    /// \ref run() or \ref init(), then an instance will be allocated
    /// automatically. The destructor deallocates this automatically allocated
    /// map, of course.
    ///
    /// \return <tt> (*this) </tt>
    UniSparseComp& toInputNodeMap(ToInputNodeMap& m)
    {
      return static_cast<UniSparseComp&>(Parent::toInputNodeMap(m));
    }

    /// \brief Sets the \c ToInnerNodeMap.
    ///
    /// Sets the \c ToInnerNodeMap.
    ///
    /// \param m The \c ToInnerNodeMap of the input graph.
    ///
    /// If you don't use this function before calling \ref checkSparse(),
    /// \ref run() or \ref init(), then an instance will be allocated
    /// automatically. The destructor deallocates this automatically allocated
    /// map, of course.
    ///
    /// \return <tt> (*this) </tt>
    UniSparseComp& toInnerNodeMap(ToInnerNodeMap& m)
    {
      return static_cast<UniSparseComp&>(Parent::toInnerNodeMap(m));
    }

    /// \brief Sets the \c ToInputEdgeMap.
    ///
    /// Sets the \c ToInputEdgeMap.
    ///
    /// \param m The \c ToInputEdgeMap of the inner digraph.
    ///
    /// If you don't use this function before calling \ref checkSparse(),
    /// \ref run() or \ref init(), then an instance will be allocated
    /// automatically. The destructor deallocates this automatically allocated
    /// map, of course.
    ///
    /// \return <tt> (*this) </tt>
    UniSparseComp& toInputEdgeMap(ToInputEdgeMap& m)
    {
      return static_cast<UniSparseComp&>(Parent::toInputEdgeMap(m));
    }

    /// \brief Sets the \c ToInnerArcMap.
    ///
    /// Sets the \c ToInnerArcMap.
    ///
    /// \param m The \c ToInnerArcMap of the input graph.
    ///
    /// If you don't use this function before calling \ref checkSparse(),
    /// \ref run() or \ref init(), then an instance will be allocated
    /// automatically. The destructor deallocates this automatically allocated
    /// map, of course.
    ///
    /// \return <tt> (*this) </tt>
    UniSparseComp& toInnerArcMap(ToInnerArcMap& m)
    {
      return static_cast<UniSparseComp&>(Parent::toInnerArcMap(m));
    }

  public:
    /// \name Execution Control
    /// The simplest way to use UniSparseComp is to call either the
    /// member function \ref checkSparse() or \ref run().
    /// If you need better control on the execution, you have to call \ref
    /// init() first, then you can process the edges with \ref
    /// processNextEdge() until \ref isAllDone() (or \ref isAllProcessed())
    /// returns \c true, as shown by the following code snippet.
    ///
    /// \code
    ///   usc.init();
    ///   while(!usc.isAlldone()) {
    ///     usc.processNextEdge();
    ///   }
    /// \endcode
    ///
    /// You can also control which edge to process. For \f$ l > k \f$ in the
    /// unweighted case, the algorithm must proceed node by node: you need to
    /// initialize a node \c u by calling \ref initNode(const Node)
    /// "initNode(u)", then any edges incident to \f$ u \f$ may be processed by
    /// calling \ref processEdge(const Edge&) "processEdge(e)". The following
    /// snippet shows an example.
    ///
    /// \code
    ///   usc.init();
    ///   for(const auto& u : g.nodes()) {
    ///     usc.initNode(u);
    ///     for(const auto& e : g.trueIncEdges(u)) {
    ///       if(u < g.oppositeNode(u, e)) {
    ///         usc.processEdge(e);
    ///       }
    ///     }
    ///   }
    /// \endcode
    ///
    /// \warning The quadratic running time of the algorithm is guaranteed only
    /// if each node is initialized (at most) once.
    ///
    /// The nodes need to be initialized only in the unweighted case if
    /// \f$ l > k \f$, in all other cases, you can freely determine which edge
    /// to process next by calling \ref processEdge(const Edge&)
    /// "processEdge(e)":
    ///
    /// \code
    ///   usc.init();
    ///   for(const auto& e : g.edges()) {
    ///     usc.processEdge(e);
    ///   }
    /// \endcode
    ///
    /// You can set the constant 1 weight function to turn an unweighted
    /// problem into a weighted one, so that the edges can be processed in
    /// arbitrary order, see \ref SetAllOneWeights.

    /// @{

    /// \brief Initializes the internal data structures.
    ///
    /// Initializes the internal data structures.
    void init()
    {
      Parent::init();           // sorts _processingOrderContainer

      if(lowerRangeCase()) {
        if(!_lowerComp) {
          _lowerComp = new LowerCompMap(*_innerDigraph, -1);
        }
        else {
          for(DNodeIt n(*_innerDigraph); n != INVALID; ++n) {
            _lowerComp->set(n, -1);
          }
        }
      }
      else {
        if(!_upperCompUnionCV) {
          _upperCompUnionCV = new UpperCompUnionMap(*_innerDigraph, false);
        }
        if(weightedCase()) {
          if(!_upperCompCV) {
            _upperCompCV = new UpperCompUnionMap(*_innerDigraph, false);
          }
          delete _upperCompMtx;
          _upperCompMtx = new UpperCompMtx(*_innerDigraph, _numNodes);
          for(DNodeIt n(*_innerDigraph); n != INVALID; ++n) {
            _upperCompMtx->set(n, n, true);
          }
        }
        else {
          _nodeIt = NodeIt(_inputGraph);
          if(_nodeIt != INVALID) {
            _incEdgeIt = TrueIncEdgeIt(_inputGraph, _nodeIt);
            upperStepItToNextValid();
          }
          else {
            _incEdgeIt = TrueIncEdgeIt(INVALID);
          }
        }
      }

      _comps.resize(0);
      if(std::is_same<RangeSelector, unisparse_bits::UpperRange>::value // cto
         || _k <= _l) {            // every node is a comp in itself
        _comps.resize(_numNodes);
        typename Comps::iterator nextComp = _comps.begin();
        for(DNodeIt n(*_innerDigraph); n != INVALID; ++nextComp, ++n) {
          nextComp->push_back(n);
        }
      }
    }

    /// \brief Initializes a new node whose incident edges can be processed in
    /// the unweighted case when \f$ l > k \f$
    ///
    /// Initializes a new node whose incident edges can be processed in the
    /// unweighted case \f$ l > k \f$. The following code snippet shows an
    /// example.
    ///
    /// \code
    ///   usc.init();
    ///   for(const auto& u : g.nodes()) {
    ///     usc.initNode(u);
    ///     for(const auto& e : g.trueIncEdges(u)) {
    ///       if(u < g.oppositeNode(u, e)) {
    ///         usc.processEdge(e);
    ///       }
    ///     }
    ///   }
    /// \endcode
    ///
    /// \param u The new node whose incident edges are to be processed next.
    ///
    /// \pre Function \ref init() must be called before using this function.
    /// \pre The edges must be processed by \ref processEdge(const Edge&)
    /// "processEdge(e)" and the edge being processed must be incident to \c u.
    /// \pre This function can only be called in the unweighted case
    /// when \f$ l > k \f$.
    void initNode(const Node u)
    {
      LEMON_ASSERT(u != INVALID, "Called initNode with INVALID node!");
      LEMON_ASSERT(upperRangeCase() && !weightedCase(),
                   "initNode can only be called in the weighted l>k case!");
      _nodeIt = NodeIt(_inputGraph, u);
      upperInitCurrNode();
    }

    /// \brief Returns the next edge to be processed.
    ///
    /// \return The next edge to be processed.
    ///
    /// \pre Function \ref init() must be called before using this function.
    Edge nextEdge() const
    {
      return lowerRangeCase() ? Parent::nextEdge()
        : static_cast<Edge>(_incEdgeIt);
    }

    /// \brief Returns the next node to be processed in the unweighted case
    /// when \f$ l > k \f$.
    ///
    /// \return The next node to be processed in the unweighted case when
    /// \f$ l > k \f$.
    ///
    /// \pre Function \ref init() must be called before using this function.
    /// \pre This function can only be called in the unweighted case
    /// when \f$ l > k \f$.
    Node nextNode() const
    {
      LEMON_ASSERT(upperRangeCase() && !weightedCase(),
                   "nextNode can only be called if l>k!");
      return _nodeIt;
    }

    /// \brief Returns \c true if all edges are processed.
    ///
    /// \return \c true if all edges are processed.
    ///
    /// \pre This function works correctly only if edges are processed by
    /// \ref checkSparse(), \ref run() or \ref processNextEdge(), but not by
    /// \ref processEdge(const Edge&) "processEdge(e)".
    /// \note Consider using the function \ref isAllDone() instead, which
    /// also detects if no more edges may be accepted.
    bool isAllProcessed() const
    {
      if(lowerRangeCase()) {
        if(weightedCase()) {
          return _currPOCIndex >= _numEdges;
        }
        else {
          return _nextEdgeIt == INVALID;
        }
      }
      else {
        if(weightedCase()) {
          return _currPOCIndex >= _numEdges;
        }
        else {
          return _nodeIt == INVALID; // && _incEdgeIt == INVALID
        }
      }
    }

    /// \brief Returns \c true if all edges are processed or no other edge
    /// may be accepted.
    ///
    /// \return \c true if all edges are processed or no other edge may be
    /// accepted.
    ///
    /// This function is just a shortcut of
    ///
    /// \code
    ///   sparseSize() >= fullRank() || isAllProcessed()
    /// \endcode
    ///
    /// \pre This function works correctly only if edges are processed by
    /// \ref checkSparse(), \ref run() or \ref processNextEdge(), but not by
    /// \ref processEdge(const Edge&) "processEdge(e)".
    bool isAllDone() const
    {
      return sparseSize() >= fullRank() || isAllProcessed();
    }

    /// \brief Processes the given edge.
    ///
    /// Processes the given edge.
    ///
    /// \param e The edge to be processed.
    ///
    /// \return The resulting \c Arc if the edge has been accepted, otherwise
    /// \c INVALID.
    ///
    /// \pre Function \ref init() must be called before using this function.
    /// \pre In the unweighted case when \f$ l > k \f$, the edge \c e must be
    /// incident to the latest node initialized by \ref initNode(const Node)
    /// "initNode(u)".
    /// \warning It is the caller's responsibility to process each edge only
    /// once. If an edge is processed multiple times, then it may get accepted
    /// several times and/or the algorithm may run slower.
    Arc processEdge(const Edge& e)
    {
      LEMON_ASSERT(e != INVALID, "Processing INVALID edge!");
      return processEdge(e, _inputGraph.u(e), _inputGraph.v(e));
    }

    /// \brief Processes the given edge.
    ///
    /// Processes the given edge.
    ///
    /// \param e The edge to be processed.
    /// \param from The incident node from which the arc should be oriented
    /// (if possible) in case \c e is accepted.
    ///
    /// \return The resulting \c Arc if the edge has been accepted, otherwise
    /// \c INVALID.
    ///
    /// \pre Function \ref init() must be called before using this function.
    /// \pre In the unweighted case when \f$ l > k \f$, the edge \c e must be
    /// incident to the latest node initialized by \ref initNode(const Node)
    /// "initNode(u)".
    /// \warning The arc will be oriented from the node \c from only if its
    /// outdegree is smaller than \f$ k \f$, otherwise, the desired direction
    /// will be ignored.
    /// \warning It is the caller's responsibility to process each edge only
    /// once. If an edge is processed multiple times, then it may get accepted
    /// several times and/or the algorithm may run slower.
    Arc processEdge(const Edge& e, const Node from)
    {
      LEMON_ASSERT(e != INVALID, "Processing INVALID edge!");
      LEMON_ASSERT(_inputGraph.u(e) == from || _inputGraph.v(e) == from,
                   "Bad orientation request!");
      return processEdge(e, from, _inputGraph.oppositeNode(from, e));
    }

    /// \brief Processes the given edge.
    ///
    /// Processes the given edge.
    ///
    /// \param e The edge to be processed.
    /// \param from The incident node from which the arc should be oriented
    /// (if possible) in case \c e is accepted.
    /// \param to The incident node to which the arc should be oriented
    /// (if possible) in case \c e is accepted.
    ///
    /// \return The resulting \c Arc if the edge has been accepted, otherwise
    /// \c INVALID.
    ///
    /// \pre Function \ref init() must be called before using this function.
    /// \pre In the unweighted case when \f$ l > k \f$, the edge \c e must be
    /// incident to the latest node initialized by \ref initNode(const Node)
    /// "initNode(u)".
    /// \warning The arc will be oriented from the node \c from only if its
    /// outdegree is smaller than \f$ k \f$, otherwise, the desired direction
    /// will be ignored.
    /// \warning It is the caller's responsibility to process each edge only
    /// once. If an edge is processed multiple times, then it may get accepted
    /// several times and/or the algorithm may run slower.
    Arc processEdge(const Edge& e, const Node from, const Node to)
    {
      return lowerRangeCase() ? _processEdge<0>(e, from, to)
        : _processEdge<1>(e, from, to);
    }

    /// \brief Processes the next edge.
    ///
    /// Processes the next edge and steps the iterator to the next edge.
    /// The following code snippet shows how this function can be used for
    /// better control on the execution.
    ///
    /// \code
    ///   usc.init();
    ///   while(!usc.isAllDone()) {
    ///     usc.processNextEdge();
    ///   }
    /// \endcode
    ///
    /// \return The resulting \c Arc if the edge has been accepted, otherwise
    /// \c INVALID.
    ///
    /// \pre init() must be called before using this function.
    Arc processNextEdge()
    {
      if(lowerRangeCase()) {
        if(weightedCase()) {
          return lowerWeightedProcessNextEdge();
        }
        else {
          return lowerUnweightedProcessNextEdge();
        }
      }
      else {
        if(weightedCase()) {
          return upperWeightedProcessNextEdge();
        }
        else {
          return upperUnweightedProcessNextEdge();
        }
      }
    }

    /// \brief Runs the algorithm to check \f$ (k,l) \f$-sparsity.
    ///
    /// This function runs the \c UniSparseComp algorithm to check
    /// \f$ (k,l) \f$-sparsity.
    ///
    /// \param heuristic The type of \c Heuristic. In the weighted case, either
    /// \ref AUTO or \ref NODE_BASIC must be used.
    ///
    /// \return \c true if the graph is \f$ (k,l) \f$-sparse.
    bool checkSparse(Heuristic heuristic)
    {
      LEMON_ASSERT(heuristic == NODE_BASIC
                   || heuristic == AUTO
                   || !weightedCase(),
                   "Only BASIC and AUTO are available in the weighted case!");
      switch(heuristic) {
      case AUTO:
        return checkSparse<Auto>();
      case NODE_BASIC:
        return checkSparse<NodeBasic>();
      case NODE_DEG_MIN:
        return checkSparse<NodeDegMin>();
      case NODE_PROC_MIN:
        return checkSparse<NodeProcMin>();
      case NODE_OUT_DEG_MIN:
        return checkSparse<NodeOutDegMin>();
      default:
        LEMON_ASSERT(0, "Unknown heuristic!");
        return false; // avoid warning
      }
    }

    /// \brief Runs the algorithm to check \f$ (k,l) \f$-sparsity.
    ///
    /// This function runs the \c UniSparseComp algorithm to check
    /// \f$ (k,l) \f$-sparsity.
    ///
    /// \tparam HeuristicImpl The class containing the implementation of the
    /// member function \c checkSparse to check the sparsity. By default, the
    /// heuristic \ref AUTO is used.
    ///
    /// \return \c true if the graph is \f$ (k,l) \f$-sparse.
    template<typename HeuristicImpl = Auto>
    bool checkSparse()
    {
      init();
      return HeuristicImpl(*this).checkSparse();
    }

    /// \brief Runs the algorithm to find a(n optimal) largest
    /// \f$ (k,l) \f$-sparse subgraph.
    ///
    /// This function runs the \c UniSparseComp algorithm to find a(n optimal)
    /// \f$ (k,l) \f$-sparse subgraph.
    ///
    /// The algorithm finds a largest sparse subgraph or, if edge weights
    /// were given, a maximum- or minimum-weight largest sparse subgraph.
    /// The components, that is, the inclusion-wise maximal tight subgraphs
    /// are also computed.
    ///
    /// \tparam HeuristicImpl The class containing the implementation of the
    /// member function \c run to run the algorithm. By default, the
    /// heuristic \ref AUTO is used.
    ///
    /// \return \c true if the graph is \f$ (k,l) \f$-sparse.
    template<typename HeuristicImpl = Auto>
    bool run()
    {
      init();
      return HeuristicImpl(*this).run();
    }

    /// \brief Runs the algorithm to find a(n optimal) largest
    /// \f$ (k,l) \f$-sparse subgraph.
    ///
    /// This function runs the \c UniSparseComp algorithm to find a(n optimal)
    /// \f$ (k,l) \f$-sparse subgraph.
    ///
    /// The algorithm finds a largest sparse subgraph or, if edge weights
    /// were given, a maximum- or minimum-weight largest sparse subgraph.
    /// The components, that is, the inclusion-wise maximal tight subgraphs
    /// are also computed.
    ///
    /// \param heuristic The type of \c Heuristic. In the weighted case, either
    /// \ref AUTO or \ref NODE_BASIC must be used.
    ///
    /// \return \c true if the graph is \f$ (k,l) \f$-sparse.
    bool run(Heuristic heuristic)
    {
      switch(heuristic) {
      case AUTO:
        return run<Auto>();
      case NODE_BASIC:
        return run<NodeBasic>();
      case NODE_DEG_MIN:
        return run<NodeDegMin>();
      case NODE_PROC_MIN:
        return run<NodeProcMin>();
      case NODE_OUT_DEG_MIN:
        return run<NodeOutDegMin>();
      default:
        LEMON_ASSERT(0, "Unknown heuristic!");
        return false; // avoid warning
      }
    }

    /// @}

  private:
    template<bool range>        // lower ~ 0, upper ~ 1
    bool inSameComp(const DNode u, const DNode v) const
    {
      if(!range) {
        return (*_lowerComp)[u] >= 0 && (*_lowerComp)[u] == (*_lowerComp)[v];
      }
      else {
        if(weightedCase()) {
          return _upperCompMtx->get(u, v);
        }
        else {
          LEMON_ASSERT((*_toInnerNode)[_nodeIt] == u
                       || (*_toInnerNode)[_nodeIt] == v,
                       "Edge being processed must be incident to _nodeIt!");
          return (*_upperCompUnionCV)[u] && (*_upperCompUnionCV)[v];
        }
      }
    }

    template<bool range>        // lower ~ 0, upper ~ 1
    Arc _processEdge(const Edge& e)
    {
      LEMON_ASSERT(e != INVALID, "Processing INVALID edge!");
      return _processEdge<range>(e, _inputGraph.u(e), _inputGraph.v(e));
    }

    template<bool range>        // lower ~ 0, upper ~ 1
    Arc _processEdge(const Edge& e, const Node from, const Node to)
    {
      LEMON_ASSERT(e != INVALID, "Processing INVALID edge!");
      LEMON_ASSERT((_inputGraph.u(e) == from && _inputGraph.v(e) == to)
                   || (_inputGraph.u(e) == to && _inputGraph.v(e) == from),
                   "Bad orientation request!");
      LEMON_ASSERT(!range || weightedCase() || _nodeIt == _inputGraph.u(e)
                   || _nodeIt == _inputGraph.v(e),
                   "The edge being processed should be incident to _nodeIt!");

      _previousEdge = e;

      const DNode innerU = (*_toInnerNode)[from];
      const DNode innerV = (*_toInnerNode)[to];

      if((_l >= _k && innerU == innerV) || inSameComp<range>(innerU, innerV)) {
        return INVALID;
      }

      reversePaths(innerU, innerV);

      LEMON_ASSERT(Parent::isInsertable(innerU, innerV),
                   "Cannot insert yet not induced by any comp!");

      const Arc a = insertArc(innerU, innerV);
      registerAcceptance(e, a);

      if(compDet(innerU, innerV)) {
        if(!range || !weightedCase()) {
          compMerge<range>();
        }
        else {
          compMergeUpperMtx();
        }
      }

      return a;
    }

    Arc upperWeightedProcessNextEdge()
    {
      LEMON_ASSERT(weightedCase(),
                   "Called upperWeightedProcessNextEdge in unweighted case!");
      LEMON_ASSERT(upperRangeCase(),
                   "Called upperWeightedProcessNextEdge for l<=k!");
      LEMON_ASSERT(_currPOCIndex < _numEdges, "Index out of bounds!");
      const Edge& e = (*_processingOrderContainer)[_currPOCIndex++];
      const Arc a = _processEdge<1>(e);
      return a;
    }

    Arc upperUnweightedProcessNextEdge()
    {
      LEMON_ASSERT(!weightedCase(),
                   "Called upperUnweightedProcessNextEdge in weighted case!");
      LEMON_ASSERT(upperRangeCase(),
                   "Called upperUnweightedProcessNextEdge for l<=k!");
      LEMON_ASSERT(_incEdgeIt != INVALID, "_incEdgeIt is INVALID!");
      const Arc a = _processEdge<1>(_incEdgeIt);
      ++_incEdgeIt;
      if(upperStepItToNextValid()) {
        // start processing a new node
        upperInitCurrNode();
      }
      return a;
    }

    Arc lowerUnweightedProcessNextEdge()
    {
      LEMON_ASSERT(!weightedCase(),
                   "Called lowerUnweightedProcessNextEdge in weighted case!");
      LEMON_ASSERT(lowerRangeCase(),
                   "Called lowerUnweightedProcessNextEdge for l>k!");
      LEMON_ASSERT(_nextEdgeIt != INVALID, "IncEdgeIt is INVALID!");
      const Arc a = _processEdge<0>(_nextEdgeIt);
      ++_nextEdgeIt;
      return a;
    }

    Arc lowerWeightedProcessNextEdge()
    {
      LEMON_ASSERT(weightedCase(),
                   "Called lowerWeightedProcessNextEdge in unweighted case!");
      LEMON_ASSERT(lowerRangeCase(),
                   "Called lowerWeightedProcessNextEdge for l>k!");
      LEMON_ASSERT(_currPOCIndex < _numEdges, "Index out of bounds!");
      const Edge& e = (*_processingOrderContainer)[_currPOCIndex++];
      return _processEdge<0>(e);
    }

    // Steps _incEdgeIt and _nodeIt until they get valid. Returns true if new
    // non-invalid node is found. Assumes that _nodeIt != INVALID
    bool upperStepItToNextValid()
    {
      LEMON_ASSERT(upperRangeCase(),
                   "Called upperStepItToNextValid in lower range!");
      LEMON_ASSERT(_nodeIt != INVALID,
                   "Called upperStepItToNextValid for INVALID _nodeIt!");
      bool nodeStepped = false;
      while(true) {
        if(_incEdgeIt == INVALID) {
          // step to the next node
          if(++_nodeIt != INVALID) {
            _incEdgeIt = TrueIncEdgeIt(_inputGraph, _nodeIt);
            nodeStepped = true;
          }
          else {
            return false;
          }
        }
        else if(_inputGraph.runningNode(_incEdgeIt) < _nodeIt) {
          // edge will be processed at its other endpoint
          ++_incEdgeIt;
        }
        else {
          // found the next edge
          return nodeStepped;
        }
      }
    }

    // Detects new components if any are formed.
    bool compDet(const DNode u, const DNode v)
    {
      if(Parent::isInsertable(u, v)) {
        return false;
      }
      _revBfs->init();
      for(DNodeIt n(*_innerDigraph); n != INVALID; ++n) {
        if((*_outDeg)[n] < _k && n != u && n != v) {
          _revBfs->addSource(n);
        }
      }
      return !_revBfs->anyReachable(u, v);
    }

    // Prepares for processing _nodeIt. Upper range only!
    void upperInitCurrNode()
    {
      LEMON_ASSERT(upperRangeCase() && !weightedCase(),
                   "Called upperInitCurrNode in lower range!");
      const auto currInnerNode = (*_toInnerNode)[_nodeIt];
      for(DNodeIt n(*_innerDigraph); n != INVALID; ++n) {
        _upperCompUnionCV->set(n, false);
      }
      for(const auto& c : _comps) {
        for(const auto& v : c) {
          if(v == currInnerNode) {
            for(const auto& w : c) {
              _upperCompUnionCV->set(w, true);
            }
            break;
          }
        }
      }
    }

    // Merges the components for the lower range and the unweighted upper range
    // case. Deletes the merged components if any exist. Assumes compDet was
    // just called (i.e. _revBfs->reachedMap is the indicator of the nodes of
    // the component inducing the newly added arc.
    template<bool range>        // lower ~ 0, upper ~ 1
    void compMerge()
    {
      LEMON_ASSERT(upperRangeCase() == range, "Bad comp care!");
      const auto& reached = _revBfs->reachedMap();
      for(size_t i = 0; i < _comps.size(); ) { // no incr
        const Comp& comp = _comps[i];
        LEMON_ASSERT(comp.size(), "Empty comp!");
        // comp is a subset of the new comp iff |comp|=1 and its element is not
        // reached, or |comp|>=2 and its first two elements are not reached
        if(!reached[comp[0]]
           && (!range || comp.size() == 1 || !reached[comp[1]])) {
          // Now comp is a subset of the new comp!
          if(i+1 != _comps.size()) { // cannot move to itself
            _comps[i] = std::move(_comps.back());
          }
          _comps.pop_back();
        }
        else {
          ++i;
        }
      }

      _comps.emplace_back();
      Comp& newComp = _comps.back();
      for(DNodeIt n(*_innerDigraph); n != INVALID; ++n) {
        if(!reached[n]) {
          newComp.push_back(n);
          if(!range) {          // lower range
            _lowerComp->set(n, _numInserted);
          }
          else {                // upper range
            _upperCompUnionCV->set(n, true);
          }
        }
      }
      LEMON_ASSERT(newComp.size(), "Empty comp found!");
    }

    // Merges the components for the weighted upper range case. Deletes the
    // merged components if any exist. Assumes compDet was just called (i.e.
    // !_revBfs->reachedMap is the indicator of the nodes of the component
    // inducing the newly added arc.
    void compMergeUpperMtx()
    {
      LEMON_ASSERT(weightedCase(),
                   "Called compMergeUpperMtx in unweighted case!");
      LEMON_ASSERT(upperRangeCase(),
                   "Called compMergeUpperMtx in lower range!");
      LEMON_ASSERT(_numNodes == 0
                   || mapMaxValue(*_innerDigraph, *_upperCompUnionCV) == 0,
                   "_upperCompUnionCV should be all 0!");
      LEMON_ASSERT(_numNodes == 0
                   || mapMaxValue(*_innerDigraph, *_upperCompCV) == 0,
                   "_upperCompCV should be all 0!");

      Comp newComp;
      const auto& reached = _revBfs->reachedMap();
      // remove comps to merge, compute their union (newComp), update matrix
      for(size_t i = 0; i < _comps.size(); ) { // no incr
        Comp& comp = _comps[i];
        LEMON_ASSERT(comp.size(), "Empty comp!");
        // comp is a subset of the new comp iff |comp|=1 and its element is not
        // reached, or |comp|>=2 and its first two elements are not reached
        if(!reached[comp[0]] && (comp.size() == 1 || !reached[comp[1]])) {
          // now we know that comp is a subset of the new comp
          // update the matrix:
          // move the nodes in (comp \cap newComp) to the front of comp
          const size_t fstInDiff
            = std::distance(std::begin(comp),
                            std::partition(std::begin(comp), std::end(comp),
                                           mapToFunctor(*_upperCompUnionCV)));
          // mark the nodes of (comp \cap newComp) in _upperCompCV
          for(size_t j = 0; j < fstInDiff; ++j) { // comp \cap newComp
            const DNode u = comp[j];
            _upperCompCV->set(u, 1);
          }
          // mark the matrix entries
          for(const DNode u : newComp) {
            if(!(*_upperCompCV)[u]) { // newComp \ comp
              for(size_t j = fstInDiff; j < comp.size(); ++j) { // comp\newComp
                const DNode v = comp[j];
                _upperCompMtx->set(u, v, true);
              }
            }
          }
          // undo marking the nodes of (comp \cap newComp) in _upperCompCV
          for(size_t j = 0; j < fstInDiff; ++j) { // comp \cap newComp
            const DNode u = comp[j];
            _upperCompCV->set(u, 0);
          }
          // add comp to newComp
          for(size_t j = fstInDiff; j < comp.size(); ++j) { // comp \ newComp
            const DNode u = comp[j];
            LEMON_ASSERT((*_upperCompUnionCV)[u] == 0, "Bad comp handling!");
            _upperCompUnionCV->set(u, true);
            newComp.push_back(u);
          }
          // remove comp
          if(i+1 != _comps.size()) { // cannot move to itself
            comp = std::move(_comps.back());
          }
          _comps.pop_back();
        }
        else {
          ++i;
        }
      }
      // now newComp is the union of the merged components, _upperCompUnionCV
      // is its char. vector

      // add the rest of the non-reached nodes to newComp
      const size_t fstNotInUnion = newComp.size();
      for(DNodeIt n(*_innerDigraph); n != INVALID; ++n) {
        if(!reached[n] && !(*_upperCompUnionCV)[n]) {
          newComp.push_back(n);
        }
      }

      // update the matrix for
      // newComp[fstNotInUnion,...] x newComp[...,fstNotInUnion)
      for(size_t i = fstNotInUnion; i < newComp.size(); ++i) {
        const DNode u = newComp[i];
        for(size_t j = 0; j < fstNotInUnion; ++j) {
          const DNode v = newComp[j];
          _upperCompMtx->set(u, v, true);
        }
      }
      // update the matrix for
      // newComp[fstNotInUnion,...] x newComp[fstNotInUnion,...]
      for(size_t i = fstNotInUnion + 1; i < newComp.size(); ++i) {
        const DNode u = newComp[i];
        for(size_t j = fstNotInUnion; j < i; ++j) {
          const DNode v = newComp[j];
          _upperCompMtx->set(u, v, true);
        }
      }

      LEMON_ASSERT(newComp.size(), "Empty comp found!");

      for(const DNode n : newComp) {
        _upperCompUnionCV->set(n, false);
      }

      _comps.push_back(std::move(newComp));

      if(0) {                   // DBG
        DigraphNodeMap<DigraphNodeMap<bool>*> mtx(*_innerDigraph);
        for(DNodeIt n(*_innerDigraph); n != INVALID; ++n) {
          mtx.set(n, new DigraphNodeMap<bool>(*_innerDigraph, false));
          (*mtx[n])[n] = true;
        }
        for(const Comp& c : _comps) {
          for(const DNode& u : c) {
            for(const DNode& v : c) {
              (*mtx[u])[v] = true;
            }
          }
        }
        for(DNodeIt u(*_innerDigraph); u != INVALID; ++u) {
          for(DNodeIt v(*_innerDigraph); v != INVALID; ++v) {
            if((*mtx[u])[v] != _upperCompMtx->get(u, v)) {
              LEMON_ASSERT(0, "Bad matrix handling!");
              std::cerr << "Bad matrix handling!" << std::endl;
              exit(1);
            }
          }
        }
        for(DNodeIt n(*_innerDigraph); n != INVALID; ++n) {
          delete(mtx[n]);
        }
      }
    }

  public:
    /// \name Query Functions
    /// The result of the algorithm can be obtained using the following
    /// functions.
    /// \pre The algorithm should be run before using these functions.

    /// @{

    using Parent::innerDigraph;
    using Parent::toInnerArcMap;
    using Parent::toInnerNodeMap;
    using Parent::toInputEdgeMap;
    using Parent::toInputNodeMap;

    /// \brief Returns const reference to the components.
    ///
    /// \return Const reference to the components.
    ///
    /// Returns a const reference to the components. Also see the class
    /// \ref CompIt, which provides a convenient way to access the nodes and
    /// edges of the components.
    const Comps& comps() const
    {
      return _comps;
    }

    /// \brief Returns a const reference to the \c UpperCompUnionMap.
    ///
    /// \return Const reference to the \c UpperCompUnionMap.
    ///
    /// \pre One of \ref checkSparse(), \ref run() or \ref init() must be
    /// called before using this function.
    ///
    /// \warning This function can be used only in the case \f$ l > k \f$.
    const UpperCompUnionMap& upperCompUnion() const
    {
      LEMON_ASSERT(_upperCompUnionCV, "No upperCompUnion allocated!");
      return *_upperCompUnionCV;
    }

    /// \brief Returns a const reference to the \c LowerCompMap.
    ///
    /// \return Const reference to the \c LowerCompMap.
    ///
    /// \pre One of \ref checkSparse(), \ref run() or \ref init() must be
    /// called before using this function.
    ///
    /// \warning This function can be used only in the case \f$ l \leq k \f$.
    const LowerCompMap& lowerCompMap() const
    {
      LEMON_ASSERT(_lowerComp, "No lowerComp allocated!");
      return *_lowerComp;
    }

    /// @}

    /// \name Iterators
    /// In case the latest edge was rejected (i.e. the functions \ref
    /// processNextEdge(), \ref processEdge(const Edge&) "processEdge(e)"
    /// return \c INVALID, or \ref checkSparse() return \c false), one can
    /// query a tight subgraph blocking the insertion of the edge using
    /// \ref nodesOfLastBlockingTight() and \ref edgesOfLastBlockingTight(), or
    /// alternatively, the \ref LastBlockingTightNodeIt and
    /// \ref LastBlockingTightEdgeIt iterators. The code snippet below shows an
    /// example.
    /// \warning If the latest edge has been accepted, then the behavior is
    /// undefined!
    ///
    /// \code
    ///   using BNodeIt = UniSparseComp<ListGraph>::LastBlockingTightNodeIt;
    ///   using BEdgeIt = UniSparseComp<ListGraph>::LastBlockingTightEdgeIt;
    ///
    ///   UniSparseComp<ListGraph> usc(g, k, l);
    ///   if(!usc.checkSparse()) {
    ///     // Nodes
    ///     for(const auto& n : usc.nodesOfLastBlockingTight()) {
    ///       std::cout << g.id(n) << std::endl;
    ///     }
    ///     // Same as above
    ///     for(BNodeIt n(usc); n != INVALID; ++n) {
    ///       std::cout << g.id(n) << std::endl;
    ///     }
    ///     // Edges
    ///     for(const auto& e : usc.edgesOfLastBlockingTight()) {
    ///       std::cout << g.id(e) << std::endl;
    ///     }
    ///     // Same as above
    ///     for(BEdgeIt e(usc); e != INVALID; ++e) {
    ///       std::cout << g.id(e) << std::endl;
    ///     }
    ///   }
    /// \endcode
    ///
    /// Moreover, iterators can be used for accessing the nodes and the edges
    /// of the components. The following example demonstrates the usage of
    /// these.
    ///
    /// \code
    ///   UniSparseComp<ListGraph> usc(g, k, l);
    ///   usc.run();
    ///   for(const auto& comp : usc.components()) {
    ///     // Nodes
    ///     for(const auto& n : comp.nodes()) {
    ///       std::cout << g.id(n) << std::endl;
    ///     }
    ///     // Edges
    ///     for(const auto& e : comp.edges()) {
    ///       std::cout << g.id(e) << std::endl;
    ///     }
    ///   }
    /// \endcode
    ///
    /// Alternatively, \ref CompIt::nodes() "nodes()"
    /// and \ref CompIt::edges() "edges()" can be used for the same purpose as
    /// follows.
    ///
    /// \code
    ///   using CIt = UniSparseComp<ListGraph>::CompIt;
    ///   using CNodeIt = UniSparseComp<ListGraph>::CompNodeIt;
    ///   using CEdgeIt = UniSparseComp<ListGraph>::CompEdgeIt;
    ///
    ///   UniSparseComp<ListGraph> usc(g, k, l);
    ///   usc.run();
    ///   for(CIt comp(usc); comp != INVALID; ++comp) {
    ///     // Nodes
    ///     for(CNodeIt n(comp); n != INVALID; ++n) {
    ///       std::cout << g.id(n) << std::endl;
    ///     }
    ///     // Edges
    ///     for(CEdgeIt e(comp); e != INVALID; ++e) {
    ///       std::cout << g.id(e) << std::endl;
    ///     }
    ///   }
    /// \endcode

    /// @{

    class LastBlockingTightNodeIt;
    class LastBlockingTightEdgeIt;

    /// \brief Iterator class for the nodes of the blocking tight subgraph.
    ///
    /// In case the latest edge was rejected (i.e. the functions
    /// \ref processNextEdge(), \ref processEdge(const Edge&) "processEdge(e)"
    /// return \c INVALID, or \ref checkSparse() return \c false), one can
    /// iterate on the node set of a tight subgraph blocking the insertion. The
    /// acceptance of any edge invalidates this iterator.
    ///
    /// The following snippet uses \ref nodesOfLastBlockingTight() to access
    /// the node set of a blocking tight subgraph after \ref checkSparse()
    /// returns \c false, i.e. rejects the last processed edge.
    ///
    /// \code
    ///   UniSparseComp<ListGraph> usc(g, k, l);
    ///   if(!usc.checkSparse()) {
    ///     for(const auto& n : usc.nodesOfLastBlockingTight()) {
    ///       std::cout << g.id(n) << std::endl;
    ///     }
    ///   }
    /// \endcode
    ///
    /// Alternatively, \ref LastBlockingTightNodeIt can be used for the same
    /// purpose as follows.
    ///
    /// \code
    ///   using BNodeIt = UniSparseComp<ListGraph>::LastBlockingTightNodeIt;
    ///   UniSparseComp<ListGraph> usc(g, k, l);
    ///   if(!usc.checkSparse()) {
    ///     for(BNodeIt n(usc); n != INVALID; ++n) {
    ///       std::cout << g.id(n) << std::endl;
    ///     }
    ///   }
    /// \endcode
    ///
    /// \pre The latest edge must be rejected.
    /// \pre The type of the node map \ref
    /// UniSparseDefaultTraits::ToInputNodeMap "ToInputNodeMap" of the
    /// underlying \c UniSparseComp class must not be \c NullMap.
    class LastBlockingTightNodeIt {
    protected:
      const UniSparseComp* const _usc;
      const Comp* const _comp;
      int _nodeIndex;

    public:
      /// \brief Constructor.
      ///
      /// Constructor. Sets the iterator to the first node.
      LastBlockingTightNodeIt(const UniSparseComp& usc)
        : _usc(&usc), _comp(findInComponent(_usc->previousEdge())),
          _nodeIndex(_comp ? _comp->size() - 1 : 0)
      {}

      LastBlockingTightNodeIt(const LastBlockingTightNodeIt& usc) = default;

      /// \brief Initializes the iterator to be invalid.
      //
      /// Initializes the iterator to be invalid.
      /// \sa Invalid for more details.
      LastBlockingTightNodeIt(Invalid)
        : _usc(nullptr), _comp(nullptr), _nodeIndex(-1)
      {}

      /// \brief Node conversion.
      ///
      /// Node conversion.
      operator Node() const
      {
        if(_comp) {
          return _nodeIndex >= 0 ? _usc->toInputNodeMap()[(*_comp)[_nodeIndex]]
            : INVALID;
        }
        // the last rejected edge is a loop, hence the node is the blocking set
        return _usc->_inputGraph.u(_usc->previousEdge());
      }

      /// \brief Steps the iterator to the next node.
      ///
      /// Steps the iterator to the next node.
      LastBlockingTightNodeIt& operator++()
      {
        --_nodeIndex;
        return *this;
      }

      /// \brief Inequality operator.
      ///
      /// Inequality operator.
      /// \pre The compared iterators belong to the same instance of
      /// \ref UniSparseComp.
      bool operator!=(const LastBlockingTightNodeIt& rhs) const
      {
        return rhs._nodeIndex != _nodeIndex;
      }

    private:
      // Tries to find the endpoints of e in a component.
      const Comp* findInComponent(const Edge& e)
      {
        if(e != INVALID) {
          const DNode innerU = _usc->toInnerNodeMap()[_usc->_inputGraph.u(e)];
          const DNode innerV = _usc->toInnerNodeMap()[_usc->_inputGraph.v(e)];
          for(auto c = _usc->_comps.rbegin(); c != _usc->_comps.rend(); ++c) {
            bool foundFirst = innerU == innerV;
            for(const auto v : *c) {
              if(v == innerU || v == innerV) {
                if(foundFirst) {
                  return &*c;
                }
                foundFirst = true;
              }
            }
          }
        }
        return nullptr;
      }
    };

    /// \brief Returns the collection of the nodes of the last blocking tight
    /// subgraph.
    ///
    /// This function can be used for iterating on the nodes of the last
    /// blocking tight subgraph. It returns a wrapped LastBlockingTightNodeIt,
    /// which behaves as an STL container and can be used in range-based for
    /// loops and STL algorithms.
    /// Processing any edge invalidates this iterator.
    ///
    /// The following code demonstrates the usage of the wrapped iterator.
    ///
    /// \code
    ///   for(const auto& n : us.nodesOfLastBlockingTight()) {
    ///     std::cout << g.id(n) << std::endl;
    ///   }
    /// \endcode
    ///
    /// \pre The latest edge must be rejected, otherwise the blocking tight
    /// subgraph and hence the behavior is undefined!
    /// \pre The type of the node map \ref
    /// UniSparseDefaultTraits::ToInputNodeMap "ToInputNodeMap" of the
    /// underlying \c UniSparseComp class must not be \c NullMap.
    LemonRangeWrapper1<LastBlockingTightNodeIt, UniSparseComp<GR, WM, TR>>
    nodesOfLastBlockingTight() const
    {
      return LemonRangeWrapper1<LastBlockingTightNodeIt,
                                UniSparseComp<GR, WM, TR>>(*this);
    }

    /// \brief Iterator class for the edges of the blocking tight subgraph.
    ///
    /// In case the latest edge was rejected (i.e. the functions
    /// \ref processNextEdge(), \ref processEdge(const Edge&) "processEdge(e)"
    /// return \c INVALID, or \ref checkSparse() return \c false), one can
    /// iterate on the edge set of an inclusion-wise minimal tight subgraph
    /// blocking the insertion. The acceptance of any edge invalidates this
    /// iterator. This iterator allocated a NodeMap<bool>, hence it takes
    /// linear space in the number of the nodes.
    ///
    /// The following snippet uses \ref edgesOfLastBlockingTight() to access
    /// the edge set of the blocking tight subgraph after \ref checkSparse()
    /// returns \c false.
    ///
    /// \code
    ///   UniSparseComp<ListGraph> usc(g, k, l);
    ///   if(!usc.checkSparse()) {
    ///     for(const auto& e : usc.edgesOfLastBlockingTight()) {
    ///       std::cout << g.id(e) << std::endl;
    ///     }
    ///   }
    /// \endcode
    ///
    /// Alternatively, \ref LastBlockingTightEdgeIt can be used for the same
    /// purpose as follows.
    ///
    /// \code
    ///   using EdgeIt = UniSparseComp<ListGraph>::LastBlockingTightEdgeIt;
    ///   UniSparseComp<ListGraph> usc(g, k, l);
    ///   if(!usc.checkSparse()) {
    ///     for(EdgeIt e(usc); e != INVALID; ++e) {
    ///       std::cout << g.id(e) << std::endl;
    ///     }
    ///   }
    /// \endcode
    ///
    /// \pre The latest edge must be rejected, otherwise the blocking tight
    /// subgraph and hence the behavior is undefined!
    /// \pre The type of the edge map \ref
    /// UniSparseDefaultTraits::ToInputEdgeMap "ToInputEdgeMap" of the
    /// underlying \c UniSparseComp class must not be \c NullMap.
    class LastBlockingTightEdgeIt : private LastBlockingTightNodeIt {
      using Parent = LastBlockingTightNodeIt;
      using InTightMap = typename Digraph::template NodeMap<bool>;

      using Parent::_usc;
      using Parent::_comp;
      using Parent::_nodeIndex;
      InTightMap* _inTight;
      OutArcIt _outArcIt;

    public:
      /// \brief Constructor.
      ///
      /// Constructor. Sets the iterator to the first edge.
      LastBlockingTightEdgeIt(const UniSparseComp& usc)
        : Parent(usc), _inTight(new InTightMap(_usc->innerDigraph())),
          _outArcIt(INVALID)
      {
        if(_comp) {
          for(const auto v : *_comp) {
            (*_inTight)[v] = true;
          }
          _outArcIt = OutArcIt(_usc->innerDigraph(),
                               (*_comp)[Parent::_nodeIndex]);
          stepOutArcToNextValid();
        }
      }

      // /// \brief Copy constructor.
      // ///
      // /// Copy constructor. Copies a NodeMap.
      // LastBlockingTightEdgeIt(const LastBlockingTightEdgeIt& rhs)
      //   : Parent(rhs), _inTight( nullptr), _outArcIt(rhs._outArcIt)
      // {
      //   if(rhs._inTight) {
      //     _inTight = new InTightMap(_usc->innerDigraph());
      //     mapCopy(_usc->innerDigraph(), *rhs._inTight, *_inTight);
      //   }
      // }

      /// \brief Move constructor.
      ///
      /// Move constructor.
      LastBlockingTightEdgeIt(LastBlockingTightEdgeIt&& rhs)
        : Parent(rhs), _inTight(rhs._inTight), _outArcIt(INVALID)
      {
        rhs._inTight = nullptr;
      }

      /// \brief Destructor.
      ///
      /// Destructor.
      ~LastBlockingTightEdgeIt()
      {
        delete _inTight;
      }

      /// \brief Initializes the iterator to be invalid.
      ///
      /// Initializes the iterator to be invalid.
      /// \sa Invalid for more details.
      LastBlockingTightEdgeIt(Invalid)
        : Parent(INVALID), _inTight(nullptr), _outArcIt(INVALID)
      {}

      /// \brief Edge conversion.
      ///
      /// Edge conversion.
      operator Edge() const
      {
        return _outArcIt != INVALID ? _usc->toInputEdgeMap()[_outArcIt]
          : INVALID;
      }

      /// \brief Steps the iterator to the next edge.
      ///
      /// Steps the iterator to the next edge.
      LastBlockingTightEdgeIt& operator++()
      {
        ++_outArcIt;
        stepOutArcToNextValid();
        return *this;
      }

      /// \brief Inequality operator.
      ///
      /// Inequality operator.
      /// \pre The compared iterators belong to the same instance of
      /// \ref UniSparseComp.
      bool operator!=(const LastBlockingTightEdgeIt& rhs) const
      {
        return _outArcIt != rhs._outArcIt;
      }

    private:
      void stepOutArcToNextValid()
      {
        const auto& dg = _usc->innerDigraph();
        while(true) {
          if(_outArcIt == INVALID) {
            // step to the next node
            if(_nodeIndex-- != 0) {
              _outArcIt = OutArcIt(dg, (*_comp)[_nodeIndex]);
            }
            else {
              // no more edges left
              return;
            }
          }
          else if((*_inTight)[dg.target(_outArcIt)]) {
            // found the next arc
            return;
          }
          else {
            // arc is not in tight, take the next arc
            ++_outArcIt;
          }
        }
      }
    };

    /// \brief Returns the collection of the edges of the last blocking tight
    /// subgraph.
    ///
    /// This function can be used for iterating on the edges of the last
    /// blocking tight subgraph. It returns a wrapped LastBlockingTightEdgeIt,
    /// which behaves as an STL container and can be used in range-based for
    /// loops and STL algorithms.
    /// The acceptance of any edge invalidates this iterator.
    ///
    /// The following code demonstrates the usage of the wrapped iterator.
    ///
    /// \code
    ///   for(const auto& e : usc.edgesOfLastBlockingTight()) {
    ///     std::cout << g.id(e) << std::endl;
    ///   }
    /// \endcode
    ///
    /// \pre The latest edge must be rejected, otherwise the blocking tight
    /// subgraph and hence the behavior is undefined!
    /// \pre The type of the edge map \ref
    /// UniSparseDefaultTraits::ToInputEdgeMap "ToInputEdgeMap" of the
    /// underlying \c UniSparseComp class must not be \c NullMap.
    unisparse_bits::RangeWrapperMoveOnly<LastBlockingTightEdgeIt,
                                         UniSparseComp<GR, WM, TR>>
    edgesOfLastBlockingTight() const
    {
      using namespace unisparse_bits;
      return RangeWrapperMoveOnly<LastBlockingTightEdgeIt,
                                  UniSparseComp<GR, WM, TR>>(*this);
    }


    class CompNodeIt;
    class CompEdgeIt;

    /// \brief Iterator class for the components.
    ///
    /// This class can be used for iterating on the components, that is, the
    /// inclusion-wise maximal tight subgraphs. The nodes and edges of each
    /// component can be accessed using \ref CompNodeIt and \ref CompEdgeIt,
    /// respectively. The acceptance of any edge invalidates these iterators.
    /// The wrappers \ref components(), \ref CompIt::nodes() and
    /// \ref CompIt::edges() give a comfortable way to use these iterators.
    /// The following code snippet demonstrates their usage.
    ///
    /// \code
    ///   UniSparseComp<ListGraph> usc(g, k, l);
    ///   usc.run();
    ///   for(const auto& comp : usc.components()) {
    ///     // Nodes
    ///     for(const auto& n : comp.nodes()) {
    ///       std::cout << g.id(n) << std::endl;
    ///     }
    ///     // Edges
    ///     for(const auto& e : comp.edges()) {
    ///       std::cout << g.id(e) << std::endl;
    ///     }
    ///   }
    /// \endcode
    ///
    /// Alternatively, \ref CompIt can be used directly for the same purpose as
    /// follows.
    ///
    /// \code
    ///   using CIt = UniSparseComp<ListGraph>::CompIt;
    ///   using CNodeIt = UniSparseComp<ListGraph>::CompNodeIt;
    ///   using CEdgeIt = UniSparseComp<ListGraph>::CompEdgeIt;
    ///
    ///   UniSparseComp<ListGraph> usc(g, k, l);
    ///   usc.run();
    ///   for(CIt comp(usc); comp != INVALID; ++comp) {
    ///     // Nodes
    ///     for(CNodeIt n(comp); n != INVALID; ++n) {
    ///       std::cout << g.id(n) << std::endl;
    ///     }
    ///     // Edges
    ///     for(CEdgeIt e(comp); e != INVALID; ++e) {
    ///       std::cout << g.id(e) << std::endl;
    ///     }
    ///   }
    /// \endcode
    ///
    /// \pre One of \ref checkSparse(), \ref init() or \ref run() must be
    /// called before using this iterator.
    /// \note If the edges are processed by explicit calls of
    /// \ref processEdge(const Edge&) "processEdge(e)" or
    /// \ref processNextEdge(), then the components can be queried
    /// after processing each edge.
    class CompIt {
      using InCompMap = typename Digraph::template NodeMap<bool>;

      friend class UniSparseComp::CompNodeIt;
      friend class UniSparseComp::CompEdgeIt;

      const UniSparseComp* const _usc;
      mutable InCompMap* _inComp;
      bool _inCompUpToDate;
      int _compIndex;

    public:
      /// \brief Constructor.
      ///
      /// Constructor. Sets the iterator to the first component.
      CompIt(const UniSparseComp& usc)
        : _usc(&usc), _inComp(nullptr), _inCompUpToDate(false),
          _compIndex(static_cast<int>(usc._comps.size()) - 1)
      {}

      /// \brief Initializes the iterator to be invalid.
      ///
      /// Initializes the iterator to be invalid.
      /// \sa Invalid for more details.
      CompIt(Invalid)
        : _usc(nullptr), _inComp(nullptr), _inCompUpToDate(false),
          _compIndex(-1)
      {}

      /// \brief Move constructor.
      ///
      /// Move constructor.
      CompIt(CompIt&& rhs)
        : _usc(rhs._usc), _inComp(rhs._inComp),
          _inCompUpToDate(rhs._inCompUpToDate), _compIndex(rhs._compIndex)
      {
        rhs._inComp = nullptr;
      }

      // Implicitly deleted copy constructor.
      CompIt(const CompIt&) = delete;

      /// \brief Destructor.
      ///
      /// Destructor.
      ~CompIt()
      {
        delete _inComp;
      }

      /// \brief Steps the iterator to the next component.
      ///
      /// Steps the iterator to the next component.
      CompIt& operator++()
      {
        _inCompUpToDate = false;
        --_compIndex;
        return *this;
      }

      /// \brief Inequality operator.
      ///
      /// Inequality operator. Assumes that the underlying UniSparseComp
      /// instances are the same.
      bool operator!=(const CompIt& rhs) const
      {
        return _compIndex != rhs._compIndex;
      }

      /// \brief Returns the collection of the nodes of a component.
      ///
      /// This function can be used for iterating on the nodes of a
      /// component. It returns a wrapped CompIt, which behaves as an STL
      /// container and can be used in range-based for loops and STL
      /// algorithms. The acceptance of any edge invalidates this iterator.
      ///
      /// The following code demonstrates the usage of the wrapped iterator.
      ///
      /// \code
      ///   for(const auto& comp : usc.components()) {
      ///     for(const auto& n : comp.nodes()) {
      ///       std::cout << g.id(n) << std::endl;
      ///     }
      ///   }
      /// \endcode
      ///
      /// \pre One of \ref checkSparse(), \ref run() or \ref init() must be
      /// called before using this iterator.
      /// \pre The type of the node map \ref
      /// UniSparseDefaultTraits::ToInputNodeMap "ToInputNodeMap" of the
      /// underlying \c UniSparseComp class must not be \c NullMap.
      LemonRangeWrapper1<CompNodeIt, CompIt> nodes() const
      {
        return LemonRangeWrapper1<CompNodeIt, CompIt>(*this);
      }

      /// \brief Returns the collection of the edges of a component.
      ///
      /// This function can be used for iterating on the edges of a
      /// component. It returns a wrapped CompIt, which behaves as an STL
      /// container and can be used in range-based for loops and STL
      /// algorithms. The acceptance of any edge invalidates this iterator.
      ///
      /// The following code demonstrates the usage of the wrapped iterator.
      ///
      /// \code
      ///   for(const auto& comp : usc.components()) {
      ///     for(const auto& e : comp.edges()) {
      ///       std::cout << g.id(e) << std::endl;
      ///     }
      ///   }
      /// \endcode
      ///
      /// \pre One of \ref checkSparse(), \ref run() or \ref init() must be
      /// called before using this iterator.
      /// \pre The type of the node map \ref
      /// UniSparseDefaultTraits::ToInnerNodeMap "ToInnerNodeMap" of the
      /// underlying \c UniSparseComp class must not be \c NullMap.
      /// \pre The type of the edge map \ref
      /// UniSparseDefaultTraits::ToInputEdgeMap "ToInputEdgeMap" of the
      /// underlying \c UniSparseComp class must not be \c NullMap.
      LemonRangeWrapper1<CompEdgeIt, CompIt> edges() const
      {
        using namespace unisparse_bits;
        return LemonRangeWrapper1<CompEdgeIt, CompIt>(*this);
      }
    };

    /// \brief Returns the collection of the components.
    ///
    /// This class can be used for iterating on the components, that is, the
    /// inclusion-wise maximal tight subgraphs. It returns a wrapped CompIt,
    /// which behaves as an STL container and can be used in range-based for
    /// loops and STL algorithms. The acceptance of any edge invalidates this
    /// iterator.
    ///
    /// The following code demonstrates the usage of the wrapped iterator.
    ///
    /// \code
    ///   UniSparseComp<ListGraph> usc(g, k, l);
    ///   usc.run();
    ///   for(const auto& comp : usc.components()) {
    ///     // Nodes
    ///     for(const auto& n : comp.nodes()) {
    ///       std::cout << g.id(n) << std::endl;
    ///     }
    ///     // Edges
    ///     for(const auto& e : comp.edges()) {
    ///       std::cout << g.id(e) << std::endl;
    ///     }
    ///   }
    /// \endcode
    ///
    /// \pre One of \ref checkSparse(), \ref run() or \ref init() must be
    /// called before using this iterator.
    unisparse_bits::RangeWrapperMoveOnly<CompIt, UniSparseComp<GR, WM, TR>>
    components() const
    {
      using namespace unisparse_bits;
      return RangeWrapperMoveOnly<CompIt, UniSparseComp<GR, WM, TR>>(*this);
    }

    /// \brief Iterator class for the nodes of a component.
    ///
    /// This iterator goes through the nodes of a component. The acceptance of
    /// any edge invalidates this iterator. See \ref UniSparseComp::CompIt for
    /// more details.
    ///
    /// \pre One of \ref checkSparse(), \ref run() or \ref init() must be
    /// called before using this iterator.
    /// \pre The type of the node map \ref
    /// UniSparseDefaultTraits::ToInputNodeMap "ToInputNodeMap" of the
    /// underlying \c UniSparseComp class must not be \c NullMap.
    /// \note If the edges are processed by explicit calls of
    /// \ref processEdge(const Edge&) "processEdge(e)" or
    /// \ref processNextEdge(), then the components can be queried
    /// after processing each edge.
    class CompNodeIt {
    protected:
      const CompIt* const _compIt;
      int _nodeIndex;

    public:
      /// \brief Constructor.
      ///
      /// Constructor. Sets the iterator to the first node.
      CompNodeIt(const CompIt& compIt)
        : _compIt(&compIt),
          _nodeIndex(_compIt->_usc->_comps[compIt._compIndex].size() - 1)
      {}

      /// \brief Initializes the iterator to be invalid.
      //
      /// Initializes the iterator to be invalid.
      /// \sa Invalid for more details.
      CompNodeIt(Invalid) : _compIt(nullptr), _nodeIndex(-1)
      {}

      /// \brief Node conversion.
      ///
      /// Node conversion.
      operator Node() const
      {
        const auto& usc = _compIt->_usc;
        return _compIt
          ? usc->toInputNodeMap()[usc->_comps[_compIt->_compIndex][_nodeIndex]]
          : INVALID;
      }

      /// \brief Steps the iterator to the next node.
      ///
      /// Steps the iterator to the next node.
      CompNodeIt& operator++()
      {
        --_nodeIndex;
        return *this;
      }

      /// \brief Inequality operator.
      ///
      /// Inequality operator.
      bool operator!=(const CompNodeIt& rhs) const
      {
        return rhs._nodeIndex != _nodeIndex;
      }

    protected:
      // DNode conversion.
      DNode getDNode() const
      {
        return _compIt ? _compIt->_usc->_comps[_compIt->_compIndex][_nodeIndex]
          : INVALID;
      }
    };

    /// \brief Iterator class for the edges of a component.
    ///
    /// This iterator goes through the edges of a component. The acceptance of
    /// any edge invalidates this iterator. See \ref UniSparseComp::CompIt for
    /// more details.
    ///
    /// \pre One of \ref checkSparse(), \ref run() or \ref init() must be
    /// called before using this iterator.
    /// \pre The type of the node map \ref
    /// UniSparseDefaultTraits::ToInnerNodeMap "ToInnerNodeMap" of the
    /// underlying \c UniSparseComp class must not be \c NullMap.
    /// \pre The type of the edge map \ref
    /// UniSparseDefaultTraits::ToInputEdgeMap "ToInputEdgeMap" of the
    /// underlying \c UniSparseComp class must not be \c NullMap.
    /// \note If the edges are processed by explicit calls of
    /// \ref processEdge(const Edge&) "processEdge(e)" or
    /// \ref processNextEdge(), then the components can be queried
    /// after processing each edge.
    class CompEdgeIt : private CompNodeIt {
      using Parent = CompNodeIt;
      using InCompMap = typename Digraph::template NodeMap<bool>;

      using Parent::_nodeIndex;
      using Parent::_compIt;
      OutArcIt _outArcIt;

    public:
      /// \brief Constructor.
      ///
      /// Constructor. Sets the iterator to the first edge.
      CompEdgeIt(const CompIt& compIt)
        : Parent(compIt),
          _outArcIt(_compIt->_usc->innerDigraph(),
                    _compIt->_usc->_comps[_compIt->_compIndex][_nodeIndex])
      {
        const auto& usc = _compIt->_usc;
        if(!_compIt->_inCompUpToDate) {
          if(!_compIt->_inComp) {
            _compIt->_inComp = new InCompMap(usc->innerDigraph(), false);
          }
          else if(_compIt->_compIndex
                  < static_cast<int>(usc->_comps.size() - 1)) {
            for(const auto v : usc->_comps[_compIt->_compIndex + 1]) {
              (*_compIt->_inComp)[v] = false;
            }
          }
          for(const auto v : usc->_comps[_compIt->_compIndex]) {
            (*_compIt->_inComp)[v] = true;
          }
        }
        stepOutArcToNextValid();
      }

      /// \brief Initializes the iterator to be invalid.
      ///
      /// Initializes the iterator to be invalid.
      /// \sa Invalid for more details.
      CompEdgeIt(Invalid) : Parent(INVALID), _outArcIt(INVALID)
      {}

      /// \brief Edge conversion.
      ///
      /// Edge conversion.
      operator Edge() const
      {
        return _outArcIt != INVALID ? (*_compIt->_usc->_toInputEdge)[_outArcIt]
          : INVALID;
      }

      /// \brief Steps the iterator to the next edge.
      ///
      /// Steps the iterator to the next edge.
      CompEdgeIt& operator++()
      {
        ++_outArcIt;
        stepOutArcToNextValid();
        return *this;
      }

      /// \brief Inequality operator.
      ///
      /// Inequality operator.
      bool operator!=(const CompEdgeIt& rhs) const
      {
        return _outArcIt != rhs._outArcIt;
      }

    private:
      void stepOutArcToNextValid()
      {
        const auto& dg = _compIt->_usc->innerDigraph();
        while(true) {
          if(_outArcIt == INVALID) {
            // step to the next node
            if(_nodeIndex-- != 0) {
              _outArcIt = OutArcIt(dg, this->getDNode());
            }
            else {
              // no more edges left
              return;
            }
          }
          else if((*_compIt->_inComp)[dg.target(_outArcIt)]) {
            // found the next arc
            return;
          }
          else {
            // arc is not in tight, take the next arc
            ++_outArcIt;
          }
        }
      }
    };

    /// @}

  };


  // this is a Traits class for UniSparseSpec
  template<typename GR>
  class UniSparseSpecWizardBase {
  public:
    using Graph = GR;
    using Node = typename Graph::Node;
    using Edge = typename Graph::Edge;
    using Digraph = ListDigraph;
    using DNode = typename Digraph::Node;
    using Arc = typename Digraph::Arc;

    using ToInputNodeMap = NullMap<DNode, Node>;
    using ToInnerNodeMap = typename Graph::template NodeMap<DNode>;
    using ToInputEdgeMap = NullMap<Arc, Edge>;
    using ToInnerArcMap = NullMap<Edge, Arc>;

  protected:
    using IsSet_ToInputNodeMap = std::false_type;
    using IsSet_ToInnerNodeMap = std::false_type;
    using IsSet_ToInputEdgeMap = std::false_type;
    using IsSet_ToInnerArcMap = std::false_type;

    const Graph& _g;
    const int _k;
    void* _digraph;
    void* _toInputNodeMap;
    void* _toInnerNodeMap;
    void* _toInputEdgeMap;
    void* _toInnerArcMap;

  public:
    UniSparseSpecWizardBase(const Graph& g, const int k)
      : _g(g), _k(k), _digraph(nullptr), _toInputNodeMap(nullptr),
        _toInnerNodeMap(nullptr), _toInputEdgeMap(nullptr),
        _toInnerArcMap(nullptr)
    {}

    ~UniSparseSpecWizardBase()
    {}

    static Digraph* createInnerDigraph()
    {
      return new Digraph;
    }

    static ToInputNodeMap* createToInputNodeMap(const Digraph&)
    {
      return new ToInputNodeMap; // the owner is UniSparseSpec
    }

    static ToInnerNodeMap* createToInnerNodeMap(const Graph& g)
    {
      return new ToInnerNodeMap(g, INVALID); // the owner is UniSparseSpec
    }

    static ToInputEdgeMap* createToInputEdgeMap(const Digraph&)
    {
      return new ToInputEdgeMap; // the owner is UniSparseSpec
    }

    static ToInnerArcMap* createToInnerArcMap(const Graph&)
    {
      return new ToInnerArcMap; // the owner is UniSparseSpec
    }
  };

  /// \brief Auxiliary class for the function-type interface of UniSparseSpec
  /// class.
  ///
  /// This auxiliary class implements the
  /// \ref uniSparseSpec() "function-type interface" of \ref UniSparseSpec
  /// algorithm.
  ///
  /// This class should only be used through the \ref uniSparseSpec() function.
  ///
  /// \tparam TR The traits class that defines various types used by the
  /// algorithm.
  template<typename TR>
  class UniSparseSpecWizard : public TR {
    using Parent = TR;

  public:
    using typename Parent::Graph;
    using typename Parent::Digraph;
    using typename Parent::Node;
    using typename Parent::Edge;
    using typename Parent::DNode;
    using typename Parent::Arc;
    using typename Parent::ToInputNodeMap;
    using typename Parent::ToInnerNodeMap;
    using typename Parent::ToInputEdgeMap;
    using typename Parent::ToInnerArcMap;

  protected:
    using typename Parent::IsSet_ToInputNodeMap;
    using typename Parent::IsSet_ToInnerNodeMap;
    using typename Parent::IsSet_ToInputEdgeMap;
    using typename Parent::IsSet_ToInnerArcMap;

    using Parent::_g;
    using Parent::_k;
    using Parent::_digraph;
    using Parent::_toInputNodeMap;
    using Parent::_toInnerNodeMap;
    using Parent::_toInputEdgeMap;
    using Parent::_toInnerArcMap;

    template<typename USS>
    void setData(USS& uss)
    {
      if(_digraph) {
        uss.innerDigraph(*reinterpret_cast<Digraph*>(_digraph));
      }
      if(_toInputNodeMap) {
        uss.toInputNodeMap(*reinterpret_cast<ToInputNodeMap*>
                           (_toInputNodeMap));
      }
      if(_toInnerNodeMap) {
        uss.toInnerNodeMap(*reinterpret_cast<ToInnerNodeMap*>
                           (_toInnerNodeMap));
      }
      if(_toInputEdgeMap) {
        uss.toInputEdgeMap(*reinterpret_cast<ToInputEdgeMap*>
                           (_toInputEdgeMap));
      }
      if(_toInnerArcMap) {
        uss.toInnerArcMap(*reinterpret_cast<ToInnerArcMap*>
                          (_toInnerArcMap));
      }
    }

  public:
    UniSparseSpecWizard(const Graph& g, const int k) : Parent(g, k)
    {}

    UniSparseSpecWizard(const Parent& p) : Parent(p)
    {}

    UniSparseSpecWizard(const UniSparseSpecWizard& p) : Parent(p)
    {}

    ~UniSparseSpecWizard()
    {}

    template<typename DGR>
    struct SetInnerDigraph : public Parent {
      using Digraph = DGR;
      using DNode = typename Digraph::Node;
      using Arc = typename Digraph::Arc;
      using ToInputNodeMap = typename // resort to default if not already set
        std::conditional<std::is_same<IsSet_ToInputNodeMap,
                                      std::true_type>::value,
                         typename Parent::ToInputNodeMap,
                         NullMap<DNode, Node>>::type;
      using ToInnerNodeMap = typename // resort to default if not already set
        std::conditional<std::is_same<IsSet_ToInnerNodeMap,
                                      std::true_type>::value,
                         typename Parent::ToInnerNodeMap,
                         typename Graph::template NodeMap<DNode>>::type;
      using ToInputEdgeMap = typename // resort to default if not already set
        std::conditional<std::is_same<IsSet_ToInputEdgeMap,
                                      std::true_type>::value,
                         typename Parent::ToInputEdgeMap,
                         NullMap<Arc, Edge>>::type;
      using ToInnerArcMap = typename // resort to default if not already set
        std::conditional<std::is_same<IsSet_ToInnerArcMap,
                                      std::true_type>::value,
                         typename Parent::ToInnerArcMap,
                         NullMap<Edge, Arc>>::type;

      static Digraph* createInnerDigraph()
      {
        LEMON_ASSERT(false, "Digraph is not initialized!");
        return nullptr;
      }

      // update Parent::createToInputNodeMap if ToInputNodeMap is not set
      template<typename T = IsSet_ToInputNodeMap>
      static typename std::enable_if<std::is_same<T, std::false_type>::value,
                                     ToInputNodeMap*>::type
      createToInputNodeMap(const Digraph&)
      {
        return new ToInputNodeMap; // the owner is UniSparseSpec
      }
      // do nothing if already set
      template<typename T = IsSet_ToInputNodeMap>
      static typename std::enable_if<std::is_same<T, std::true_type>::value,
                                     ToInputNodeMap*>::type
      createToInputNodeMap(const Digraph&)
      {
        LEMON_ASSERT(false, "ToInputNodeMap is not initialized!");
        return nullptr;
      }

      // update Parent::createToInnerNodeMap if ToInnerNodeMap is not set
      template<typename T = IsSet_ToInnerNodeMap>
      static typename std::enable_if<std::is_same<T, std::false_type>::value,
                                     ToInnerNodeMap*>::type
      createToInnerNodeMap(const Graph& g)
      {
        return new ToInnerNodeMap(g, INVALID); // the owner is UniSparseSpec
      }
      // do nothing if already set
      template<typename T = IsSet_ToInnerNodeMap>
      static typename std::enable_if<std::is_same<T, std::true_type>::value,
                                     ToInnerNodeMap*>::type
      createToInnerNodeMap(const Graph&)
      {
        LEMON_ASSERT(false, "ToInnerNodeMap is not initialized!");
        return nullptr;
      }

      // update Parent::createToInputEdgeMap if ToInputEdgeMap is not set
      template<typename T = IsSet_ToInputEdgeMap>
      static typename std::enable_if<std::is_same<T, std::false_type>::value,
                                     ToInputEdgeMap*>::type
      createToInputEdgeMap(const Digraph&)
      {
        return new ToInputEdgeMap; // the owner is UniSparseSpec
      }
      // do nothing if already set
      template<typename T = IsSet_ToInputEdgeMap>
      static typename std::enable_if<std::is_same<T, std::true_type>::value,
                                     ToInputEdgeMap*>::type
      createToInputEdgeMap(const Digraph&)
      {
        LEMON_ASSERT(false, "ToInputEdgeMap is not initialized!");
        return nullptr;
      }

      // update Parent::createToInnerArcMap if ToInnerArcMap is not set
      template<typename T = IsSet_ToInnerArcMap>
      static typename std::enable_if<std::is_same<T, std::false_type>::value,
                                     ToInnerArcMap*>::type
      createToInnerArcMap(const Graph&)
      {
        return new ToInnerArcMap; // the owner is UniSparse
      }
      // do nothing if already set
      template<typename T = IsSet_ToInnerArcMap>
      static typename std::enable_if<std::is_same<T, std::true_type>::value,
                                     ToInnerArcMap*>::type
      createToInnerArcMap(const Graph&)
      {
        LEMON_ASSERT(false, "ToInnerArcMap is not initialized!");
        return nullptr;
      }

      SetInnerDigraph(const Parent& p, DGR& dg) : Parent(p)
      {
        Parent::_digraph = reinterpret_cast<void*>(&dg);
      }
    };

    /// \brief \ref named-templ-param "Named parameter" for setting
    /// the \c InnerDigraph.
    ///
    /// \ref named-templ-param "Named parameter" for setting the
    /// \c InnerDigraph.
    template<typename DGR>
    UniSparseSpecWizard<SetInnerDigraph<DGR>> innerDigraph(const DGR& dg)
    {
      SetInnerDigraph<DGR> setInnerDigraph(*this, const_cast<DGR&>(dg));
      return UniSparseSpecWizard<SetInnerDigraph<DGR>>(setInnerDigraph);
    }

    template<typename NM>
    struct SetToInputNodeMap : public Parent {
      using ToInputNodeMap = NM;
      using IsSet_ToInputNodeMap = std::true_type;

      static ToInputNodeMap* createToInputNodeMap(const Digraph&)
      {
        LEMON_ASSERT(false, "ToInputNodeMap is not initialized!");
        return nullptr;
      }

      SetToInputNodeMap(const Parent& p, NM& nm) : Parent(p)
      {
        Parent::_toInputNodeMap = reinterpret_cast<void*>(&nm);
      }
    };

    /// \brief \ref named-templ-param "Named parameter" for setting
    /// the \c ToInputNodeMap.
    ///
    /// \ref named-templ-param "Named parameter" function for setting the node
    /// map that converts the nodes of the inner digraph to the input graph.
    template<typename NM>
    UniSparseSpecWizard<SetToInputNodeMap<NM>> toInputNodeMap(const NM& nm)
    {
      SetToInputNodeMap<NM> setToInputNodeMap(*this, const_cast<NM&>(nm));
      return UniSparseSpecWizard<SetToInputNodeMap<NM>>(setToInputNodeMap);
    }

    template<typename NM>
    struct SetToInnerNodeMap : public Parent {
      using ToInnerNodeMap = NM;
      using IsSet_ToInnerNodeMap = std::true_type;

      static ToInnerNodeMap* createToInnerNodeMap(const Graph&)
      {
        LEMON_ASSERT(false, "ToInnerNodeMap is not initialized!");
        return nullptr;
      }

      SetToInnerNodeMap(const Parent& p, NM& nm) : Parent(p)
      {
        Parent::_toInnerNodeMap = reinterpret_cast<void*>(&nm);
      }
    };

    /// \brief \ref named-templ-param "Named parameter" for setting
    /// the \c ToInnerNodeMap.
    ///
    /// \ref named-templ-param "Named parameter" function for setting the node
    /// map that converts the nodes of the input graph to the inner digraph.
    template<typename NM>
    UniSparseSpecWizard<SetToInnerNodeMap<NM>> toInnerNodeMap(const NM& nm)
    {
      SetToInnerNodeMap<NM> setToInnerNodeMap(*this, const_cast<NM&>(nm));
      return UniSparseSpecWizard<SetToInnerNodeMap<NM>>(setToInnerNodeMap);
    }

    template<typename AM>
    struct SetToInputEdgeMap : public Parent {
      using ToInputEdgeMap = AM;
      using IsSet_ToInputEdgeMap = std::true_type;

      static ToInputEdgeMap* createToInputEdgeMap(const Digraph&)
      {
        LEMON_ASSERT(false, "ToInputEdgeMap is not initialized!");
        return nullptr;
      }

      SetToInputEdgeMap(const Parent& p, AM& am) : Parent(p)
      {
        Parent::_toInputEdgeMap = reinterpret_cast<void*>(&am);
      }
    };

    /// \brief \ref named-templ-param "Named parameter" for setting
    /// the \c ToInputEdgeMap.
    ///
    /// \ref named-templ-param "Named parameter" function for setting the arc
    /// map that converts the arcs of the inner digraph to the edges of the
    /// input graph.
    template<typename AM>
    UniSparseSpecWizard<SetToInputEdgeMap<AM>> toInputEdgeMap(const AM& am)
    {
      SetToInputEdgeMap<AM> setToInputEdgeMap(*this, const_cast<AM&>(am));
      return UniSparseSpecWizard<SetToInputEdgeMap<AM>>(setToInputEdgeMap);
    }

    template<typename EM>
    struct SetToInnerArcMap : public Parent {
      using ToInnerArcMap = EM;
      using IsSet_ToInnerArcMap = std::true_type;

      static ToInnerArcMap* createToInnerArcMap(const Graph&)
      {
        LEMON_ASSERT(false, "ToInnerArcMap is not initialized!");
        return nullptr;
      }

      SetToInnerArcMap(const Parent& p, EM& em) : Parent(p) {
        Parent::_toInnerArcMap = reinterpret_cast<void*>(&em);
      }
    };

    /// \brief \ref named-templ-param "Named parameter" for setting
    /// the \c ToInnerArcMap.
    ///
    /// \ref named-templ-param "Named parameter" function for setting the edge
    /// map that converts the edges of the input graph to the arcs of the inner
    /// digraph.
    template<typename EM>
    UniSparseSpecWizard<SetToInnerArcMap<EM>> toInnerArcMap(const EM& em)
    {
      SetToInnerArcMap<EM> setToInnerArcMap(*this, const_cast<EM&>(em));
      return UniSparseSpecWizard<SetToInnerArcMap<EM>>(setToInnerArcMap);
    }

    /// \brief Runs the \ref UniSparseSpec algorithm to find the inclusion-wise
    /// maximal \f$ (k,2k) \f$-sparse subgraph.
    ///
    /// This function runs the \ref UniSparseSpec algorithm to determine the
    /// inclusion-wise maximal \f$ (k,2k) \f$-sparse subgraph.
    ///
    /// \return \c true if the graph is \f$ (k,2k) \f$-sparse.
    bool run()
    {
      UniSparseSpec<Graph, TR> uss(_g, _k);
      setData(uss);
      return uss.run();
    }

    /// \brief Runs the \ref UniSparseSpec algorithm to check
    /// \f$ (k,2k) \f$-sparsity.
    ///
    /// This function runs the \ref UniSparseSpec algorithm to check
    /// \f$ (k,2k) \f$-sparsity. The algorithm will terminate as soon as an
    /// edge gets rejected.
    ///
    /// \return \c true if the graph is \f$ (k,2k) \f$-sparse.
    bool checkSparse()
    {
      UniSparseSpec<Graph, TR> uss(_g, _k);
      setData(uss);
      return uss.checkSparse();
    }

    /// \brief Runs the \ref UniSparseSpec algorithm to find the size of an
    /// inclusion-wise maximal \f$ (k,2k) \f$-sparse subgraph.
    ///
    /// Runs the \ref UniSparseSpec algorithm to find the size of an
    /// inclusion-wise maximal \f$ (k,2k) \f$-sparse subgraph.
    ///
    /// \return The size of the largest \f$ (k,2k) \f$-sparse.
    int maxSparseSize()
    {
      UniSparseSpec<Graph, TR> uss(_g, _k);
      setData(uss);
      uss.run();
      return uss.sparseSize();
    }
  };

  // this is a Traits class for UniSparseSpec
  template<typename GR, typename WM = NullMap<typename GR::Edge, int>>
  class UniSparseWizardBase : public UniSparseSpecWizardBase<GR> {
    using Parent = UniSparseSpecWizardBase<GR>;

  public:
    using typename Parent::Graph;
    using typename Parent::Digraph;
    using typename Parent::Node;
    using typename Parent::Edge;
    using typename Parent::DNode;
    using typename Parent::Arc;

    using typename Parent::ToInputNodeMap;
    using typename Parent::ToInnerNodeMap;
    using typename Parent::ToInputEdgeMap;
    using typename Parent::ToInnerArcMap;

    using WeightMap = WM;
    using ProcessingOrderContainer = std::vector<Edge>;
    using RangeSelector = unisparse_bits::UnknownRange;
    using AllOneWeights = std::false_type;

  protected:
    using Parent::_g;
    using Parent::_k;
    using Parent::_digraph;
    using Parent::_toInputNodeMap;
    using Parent::_toInnerNodeMap;
    using Parent::_toInputEdgeMap;
    using Parent::_toInnerArcMap;

    const int _l;
    const WM* _weights;
    bool _maximize;
    void* _poc;

  public:
    UniSparseWizardBase(const Graph& g, const int k, const int l)
      : Parent(g, k), _l(l), _weights(nullptr), _maximize(1), _poc(nullptr)
    {}

    UniSparseWizardBase(const Graph& g, const int k, const int l, const WM& w)
      : Parent(g, k), _l(l), _weights(&w), _maximize(1), _poc(nullptr)
    {}

    ~UniSparseWizardBase()
    {}

    static ProcessingOrderContainer* createProcessingOrderContainer()
    {
      return new ProcessingOrderContainer;
    }
  };

  /// \brief Auxiliary class for the function-type interface of UniSparse and
  /// UniSparseComp classes.
  ///
  /// This auxiliary class implements the
  /// \ref uniSparse() "function-type interface" of \ref UniSparse algorithm,
  /// and \ref uniSparseComp() "function-type interface" of \ref UniSparseComp
  /// algorithm.
  ///
  /// This class should only be used through the \ref uniSparse() and
  /// \ref uniSparseComp() functions.
  ///
  /// \tparam US Either UniSparse or UniSparseComp.
  /// \tparam TR The traits class that defines various types used by the
  /// algorithm.
  template<template<typename, typename, typename> class US, typename TR>
  class UniSparseWizard : public TR {
    using Parent = TR;

  public:
    using typename Parent::Graph;
    using typename Parent::Digraph;
    using typename Parent::Node;
    using typename Parent::Edge;
    using typename Parent::DNode;
    using typename Parent::Arc;
    using typename Parent::ToInputNodeMap;
    using typename Parent::ToInnerNodeMap;
    using typename Parent::ToInputEdgeMap;
    using typename Parent::ToInnerArcMap;

    using typename Parent::ProcessingOrderContainer;
    using typename Parent::RangeSelector;
    using typename Parent::AllOneWeights;
    using typename Parent::WeightMap;

  protected:
    using typename Parent::IsSet_ToInputNodeMap;
    using typename Parent::IsSet_ToInnerNodeMap;
    using typename Parent::IsSet_ToInputEdgeMap;
    using typename Parent::IsSet_ToInnerArcMap;

    using Parent::_g;
    using Parent::_k;
    using Parent::_digraph;
    using Parent::_toInputNodeMap;
    using Parent::_toInnerNodeMap;
    using Parent::_toInputEdgeMap;
    using Parent::_toInnerArcMap;

    using Parent::_l;
    using Parent::_weights;
    using Parent::_maximize;
    using Parent::_poc;

  public:
    UniSparseWizard(const Graph& g, const int k, const int l,
                    const WeightMap& w)
      : Parent(g, k, l, w)
    {}

    UniSparseWizard(const Graph& g, const int k, const int l)
      : Parent(g, k, l)
    {}

    UniSparseWizard(const Parent& p) : Parent(p)
    {}

    UniSparseWizard(const UniSparseWizard& p) : Parent(p)
    {}

    ~UniSparseWizard()
    {}

    template<typename DGR>
    struct SetInnerDigraph : public Parent {
      using Digraph = DGR;
      using DNode = typename Digraph::Node;
      using Arc = typename Digraph::Arc;
      using ToInputNodeMap = typename // resort to default if not already set
        std::conditional<std::is_same<IsSet_ToInputNodeMap,
                                      std::true_type>::value,
                         typename Parent::ToInputNodeMap,
                         NullMap<DNode, Node>>::type;
      using ToInnerNodeMap = typename // resort to default if not already set
        std::conditional<std::is_same<IsSet_ToInnerNodeMap,
                                      std::true_type>::value,
                         typename Parent::ToInnerNodeMap,
                         typename Graph::template NodeMap<DNode>>::type;
      using ToInputEdgeMap = typename // resort to default if not already set
        std::conditional<std::is_same<IsSet_ToInputEdgeMap,
                                      std::true_type>::value,
                         typename Parent::ToInputEdgeMap,
                         NullMap<Arc, Edge>>::type;
      using ToInnerArcMap = typename // resort to default if not already set
        std::conditional<std::is_same<IsSet_ToInnerArcMap,
                                      std::true_type>::value,
                         typename Parent::ToInnerArcMap,
                         NullMap<Edge, Arc>>::type;

      static Digraph* createInnerDigraph()
      {
        LEMON_ASSERT(false, "Digraph is not initialized!");
        return nullptr;
      }

      // update Parent::createToInputNodeMap if ToInputNodeMap is not set
      template<typename T = IsSet_ToInputNodeMap>
      static typename std::enable_if<std::is_same<T, std::false_type>::value,
                                     ToInputNodeMap*>::type
      createToInputNodeMap(const Digraph&)
      {
        return new ToInputNodeMap; // the owner is UniSparse
      }
      // do nothing if already set
      template<typename T = IsSet_ToInputNodeMap>
      static typename std::enable_if<std::is_same<T, std::true_type>::value,
                                     ToInputNodeMap*>::type
      createToInputNodeMap(const Digraph&)
      {
        LEMON_ASSERT(false, "ToInputNodeMap is not initialized!");
        return nullptr;
      }

      // update Parent::createToInnerNodeMap if ToInnerNodeMap is not set
      template<typename T = IsSet_ToInnerNodeMap>
      static typename std::enable_if<std::is_same<T, std::false_type>::value,
                                     ToInnerNodeMap*>::type
      createToInnerNodeMap(const Graph& g)
      {
        return new ToInnerNodeMap(g, INVALID);
      }
      // do nothing if already set
      template<typename T = IsSet_ToInnerNodeMap>
      static typename std::enable_if<std::is_same<T, std::true_type>::value,
                                     ToInnerNodeMap*>::type
      createToInnerNodeMap(const Graph&)
      {
        LEMON_ASSERT(false, "ToInnerNodeMap is not initialized!");
        return nullptr;
      }

      // update Parent::createToInputEdgeMap if ToInputEdgeMap is not set
      template<typename T = IsSet_ToInputEdgeMap>
      static typename std::enable_if<std::is_same<T, std::false_type>::value,
                                     ToInputEdgeMap*>::type
      createToInputEdgeMap(const Digraph&)
      {
        return new ToInputEdgeMap;
      }
      // do nothing if already set
      template<typename T = IsSet_ToInputEdgeMap>
      static typename std::enable_if<std::is_same<T, std::true_type>::value,
                                     ToInputEdgeMap*>::type
      createToInputEdgeMap(const Digraph&)
      {
        LEMON_ASSERT(false, "ToInputEdgeMap is not initialized!");
        return nullptr;
      }

      // update Parent::createToInnerArcMap if ToInnerArcMap is not set
      template<typename T = IsSet_ToInnerArcMap>
      static typename std::enable_if<std::is_same<T, std::false_type>::value,
                                     ToInnerArcMap*>::type
      createToInnerArcMap(const Graph&)
      {
        return new ToInnerArcMap; // the owner is UniSparse
      }
      // do nothing if already set
      template<typename T = IsSet_ToInnerArcMap>
      static typename std::enable_if<std::is_same<T, std::true_type>::value,
                                     ToInnerArcMap*>::type
      createToInnerArcMap(const Graph&)
      {
        LEMON_ASSERT(false, "ToInnerArcMap is not initialized!");
        return nullptr;
      }

      SetInnerDigraph(const Parent& p, DGR& dg) : Parent(p)
      {
        Parent::_digraph = reinterpret_cast<void*>(&dg);
      }
    };

    /// \brief \ref named-templ-param "Named parameter" for setting
    /// the \c InnerDigraph.
    ///
    /// \ref named-templ-param "Named parameter" for setting the
    /// \c InnerDigraph.
    template<typename DGR>
    UniSparseWizard<US, SetInnerDigraph<DGR>> innerDigraph(const DGR& dg)
    {
      SetInnerDigraph<DGR> setInnerDigraph(*this, const_cast<DGR&>(dg));
      return UniSparseWizard<US, SetInnerDigraph<DGR>>(setInnerDigraph);
    }

    template<typename NM>
    struct SetToInputNodeMap : public Parent {
      using ToInputNodeMap = NM;
      using IsSet_ToInputNodeMap = std::true_type;

      static ToInputNodeMap* createToInputNodeMap(const Digraph&)
      {
        LEMON_ASSERT(false, "ToInputNodeMap is not initialized!");
        return nullptr;
      }

      SetToInputNodeMap(const Parent& p, NM& nm) : Parent(p)
      {
        Parent::_toInputNodeMap = reinterpret_cast<void*>(&nm);
      }
    };

    /// \brief \ref named-templ-param "Named parameter" for setting
    /// the \c ToInputNodeMap.
    ///
    /// \ref named-templ-param "Named parameter" function for setting the node
    /// map that converts the nodes of the inner digraph to the input graph.
    template<typename NM>
    UniSparseWizard<US, SetToInputNodeMap<NM>> toInputNodeMap(const NM& nm)
    {
      SetToInputNodeMap<NM> setToInputNodeMap(*this, const_cast<NM&>(nm));
      return UniSparseWizard<US, SetToInputNodeMap<NM>>(setToInputNodeMap);
    }

    template<typename NM>
    struct SetToInnerNodeMap : public Parent {
      using ToInnerNodeMap = NM;
      using IsSet_ToInnerNodeMap = std::true_type;

      static ToInnerNodeMap* createToInnerNodeMap(const Graph&)
      {
        LEMON_ASSERT(false, "ToInnerNodeMap is not initialized!");
        return nullptr;
      }

      SetToInnerNodeMap(const Parent& p, NM& nm) : Parent(p)
      {
        Parent::_toInnerNodeMap = reinterpret_cast<void*>(&nm);
      }
    };

    /// \brief \ref named-templ-param "Named parameter" for setting
    /// the \c ToInnerNodeMap.
    ///
    /// \ref named-templ-param "Named parameter" function for setting the node
    /// map that converts the nodes of the input graph to the inner digraph.
    template<typename NM>
    UniSparseWizard<US, SetToInnerNodeMap<NM>>
    toInnerNodeMap(const NM& nm)
    {
      SetToInnerNodeMap<NM> setToInnerNodeMap(*this, const_cast<NM&>(nm));
      return UniSparseWizard<US, SetToInnerNodeMap<NM>>(setToInnerNodeMap);
    }

    template<typename AM>
    struct SetToInputEdgeMap : public Parent {
      using ToInputEdgeMap = AM;
      using IsSet_ToInputEdgeMap = std::true_type;

      static ToInputEdgeMap* createToInputEdgeMap(const Digraph&)
      {
        LEMON_ASSERT(false, "ToInputEdgeMap is not initialized!");
        return nullptr;
      }

      SetToInputEdgeMap(const Parent& p, AM& am) : Parent(p)
      {
        Parent::_toInputEdgeMap = reinterpret_cast<void*>(&am);
      }
    };

    /// \brief \ref named-templ-param "Named parameter" for setting
    /// the \c ToInputEdgeMap.
    ///
    /// \ref named-templ-param "Named parameter" function for setting the arc
    /// map that converts the arcs of the inner digraph to the edges of the
    /// input graph.
    template<typename AM>
    UniSparseWizard<US, SetToInputEdgeMap<AM>>
    toInputEdgeMap(const AM& am)
    {
      SetToInputEdgeMap<AM> setToInputEdgeMap(*this, const_cast<AM&>(am));
      return UniSparseWizard<US, SetToInputEdgeMap<AM>>(setToInputEdgeMap);
    }

    template<typename EM>
    struct SetToInnerArcMap : public Parent {
      using ToInnerArcMap = EM;
      using IsSet_ToInnerArcMap = std::true_type;

      static ToInnerArcMap* createToInnerArcMap(const Graph&)
      {
        LEMON_ASSERT(false, "ToInnerArcMap is not initialized!");
        return nullptr;
      }

      SetToInnerArcMap(const Parent& p, EM& em) : Parent(p) {
        Parent::_toInnerArcMap = reinterpret_cast<void*>(&em);
      }
    };

    /// \brief \ref named-templ-param "Named parameter" for setting
    /// the \c ProcessingOrderContainer.
    ///
    /// \ref named-templ-param "Named parameter" function for setting the
    /// \c ProcessingOrderContainer in which the edges will be inserted and
    /// sorted by their weights.
    template<typename EM>
    UniSparseWizard<US, SetToInnerArcMap<EM>> toInnerArcMap(const EM& em)
    {
      SetToInnerArcMap<EM> setToInnerArcMap(*this, const_cast<EM&>(em));
      return UniSparseWizard<US, SetToInnerArcMap<EM>>(setToInnerArcMap);
    }

    template<typename POC>
    struct SetProcessingOrderContainer : public Parent {
      using ProcessingOrderContainer = POC;

      static ProcessingOrderContainer* createProcessingOrderContainer()
      {
        LEMON_ASSERT(false, "ProcessingOrderContainer is not initialized!");
        return nullptr;
      }

      SetProcessingOrderContainer(const Parent& p, POC& poc) : Parent(p) {
        Parent::_poc = reinterpret_cast<void*>(&poc);
      }
    };

    /// \brief \ref named-templ-param "Named parameter" for setting
    /// the \c ToInnerArcMap.
    ///
    /// \ref named-templ-param "Named parameter" function for setting the edge
    /// map that converts the edges of the input graph to the arcs of the inner
    /// digraph.
    template<typename POC>
    UniSparseWizard<US, SetProcessingOrderContainer<POC>>
    processingOrderContainer(const POC& poc)
    {
      SetProcessingOrderContainer<POC> setPOC(*this, const_cast<POC&>(poc));
      return UniSparseWizard<US, SetProcessingOrderContainer<POC>>(setPOC);
    }

    /// \brief \ref named-templ-param "Named parameter" for setting
    /// the sense of optimization to maximization.
    ///
    /// \ref named-templ-param "Named parameter" function for setting the sense
    /// of optimization to maximization. This is the default setting.
    UniSparseWizard<US, TR>& maximize()
    {
      _maximize = true;
      return *this;
    }

    /// \brief \ref named-templ-param "Named parameter" for setting
    /// the sense of optimization to minimization.
    ///
    /// \ref named-templ-param "Named parameter" function for setting
    /// the sense of optimization to minimization.
    UniSparseWizard<US, TR>& minimize()
    {
      _maximize = false;
      return *this;
    }

  private:
    template<typename USVariant>
    void setData(USVariant& us)
    {
      if(!_maximize) {
        us.minimize();
      }
      if(_digraph) {
        us.innerDigraph(*reinterpret_cast<Digraph*>(_digraph));
      }
      if(_toInputNodeMap) {
        us.toInputNodeMap(*reinterpret_cast<ToInputNodeMap*>(_toInputNodeMap));
      }
      if(_toInnerNodeMap) {
        us.toInnerNodeMap(*reinterpret_cast<ToInnerNodeMap*>(_toInnerNodeMap));
      }
      if(_toInputEdgeMap) {
        us.toInputEdgeMap(*reinterpret_cast<ToInputEdgeMap*>(_toInputEdgeMap));
      }
      if(_toInnerArcMap) {
        us.toInnerArcMap(*reinterpret_cast<ToInnerArcMap*>(_toInnerArcMap));
      }
      if(_poc) {
        us.processingOrderContainer(*reinterpret_cast<
                                    ProcessingOrderContainer*>(_poc));
      }
    }

  public:
    /// \brief Runs the \ref UniSparse or \ref UniSparseComp algorithm to find
    /// a(n optimal) largest \f$ (k,l) \f$-sparse subgraph.
    ///
    /// This function runs the \c UniSparse or \ref UniSparseComp algorithm to
    /// find a largest sparse subgraph or, if edge weights
    /// were given, a maximum- or minimum-weight largest sparse subgraph.
    ///
    /// \return \c true if the graph is \f$ (k,l) \f$-sparse.
    bool run()
    {
      if(_l <= _k) {
        typename US<Graph, WeightMap, Parent>
          ::SetLowerRange
          ::Create uss(_g, _k, _l, *_weights);
        setData(uss);
        return uss.run();
      }
      else {
        typename US<Graph, WeightMap, Parent>
          ::SetUpperRange
          ::Create uss(_g, _k, _l, *_weights);
        setData(uss);
        return uss.run();
      }
    }

    /// \brief Runs the \ref UniSparse or \ref UniSparseComp algorithm to check
    /// \f$ (k,l) \f$-sparsity.
    ///
    /// This function runs the \ref UniSparse or \ref UniSparseComp algorithm
    /// to check \f$ (k,l) \f$-sparsity. The algorithm will terminate as soon
    /// as an edge gets rejected.
    ///
    /// \return \c true if the graph is \f$ (k,l) \f$-sparse.
    bool checkSparse()
    {
      if(_l <= _k) {
        typename US<Graph, WeightMap, Parent>
          ::SetLowerRange
          ::Create uss(_g, _k, _l, *_weights);
        setData(uss);
        return uss.checkSparse();
      }
      else {
        typename US<Graph, WeightMap, Parent>
          ::SetUpperRange
          ::Create uss(_g, _k, _l, *_weights);
        setData(uss);
        return uss.checkSparse();
      }
    }

    /// \brief Runs the \ref UniSparse or \ref UniSparseComp algorithm to find
    /// the size of the largest \f$ (k,l) \f$-sparse subgraph.
    ///
    /// Runs the \ref UniSparse or \ref UniSparseComp algorithm to find the
    /// size of the largest \f$ (k,l) \f$-sparse subgraph.
    ///
    /// \return The size of the largest \f$ (k,l) \f$-sparse.
    int maxSparseSize()
    {
      if(_l <= _k) {
        typename US<Graph, WeightMap, Parent>
          ::SetLowerRange
          ::Create uss(_g, _k, _l, *_weights);
        setData(uss);
        uss.run();
        return uss.sparseSize();
      }
      else {
        typename US<Graph, WeightMap, Parent>
          ::SetUpperRange
          ::Create uss(_g, _k, _l, *_weights);
        setData(uss);
        uss.run();
        return uss.sparseSize();
      }
    }

    /// \brief Runs the \ref UniSparse or \ref UniSparseComp algorithm to find
    /// the maximum (or minimum) weight of a largest \f$ (k,l) \f$-sparse
    /// subgraph.
    ///
    /// Runs the \ref UniSparse or \ref UniSparseComp algorithm to find the
    /// maximum (or minimum) weight of a largest \f$ (k,l) \f$-sparse subgraph.
    /// By default, a maximum-weight solution is found. To change the sense of
    /// optimization, use \ref minimize().
    ///
    /// \return The maximum (or minimum) weight of the largest
    /// \f$ (k,l) \f$-sparse.
    typename WeightMap::Value optSparseWeight()
    {
      if(_l <= _k) {
        typename US<Graph, WeightMap, Parent>
          ::SetLowerRange
          ::Create uss(_g, _k, _l, *_weights);
        setData(uss);
        uss.run();
        return uss.sparseWeight();
      }
      else {
        typename US<Graph, WeightMap, Parent>
          ::SetUpperRange
          ::Create uss(_g, _k, _l, *_weights);
        setData(uss);
        uss.run();
        return uss.sparseWeight();
      }
    }
  };

  /// Function-type interface for UniSparse* classes.

  /// \brief Function-type interface for UniSparseSpec class.
  ///
  /// \param g The undirected graph the algorithm runs on.
  /// \param k The parameter \f$ k \f$ of \f$ (k,l) \f$-sparsity.
  /// \param l The parameter \f$ l \f$ of \f$ (k,l) \f$-sparsity.
  ///
  /// This function has several \ref named-func-param "named parameters",
  /// which are declared as the members of class \ref UniSparseSpecWizard.
  /// \warning Don't forget to put the \ref UniSparseSpecWizard::run() "run()",
  /// \ref UniSparseSpecWizard::checkSparse() "checkSparse()", or
  /// \ref UniSparseSpecWizard::maxSparseSize() "maxSparseSize()"
  /// function to the end of the parameter list.
  /// \sa UniSparseSpecWizard
  /// \sa UniSparseSpec
  template<typename GR>
  UniSparseSpecWizard<UniSparseSpecWizardBase<GR>>
  uniSparseSpec(const GR& g, const int k)
  {
    return UniSparseSpecWizard<UniSparseSpecWizardBase<GR>>(g, k);
  }

  /// \brief Function-type interface for UniSparse class.
  ///
  /// \param g The undirected graph the algorithm runs on.
  /// \param k The parameter \f$ k \f$ of \f$ (k,l) \f$-sparsity.
  /// \param l The parameter \f$ l \f$ of \f$ (k,l) \f$-sparsity.
  ///
  /// This function has several \ref named-func-param "named parameters",
  /// which are declared as the members of class \ref UniSparseWizard.
  /// \warning Don't forget to put the \ref UniSparseWizard::run() "run()",
  /// \ref UniSparseWizard::checkSparse() "checkSparse()", or
  /// \ref UniSparseWizard::maxSparseSize() "maxSparseSize()"
  /// function to the end of the parameter list.
  /// \sa UniSparseWizard
  /// \sa UniSparse
  template<typename GR>
  UniSparseWizard<UniSparse, UniSparseWizardBase<GR>>
  uniSparse(const GR& g, const int k, const int l)
  {
    return UniSparseWizard<UniSparse, UniSparseWizardBase<GR>>(g, k, l);
  }

  /// \brief Function-type interface for UniSparse class.
  ///
  /// \param g The undirected graph the algorithm runs on.
  /// \param k The parameter \f$ k \f$ of \f$ (k,l) \f$-sparsity.
  /// \param l The parameter \f$ l \f$ of \f$ (k,l) \f$-sparsity.
  /// \param w The edge map storing the weights.
  ///
  /// This function has several \ref named-func-param "named parameters",
  /// which are declared as the members of class \ref UniSparseWizard.
  /// \warning Don't forget to put the \ref UniSparseWizard::run() "run()",
  /// \ref UniSparseWizard::checkSparse() "checkSparse()",
  /// \ref UniSparseWizard::maxSparseSize() "maxSparseSize()", or
  /// \ref UniSparseWizard::optSparseWeight() "optSparseWeight()"
  /// function to the end of the parameter list.
  /// \sa UniSparseWizard
  /// \sa UniSparse
  template<typename GR, typename WM>
  UniSparseWizard<UniSparse, UniSparseWizardBase<GR, WM>>
  uniSparse(const GR& g, const int k, const int l, const WM& w)
  {
    return UniSparseWizard<UniSparse,
                           UniSparseWizardBase<GR, WM>> (g, k, l, w);
  }

  /// \brief Function-type interface for UniSparse class.
  ///
  /// \param g The undirected graph the algorithm runs on.
  /// \param k The parameter \f$ k \f$ of \f$ (k,l) \f$-sparsity.
  /// \param l The parameter \f$ l \f$ of \f$ (k,l) \f$-sparsity.
  ///
  /// This function has several \ref named-func-param "named parameters",
  /// which are declared as the members of class \ref UniSparseWizard.
  /// \warning Don't forget to put the \ref UniSparseWizard::run() "run()",
  /// \ref UniSparseWizard::checkSparse() "checkSparse()", or
  /// \ref UniSparseWizard::maxSparseSize() "maxSparseSize()"
  /// function to the end of the parameter list.
  /// \sa UniSparseWizard
  /// \sa UniSparseComp
  template<typename GR>
  UniSparseWizard<UniSparseComp, UniSparseWizardBase<GR>>
  uniSparseComp(const GR& g, const int k, const int l)
  {
    return UniSparseWizard<UniSparseComp, UniSparseWizardBase<GR>>(g, k, l);
  }

  /// \brief Function-type interface for UniSparse class.
  ///
  /// \param g The undirected graph the algorithm runs on.
  /// \param k The parameter \f$ k \f$ of \f$ (k,l) \f$-sparsity.
  /// \param l The parameter \f$ l \f$ of \f$ (k,l) \f$-sparsity.
  /// \param w The edge map storing the weights.
  ///
  /// This function has several \ref named-func-param "named parameters",
  /// which are declared as the members of class \ref UniSparseWizard.
  /// \warning Don't forget to put the \ref UniSparseWizard::run() "run()",
  /// \ref UniSparseWizard::checkSparse() "checkSparse()",
  /// \ref UniSparseWizard::maxSparseSize() "maxSparseSize()", or
  /// \ref UniSparseWizard::optSparseWeight() "optSparseWeight()"
  /// function to the end of the parameter list.
  /// \sa UniSparseWizard
  /// \sa UniSparseComp
  template<typename GR, typename WM>
  UniSparseWizard<UniSparseComp, UniSparseWizardBase<GR, WM>>
  uniSparseComp(const GR& g, const int k, const int l, const WM& w)
  {
    return UniSparseWizard<UniSparseComp,
                           UniSparseWizardBase<GR, WM>>(g, k, l, w);
  }

} // namespace lemon

#endif // LEMON_SPARSITY_H
