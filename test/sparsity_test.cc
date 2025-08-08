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

#include <lemon/arg_parser.h>
#include <lemon/connectivity.h>
#include <lemon/lgf_reader.h>
#include <lemon/lgf_writer.h>
#include <lemon/list_graph.h>
#include <lemon/maps.h>
#include <lemon/nauty_reader.h>
#include <lemon/smart_graph.h>
#include <lemon/sparsity.h>

#include <test/test_tools.h>

using namespace lemon;

template<class US>
bool isToInputNodeMapNullMap(const US& us)
{
  return std::is_same<typename std::remove_cv<typename std::remove_reference<
    decltype(us.toInputNodeMap())>::type>::type,
                      NullMap<typename US::Digraph::Node,
                              typename US::Graph::Node>>::value;
}

// checks functions of the given UniSparse instance
template<class US>
void checkUniSparseMinimalSpec(US& us, const US& const_us,
                               const typename US::Graph& g)
{
  int i = 0;
  bool b = false;
  typename US::Digraph::Arc a;
  typename US::Graph::Edge e = INVALID;
  typename US::Graph::Node n = INVALID;

  for(const auto& _e : g.edges()) {
    e = _e;
    break;
  }

  ignore_unused_variable_warning(i, b, e);

  us.init();

  b = const_us.isAllProcessed();
  b = const_us.isAllDone();
  if(!const_us.isAllDone()) {
    a = us.processNextEdge();
  }

  b = const_us.isSparse();
  b = const_us.isTight();

  if(e != INVALID) {
    b = us.isInduced(e);
  }
  i = const_us.sparseSize();

  e = us.nextEdge();
  e = us.previousEdge();

  if(isToInputNodeMapNullMap(us)) {
    return;
  }

  for(typename US::LastBlockingTightNodeIt blockIt(const_us);
      blockIt != INVALID; ++blockIt) {
    n = blockIt;
  }

  for(typename US::LastBlockingTightEdgeIt blockIt(const_us);
      blockIt != INVALID; ++blockIt) {
    e = blockIt;
  }

  for(const auto& node : const_us.nodesOfLastBlockingTight()) {
    n = node;
  }

  for(const auto& edge : const_us.edgesOfLastBlockingTight()) {
    e = edge;
  }
}

// checks functions of the given UniSparse instance
template<class US>
void checkUniSparseMinimal(US& us, const US& const_us,
                           const typename US::Graph& g)
{
  bool b = const_us.isSpanning();
  ignore_unused_variable_warning(b);
  checkUniSparseMinimalSpec(us, const_us, g);
}

// checks more functions of the given UniSparse instance
template<class US>
void checkUniSparse(US& us, const US& const_us,
                    const typename US::Graph& g)
{
  int i = 0;
  bool b = false;

  ignore_unused_variable_warning(i, b);

  checkUniSparseMinimal(us, const_us, g);

  b = const_us.weightedCase();

  i = const_us.sparseWeight();
}

char test_lgf[] =
  "@nodes\n"
  "label\n"
  "0\n"
  "1\n"
  "2\n"
  "3\n"
  "4\n"
  "5\n"
  "@edges\n"
  "                label   weights\n"
  "0       1       0       14\n"
  "1       2       1       58\n"
  "2       3       2       71\n"
  "3       5       3       49\n"
  "0       4       4       72\n"
  "0       4       5       30\n"
  "5       2       6       7\n";

char test_simple_lgf[] =
  "@nodes\n"
  "label\n"
  "0\n"
  "1\n"
  "2\n"
  "3\n"
  "4\n"
  "5\n"
  "@edges\n"
  "                label\n"
  "0       1       0\n"
  "1       2       1\n"
  "2       3       2\n"
  "3       5       3\n"
  "0       4       4\n"
  "5       2       5\n";

class CompileCheck {
  using Graph = concepts::Graph;
  using Edge = Graph::Edge;
  using Node = Graph::Node;

public:
  void checkUniSparseCompile()
  {
    Graph g;
    int k = 2, l = 3;

    int i;
    bool b;
    Edge e;
    Node n;

    ignore_unused_variable_warning(k, l, i, b, e);

    // UniSparse
    {
      typedef UniSparse<Graph> US;

      US us(g, k, l);
      const US& const_us = us;

      checkUniSparse(us, const_us, g);
    }

    // UniSparseComp
    {
      typedef UniSparseComp<Graph> US;

      US us(g, k, l);
      const US& const_us = us;

      checkUniSparse(us, const_us, g);
    }

    // UniSparseSpec (l = 2k)
    {
      typedef UniSparseSpec<Graph> USC;

      USC us(g, k);
      const USC& const_us = us;

      checkUniSparseMinimalSpec(us, const_us, g);
    }
  }

  void checkUniSparseTemplateCompile()
  {
    class InnerDigraph : public concepts::Digraph {
    public:
      Node addNode()
      {
        return INVALID;
      }

      Arc addArc(Node, Node)
      {
        return INVALID;
      }

      void reverseArc(Arc)
      {}

      void clear()
      {}
    };

    typedef InnerDigraph Digraph;
    typedef Digraph::Node DNode;
    typedef Digraph::Arc Arc;
    typedef concepts::ReadMap<Edge, int> WeightMap;
    // typedef std::vector<Edge> ProcessingOrderContainer;
    typedef std::deque<Edge> ProcessingOrderContainer;
    typedef concepts::ReadWriteMap<Edge, bool> IndMap;
    typedef concepts::ReadWriteMap<DNode, Node> ToInputNodeMap;
    typedef concepts::ReadWriteMap<Node, DNode> ToInnerNodeMap;
    typedef concepts::ReadWriteMap<Arc, Edge> ToInputEdgeMap;
    typedef concepts::ReadWriteMap<Edge, Arc> ToInnerArcMap;

    Digraph digraph;
    WeightMap weightMap;
    ProcessingOrderContainer processingOrderContainer;
    IndMap indMap;
    ToInputNodeMap toInputNodeMap;
    ToInnerNodeMap toInnerNodeMap;
    ToInputEdgeMap toInputEdgeMap;
    ToInnerArcMap toInnerArcMap;

    Graph g;
    int k = 2, l = 1;

    int i;
    bool b;
    Edge e;
    Node n;

    ignore_unused_variable_warning(i, b, e);

    // UniSparse
    {
      {
        typedef typename UniSparse<Graph, WeightMap>
          ::template SetInnerDigraph<Digraph>
          ::template SetProcessingOrderContainer<ProcessingOrderContainer>
          ::template SetToInputNodeMap<ToInputNodeMap>
          ::template SetToInnerNodeMap<ToInnerNodeMap>
          ::template SetToInputEdgeMap<ToInputEdgeMap>
          ::template SetToInnerArcMap<ToInnerArcMap>
          ::Create US;

        US us(g, k, l, weightMap);
        const US& const_us = us;

        b = us
          .innerDigraph(digraph)
          .processingOrderContainer(processingOrderContainer)
          .toInputNodeMap(toInputNodeMap)
          .toInnerNodeMap(toInnerNodeMap)
          .toInputEdgeMap(toInputEdgeMap)
          .toInnerArcMap(toInnerArcMap)
          .run();

        checkUniSparse(us, const_us, g);
      }

      {
        typedef typename UniSparse<Graph, WeightMap>
          ::template SetProcessingOrderContainer<ProcessingOrderContainer>
          ::template SetToInputNodeMap<ToInputNodeMap>
          ::template SetToInnerNodeMap<ToInnerNodeMap>
          ::template SetToInputEdgeMap<ToInputEdgeMap>
          ::template SetToInnerArcMap<ToInnerArcMap>
          ::template SetInnerDigraph<Digraph> // !
          ::Create US;

        US us(g, k, l, weightMap);
        const US& const_us = us;

        b = us
          .processingOrderContainer(processingOrderContainer)
          .toInputNodeMap(toInputNodeMap)
          .toInnerNodeMap(toInnerNodeMap)
          .innerDigraph(digraph)
          .toInputEdgeMap(toInputEdgeMap)
          .toInnerArcMap(toInnerArcMap)
          .run();

        checkUniSparse(us, const_us, g);
      }

      b = uniSparse(g, k, l, weightMap)
        .innerDigraph(digraph)
        .minimize()
        .maximize()
        .processingOrderContainer(processingOrderContainer)
        .toInputNodeMap(toInputNodeMap)
        .toInnerNodeMap(toInnerNodeMap)
        .toInputEdgeMap(toInputEdgeMap)
        .toInnerArcMap(toInnerArcMap)
        .run();

      b = uniSparse(g, k, l, weightMap)
        .processingOrderContainer(processingOrderContainer)
        .maximize()
        .minimize()
        .toInputNodeMap(toInputNodeMap)
        .toInnerNodeMap(toInnerNodeMap)
        .toInputEdgeMap(toInputEdgeMap)
        .toInnerArcMap(toInnerArcMap)
        .innerDigraph(digraph)
        .run();

      b = uniSparse(g, k, l)
        .innerDigraph(digraph)
        .minimize()
        .maximize()
        .processingOrderContainer(processingOrderContainer)
        .toInputNodeMap(toInputNodeMap)
        .toInnerNodeMap(toInnerNodeMap)
        .toInputEdgeMap(toInputEdgeMap)
        .toInnerArcMap(toInnerArcMap)
        .run();

      b = uniSparse(g, k, l)
        .processingOrderContainer(processingOrderContainer)
        .maximize()
        .minimize()
        .toInputNodeMap(toInputNodeMap)
        .toInnerNodeMap(toInnerNodeMap)
        .toInputEdgeMap(toInputEdgeMap)
        .toInnerArcMap(toInnerArcMap)
        .innerDigraph(digraph)
        .run();
    }

    // UniSparseComp
    {
      {
        typedef
          typename UniSparseComp<Graph, WeightMap>
          ::template SetInnerDigraph<Digraph>
          ::template SetProcessingOrderContainer<ProcessingOrderContainer>
          ::template SetToInputNodeMap<ToInputNodeMap>
          ::template SetToInnerNodeMap<ToInnerNodeMap>
          ::template SetToInputEdgeMap<ToInputEdgeMap>
          ::template SetToInnerArcMap<ToInnerArcMap>
          ::Create USC;

        USC us(g, k, l, weightMap);
        const USC& const_us = us;
        checkUniSparse(us, const_us, g);

        b = us
          .innerDigraph(digraph)
          .processingOrderContainer(processingOrderContainer)
          .toInputNodeMap(toInputNodeMap)
          .toInnerNodeMap(toInnerNodeMap)
          .toInputEdgeMap(toInputEdgeMap)
          .toInnerArcMap(toInnerArcMap)
          .run();
      }

      {
        typedef
          typename UniSparseComp<Graph, WeightMap>
          ::template SetProcessingOrderContainer<ProcessingOrderContainer>
          ::template SetToInputNodeMap<ToInputNodeMap>
          ::template SetToInnerNodeMap<ToInnerNodeMap>
          ::template SetToInputEdgeMap<ToInputEdgeMap>
          ::template SetToInnerArcMap<ToInnerArcMap>
          ::template SetInnerDigraph<Digraph>
          ::Create USC;

        USC us(g, k, l, weightMap);
        const USC& const_us = us;
        checkUniSparse(us, const_us, g);

        b = us
          .innerDigraph(digraph)
          .processingOrderContainer(processingOrderContainer)
          .toInputNodeMap(toInputNodeMap)
          .toInnerNodeMap(toInnerNodeMap)
          .toInputEdgeMap(toInputEdgeMap)
          .toInnerArcMap(toInnerArcMap)
          .run();
      }

      b = uniSparseComp(g, k, l)
        .innerDigraph(digraph)
        .minimize()
        .maximize()
        .processingOrderContainer(processingOrderContainer)
        .toInputNodeMap(toInputNodeMap)
        .toInnerNodeMap(toInnerNodeMap)
        .toInputEdgeMap(toInputEdgeMap)
        .toInnerArcMap(toInnerArcMap)
        .run();

      b = uniSparseComp(g, k, l)
        .processingOrderContainer(processingOrderContainer)
        .maximize()
        .minimize()
        .toInputNodeMap(toInputNodeMap)
        .toInnerNodeMap(toInnerNodeMap)
        .toInputEdgeMap(toInputEdgeMap)
        .toInnerArcMap(toInnerArcMap)
        .innerDigraph(digraph)
        .run();
    }

    // UniSparseSpec (l = 2k)
    {
      typedef typename UniSparseSpec<Graph>
        ::template SetInnerDigraph<Digraph>
        ::template SetToInputNodeMap<ToInputNodeMap>
        ::template SetToInnerNodeMap<ToInnerNodeMap>
        ::template SetToInputEdgeMap<ToInputEdgeMap>
        ::template SetToInnerArcMap<ToInnerArcMap>
        ::Create USS;

      USS us(g, k);
      const USS& const_us = us;

      us
        .innerDigraph(digraph)
        .toInputNodeMap(toInputNodeMap)
        .toInnerNodeMap(toInnerNodeMap)
        .toInputEdgeMap(toInputEdgeMap)
        .toInnerArcMap(toInnerArcMap)
        .run();

      checkUniSparseMinimalSpec(us, const_us, g);

      b = uniSparseSpec(g, k)
        .innerDigraph(digraph)
        .toInputNodeMap(toInputNodeMap)
        .toInnerNodeMap(toInnerNodeMap)
        .toInputEdgeMap(toInputEdgeMap)
        .toInnerArcMap(toInnerArcMap)
        .run();

      b = uniSparseSpec(g, k)
        .toInputNodeMap(toInputNodeMap)
        .toInnerNodeMap(toInnerNodeMap)
        .toInputEdgeMap(toInputEdgeMap)
        .toInnerArcMap(toInnerArcMap)
        .innerDigraph(digraph)
        .run();
    }
  }

};


template<class US, class Weight = int>
void checkAllWeighted(US& us, bool isSparse, int maxSparse, Weight optWeight,
                      const std::string msg)
{
  check(isSparse == us.checkSparse(),
        "CheckSparse without heuristic failed for " + msg);

  check(isSparse == us.run(),
        "CheckSparse without heuristic failed for " + msg);
  check(maxSparse == us.sparseSize(),
        "Maximal sparse size failed after run without heuristic for " + msg);

  check(isSparse == us.run(),
        "CheckSparse without heuristic failed for " + msg);
  check(maxSparse == us.sparseSize(),
        "Maximal sparse size failed after run without heuristic for " + msg);
  check(optWeight == us.sparseWeight(),
        "Maximal sparse weight failed after run without heuristic for " + msg);
}


template<class US, class Heur, class Weight = int>
void checkAllUnweighted(US& us, const std::vector<Heur>& heuristics,
                        bool isSparse, int maxSparse, Weight optWeight,
                        const std::string msg)
{
  for(const auto& h : heuristics) {
    check(isSparse == us.checkSparse(h),
          "CheckSparse with heuristic failed for " + msg);
  }

  for(const auto& h : heuristics) {
    check(isSparse == us.run(h),
          "CheckSparse with heuristic failed for " + msg);
    check(maxSparse == us.sparseSize(),
          "Maximal sparse size failed after run without heuristic for "
          + msg);
  }

  check(isSparse == us.run(),
        "CheckSparse without heuristic failed for " + msg);
  check(maxSparse == us.sparseSize(),
        "Maximal sparse size failed after run without heuristic for " + msg);
  check(optWeight == us.sparseWeight(),
        "Maximal sparse weight failed after run without heuristic for " + msg);
}


template<typename Graph>
class CorrectnessCheck {
  using Node = typename Graph::Node;
  using Edge = typename Graph::Edge;
  using Weight = double;
  using WeightMap = typename Graph::template EdgeMap<Weight>;

  using US = UniSparse<Graph>;
  using USW = UniSparse<Graph, WeightMap>;
  using USC = UniSparseComp<Graph>;
  using USCW = UniSparseComp<Graph, WeightMap>;
  const std::vector<typename US::Heuristic> heursUS = {US::AUTO, US::BASIC,
    US::TRANSP, US::TRANSP_MEM, US::TRANSP_ONE_OUT, US::TRANSP_ONE_OUT_MEM,
    US::FORESTS_BFS, US::FORESTS_DFS, US::PFORESTS_BFS, US::PFORESTS_DFS,
    US::NODE_BASIC, US::NODE_DEG_MIN, US::NODE_PROC_MIN, US::NODE_OUT_DEG_MIN};
  const std::vector<typename USW::Heuristic> heursUSW = {US::AUTO, USW::BASIC};
  const std::vector<typename USC::Heuristic> heursUSC = {USC::AUTO,
    USC::NODE_BASIC, USC::NODE_DEG_MIN, USC::NODE_PROC_MIN,
    USC::NODE_OUT_DEG_MIN};
  const std::vector<typename USCW::Heuristic> heursUSCW = {USCW::AUTO,
    USCW::NODE_BASIC};

  Graph g, simple_g;
  WeightMap weightMap;

  const int maxK = 5;

  const std::vector<std::vector<bool>> isSparse{
    {false, false, false},
    {true, true, true, false, false},
    {true, true, true, true, true, false, true},
    {true, true, true, true, true, true, true, false, true},
    {true, true, true, true, true, true, true, true, true, false, true}};

  const std::vector<std::vector<int>> maxSparse{
    {6, 5, 2},
    {7, 7, 7, 6, 5},
    {7, 7, 7, 7, 7, 6, 6},
    {7, 7, 7, 7, 7, 7, 7, 6, 6},
    {7, 7, 7, 7, 7, 7, 7, 7, 7, 6, 6}};

  const std::vector<std::vector<Weight>> maxWeight{
    {294, 264},
    {301, 301, 301, 271},
    {301, 301, 301, 301, 301, 271},
    {301, 301, 301, 301, 301, 301, 301, 271},
    {301, 301, 301, 301, 301, 301, 301, 301, 301, 271}};

  const std::vector<std::vector<Weight>> minWeight{
    {229, 158},
    {301, 301, 301, 229},
    {301, 301, 301, 301, 301, 229},
    {301, 301, 301, 301, 301, 301, 301, 229},
    {301, 301, 301, 301, 301, 301, 301, 301, 301, 229}};

public:
  CorrectnessCheck(): g(), simple_g(), weightMap(g)
  {
    std::istringstream input(test_lgf);
    std::istringstream simple_input(test_simple_lgf);
    graphReader(g, input).edgeMap("weights", weightMap).run();
    graphReader(simple_g, simple_input).run();
  }

public:
  void run()
  {
    for(int k = 1; k <= maxK; ++k) {
      for(int l = 0; l < 2 * k; ++l) {
        const auto& _isSparse = isSparse[k - 1][l];
        const auto& _maxSparse = maxSparse[k - 1][l];
        const auto& _maxWeight = maxWeight[k - 1][l];
        const auto& _minWeight = minWeight[k - 1][l];
        // UniSparse unweighted
        {
          US us(g, k, l);
          checkAllUnweighted(us, heursUS, _isSparse, _maxSparse, 0,
                             "UniSparse");
        }
        // UniSparseComp unweighted
        {
          USC usc(g, k, l);
          checkAllUnweighted(usc, heursUSC, _isSparse, _maxSparse, 0,
                             "UniSparseComp");
        }
        // UniSparse weighted
        {
          USW us(g, k, l, weightMap);
          // max weighted case
          checkAllWeighted(us, _isSparse, _maxSparse, _maxWeight, "UniSparse");
          // min weighted case
          us.minimize();
          checkAllWeighted(us, _isSparse, _maxSparse, _minWeight, "UniSparse");
        }
        // UniSparseComp weighted
        {
          USCW usc(g, k, l, weightMap);
          // max weighted case
          checkAllWeighted(usc, _isSparse, _maxSparse, _maxWeight,
                           "UniSparseComp");
          // min weighted case
          usc.minimize();
          checkAllWeighted(usc, _isSparse, _maxSparse, _minWeight,
                           "UniSparseComp");
        }
        // Wizards
        {
          check(uniSparse(g, k, l, weightMap).run() == _isSparse,
                "Wizard failed!");
          check(uniSparse(g, k, l, weightMap).checkSparse() == _isSparse,
                "Wizard failed!");
          check(uniSparse(g, k, l, weightMap).maxSparseSize() == _maxSparse,
                "Wizard failed!");
          check(uniSparse(g, k, l, weightMap).optSparseWeight() == _maxWeight,
                "Wizard failed!");
          check(uniSparse(g, k, l, weightMap).minimize().optSparseWeight()
                == _minWeight, "Wizard failed!");
          check(uniSparseComp(g, k, l, weightMap).run() == _isSparse,
                "Wizard failed!");
          check(uniSparseComp(g, k, l, weightMap).checkSparse() == _isSparse,
                "Wizard failed!");
          check(uniSparseComp(g, k, l, weightMap).maxSparseSize() == _maxSparse,
                "Wizard failed!");
          check(uniSparseComp(g, k, l, weightMap).optSparseWeight()
                == _maxWeight, "Wizard failed!");
          check(uniSparseComp(g, k, l, weightMap).minimize().optSparseWeight()
                == _minWeight, "Wizard failed!");
        }
        // Wizards with Orienter
        {
          typedef Orienter<SmartGraph> OriDG;
          SmartGraph toOrient;
          SmartGraph::EdgeMap<bool> edgeDirectionMap(toOrient, false);
          OriDG dg2(toOrient, edgeDirectionMap);
          check(uniSparse(g, k, l, weightMap)
                .innerDigraph(dg2)
                .run()
                == _isSparse, "Wizard failed!");
          check(uniSparse(g, k, l, weightMap)
                .innerDigraph(dg2)
                .checkSparse()
                == _isSparse, "Wizard failed!");
          check(uniSparse(g, k, l, weightMap)
                .innerDigraph(dg2)
                .maxSparseSize()
                == _maxSparse, "Wizard failed!");
          check(uniSparse(g, k, l, weightMap)
                .innerDigraph(dg2)
                .optSparseWeight()
                == _maxWeight, "Wizard failed!");
          check(uniSparse(g, k, l, weightMap)
                .minimize()
                .innerDigraph(dg2)
                .optSparseWeight()
                == _minWeight, "Wizard failed!");
          check(uniSparseComp(g, k, l, weightMap)
                .innerDigraph(dg2)
                .run()
                == _isSparse, "Wizard failed!");
          check(uniSparseComp(g, k, l, weightMap)
                .innerDigraph(dg2)
                .checkSparse()
                == _isSparse, "Wizard failed!");
          check(uniSparseComp(g, k, l, weightMap)
                .innerDigraph(dg2)
                .maxSparseSize()
                == _maxSparse, "Wizard failed!");
          check(uniSparseComp(g, k, l, weightMap)
                .innerDigraph(dg2)
                .optSparseWeight()
                == _maxWeight, "Wizard failed!");
          check(uniSparseComp(g, k, l, weightMap)
                .minimize()
                .innerDigraph(dg2)
                .optSparseWeight()
                == _minWeight, "Wizard failed!");
        }
        // iterators
        UniSparse<Graph> us(g, k, l);
        checkUniSparseBlockingIterators<UniSparse<Graph>>(us, g, k, l);
        UniSparseComp<Graph> usc(g, k, l);
        checkUniSparseBlockingIterators<UniSparseComp<Graph>>(usc, g, k, l);
        checkUniSparseCompIterators();
      }
      // UniSparseSpec
      UniSparseSpec<Graph> us(simple_g, k);
      check(isSparse[k - 1][2 * k] == us.checkSparse(),
            "CheckSparse failed for UniSparseSpec");
      check(isSparse[k - 1][2 * k] == us.run(),
            "Run failed for sparse for UniSparseSpec");
      check(maxSparse[k - 1][2 * k] == us.sparseSize(),
            "MaxSparse failed for UniSparseSpec");
      UniSparseSpec<Graph> uss(simple_g, k);
      checkUniSparseBlockingIterators<UniSparseSpec<Graph>>(uss, simple_g,
                                                            k, -1);
    }
  }

private:
  void checkUniSparseCompIterators()
  {
    typedef UniSparseComp<Graph> USC;

    for(int k = 1; k <= maxK; ++k) {
      for(int l = 0; l < 2 * k; ++l) {
        USC usc(g, k, l);
        usc.run();
        for(typename USC::CompIt c(usc); c != INVALID; ++c) {
          std::vector<Node> compNodes;
          for(const auto& n : c.nodes()) {
            compNodes.push_back(n);
          }
          std::vector<Node> compNodes2;
          for(typename USC::CompNodeIt n(c); n != INVALID; ++n) {
            compNodes2.push_back(n);
          }
          check(compNodes == compNodes2, "Bad CompNodeIt!");

          std::vector<Edge> compEdges;
          for(const auto& e : c.edges()) {
            compEdges.push_back(e);
          }
          std::vector<Edge> compEdges2;
          for(typename USC::CompEdgeIt e(c); e != INVALID; ++e) {
            compEdges2.push_back(e);
          }
          check(compEdges == compEdges2, "Bad CompEdgeIt!");

          Graph compGraph;
          typename Graph::template NodeMap<Node> toCompNode(g, INVALID);
          for(const auto& n : c.nodes()) {
            toCompNode[n] = compGraph.addNode();
          }
          for(const auto& e : c.edges()) {
            compGraph.addEdge(toCompNode[g.u(e)], toCompNode[g.v(e)]);
          }
          UniSparse<Graph> us(compGraph, k, l);
          us.run();
          check(us.isTight(), "Comp is not tight!");
        }
      }
    }
  }

  template<class US>
  void checkUniSparseBlockingIterators(US& us, const Graph& g, const int k,
                                       const int l)
  {
    us.init();
    while(!us.isAllDone()) {
      if(us.processNextEdge() == INVALID) {
        std::vector<Node> blockingNodes;
        for(typename US::LastBlockingTightNodeIt n(us); n != INVALID; ++n) {
          blockingNodes.push_back(n);
        }
        std::vector<Node> blockingNodes2;
        for(const auto& n : us.nodesOfLastBlockingTight()) {
          blockingNodes2.push_back(n);
        }
        check(blockingNodes == blockingNodes2 , "Bad LastBlockingTightNodeIt");

        std::vector<Edge> blockEdges;
        for(const auto& e : us.edgesOfLastBlockingTight()) {
          blockEdges.push_back(e);
        }
        std::vector<Edge> blockEdges2;
        for(typename US::LastBlockingTightEdgeIt e(us); e != INVALID; ++e) {
          blockEdges2.push_back(e);
        }
        check(blockEdges == blockEdges2, "Bad LastBlockingTightEdgeIt!");

        Graph blockCopy;
        typename Graph::template NodeMap<Node> toBlockNode(g, INVALID);
        for(typename US::LastBlockingTightNodeIt n(us); n != INVALID; ++n) {
          toBlockNode[n] = blockCopy.addNode();
        }
        for(const auto& e : us.edgesOfLastBlockingTight()) {
          const auto u = toBlockNode[g.u(e)], v = toBlockNode[g.v(e)];
          check(u != INVALID && v != INVALID,
                "Endpoint of a blocking edge is not in the blocking "
                "subgraph");
          blockCopy.addEdge(u, v);
        }
        if(l == -1) {
          UniSparseSpec<Graph> blockChecker(blockCopy, k);
          blockChecker.run();
          check(blockChecker.isTight(), "Blocking graph is not tight!");
        }
        else {
          UniSparseComp<Graph> blockChecker(blockCopy, k, l);
          blockChecker.run();
          check(blockChecker.isTight(), "Blocking graph is not tight!");
        }
      }
    }
  }
};

int main()
{
  CorrectnessCheck<ListGraph> c;
  c.run();
  CorrectnessCheck<SmartGraph> c2;
  c2.run();
  return 0;
}
