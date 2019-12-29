#include <iostream>
#include <stdexcept>
#include <cassert>
#include <limits.h>
#include <optional>
#include <type_traits>
#include <vector>
#include <queue>


namespace NFlow{

typedef unsigned int TVertex;
typedef unsigned int TVertexCount;
typedef unsigned int TEdgeNum;


template<typename TFlow>
class TNetwork {
private:
    struct TEdge_;

public:
    class TEdgeIterator {
        friend class TNetwork;

    public:
        TFlow getFlow() const {
            return getEdge_().flow;
        }

        TFlow getCapacity() const {
            return getEdge_().capacity;
        }

        TFlow getResudialCapacity() const {
            return getCapacity() - getFlow();
        }

        TVertex getFinish() const {
            return getEdge_().finish;
        }

        void pushFlow(TFlow flow_value) {
            const auto edge_num = network_->graph_[vertex_][edge_num_];
            auto& edges_ = network_->edges_;
            if (edges_[edge_num].flow + flow_value > edges_[edge_num].capacity) {
                throw std::logic_error("Edge's flow is bigger than capacity");
            }
            edges_[edge_num].flow     += flow_value;
            edges_[edge_num ^ 1].flow -= flow_value;
        }

        TEdgeIterator& operator++() {
            if (edge_num_ < network_->graph_[vertex_].size()) {
                ++edge_num_;
            }
            return *this;
        }

        bool isEnd() const {
            return edge_num_ == network_->graph_[vertex_].size();
        }

    private:
        typedef unsigned int TEdgeNum_;

        TNetwork* network_;
        TVertex   vertex_;
        TEdgeNum_ edge_num_;

        TEdgeIterator(TNetwork* network, TVertex vertex) :
                network_(network),
                vertex_(vertex),
                edge_num_(0)
        {}

        const TEdge_& getEdge_() const {
            if (isEnd()) {
                throw std::out_of_range("Iterator out of range");
            }
            const auto edge_num = network_->graph_[vertex_][edge_num_];
            return network_->edges_[edge_num];
        }
    };

    TNetwork(TVertexCount vertex_count, TVertex source, TVertex sink) :
            vertex_count_(vertex_count),
            source_(source),
            sink_(sink)
    {
        if (source >= vertex_count || sink >= vertex_count) {
            throw std::out_of_range("Source or sink index is too large");
        }
        if (source == sink) {
            throw std::logic_error("Source and sink are the same");
        }
        graph_.resize(vertex_count);
    }

    void addEdge(TVertex start, TVertex finish, TFlow capacity) {
        // add forward edge
        addEdge_(start, finish, capacity);
        // add backward edge
        addEdge_(finish, start, /* capacity = */ 0);
    }

    TEdgeIterator getEdgeIterator(TVertex vertex) {
        return TEdgeIterator(this, vertex);
    }

    TVertexCount getVertexCount() const {
        return vertex_count_;
    }

    TVertex getSource() const {
        return source_;
    }

    TVertex getSink() const {
        return sink_;
    }

    TFlow getFlowValue() const {
        TFlow flow = 0;
        for (auto edge_num : graph_[source_]) {
            const auto& edge = edges_[edge_num];
            flow += edge.flow;
        }
        return flow;
    }

private:
    struct TEdge_ {
        TVertex finish;
        TFlow   flow;
        TFlow   capacity;

        TEdge_(TVertex finish, TFlow flow, TFlow capacity) :
                finish(finish),
                flow(flow),
                capacity(capacity)
        {}
    };

    std::vector< std::vector<TEdgeNum> > graph_;
    std::vector<TEdge_> edges_;
    TVertex vertex_count_;
    TVertex source_;
    TVertex sink_;

    void addEdge_(TVertex start, TVertex finish, TFlow capacity) {
        graph_[start].push_back(edges_.size());
        edges_.emplace_back(finish, /* flow = */ 0, capacity);
    }
};


template<typename TFlow>
class TFlowAlgo {
public:
    virtual void findMaxFlow(TNetwork<TFlow>& network) = 0;
    virtual ~TFlowAlgo()
    {}

protected:
    TNetwork<TFlow>* network_;
};


template<typename TFlow>
class TBlockingFlow : public TFlowAlgo<TFlow> {
public:
    void findMaxFlow(TNetwork<TFlow>& network) override {
        network_ = &network;
        init_();
        while (bfs_()) {
            runAlgo_();
        }
        free_();
    }

    virtual ~TBlockingFlow()
    {}

protected:
    typedef unsigned int TDist_;

    static constexpr auto INF_ = std::numeric_limits<TDist_>::max();

    using TFlowAlgo<TFlow>::network_;

    std::vector<TDist_> distance_;

    virtual void init_()    = 0;
    virtual void runAlgo_() = 0;
    virtual void free_()    = 0;

    bool bfs_() {
        const auto vertex_count = network_->getVertexCount();
        const auto source       = network_->getSource();
        const auto sink         = network_->getSink();

        distance_.assign(vertex_count, INF_);
        distance_[source] = 0;

        std::queue<TVertex> queue;
        queue.push(source);

        while (!queue.empty()) {
            const auto cur_vertex = queue.front();
            queue.pop();
            for (auto it = network_->getEdgeIterator(cur_vertex); !it.isEnd(); ++it) {
                const auto cur_finish = it.getFinish();
                if (it.getResudialCapacity() > 0){
                    if (distance_[cur_finish] == INF_) {
                        distance_[cur_finish] = distance_[cur_vertex] + 1;
                        queue.push(cur_finish);
                    }
                }
            }
        }

        return distance_[sink] != INF_;
    }
};


template<typename TFlow>
class TMalhotra : public TBlockingFlow<TFlow> {
public:
    virtual ~TMalhotra()
    {}

private:
    typedef typename TNetwork<TFlow>::TEdgeIterator TEdgeIterator_;
    typedef std::make_unsigned_t<TFlow> TPotential_;
    typedef unsigned int                TDist_;

    using TBlockingFlow<TFlow>::network_;
    using TBlockingFlow<TFlow>::distance_;
    using TBlockingFlow<TFlow>::INF_;

    struct TEdge_ {
        TVertex        finish;
        TEdgeIterator_ network_edge;
        TEdge_(TVertex finish, TEdgeIterator_ network_edge) :
            finish(finish),
            network_edge(network_edge)
        {}
    };

    enum EDirection_ {
        FORWARD,
        BACKWARD
    };

    std::vector<TPotential_>           incoming_potential_;
    std::vector<TPotential_>           outcoming_potential_;
    std::vector<bool>                  is_available_;
    std::vector< std::vector<TEdge_> > graph_;
    std::vector< std::vector<TEdge_> > reversed_graph_;

    void init_() override {
        const auto vertex_count = network_->getVertexCount();
        incoming_potential_ .resize(vertex_count);
        outcoming_potential_.resize(vertex_count);
        is_available_       .resize(vertex_count);
        graph_              .resize(vertex_count);
        reversed_graph_     .resize(vertex_count);
    }

    void free_() override {
        incoming_potential_ .clear();
        outcoming_potential_.clear();
        is_available_       .clear();
        graph_              .clear();
        reversed_graph_     .clear();
        distance_           .clear();
    }

    TPotential_ getPotential_(TVertex vertex) const {
        if (vertex == network_->getSource()) {
            return outcoming_potential_[vertex];
        }
        if (vertex == network_->getSink()) {
            return incoming_potential_[vertex];
        }
        return std::min(incoming_potential_[vertex], outcoming_potential_[vertex]);
    }

    TVertex getMinPotentialVertex_() const {
        TVertex min_potential_vertex = network_->getSource();
        for (TVertexCount vertex = 0; vertex < network_->getVertexCount(); ++vertex) {
            if (is_available_[vertex] && getPotential_(vertex) < getPotential_(min_potential_vertex)) {
                min_potential_vertex = vertex;
            }
        }
        return min_potential_vertex;
    }

    void removeZeroPotentialVertex_(TVertex vertex) {
        is_available_[vertex] = false;
        for (const auto& edge : graph_[vertex]) {
            incoming_potential_[edge.finish] -= edge.network_edge.getResudialCapacity();
        }
        for (const auto& edge : reversed_graph_[vertex]) {
            outcoming_potential_[edge.finish] -= edge.network_edge.getResudialCapacity();
        }
    }

    void runAlgo_() override {
        buildGraph_();
        calcPotential_();
        const auto source = network_->getSource();
        const auto sink   = network_->getSink();
        while (std::min(getPotential_(source), getPotential_(sink)) > 0) {
            const auto min_potential_vertex = getMinPotentialVertex_();
            if (getPotential_(min_potential_vertex) == 0) {
                removeZeroPotentialVertex_(min_potential_vertex);
            } else {
                pushFlow_(min_potential_vertex);
            }
        }
    }

    void buildGraph_() {
        const auto vertex_count = network_->getVertexCount();

        for (TVertexCount vertex = 0; vertex < vertex_count; ++vertex) {
            graph_[vertex].clear();
            reversed_graph_[vertex].clear();
            is_available_[vertex] = distance_[vertex] != INF_;
        }

        for (TVertexCount vertex = 0; vertex < vertex_count; ++vertex) {
            for (auto it = network_->getEdgeIterator(vertex); !it.isEnd(); ++it) {
                const auto finish = it.getFinish();
                if (distance_[finish] == distance_[vertex] + 1) {
                    graph_         [vertex].emplace_back(finish, it);
                    reversed_graph_[finish].emplace_back(vertex, it);
                }
            }
        }
    }

    void calcPotential_() {
        for (TVertexCount vertex = 0; vertex < network_->getVertexCount(); ++vertex) {
            incoming_potential_ [vertex] = 0;
            outcoming_potential_[vertex] = 0;
            for (const auto& edge : reversed_graph_[vertex]) {
                incoming_potential_[vertex] += edge.network_edge.getResudialCapacity();
            }
            for (const auto& edge : graph_[vertex]) {
                outcoming_potential_[vertex] += edge.network_edge.getResudialCapacity();
            }
        }
    }

    void directedPushFlow_(TVertex min_potential_vertex, TFlow flow_value, const EDirection_& direction) {
        const TVertex finish = (direction == FORWARD) ? network_->getSink() : network_->getSource();
        std::queue< std::pair<TVertex, TFlow> > queue;
        queue.push({min_potential_vertex, flow_value});

        while (!queue.empty()) {
            auto [cur_vertex, flow] = queue.front();
            queue.pop();
            if (cur_vertex == finish) {
                continue;
            }
            auto& graph = (direction == FORWARD) ? graph_[cur_vertex] : reversed_graph_[cur_vertex];
            while (flow) {
                auto& cur_edge = graph.back();
                if (!is_available_[cur_edge.finish] || cur_edge.network_edge.getResudialCapacity() == 0) {
                    graph.pop_back();
                } else {
                    TFlow cur_flow = std::min(flow, cur_edge.network_edge.getResudialCapacity());
                    cur_edge.network_edge.pushFlow(cur_flow);
                    outcoming_potential_[(direction == FORWARD) ? cur_vertex : cur_edge.finish] -= cur_flow;
                    incoming_potential_[(direction == BACKWARD) ? cur_vertex : cur_edge.finish] -= cur_flow;
                    flow -= cur_flow;
                    queue.push({cur_edge.finish, cur_flow});
                }
            }
        }
    }

    void pushFlow_(TVertex min_potential_vertex) {
        TFlow flow_value = getPotential_(min_potential_vertex);
        directedPushFlow_(min_potential_vertex, flow_value, FORWARD);
        directedPushFlow_(min_potential_vertex, flow_value, BACKWARD);
    }
};


template<typename TFlow>
class TPreflowPush : public TFlowAlgo<TFlow> {
public:
    virtual ~TPreflowPush()
    {}

protected:
    typedef typename TNetwork<TFlow>::TEdgeIterator TEdgeIterator_;
    typedef std::make_unsigned_t<TFlow> TPotential_;
    typedef unsigned int                THeight_;

    using TFlowAlgo<TFlow>::network_;

    std::vector<THeight_>       height_;
    std::vector<TPotential_>    potential_;
    std::vector<TEdgeIterator_> edge_iterator_;
    std::queue<TVertex>         overflowed_vertexes_;

    void pushFlow_(TVertex vertex, TEdgeIterator_ edge) {
        const TFlow flow  = std::min(potential_[vertex], (TPotential_)edge.getResudialCapacity());
        const auto source = network_->getSource();
        const auto sink   = network_->getSink();
        if (vertex != source && vertex != sink) {
            potential_[vertex] -= flow;
        }
        const auto finish = edge.getFinish();
        if (finish != source && finish != sink) {
            potential_[finish] += flow;
        }
        edge.pushFlow(flow);
    }

    void relabel_(TVertex vertex) {
        THeight_ new_height = std::numeric_limits<THeight_>::max();
        for (auto it = network_->getEdgeIterator(vertex); !it.isEnd(); ++it) {
            if (it.getResudialCapacity() > 0) {
                new_height = std::min(new_height, height_[it.getFinish()] + 1);
            }
        }
        height_[vertex] = new_height;
    }

    void discharge_(TVertex vertex) {
        auto& edge = edge_iterator_[vertex];
        while (potential_[vertex] > 0) {
            if (edge.isEnd()) {
                relabel_(vertex);
                edge = network_->getEdgeIterator(vertex);
            } else {
                const TVertex finish = edge.getFinish();
                if (edge.getResudialCapacity() > 0 && height_[vertex] == height_[finish] + 1) {
                    const bool was_overflowed = potential_[finish] > 0;
                    pushFlow_(vertex, edge);
                    if (!was_overflowed && potential_[finish] > 0) {
                        overflowed_vertexes_.push(finish);
                    }
                } else {
                    ++edge;
                }
            }
        }
    }
};


template<typename TFlow>
class TGoldberg : public TPreflowPush<TFlow> {
public:
    void findMaxFlow(TNetwork<TFlow>& network) override {
        network_ = &network;
        init_();
        runAlgo_();
        free_();
    }

    ~TGoldberg()
    {}

private:
    using TPreflowPush<TFlow>::network_;
    using TPreflowPush<TFlow>::height_;
    using TPreflowPush<TFlow>::potential_;
    using TPreflowPush<TFlow>::edge_iterator_;
    using TPreflowPush<TFlow>::overflowed_vertexes_;
    using TPreflowPush<TFlow>::discharge_;

    void init_() {
        const auto vertex_count = network_->getVertexCount();
        height_   .resize(vertex_count);
        potential_.resize(vertex_count);
        for (TVertexCount vertex = 0; vertex < vertex_count; ++vertex) {
            edge_iterator_.emplace_back(network_->getEdgeIterator(vertex));
        }
    }

    void free_() {
        height_       .clear();
        potential_    .clear();
        edge_iterator_.clear();
    }

    void runAlgo_() {
        for (TVertexCount vertex = 0; vertex < network_->getVertexCount(); ++vertex) {
            potential_[vertex] = 0;
            height_[vertex]    = 0;
        }

        const auto source = network_->getSource();
        height_[source]   = network_->getVertexCount();

        for (auto it = network_->getEdgeIterator(source); !it.isEnd(); ++it) {
            const auto cur_finish = it.getFinish();
            const auto sink       = network_->getSink();
            const auto flow       = it.getResudialCapacity();
            it.pushFlow(flow);
            if (cur_finish != sink) {
                potential_[cur_finish] += flow;
            }

            if (potential_[cur_finish] > 0) {
                overflowed_vertexes_.push(cur_finish);
            }
        }

        while (!overflowed_vertexes_.empty()) {
            const auto cur_vertex = overflowed_vertexes_.front();
            overflowed_vertexes_.pop();
            discharge_(cur_vertex);
        }
    }
};


template<typename TFlow>
class TSolver {
public:
    struct TData {
        struct TEdge {
            TVertex start;
            TVertex finish;
        };

        TVertexCount       n;
        std::vector<TFlow> cost;
        std::vector<TEdge> edges;
    };

    TData readData(std::istream& input_stream) const {
        TData result;
        input_stream >> result.n;
        result.cost.resize(result.n);
        for (std::size_t i = 0; i < result.n; ++i) {
            input_stream >> result.cost[i];
        }

        for (TVertexCount vertex = 0; vertex < result.n; ++vertex) {
            TVertexCount cnt;
            input_stream >> cnt;
            while(cnt--) {
                TVertex parent;
                input_stream >> parent;
                parent--;
                result.edges.push_back({ parent, vertex });
            }
        }

        return result;
    }

    TFlow solve(const TData& data, TFlowAlgo<TFlow>&& flow_algo) const {
        const TFlow        INF    = std::numeric_limits<TFlow>::max();
        const TVertexCount n      = data.n;
        const TVertex      source = n;
        const TVertex      sink   = n + 1;
        TNetwork<TFlow> network(n + 2, source, sink);

        for (const auto& edge : data.edges) {
            network.addEdge(edge.finish, edge.start, INF);
        }

        TFlow result = 0;

        for (TVertexCount vertex = 0; vertex < n; vertex++) {
            const auto cost = data.cost[vertex];
            if (cost > 0) {
                result += cost;
                network.addEdge(source, vertex, cost);
            } else {
                network.addEdge(vertex, sink, -cost);
            }
        }

        flow_algo.findMaxFlow(network);
        return result - network.getFlowValue();
    }

    void writeResult(std::ostream& output_stream, TFlow result) const {
        output_stream << result;
    }
};

} // end of namespace NFlow

void solve() {
    NFlow::TSolver<int> solver;
    const auto data = solver.readData(std::cin);
    const auto malhotra_result = solver.solve(data, NFlow::TMalhotra<int>());
    const auto goldberg_result = solver.solve(data, NFlow::TGoldberg<int>());
    assert(malhotra_result == goldberg_result);
    solver.writeResult(std::cout, malhotra_result);
}

int main(){
    solve();
}