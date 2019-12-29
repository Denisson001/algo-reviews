#include <iostream>
#include <vector>
#include <cassert>
#include <string.h>
#include <map>
#include <algorithm>


namespace NSuffixStructures {
    template<typename TElement>
    class TSuffixArrayBuilder {
    public:
        typedef size_t                TSuffix;
        typedef std::vector<TSuffix>  TSuffixArray;
        typedef std::vector<TElement> TArray;
        typedef std::vector<size_t>   TLCPArray;

        TSuffixArray buildSuffixArray(const TArray& array) {
            const auto modified_array = _modifyArray(array);
            _init(modified_array);
            auto suffixes_permutation = _buildInitialLevel(modified_array);
            for (_TStep step = 0; (size_t)(1 << step) < modified_array.size(); ++step) {
                _buildNextLevel(suffixes_permutation, step);
            }
            _free();
            _modifyPermutation(suffixes_permutation);
            return suffixes_permutation;
        }

        TLCPArray buildLCP(const TArray& array, const TSuffixArray& suffix_array) const {
            std::vector<size_t> inversed_suffix_array(suffix_array.size());
            TLCPArray lcp(suffix_array.size() - 1);
            for (size_t i = 0; i < suffix_array.size(); ++i) {
                inversed_suffix_array[suffix_array[i]] = i;
            }

            size_t counter = 0;
            for (TSuffix suffix = 0; suffix < suffix_array.size(); ++suffix) {
                if (counter > 0) {
                    --counter;
                }
                if (inversed_suffix_array[suffix] == suffix_array.size() - 1) {
                    counter = 0;
                } else {
                    const auto next_suffix = suffix_array[inversed_suffix_array[suffix] + 1];
                    while (std::max(suffix + counter, next_suffix + counter) < suffix_array.size() &&
                           array[suffix + counter] == array[next_suffix + counter]) {
                        ++counter;
                    }
                    lcp[inversed_suffix_array[suffix]] = counter;
                }
            }

            return lcp;
        }

    private:
        typedef size_t _TStep;

        std::vector<size_t> _types;
        size_t _types_count;

        void _init(const TArray& array) {
            _types.resize(array.size(), 0);
        }

        void _free() {
            _types.clear();
        }

        TArray _modifyArray(const TArray& array) const {
            auto modified_array = array;
            modified_array.push_back(/*fake_element = */ 0);
            return modified_array;
        }

        void _modifyPermutation(TSuffixArray& suffixes_permutation) const {
            suffixes_permutation.erase(suffixes_permutation.begin());
        }

        TSuffixArray _buildInitialLevel(const TArray& array) {
            const auto suffixes_permutation = _buildInitialSuffixesPermutation(array);
            _buildInitialTypes(array, suffixes_permutation);
            return suffixes_permutation;
        }

        TSuffixArray _buildInitialSuffixesPermutation(const TArray& array) const {
            size_t alphabet_size = (*std::max_element(array.begin(), array.end())) + 1;
            std::vector<TSuffix> suffixes_permutation(array.size());
            std::vector<size_t> count(alphabet_size, 0);
            for (const auto element : array) {
                ++count[element];
            }
            for (size_t i = 1; i < alphabet_size; ++i) {
                count[i] += count[i - 1];
            }
            for (size_t i = 0; i < array.size(); ++i) {
                suffixes_permutation[--count[array[i]]] = i;
            }
            return suffixes_permutation;
        }

        void _buildInitialTypes(const TArray& array, const TSuffixArray& suffixes_permutation) {
            _types[suffixes_permutation[0]] = 0;
            _types_count = 1;
            for (size_t i = 1; i < array.size(); ++i) {
                if (array[suffixes_permutation[i]] != array[suffixes_permutation[i - 1]]) {
                    ++_types_count;
                }
                _types[suffixes_permutation[i]] = _types_count - 1;
            }
        }

        void _buildNextLevel(TSuffixArray& suffixes_permutation, _TStep step) {
            _sortSuffixes(suffixes_permutation, step);
            _recalcTypes(suffixes_permutation, step);
        }

        TSuffixArray _calcShiftedPermutation(const TSuffixArray& suffixes_permutation, _TStep step) const {
            TSuffixArray shifted_permutation(suffixes_permutation.size());
            for (size_t i = 0; i < suffixes_permutation.size(); ++i) {
                int32_t shifted_value = (int32_t)suffixes_permutation[i] - (1 << step);
                if (shifted_value < 0) {
                    shifted_value += suffixes_permutation.size();
                }
                shifted_permutation[i] = shifted_value;
            }
            return shifted_permutation;
        }

        void _sortSuffixes(TSuffixArray& suffixes_permutation, _TStep step) const {
            const auto shifted_permutation = _calcShiftedPermutation(suffixes_permutation, step);
            std::vector<size_t> count(_types_count, 0);
            for (size_t i = 0; i < suffixes_permutation.size(); ++i) {
                const auto type = _types[shifted_permutation[i]];
                ++count[type];
            }
            for (size_t i = 1; i < _types_count; ++i) {
                count[i] += count[i - 1];
            }
            for (int32_t i = (int32_t)suffixes_permutation.size() - 1; i >= 0; --i) {
                const auto type = _types[shifted_permutation[i]];
                suffixes_permutation[--count[type]] = shifted_permutation[i];
            }
        }

        void _recalcTypes(const TSuffixArray& suffixes_permutation, _TStep step) {
            std::vector<size_t> new_types(_types.size());
            new_types[suffixes_permutation[0]] = 0;
            _types_count = 1;
            for (size_t i = 1; i < suffixes_permutation.size(); ++i) {
                const size_t last_shifted_pos = (suffixes_permutation[i - 1] + (1 << step)) % suffixes_permutation.size();
                const size_t new_shifted_pos  = (suffixes_permutation[i]     + (1 << step)) % suffixes_permutation.size();
                if (_types[suffixes_permutation[i]] != _types[suffixes_permutation[i - 1]] ||
                    _types[last_shifted_pos]        != _types[new_shifted_pos]) {
                    ++_types_count;
                }
                new_types[suffixes_permutation[i]] = _types_count - 1;
            }
            swap(new_types, _types);
        }
    };

    template<typename TElement>
    class TSuffixAutomaton {
    public:
        typedef size_t TNodeNumber;

        TSuffixAutomaton() {
            _last_node = _createNewNode();
            _word_len = 0;
        }

        size_t size() const {
            return _nodes.size();
        }

        TNodeNumber getSufLink(TNodeNumber node_number) const {
            return _nodes[node_number].suf;
        }

        const std::map<TElement, TNodeNumber>& getChildren(TNodeNumber node_number) const {
            return _nodes[node_number].children;
        }

        size_t getLength(TNodeNumber node_number) const {
            return _nodes[node_number].len;
        }

        TNodeNumber getRootNumber() const {
            return _root_number;
        }

        bool isCorrectNode(TNodeNumber node_number) const {
            return node_number != _NAN;
        }

        TNodeNumber addElement(TElement element) {
            ++_word_len;
            const auto new_node  = _createNewNode();
            _nodes[new_node].len = _nodes[_last_node].len + 1;

            _recalcLastNode(new_node, element);
            _calcSufLink(new_node, element);

            _last_node = new_node;
            return new_node;
        }

    private:
        static const TNodeNumber _NAN = std::numeric_limits<TNodeNumber>::max();
        static const TNodeNumber _root_number = 0;

        struct _TNode {
            TNodeNumber suf;
            size_t      len;
            std::map<TElement, TNodeNumber> children;
        };

        std::vector<_TNode> _nodes;
        TNodeNumber         _last_node;
        size_t              _word_len;

        TNodeNumber _createNewNode() {
            TNodeNumber node_number = _nodes.size();
            _nodes.push_back({ _NAN, 0, {} });
            return node_number;
        }

        void _recalcLastNode(TNodeNumber new_node, TElement element) {
            while (_last_node != _NAN && !_nodes[_last_node].children.count(element)){
                _nodes[_last_node].children[element] = new_node;
                _last_node = _nodes[_last_node].suf;
            }
        }

        void _calcSufLink(TNodeNumber new_node, TElement element) {
            if (_last_node == _NAN){
                _nodes[new_node].suf = _root_number;
            } else {
                const auto next_node = _nodes[_last_node].children[element];
                if (_nodes[next_node].len == _nodes[_last_node].len + 1){
                    _nodes[new_node].suf = next_node;
                } else {
                    _nodes[new_node].suf = _splitNode(next_node, element);
                }
            }
        }

        TNodeNumber _splitNode(TNodeNumber splitting_node, TElement element) {
            const auto new_node        = _createNewNode();
            _nodes[new_node].children  = _nodes[splitting_node].children;
            _nodes[new_node].suf       = _nodes[splitting_node].suf;
            _nodes[new_node].len       = _nodes[_last_node].len + 1;
            _nodes[splitting_node].suf = new_node;
            while (_last_node != _NAN && _nodes[_last_node].children.count(element)){
                if (_nodes[_last_node].children[element] != splitting_node) {
                    break;
                }
                _nodes[_last_node].children[element] = new_node;
                _last_node = _nodes[_last_node].suf;
            }
            return new_node;
        }
    };

    template <typename TElement>
    class TSuffixTree {
    public:
        typedef size_t TNodeNumber;
        typedef size_t TDistance;

        struct TPosition {
            TNodeNumber node_number;
            TDistance   dist;
        };

        TSuffixTree(size_t alphabet_size) {
            const TNodeNumber _root_node_number = 0;
            const TNodeNumber _fake_node_number = 1;
            const TDistance _initial_str_pos    = 0;
            _nodes.push_back({ {}, _fake_node_number, _initial_str_pos, _fake_node_number, alphabet_size });
            _nodes.push_back({ {}, _NAN, _NAN, _NAN, alphabet_size });
            _posLastNotLeaf = {_root_node_number, _initial_str_pos};
            for (TElement element = 0; element < alphabet_size; ++element) {
                _nodes[_fake_node_number].children[element] = { _root_node_number, 1 };
            }
        }

        void addElement(TElement element) {
            while (!_canGoByElement(_posLastNotLeaf, element)) {
                const auto new_node = _buildNodeIfNeed(_posLastNotLeaf);
                _nodes[new_node].children[element] = { _nodes.size(), _INF - _word.size() };
                _nodes.push_back({ {}, _NAN, _INF, new_node, element });
                _posLastNotLeaf = { _nodes[new_node].suf, 0 };
            }
            _posLastNotLeaf = _goByElement(_posLastNotLeaf, element);
            _word.push_back(element);
        }

        size_t size() const {
            return _nodes.size();
        }

        TNodeNumber getRootNumber() const {
            return 0;
        }

        const std::map<TElement, TPosition>& getChildren(TNodeNumber node_number) const {
            return _nodes[node_number].children;
        }

        void endOfInput() {
            for (TNodeNumber node_number = 0; node_number < size(); ++node_number) {
                for (auto& [element, child] : _nodes[node_number].children) {
                    auto &edge_len = child.dist;
                    if (edge_len > _word.size()) {
                        edge_len = _word.size() - (_nodes[child.node_number].substr_end - edge_len + 1);
                    }
                }
            }
        }

    private:
        static const size_t _INF = std::numeric_limits<size_t>::max();
        static const size_t _NAN = std::numeric_limits<size_t>::max();

        struct _TNode {
            std::map<TElement, TPosition> children;
            TNodeNumber suf;
            size_t      substr_end;
            TNodeNumber parent;
            TElement    parent_element;
        };

        std::vector<_TNode>    _nodes;
        std::vector<TElement>  _word;
        TPosition              _posLastNotLeaf;

        bool _isVertex(const TPosition& pos) const {
            return pos.dist == 0;
        }

        TElement _getCurrentElement(const TPosition& pos) const {
            return _word[_nodes[pos.node_number].substr_end - pos.dist];
        }

        bool _canGoByElement(const TPosition& pos, TElement element) {
            if (_isVertex(pos)) {
                return _nodes[pos.node_number].children.count(element);
            } else {
                return element == _getCurrentElement(pos);
            }
        }

        TPosition _goByElement(TPosition pos, TElement element) const {
            if (_isVertex(pos)) {
                pos = _nodes[pos.node_number].children.at(element);
            }
            --pos.dist;
            return pos;
        }

        TNodeNumber _buildNodeIfNeed(TNodeNumber node_number) {
            const auto parent = _nodes[node_number].parent;
            TPosition pos     = { _nodes[parent].suf, 0 };
            auto right_pos    = _nodes[node_number].substr_end;
            auto left_pos     = right_pos - _nodes[parent].children[_nodes[node_number].parent_element].dist;

            while (left_pos < right_pos) {
                if (_isVertex(pos)) {
                    pos = _nodes[pos.node_number].children[_word[left_pos]];
                }
                const auto len = std::min(right_pos - left_pos, pos.dist);
                left_pos += len;
                pos.dist -= len;
            }

            return _buildNodeIfNeed(pos);
        }

        TNodeNumber _buildNodeIfNeed(TPosition pos) {
            if (_isVertex(pos)) {
                return pos.node_number;
            }

            const auto node_number    = pos.node_number;
            const auto parent         = _nodes[node_number].parent;
            const auto new_node       = _nodes.size();
            const auto element        = _getCurrentElement(pos);
            const auto parent_element = _nodes[node_number].parent_element;

            _nodes.push_back({ {}, _NAN, _nodes[node_number].substr_end - pos.dist, parent, parent_element });
            _nodes[new_node].children[element]                  = pos;
            _nodes[parent].children[parent_element].dist       -= pos.dist;
            _nodes[parent].children[parent_element].node_number = new_node;
            _nodes[new_node].suf                                = _buildNodeIfNeed(new_node);
            _nodes[node_number].parent                          = new_node;
            _nodes[node_number].parent_element                  = element;
            return new_node;
        }
    };
}; // end of namespace NSuffixStructures

namespace NSolver {
    template<typename TElement>
    class TSolver;

    template<typename TElement>
    struct TData {
        std::vector <TElement> array;
        size_t alphabet_size;
    };

    struct TResult {
        size_t length;
        size_t count;
        size_t position;

        int64_t getValue() const {
            return length * (int64_t) count;
        }

        void update(const TResult& another_result) {
            if (getValue() < another_result.getValue()) {
                *this = another_result;
            }
        }
    };

    template<typename TElement>
    class TAlgo {
        friend class TSolver<TElement>;
    private:
        virtual TResult _solve(const TData<TElement>& data) = 0;
    };

    template<typename TElement>
    class TAlgoUsingSuffixArray : public TAlgo<TElement> {
    private:
        typedef NSuffixStructures::TSuffixArrayBuilder<TElement> _TSuffixArrayBuilder;
        typedef typename _TSuffixArrayBuilder::TSuffix           _TSuffix;
        typedef typename _TSuffixArrayBuilder::TSuffixArray      _TSuffixArray;
        typedef typename _TSuffixArrayBuilder::TLCPArray         _TLCPArray;

        TResult _solve(const TData<TElement>& data) {
            _TSuffixArrayBuilder suffix_array_builder;
            const auto suffix_array = suffix_array_builder.buildSuffixArray(data.array);
            const auto lcp_array    = suffix_array_builder.buildLCP(data.array, suffix_array);
            return _calcResult(data, suffix_array, lcp_array);
        }

        TResult _calcResult(const TData<TElement>& data, const _TSuffixArray& suffix_array, const _TLCPArray& lcp_array) const {
            TResult result = { data.array.size(), 1, 0 };

            const auto left_nearest  = _calcNearestSmaller(lcp_array);
            const auto right_nearest = _calcNearestSmaller({ lcp_array.rbegin(), lcp_array.rend() });

            for (size_t i = 0; i + 1 < data.array.size(); ++i) {
                size_t segment_length = left_nearest[i] + right_nearest[lcp_array.size() - i - 1] + 2;
                result.update({ lcp_array[i], segment_length, suffix_array[i] });
            }

            return result;
        }

        std::vector<size_t> _calcNearestSmaller(const std::vector<size_t>& array) const {
            std::vector<size_t> result(array.size());
            std::vector<size_t> column_stack;
            for (size_t i = 0; i < array.size(); ++i) {
                while (!column_stack.empty() && array[column_stack.back()] >= array[i]) {
                    column_stack.pop_back();
                }
                if (column_stack.empty()) {
                    result[i] = i;
                } else {
                    result[i] = i - column_stack.back() - 1;
                }
                column_stack.push_back(i);
            }
            return result;
        }
    };

    template<typename TElement>
    class TAlgoUsingSuffixAutomaton : public TAlgo<TElement> {
    private:
        typedef NSuffixStructures::TSuffixAutomaton<TElement> _TSuffixAutomaton;
        typedef typename _TSuffixAutomaton::TNodeNumber       _TNodeNumber;
        typedef std::vector< std::vector<_TNodeNumber> >      _TSuffixTree;

        static const _TNodeNumber _NAN = std::numeric_limits<_TNodeNumber>::max();

        std::vector<_TNodeNumber> _terminal_nodes;
        std::vector<size_t> _terminals_count;
        std::vector<size_t> _dist_to_leaf;

        TResult _solve(const TData<TElement>& data) {
            const auto suffix_automaton = _buildSuffixAutomaton(data);
            _calcFunctions(suffix_automaton);
            _free();
            return _calcResult(data, suffix_automaton);
        }

        void _calcFunctions(const _TSuffixAutomaton& suffix_automaton) {
            _dist_to_leaf.resize(suffix_automaton.size(), 0);
            std::vector<bool> used(suffix_automaton.size(), false);
            _calcDistanceToLeaf(suffix_automaton, suffix_automaton.getRootNumber(), used);

            const auto suffix_tree = _buildSuffixTree(suffix_automaton);
            _terminals_count.resize(suffix_automaton.size(), 0);
            for (const auto node_number : _terminal_nodes) {
                _terminals_count[node_number] = 1;
            }
            _calcTerminalsCount(suffix_automaton.getRootNumber(), _NAN, suffix_tree);
        }

        void _calcDistanceToLeaf(const _TSuffixAutomaton& suffix_automaton, _TNodeNumber node_number, std::vector<bool>& used) {
            if (used[node_number]) {
                return;
            }
            used[node_number] = true;
            for (const auto& [element, child] : suffix_automaton.getChildren(node_number)) {
                _calcDistanceToLeaf(suffix_automaton, child, used);
                _dist_to_leaf[node_number] = std::max(_dist_to_leaf[node_number], _dist_to_leaf[child] + 1);
            }
        }

        void _calcTerminalsCount(_TNodeNumber node_number, _TNodeNumber parent_number, const _TSuffixTree& suffix_tree) {
            for (const auto& child : suffix_tree[node_number]) {
                _calcTerminalsCount(child, node_number, suffix_tree);
            }
            if (parent_number != _NAN) {
                _terminals_count[parent_number] += _terminals_count[node_number];
            }
        }

        _TSuffixAutomaton _buildSuffixAutomaton(const TData<TElement>& data) {
            _TSuffixAutomaton suffix_automaton;
            for (const auto element : data.array) {
                const auto new_node_number = suffix_automaton.addElement(element);
                _terminal_nodes.push_back(new_node_number);
            }
            return suffix_automaton;
        }

        _TSuffixTree _buildSuffixTree(const _TSuffixAutomaton& suffix_automaton) const {
            _TSuffixTree suffix_tree(suffix_automaton.size());
            for (_TNodeNumber node_number = 0; node_number < suffix_tree.size(); ++node_number) {
                const auto suf_link = suffix_automaton.getSufLink(node_number);
                if (suffix_automaton.isCorrectNode(suf_link)) {
                    suffix_tree[suf_link].push_back(node_number);
                }
            }
            return suffix_tree;
        }

        TResult _calcResult(const TData<TElement>& data, const _TSuffixAutomaton& suffix_automaton) const {
            TResult result = { data.array.size(), 1, 0 };
            for (_TNodeNumber node_number = 0; node_number < suffix_automaton.size(); ++node_number) {
                const auto substr_length = suffix_automaton.getLength(node_number);
                const auto suffix_number = data.array.size() - substr_length - _dist_to_leaf[node_number];
                result.update({ substr_length, _terminals_count[node_number], suffix_number });
            }
            return result;
        }

        void _free() {
            _terminal_nodes.clear();
            _terminals_count.clear();
            _dist_to_leaf.clear();
        }
    };

    template<typename TElement>
    class TAlgoUsingSuffixTree : public TAlgo<TElement> {
    private:
        typedef NSuffixStructures::TSuffixTree<TElement> _TSuffixTree;
        typedef typename _TSuffixTree::TNodeNumber       _TNodeNumber;
        typedef typename _TSuffixTree::TDistance         _TDistance;

        std::vector<_TDistance> _dist_to_leaf;
        std::vector<_TDistance> _dist_from_root;
        std::vector<size_t>     _terminals_count;

        TResult _solve(const TData<TElement>& data) {
            const auto suffix_tree = _buildSuffixTree(data);
            _calcFunctions(suffix_tree);
            _free();
            return _calcResult(data, suffix_tree);
        }

        void _calcFunctions(const _TSuffixTree& suffix_tree) {
            _terminals_count.resize(suffix_tree.size(), 0);
            _dist_to_leaf.resize(suffix_tree.size());
            _dist_from_root.resize(suffix_tree.size());
            for (_TNodeNumber node_number = 0; node_number < suffix_tree.size(); ++node_number) {
                if (suffix_tree.getChildren(node_number).size() == 0) {
                    ++_terminals_count[node_number];
                }
            }
            _treeDFS(suffix_tree, suffix_tree.getRootNumber(), 0);
        }

        void _treeDFS(const _TSuffixTree& suffix_tree, _TNodeNumber node_number, _TDistance dist_from_root) {
            _dist_from_root[node_number] = dist_from_root;
            for (const auto& [element, child] : suffix_tree.getChildren(node_number)) {
                const auto edge_len = child.dist;
                _treeDFS(suffix_tree, child.node_number, dist_from_root + edge_len);
                _terminals_count[node_number] += _terminals_count[child.node_number];
                _dist_to_leaf[node_number]     = _dist_to_leaf[child.node_number] + edge_len;
            }
        }

        void _free() {
            _terminals_count.clear();
            _dist_to_leaf.clear();
            _dist_from_root.clear();
        }

        _TSuffixTree _buildSuffixTree(const TData<TElement>& data) const {
            _TSuffixTree suffix_tree(data.alphabet_size);
            for (const auto element : data.array) {
                suffix_tree.addElement(element);
            }
            suffix_tree.addElement(/*fake_element = */ 0);
            suffix_tree.endOfInput();
            return suffix_tree;
        }

        TResult _calcResult(const TData<TElement>& data, const _TSuffixTree& suffix_tree) const {
            TResult result = { data.array.size(), 1, 0 };
            for (size_t node_number = 0; node_number < suffix_tree.size(); ++node_number) {
                if (_dist_from_root[node_number] <= data.array.size()) {
                    const auto suffix_number = data.array.size() - _dist_from_root[node_number] - _dist_to_leaf[node_number];
                    result.update({ _dist_from_root[node_number], _terminals_count[node_number], suffix_number });
                }
            }
            return result;
        }
    };

    template<typename TElement>
    class TSolver {
    public:
        TResult solve(const TData<TElement>& data, TAlgo<TElement>&& algo) const {
            return algo._solve(data);
        }

        TData<TElement> readData(std::istream& input_stream) const {
            TData<TElement> data;
            size_t length;
            input_stream >> length >> data.alphabet_size;
            ++data.alphabet_size;
            data.array.resize(length);
            for (size_t i = 0; i < length; ++i) {
                input_stream >> data.array[i];
            }
            return data;
        }

        void writeResult(std::ostream& output_stream, const TData<TElement>& data, const TResult& result) const {
            output_stream << result.getValue() << '\n';
            output_stream << result.length << '\n';
            for (size_t i = 0; i < result.length; ++i) {
                output_stream << data.array[result.position + i] << ' ';
            }
        }
    };
} // end of namespace NSolver

void solve(std::istream& input_stream, std::ostream& output_stream) {
    typedef int TElement;
    NSolver::TSolver<TElement> solver;
    const auto data = solver.readData(input_stream);
    const auto suffix_automaton_result = solver.solve(data, NSolver::TAlgoUsingSuffixAutomaton<TElement>());
    const auto suffix_array_result     = solver.solve(data, NSolver::TAlgoUsingSuffixArray<TElement>());
    const auto suffix_tree_result      = solver.solve(data, NSolver::TAlgoUsingSuffixTree<TElement>());
    assert(suffix_array_result.getValue() == suffix_tree_result.getValue());
    assert(suffix_array_result.getValue() == suffix_automaton_result.getValue());
    solver.writeResult(output_stream, data, suffix_array_result);
}

int main() {
    solve(std::cin, std::cout);
}