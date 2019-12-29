#include <iostream>
#include <ext/pb_ds/assoc_container.hpp>


namespace NGeometry {

typedef long double TFloatCoord;
const TFloatCoord EPS = 1e-9;

bool isLessThan(TFloatCoord first_value, TFloatCoord second_value) {
    return first_value + EPS < second_value;
}

bool isEqual(TFloatCoord first_value, TFloatCoord second_value) {
    return fabsl(first_value - second_value) < EPS;
}

bool isNotEqual(TFloatCoord first_value, TFloatCoord second_value) {
    return !isEqual(first_value, second_value);
}


template<typename TCoords>
struct TPoint {
    TCoords x;
    TCoords y;

    TPoint()
    {}

    TPoint(TCoords x, TCoords y):
            x(x),
            y(y)
    {}

    TPoint<TCoords> operator-(const TPoint<TCoords> &point) const {
        return { x - point.x, y - point.y };
    }

    bool operator==(const TPoint<TCoords> &point) const {
        return isEqual(x, point.x) && isEqual(y, point.y);
    }

    TCoords dotProduct(const TPoint<TCoords> &point) const {
        return x * point.x + y * point.y;
    }

    TCoords crossProduct(const TPoint<TCoords> &point) const {
        return x * point.y - y * point.x;
    }
};

template<typename TCoords>
std::istream& operator>> (std::istream& stream, TPoint<TCoords>& point){
    stream >> point.x >> point.y;
    return stream;
}


template<typename TCoords>
struct TSegment {
    TPoint<TCoords> first;
    TPoint<TCoords> second;

    TFloatCoord getYCoordAt(TFloatCoord x_coord) const {
        if (first.x == second.x) {
            return (TFloatCoord)(first.y + second.y) / 2;
        }
        const auto x_coeff = (TFloatCoord)(x_coord - first.x) / (second.x - first.x);
        return first.y + (second.y - first.y) * x_coeff;
    }

    bool containsPoint(const TPoint<TCoords>& point) const {
        const auto segment       = second - first;
        const auto first_vector  = point - first;
        const auto second_vector = point - second;
        if (first_vector.crossProduct(segment) != 0) {
            return false;
        }
        return first_vector.dotProduct(segment)  >= 0 &&
               second_vector.dotProduct(segment) <= 0;
    }
};

} // end of namespace NGeometry


namespace NAlgo {

typedef uint32_t TVertexCount;
typedef uint32_t TQueriesCount;


template<typename TCoords>
class TOrderedSet {
public:
    typedef NGeometry::TSegment<TCoords> TSegment;
    typedef NGeometry::TPoint<TCoords>   TPoint;

    void insert(const TSegment& segment) {
        _ordered_set.insert(segment);
    }

    void erase(const TSegment& segment) {
        _ordered_set.erase(segment);
    }

    uint32_t getSegmentsCountUnderPoint(const TPoint& point) const {
        return _ordered_set.order_of_key({ point, point });
    }

    bool isPointInSegment(const TPoint& point) const {
        auto iter = _ordered_set.lower_bound({ point, point });
        if (iter != _ordered_set.end()) {
            const auto& segment = *iter;
            if (segment.containsPoint(point)) {
                return true;
            }
        }
        if (iter != _ordered_set.begin()) {
            const auto& segment = *prev(iter);
            if (segment.containsPoint(point)) {
                return true;
            }
        }
        return false;
    }

    bool isEmpty() const {
        return _ordered_set.empty();
    }

private:
    struct _TComparator {
    public:
        bool operator()(const TSegment& first_seg, const TSegment& second_seg) const {
            const auto [min_x_proj, max_x_proj] = _getCommonXProjection(first_seg, second_seg);
            const auto mid_x_proj = (NGeometry::TFloatCoord)(min_x_proj + max_x_proj) / 2;

            const auto first_y_coord  = first_seg.getYCoordAt(mid_x_proj);
            const auto second_y_coord = second_seg.getYCoordAt(mid_x_proj);

            if (NGeometry::isNotEqual(first_y_coord, second_y_coord)) {
                return NGeometry::isLessThan(first_y_coord, second_y_coord);
            }

            const auto first_x_min_proj  = first_seg.first.x;
            const auto second_x_min_proj = second_seg.first.x;

            return NGeometry::isLessThan(first_x_min_proj, second_x_min_proj);
        }

    private:
        std::pair<TCoords, TCoords> _getCommonXProjection(const TSegment& first_seg, const TSegment& second_seg) const {
            const auto min_x = std::max(first_seg.first.x, second_seg.first.x);
            const auto max_x = std::min(first_seg.second.x, second_seg.second.x);
            return { min_x, max_x };
        }
    };

    typedef __gnu_pbds::tree<
        TSegment,
        __gnu_pbds::null_type,
        _TComparator,
        __gnu_pbds::rb_tree_tag,
        __gnu_pbds::tree_order_statistics_node_update
    > _TOrderedSet;

    _TOrderedSet _ordered_set;
};


template<typename TCoords>
class TAlgo {
public:
    typedef NGeometry::TSegment<TCoords> TSegment;
    typedef NGeometry::TPoint<TCoords>   TPoint;

    struct TData {
        std::vector<TPoint> polygon;
        std::vector<TPoint> queries;
    };

    std::vector<std::string> solve(const TData* data) {
        _init(data->polygon, data->queries);
        const auto result = _solve(data->queries);
        _free();
        return result;
    }

private:
    struct _TEvent {
        typedef uint32_t TNumber;

        enum EEventType {
            INSERT,
            CHECK_BORDER,
            ERASE,
            CHECK_INSIDE_AND_OUTSIDE
        };

        TPoint     point;
        EEventType type;
        TNumber    number;

        _TEvent(const TPoint& point, const EEventType& type, const TNumber& number) :
                point(point),
                type(type),
                number(number)
        {}
    };

    const inline static std::string _INSIDE  = "INSIDE";
    const inline static std::string _OUTSIDE = "OUTSIDE";
    const inline static std::string _BORDER  = "BORDER";
    const inline static std::string _EMPTY   = "";

    std::vector<TSegment> _segments;
    std::vector<_TEvent>  _events;

    void _init(const std::vector<TPoint>& polygon, const std::vector<TPoint>& queries) {
        _segments.resize(polygon.size() + 1);

        for (uint32_t i = 1; i <= polygon.size(); ++i) {
            uint32_t j = (i == polygon.size()) ? 1 : i + 1;
            auto first_point  = polygon[i - 1];
            auto second_point = polygon[j - 1];
            if (first_point == second_point) {
                continue;
            }
            if (first_point.x > second_point.x) {
                std::swap(first_point, second_point);
            }
            _segments[i] = { first_point, second_point };
            _events.emplace_back(first_point,  _TEvent::EEventType::INSERT, i);
            _events.emplace_back(second_point, _TEvent::EEventType::ERASE,  i);
        }

        for (uint32_t i = 0; i < queries.size(); ++i) {
            _events.emplace_back(queries[i], _TEvent::EEventType::CHECK_INSIDE_AND_OUTSIDE, i);
            _events.emplace_back(queries[i], _TEvent::EEventType::CHECK_BORDER, i);
        }
    }

    void _free() {
        _segments.clear();
        _events.clear();
    }

    std::vector<std::string> _solve(const std::vector<TPoint>& queries) {
        std::sort(_events.begin(), _events.end(), [](const _TEvent& first_event, const _TEvent& second_event){
            return first_event.point.x < second_event.point.x  ||
                   first_event.point.x == second_event.point.x &&
                   first_event.type < second_event.type;
        });

        TOrderedSet<TCoords> ordered_set;
        std::vector<std::string> result(queries.size());

        for (uint32_t i = 0; i < _events.size(); ++i) {
            const auto event_number = _events[i].number;
            const auto event_type   = _events[i].type;

            if (event_type == _TEvent::EEventType::INSERT) {
                ordered_set.insert(_segments[event_number]);

            } else if (event_type == _TEvent::EEventType::ERASE) {
                ordered_set.erase(_segments[event_number]);

            } else if (event_type == _TEvent::EEventType::CHECK_BORDER) {
                if (!ordered_set.isEmpty() && ordered_set.isPointInSegment(queries[event_number])) {
                    result[event_number] = _BORDER;
                } else {
                    result[event_number] = _EMPTY;
                }

            } else { // CHECK_INSIDE_AND_OUTSIDE
                if (result[event_number] == _EMPTY) {
                    if (ordered_set.getSegmentsCountUnderPoint(queries[event_number]) & 1) {
                        result[event_number] = _INSIDE;
                    } else {
                        result[event_number] = _OUTSIDE;
                    }
                }

            }
        }

        return result;
    }
};


template<typename TCoords>
class TSolver {
public:
    typedef typename TAlgo<TCoords>::TData TData;

    std::vector<std::string> solve(const TData& data) const {
        TAlgo<TCoords> algo;
        return algo.solve(&data);
    }

    TData readData(std::istream& input_stream) const {
        TData data;

        TVertexCount vertex_cnt;
        std::cin >> vertex_cnt;
        data.polygon.resize(vertex_cnt);
        for (int i = 0; i < vertex_cnt; ++i) {
            std::cin >> data.polygon[i];
        }

        TQueriesCount queries_cnt;
        std::cin >> queries_cnt;
        data.queries.resize(queries_cnt);
        for (int i = 0; i < queries_cnt; ++i) {
            std::cin >> data.queries[i];
        }

        return data;
    }

    void writeResult(std::ostream& output_stream, const std::vector<std::string>& result) const {
        for (const auto& word : result) {
            output_stream << word << "\n";
        }
    }
};

} // end of namespace NAlgo

void solve(std::istream& input_stream, std::ostream& output_stream) {
    NAlgo::TSolver<long long> solver;
    int test_cnt;
    input_stream >> test_cnt;
    while (test_cnt--) {
        const auto data = solver.readData(input_stream);
        const auto result = solver.solve(data);
        solver.writeResult(output_stream, result);
    }
}

int main() {
    solve(std::cin, std::cout);
}