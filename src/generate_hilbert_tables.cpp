#include <boost/graph/adjacency_list.hpp>
#include "generate_gray.h"

#include <array>
#include <cassert>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <queue>
#include <string>
#include <vector>

namespace hilbertgen {

using u8  = uint8_t;
using u32 = uint32_t;
using i32 = int32_t;

static inline u32 brgc(u32 i) { return i ^ (i >> 1); }

static inline u32 trailing_ones(u32 x) {
  u32 c = 0;
  while ((x & 1u) != 0u) {
    c++;
    x >>= 1u;
  }
  return c;
}

// Hamilton's (standard) child geometry for BRGC.
static inline u32 child_entry_std(u32 w) {
  if (w == 0u) return 0u;
  return brgc((w - 1u) & ~1u);
}

static inline u32 child_dir_std(u32 w, u32 k) {
  if (w == 0u) return 0u;
  if ((w & 1u) != 0u) return trailing_ones(w) % k;
  return trailing_ones(w - 1u) % k;
}

// 4-ary coordinate in up to 7 dimensions.
struct Coord4 {
  std::array<u8, 7> c{};
};

static inline i32 pow_int(i32 base, i32 exp) {
  i32 v = 1;
  for (i32 i = 0; i < exp; i++) v *= base;
  return v;
}

static std::vector<i32> make_pow4(int k) {
  std::vector<i32> p(k);
  p[0] = 1;
  for (int i = 1; i < k; i++) p[i] = p[i - 1] * 4;
  return p;
}

static inline i32 id_from_coord(const Coord4& coord, int k, const std::vector<i32>& pow4) {
  i32 id = 0;
  for (int i = 0; i < k; i++) {
    id += (i32)coord.c[(size_t)i] * pow4[(size_t)i];
  }
  return id;
}

static inline Coord4 coord_from_id(i32 id, int k) {
  Coord4 out;
  for (int i = 0; i < k; i++) {
    out.c[(size_t)i] = (u8)(id & 3);
    id >>= 2;
  }
  return out;
}

static inline u32 parent_pos_mask(const Coord4& coord, int k) {
  u32 m = 0u;
  for (int i = 0; i < k; i++) {
    m |= (u32)((coord.c[(size_t)i] >> 1) & 1u) << (u32)i;
  }
  return m;
}

static inline u32 local_mask(const Coord4& coord, int k) {
  u32 m = 0u;
  for (int i = 0; i < k; i++) {
    m |= (u32)(coord.c[(size_t)i] & 1u) << (u32)i;
  }
  return m;
}

static inline int ctz32(u32 x) {
  assert(x != 0u);
  return __builtin_ctz(x);
}

static inline int popcount32(u32 x) { return __builtin_popcount(x); }

using Graph = boost::adjacency_list<boost::vecS, boost::vecS, boost::directedS>;

static std::vector<i32> bfs_path(const Graph& g, i32 start, i32 finish) {
  const i32 N = (i32)boost::num_vertices(g);
  std::vector<i32> pred((size_t)N, -1);
  std::vector<u8> seen((size_t)N, 0);
  std::queue<i32> q;

  seen[(size_t)start] = 1;
  q.push(start);

  while (!q.empty()) {
    i32 u = q.front();
    q.pop();
    if (u == finish) break;

    auto [ei, ei_end] = boost::out_edges(u, g);
    for (; ei != ei_end; ++ei) {
      i32 v = (i32)boost::target(*ei, g);
      if (!seen[(size_t)v]) {
        seen[(size_t)v] = 1;
        pred[(size_t)v] = u;
        q.push(v);
      }
    }
  }

  if (!seen[(size_t)finish]) return {};

  std::vector<i32> path;
  for (i32 v = finish; v != -1; v = pred[(size_t)v]) {
    path.push_back(v);
    if (v == start) break;
  }
  std::reverse(path.begin(), path.end());
  return path;
}

struct Tables {
  int k = 0;
  std::vector<u32> gray;        // w -> vertex label (bitmask)
  std::vector<u32> gray_rank;   // vertex label -> w
  std::vector<u32> child_entry; // w -> entry corner bitmask (local)
  std::vector<u32> child_dir;   // w -> exit direction index (0..k-1)
};

// Build the layered "exit-vertex" DAG and find a path that yields child_entry/child_dir.
// Returns empty tables on failure.
static Tables build_tables(int k, const std::vector<u32>& gray_seq, bool force_nonstandard) {
  Tables t;
  t.k = k;
  const u32 num_cubes = 1u << (u32)k;
  if ((u32)gray_seq.size() != num_cubes) return {};

  t.gray = gray_seq;
  t.gray_rank.assign(num_cubes, 0u);
  for (u32 w = 0; w < num_cubes; w++) {
    t.gray_rank[t.gray[w]] = w;
  }

  // k=1 is trivial: only one Gray code [0,1] and one possible child geometry.
  if (k == 1) {
    (void)force_nonstandard;  // No alternative exists for k=1
    t.child_entry = {0u, 0u};
    t.child_dir = {0u, 0u};
    return t;
  }

  const i32 num_nodes = pow_int(4, k);
  const auto pow4 = make_pow4(k);

  // Precompute parent index for each node.
  std::vector<u32> parent_index((size_t)num_nodes, 0u);
  for (i32 id = 0; id < num_nodes; id++) {
    Coord4 coord = coord_from_id(id, k);
    u32 pos = parent_pos_mask(coord, k);
    parent_index[(size_t)id] = t.gray_rank[pos];
  }

  const i32 start_id = 0; // (0,0,...,0)

  // Finish at the parent-cube corner corresponding to the last Gray vertex.
  const u32 last_pos = t.gray[num_cubes - 1u];
  Coord4 finish_coord;
  for (int i = 0; i < k; i++) {
    const u32 bit = (last_pos >> (u32)i) & 1u;
    finish_coord.c[(size_t)i] = bit ? (u8)3 : (u8)0;
  }
  const i32 finish_id = id_from_coord(finish_coord, k, pow4);

  // Identify exit vertices.
  std::vector<u8> is_exit((size_t)num_nodes, 0u);
  for (i32 id = 0; id < num_nodes; id++) {
    if (id == finish_id) {
      is_exit[(size_t)id] = 1u;
      continue;
    }
    const u32 w = parent_index[(size_t)id];
    if (w + 1u >= num_cubes) continue;
    const Coord4 c = coord_from_id(id, k);

    bool ok = false;
    for (int ax = 0; ax < k && !ok; ax++) {
      for (int sgn : {-1, +1}) {
        int v = (int)c.c[(size_t)ax] + sgn;
        if (v < 0 || v > 3) continue;
        Coord4 cn = c;
        cn.c[(size_t)ax] = (u8)v;
        i32 nid = id_from_coord(cn, k, pow4);
        if (parent_index[(size_t)nid] == w + 1u) {
          ok = true;
          break;
        }
      }
    }
    is_exit[(size_t)id] = ok ? 1u : 0u;
  }

  // Build graph.
  Graph g((size_t)num_nodes);

  // Edges between exit vertices of consecutive cubes.
  for (i32 id = 0; id < num_nodes; id++) {
    if (!is_exit[(size_t)id]) continue;
    const u32 w = parent_index[(size_t)id];
    if (w + 1u >= num_cubes) continue; // last cube has no outgoing

    const Coord4 c = coord_from_id(id, k);

    // Step 1: cross boundary into next cube (entry vertex).
    for (int ax = 0; ax < k; ax++) {
      for (int sgn : {-1, +1}) {
        int v = (int)c.c[(size_t)ax] + sgn;
        if (v < 0 || v > 3) continue;
        Coord4 entry_c = c;
        entry_c.c[(size_t)ax] = (u8)v;
        i32 entry_id = id_from_coord(entry_c, k, pow4);
        if (parent_index[(size_t)entry_id] != w + 1u) continue;

        // Step 2: take one internal hop within that next cube to an exit vertex.
        for (int ax2 = 0; ax2 < k; ax2++) {
          for (int sgn2 : {-1, +1}) {
            int v2 = (int)entry_c.c[(size_t)ax2] + sgn2;
            if (v2 < 0 || v2 > 3) continue;
            Coord4 exit_c = entry_c;
            exit_c.c[(size_t)ax2] = (u8)v2;
            i32 exit_id = id_from_coord(exit_c, k, pow4);
            if (parent_index[(size_t)exit_id] == w + 1u && is_exit[(size_t)exit_id]) {
              boost::add_edge((size_t)id, (size_t)exit_id, g);
            }
          }
        }
      }
    }
  }

  // Start edges: from start corner to any adjacent exit vertex in cube 0.
  {
    const Coord4 c0 = coord_from_id(start_id, k);
    const u32 w0 = parent_index[(size_t)start_id];
    assert(w0 == 0u && "Gray code must start at vertex 0 for this construction");
    for (int ax = 0; ax < k; ax++) {
      for (int sgn : {-1, +1}) {
        int v = (int)c0.c[(size_t)ax] + sgn;
        if (v < 0 || v > 3) continue;
        Coord4 nb = c0;
        nb.c[(size_t)ax] = (u8)v;
        i32 nid = id_from_coord(nb, k, pow4);
        if (parent_index[(size_t)nid] == 0u && is_exit[(size_t)nid]) {
          boost::add_edge((size_t)start_id, (size_t)nid, g);
        }
      }
    }
  }

  // Collect candidate first exits (neighbors of start in cube 0).
  std::vector<i32> first_exits;
  {
    const Coord4 c0 = coord_from_id(start_id, k);
    for (int ax = 0; ax < k; ax++) {
      for (int sgn : {-1, +1}) {
        int v = (int)c0.c[(size_t)ax] + sgn;
        if (v < 0 || v > 3) continue;
        Coord4 nb = c0;
        nb.c[(size_t)ax] = (u8)v;
        i32 nid = id_from_coord(nb, k, pow4);
        if (parent_index[(size_t)nid] == 0u && is_exit[(size_t)nid]) {
          first_exits.push_back(nid);
        }
      }
    }
  }

  auto derive = [&](const std::vector<i32>& full_path) -> bool {
    const u32 last_w = num_cubes - 1u;
    if (full_path.size() != (size_t)num_cubes + 1u) return false;
    if (full_path.front() != start_id) return false;
    if (full_path.back() != finish_id) return false;

    // exit node per cube
    std::vector<i32> exit_node((size_t)num_cubes, -1);
    for (u32 w = 0; w < num_cubes; w++) {
      exit_node[(size_t)w] = full_path[(size_t)w + 1u];
      if (parent_index[(size_t)exit_node[(size_t)w]] != w) {
        return false;
      }
    }

    t.child_entry.assign(num_cubes, 0u);
    t.child_dir.assign(num_cubes, 0u);

    // w=0 entry is start corner (all zeros)
    Coord4 entry_c = coord_from_id(start_id, k);

    for (u32 w = 0; w < num_cubes; w++) {
      if (w > 0u) {
        const u32 pos_prev = t.gray[w - 1u];
        const u32 pos_cur  = t.gray[w];
        const u32 diff = pos_prev ^ pos_cur;
        if (diff == 0u || (diff & (diff - 1u)) != 0u) return false;
        const int ax = ctz32(diff);
        const int prev_bit = (int)((pos_prev >> (u32)ax) & 1u);
        const int cur_bit  = (int)((pos_cur  >> (u32)ax) & 1u);
        const int sgn = (cur_bit > prev_bit) ? +1 : -1;

        Coord4 prev_exit_c = coord_from_id(exit_node[(size_t)w - 1u], k);
        entry_c = prev_exit_c;
        int v = (int)entry_c.c[(size_t)ax] + sgn;
        if (v < 0 || v > 3) return false;
        entry_c.c[(size_t)ax] = (u8)v;

        const i32 entry_id = id_from_coord(entry_c, k, pow4);
        if (parent_index[(size_t)entry_id] != w) return false;
      }

      Coord4 exit_c = coord_from_id(exit_node[(size_t)w], k);
      const u32 e_local = local_mask(entry_c, k);
      const u32 x_local = local_mask(exit_c, k);
      const u32 step = e_local ^ x_local;
      if (popcount32(step) != 1) return false;
      const u32 d = (u32)ctz32(step);

      t.child_entry[w] = e_local;
      t.child_dir[w]   = d;
    }

    // Sanity: last cube must end at the finish corner.
    (void)last_w;
    return true;
  };

  auto is_standard = [&]() -> bool {
    for (u32 w = 0; w < num_cubes; w++) {
      if (t.child_entry[w] != child_entry_std(w)) return false;
      if (t.child_dir[w]   != child_dir_std(w, (u32)k)) return false;
    }
    return true;
  };

  // First attempt: unrestricted BFS from start to finish.
  std::vector<i32> path = bfs_path(g, start_id, finish_id);
  if (!path.empty()) {
    if (derive(path) && (!force_nonstandard || !is_standard())) {
      return t;
    }
  }

  // If we need a non-standard curve (or the first one failed), try forcing the first exit.
  // Iterate candidates in descending id order to bias away from the usual lexicographic choice.
  std::sort(first_exits.begin(), first_exits.end(), std::greater<i32>());
  for (i32 first : first_exits) {
    std::vector<i32> tail = bfs_path(g, first, finish_id);
    if (tail.empty()) continue;
    std::vector<i32> full;
    full.reserve(tail.size() + 1u);
    full.push_back(start_id);
    full.insert(full.end(), tail.begin(), tail.end());
    if (!derive(full)) continue;
    if (!force_nonstandard || !is_standard()) {
      return t;
    }
  }

  // Give up.
  return {};
}

static void write_header(const std::string& path, const std::vector<Tables>& all) {
  std::ofstream out(path);
  if (!out) {
    throw std::runtime_error("Failed to open output header");
  }

  out << "// Autogenerated by generate_hilbert_tables.cpp\n";
  out << "// Tables for Hilbert child geometry (1D..7D).\n\n";
  out << "#pragma once\n\n";
  out << "#include <stdint.h>\n\n";
  out << "#ifdef __cplusplus\nextern \"C\" {\n#endif\n\n";

  for (const auto& t : all) {
    const int k = t.k;
    const u32 n = 1u << (u32)k;

    auto emit = [&](const std::string& name, const std::vector<u32>& v) {
      out << "static const uint8_t " << name << "_" << k << "[" << n << "] = {";
      for (u32 i = 0; i < n; i++) {
        if (i % 16u == 0u) out << "\n  ";
        out << (unsigned)v[i];
        if (i + 1u != n) out << ", ";
      }
      out << "\n};\n\n";
    };

    emit("HILBERT_GRAY", t.gray);
    emit("HILBERT_GRAY_RANK", t.gray_rank);
    emit("HILBERT_CHILD_ENTRY", t.child_entry);
    emit("HILBERT_CHILD_DIR", t.child_dir);
  }

  // Convenience accessors.
  out << "static inline uint8_t hilbert_gray(uint32_t k, uint32_t w) {\n";
  out << "  switch(k) {\n";
  for (const auto& t : all) {
    out << "    case " << t.k << ": return HILBERT_GRAY_" << t.k << "[w];\n";
  }
  out << "    default: return 0;\n";
  out << "  }\n";
  out << "}\n\n";

  out << "static inline uint8_t hilbert_gray_rank(uint32_t k, uint32_t g) {\n";
  out << "  switch(k) {\n";
  for (const auto& t : all) {
    out << "    case " << t.k << ": return HILBERT_GRAY_RANK_" << t.k << "[g];\n";
  }
  out << "    default: return 0;\n";
  out << "  }\n";
  out << "}\n\n";

  out << "static inline uint8_t hilbert_child_entry(uint32_t k, uint32_t w) {\n";
  out << "  switch(k) {\n";
  for (const auto& t : all) {
    out << "    case " << t.k << ": return HILBERT_CHILD_ENTRY_" << t.k << "[w];\n";
  }
  out << "    default: return 0;\n";
  out << "  }\n";
  out << "}\n\n";

  out << "static inline uint8_t hilbert_child_dir(uint32_t k, uint32_t w) {\n";
  out << "  switch(k) {\n";
  for (const auto& t : all) {
    out << "    case " << t.k << ": return HILBERT_CHILD_DIR_" << t.k << "[w];\n";
  }
  out << "    default: return 0;\n";
  out << "  }\n";
  out << "}\n\n";

  out << "#ifdef __cplusplus\n}\n#endif\n";
}

} // namespace hilbertgen

static void print_usage(const char* prog) {
  std::cerr << "Usage: " << prog << " [--gray TYPE] [--seed N]\n";
  std::cerr << "  --gray TYPE   Gray code type: brgc, monotone, balanced, random (default: brgc)\n";
  std::cerr << "  --seed N      Random seed for 'random' gray type (default: 12345)\n";
}

int main(int argc, char* argv[]) {
  using namespace hilbertgen;

  // Parse command line arguments
  graygen::GrayCodeType gray_type = graygen::GrayCodeType::BRGC;
  uint64_t seed = 12345;

  for (int i = 1; i < argc; i++) {
    std::string arg = argv[i];
    if (arg == "--gray" && i + 1 < argc) {
      std::string type_str = argv[++i];
      if (type_str == "brgc") {
        gray_type = graygen::GrayCodeType::BRGC;
      } else if (type_str == "monotone") {
        gray_type = graygen::GrayCodeType::Monotone;
      } else if (type_str == "balanced") {
        gray_type = graygen::GrayCodeType::Balanced;
      } else if (type_str == "random") {
        gray_type = graygen::GrayCodeType::Random;
      } else {
        std::cerr << "Unknown gray type: " << type_str << "\n";
        print_usage(argv[0]);
        return 1;
      }
    } else if (arg == "--seed" && i + 1 < argc) {
      seed = std::stoull(argv[++i]);
    } else if (arg == "--help" || arg == "-h") {
      print_usage(argv[0]);
      return 0;
    } else {
      std::cerr << "Unknown argument: " << arg << "\n";
      print_usage(argv[0]);
      return 1;
    }
  }

  std::vector<Tables> all;
  all.reserve(7);

  for (int k = 1; k <= 7; k++) {
    auto gray = graygen::gray_code(k, gray_type, seed);
    Tables t = build_tables(k, gray, /*force_nonstandard=*/true);
    if (t.child_entry.empty()) {
      std::cerr << "Failed to build tables for k=" << k << "\n";
      return 1;
    }
    all.push_back(std::move(t));
  }

  const std::string header_path = "hilbert_generated_tables.h";
  write_header(header_path, all);
  std::cout << "Wrote " << header_path << "\n";
  return 0;
}
