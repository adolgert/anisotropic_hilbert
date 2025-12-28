/*
 * test_hilbert_affine.cpp
 *
 * C++ test harness for hilbert_affine.c anisotropic Hilbert curve implementation.
 *
 * Tests four properties:
 *   1. Roundtrip: encode(decode(h)) == h
 *   2. Coverage: all points in the space are visited exactly once
 *   3. Adjacency: consecutive Hilbert indices map to Manhattan-adjacent points
 *   4. Bounds: all coordinates are within valid range
 *
 * Usage:
 *   ./test_hilbert_affine       # Run tests, minimal output
 *   ./test_hilbert_affine -v    # Verbose output
 *
 * With Lean support (compile with -DWITH_LEAN):
 *   ./test_hilbert_affine_lean --lean     # Test Lean implementation
 *   ./test_hilbert_affine_lean --compare  # Compare C vs Lean
 *
 * Build (C only):
 *   g++ -std=c++17 -O2 -o test_hilbert_affine test_hilbert_affine.cpp hilbert_affine.c
 *
 * Build (with Lean):
 *   g++ -std=c++17 -O2 -DWITH_LEAN -I../lean/ffi -o test_hilbert_affine_lean \
 *       test_hilbert_affine.cpp hilbert_affine.o hilbert_ffi.o \
 *       -lleanshared -L$LEAN_LIB -L$PROJECT_LIB ...
 */

#include <algorithm>
#include <cstdarg>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <vector>

#ifdef WITH_LEAN
#include "hilbert_ffi.h"
#endif

// C interface from hilbert_affine.c
extern "C" {
    typedef __uint128_t hindex_t;
    typedef uint32_t coord_t;

    hindex_t hilbert_affine_encode(const coord_t *point, const int *m, int n);
    void hilbert_affine_decode(hindex_t h, const int *m, int n, coord_t *point);
    int hilbert_affine_index_bits(const int *m, int n);
}

// ---------------------------------------------------------------------------
// Abstraction for multiple implementations (future Lean support)
// ---------------------------------------------------------------------------

struct HilbertImpl {
    using encode_fn = hindex_t (*)(const coord_t*, const int*, int);
    using decode_fn = void (*)(hindex_t, const int*, int, coord_t*);

    encode_fn encode;
    decode_fn decode;
    const char* name;
};

static HilbertImpl affine_impl = {
    hilbert_affine_encode,
    hilbert_affine_decode,
    "hilbert_affine"
};

#ifdef WITH_LEAN
// ---------------------------------------------------------------------------
// Lean implementation wrappers
// ---------------------------------------------------------------------------

// Wrapper to adapt Lean FFI to HilbertImpl interface
static hindex_t lean_encode_wrapper(const coord_t* point, const int* m, int n) {
    uint32_t exponents[32];
    for (int i = 0; i < n; i++) exponents[i] = (uint32_t)m[i];
    return (hindex_t)hilbert_lean_encode((uint32_t)n, point, exponents);
}

static void lean_decode_wrapper(hindex_t h, const int* m, int n, coord_t* point) {
    uint32_t exponents[32];
    for (int i = 0; i < n; i++) exponents[i] = (uint32_t)m[i];
    hilbert_lean_decode((uint32_t)n, exponents, (uint64_t)h, point);
}

static HilbertImpl lean_impl = {
    lean_encode_wrapper,
    lean_decode_wrapper,
    "lean"
};

static bool lean_initialized = false;

static bool init_lean() {
    if (lean_initialized) return true;
    if (hilbert_lean_init() != 0) {
        fprintf(stderr, "Failed to initialize Lean runtime\n");
        return false;
    }
    lean_initialized = true;
    return true;
}

static void finalize_lean() {
    if (lean_initialized) {
        hilbert_lean_finalize();
        lean_initialized = false;
    }
}
#endif

// ---------------------------------------------------------------------------
// Globals
// ---------------------------------------------------------------------------

static bool verbose = false;
static int tests_run = 0;
static int tests_passed = 0;

// ---------------------------------------------------------------------------
// Utility functions
// ---------------------------------------------------------------------------

static void log(const char* fmt, ...) {
    if (verbose) {
        va_list args;
        va_start(args, fmt);
        vprintf(fmt, args);
        va_end(args);
    }
}

static void print_h128(hindex_t h) {
    uint64_t hi = (uint64_t)(h >> 64);
    uint64_t lo = (uint64_t)h;
    if (hi) {
        printf("0x%llx%016llx", (unsigned long long)hi, (unsigned long long)lo);
    } else {
        printf("%llu", (unsigned long long)lo);
    }
}

static void print_shape(const int* m, int n) {
    printf("(");
    for (int i = 0; i < n; i++) {
        printf("%d%s", m[i], i < n-1 ? "," : "");
    }
    printf(")");
}

static void print_point(const uint32_t* p, int n) {
    printf("(");
    for (int i = 0; i < n; i++) {
        printf("%u%s", p[i], i < n-1 ? "," : "");
    }
    printf(")");
}

static int sum_bits(const int* m, int n) {
    int total = 0;
    for (int i = 0; i < n; i++) {
        total += m[i];
    }
    return total;
}

static uint64_t point_to_linear_index(const uint32_t* point, const int* m, int n) {
    uint64_t idx = 0;
    uint64_t stride = 1;
    for (int i = 0; i < n; i++) {
        idx += point[i] * stride;
        stride *= (1ULL << m[i]);
    }
    return idx;
}

static int manhattan(const uint32_t* a, const uint32_t* b, int n) {
    int dist = 0;
    for (int i = 0; i < n; i++) {
        dist += std::abs((int)a[i] - (int)b[i]);
    }
    return dist;
}

// ---------------------------------------------------------------------------
// Core test function
// ---------------------------------------------------------------------------

enum class FailReason {
    None,
    OutOfBounds,
    Duplicate,
    NotAdjacent,
    RoundtripFailed,
    NotAllVisited
};

struct TestResult {
    FailReason reason = FailReason::None;
    uint64_t fail_h = 0;
    std::vector<uint32_t> fail_prev;
    std::vector<uint32_t> fail_curr;
    int fail_distance = 0;
    hindex_t fail_h_back = 0;
};

static TestResult check_shape(const HilbertImpl& impl, const int* m, int n) {
    TestResult result;

    int total_bits = sum_bits(m, n);
    if (total_bits == 0 || total_bits > 64) {
        // Skip: either trivial or too large for this test
        return result;
    }

    uint64_t N = 1ULL << total_bits;
    std::vector<bool> visited(N, false);
    std::vector<uint32_t> prev(n), curr(n);

    for (uint64_t h = 0; h < N; h++) {
        // Decode
        impl.decode((hindex_t)h, m, n, curr.data());

        // Check bounds
        for (int i = 0; i < n; i++) {
            uint32_t bound = (m[i] > 0) ? (1U << m[i]) : 1U;
            if (curr[i] >= bound) {
                result.reason = FailReason::OutOfBounds;
                result.fail_h = h;
                result.fail_curr = curr;
                return result;
            }
        }

        // Check coverage (mark visited)
        uint64_t idx = point_to_linear_index(curr.data(), m, n);
        if (visited[idx]) {
            result.reason = FailReason::Duplicate;
            result.fail_h = h;
            result.fail_curr = curr;
            return result;
        }
        visited[idx] = true;

        // Check adjacency (skip first point)
        if (h > 0) {
            int dist = manhattan(prev.data(), curr.data(), n);
            if (dist != 1) {
                result.reason = FailReason::NotAdjacent;
                result.fail_h = h;
                result.fail_prev = prev;
                result.fail_curr = curr;
                result.fail_distance = dist;
                return result;
            }
        }

        // Check roundtrip
        hindex_t h_back = impl.encode(curr.data(), m, n);
        if (h_back != (hindex_t)h) {
            result.reason = FailReason::RoundtripFailed;
            result.fail_h = h;
            result.fail_curr = curr;
            result.fail_h_back = h_back;
            return result;
        }

        std::swap(prev, curr);
    }

    // Verify all points visited
    bool all_visited = std::all_of(visited.begin(), visited.end(), [](bool b) { return b; });
    if (!all_visited) {
        result.reason = FailReason::NotAllVisited;
        return result;
    }

    return result;
}

static void report_failure(const int* m, int n, const TestResult& result) {
    printf("FAIL: m=");
    print_shape(m, n);

    switch (result.reason) {
        case FailReason::OutOfBounds:
            printf(" at h=%llu\n", (unsigned long long)result.fail_h);
            printf("  Point out of bounds: ");
            print_point(result.fail_curr.data(), n);
            printf("\n");
            break;

        case FailReason::Duplicate:
            printf(" at h=%llu\n", (unsigned long long)result.fail_h);
            printf("  Duplicate point: ");
            print_point(result.fail_curr.data(), n);
            printf("\n");
            break;

        case FailReason::NotAdjacent:
            printf(" at h=%llu\n", (unsigned long long)result.fail_h);
            printf("  Expected adjacent points, got distance=%d\n", result.fail_distance);
            printf("  prev=");
            print_point(result.fail_prev.data(), n);
            printf(" curr=");
            print_point(result.fail_curr.data(), n);
            printf("\n");
            break;

        case FailReason::RoundtripFailed:
            printf(" at h=%llu\n", (unsigned long long)result.fail_h);
            printf("  Roundtrip failed: encode(decode(h)) = ");
            print_h128(result.fail_h_back);
            printf("\n");
            printf("  point=");
            print_point(result.fail_curr.data(), n);
            printf("\n");
            break;

        case FailReason::NotAllVisited:
            printf("\n  Not all points were visited (coverage failure)\n");
            break;

        default:
            break;
    }
}

static bool test_shape(const HilbertImpl& impl, const std::vector<int>& m_vec) {
    tests_run++;

    const int* m = m_vec.data();
    int n = (int)m_vec.size();

    log("  Testing m=");
    if (verbose) {
        print_shape(m, n);
        printf(" (%llu points)...", 1ULL << sum_bits(m, n));
        fflush(stdout);
    }

    TestResult result = check_shape(impl, m, n);

    if (result.reason == FailReason::None) {
        tests_passed++;
        log(" OK\n");
        return true;
    } else {
        log(" FAIL\n");
        report_failure(m, n, result);
        return false;
    }
}

// ---------------------------------------------------------------------------
// Test generators
// ---------------------------------------------------------------------------

static bool test_named_shapes(const HilbertImpl& impl) {
    log("Named shapes:\n");
    bool all_pass = true;

    std::vector<std::vector<int>> shapes = {
        {2, 1},       // 4x2
        {3, 1},       // 8x2
        {1, 4},       // 2x16
        {4, 1},       // 16x2
        {2, 2, 1},    // 4x4x2
        {3, 2, 1},    // 8x4x2
        {3, 3, 1},    // 8x8x2
        {0, 2, 1},    // 1x4x2 (degenerate)
        {1, 1, 1, 1}, // 2x2x2x2
    };

    for (const auto& m : shapes) {
        if (!test_shape(impl, m)) {
            all_pass = false;
        }
    }

    return all_pass;
}

static bool test_exhaustive_2d(const HilbertImpl& impl) {
    log("Exhaustive 2D (exponents 0-5, max 1024 points):\n");
    bool all_pass = true;

    for (int m0 = 0; m0 <= 5; m0++) {
        for (int m1 = 0; m1 <= 5; m1++) {
            if (m0 == 0 && m1 == 0) continue;  // Skip trivial case
            if (!test_shape(impl, {m0, m1})) {
                all_pass = false;
            }
        }
    }

    return all_pass;
}

static bool test_exhaustive_3d(const HilbertImpl& impl) {
    log("Exhaustive 3D (exponents 0-4, max 4096 points):\n");
    bool all_pass = true;

    for (int m0 = 0; m0 <= 4; m0++) {
        for (int m1 = 0; m1 <= 4; m1++) {
            for (int m2 = 0; m2 <= 4; m2++) {
                if (m0 == 0 && m1 == 0 && m2 == 0) continue;
                if (!test_shape(impl, {m0, m1, m2})) {
                    all_pass = false;
                }
            }
        }
    }

    return all_pass;
}

static bool test_exhaustive_4d(const HilbertImpl& impl) {
    log("Exhaustive 4D (exponents 0-3, max 4096 points):\n");
    bool all_pass = true;

    for (int m0 = 0; m0 <= 3; m0++) {
        for (int m1 = 0; m1 <= 3; m1++) {
            for (int m2 = 0; m2 <= 3; m2++) {
                for (int m3 = 0; m3 <= 3; m3++) {
                    if (m0 == 0 && m1 == 0 && m2 == 0 && m3 == 0) continue;
                    if (!test_shape(impl, {m0, m1, m2, m3})) {
                        all_pass = false;
                    }
                }
            }
        }
    }

    return all_pass;
}

#ifdef WITH_LEAN
// ---------------------------------------------------------------------------
// Cross-implementation comparison
// ---------------------------------------------------------------------------

static bool compare_implementations(const HilbertImpl& a, const HilbertImpl& b,
                                     const int* m, int n) {
    int total_bits = sum_bits(m, n);
    if (total_bits == 0 || total_bits > 64) {
        return true;  // Skip trivial or too large
    }

    uint64_t N = 1ULL << total_bits;
    std::vector<uint32_t> point_a(n), point_b(n);

    for (uint64_t h = 0; h < N; h++) {
        // Compare decode
        a.decode((hindex_t)h, m, n, point_a.data());
        b.decode((hindex_t)h, m, n, point_b.data());

        if (point_a != point_b) {
            printf("MISMATCH decode at h=%llu:\n", (unsigned long long)h);
            printf("  %s: ", a.name);
            print_point(point_a.data(), n);
            printf("\n  %s: ", b.name);
            print_point(point_b.data(), n);
            printf("\n");
            return false;
        }

        // Compare encode (using point_a as input)
        hindex_t h_a = a.encode(point_a.data(), m, n);
        hindex_t h_b = b.encode(point_a.data(), m, n);

        if (h_a != h_b) {
            printf("MISMATCH encode at point=");
            print_point(point_a.data(), n);
            printf(":\n  %s: ", a.name);
            print_h128(h_a);
            printf("\n  %s: ", b.name);
            print_h128(h_b);
            printf("\n");
            return false;
        }
    }
    return true;
}

static bool compare_shape(const HilbertImpl& a, const HilbertImpl& b,
                          const std::vector<int>& m_vec) {
    tests_run++;

    const int* m = m_vec.data();
    int n = (int)m_vec.size();

    log("  Comparing m=");
    if (verbose) {
        print_shape(m, n);
        printf(" (%llu points)...", 1ULL << sum_bits(m, n));
        fflush(stdout);
    }

    if (compare_implementations(a, b, m, n)) {
        tests_passed++;
        log(" OK\n");
        return true;
    } else {
        log(" FAIL\n");
        return false;
    }
}

static bool compare_exhaustive_2d(const HilbertImpl& a, const HilbertImpl& b) {
    log("Comparing 2D (exponents 0-5):\n");
    bool all_pass = true;

    for (int m0 = 0; m0 <= 5; m0++) {
        for (int m1 = 0; m1 <= 5; m1++) {
            if (m0 == 0 && m1 == 0) continue;
            if (!compare_shape(a, b, {m0, m1})) {
                all_pass = false;
            }
        }
    }
    return all_pass;
}

static bool compare_exhaustive_3d(const HilbertImpl& a, const HilbertImpl& b) {
    log("Comparing 3D (exponents 0-4):\n");
    bool all_pass = true;

    for (int m0 = 0; m0 <= 4; m0++) {
        for (int m1 = 0; m1 <= 4; m1++) {
            for (int m2 = 0; m2 <= 4; m2++) {
                if (m0 == 0 && m1 == 0 && m2 == 0) continue;
                if (!compare_shape(a, b, {m0, m1, m2})) {
                    all_pass = false;
                }
            }
        }
    }
    return all_pass;
}

static bool compare_exhaustive_4d(const HilbertImpl& a, const HilbertImpl& b) {
    log("Comparing 4D (exponents 0-3):\n");
    bool all_pass = true;

    for (int m0 = 0; m0 <= 3; m0++) {
        for (int m1 = 0; m1 <= 3; m1++) {
            for (int m2 = 0; m2 <= 3; m2++) {
                for (int m3 = 0; m3 <= 3; m3++) {
                    if (m0 == 0 && m1 == 0 && m2 == 0 && m3 == 0) continue;
                    if (!compare_shape(a, b, {m0, m1, m2, m3})) {
                        all_pass = false;
                    }
                }
            }
        }
    }
    return all_pass;
}

static bool compare_exhaustive_5d(const HilbertImpl& a, const HilbertImpl& b) {
    log("Comparing 5D (exponents 0-4):\n");
    bool all_pass = true;

    for (int m0 = 0; m0 <= 4; m0++) {
        for (int m1 = 0; m1 <= 4; m1++) {
            for (int m2 = 0; m2 <= 4; m2++) {
                for (int m3 = 0; m3 <= 4; m3++) {
                    for (int m4 = 0; m4 <= 4; m4++) {
                        if (m0 == 0 && m1 == 0 && m2 == 0 && m3 == 0 && m4 == 0) continue;
                        if (m0 + m1 + m2 + m3 + m4 > 20) continue;
                        if (!compare_shape(a, b, {m0, m1, m2, m3, m4})) {
                            all_pass = false;
                        }
                    }
                }
            }
        }
    }
    return all_pass;
}

static bool compare_exhaustive_6d(const HilbertImpl& a, const HilbertImpl& b) {
    log("Comparing 6D (exponents 0-3):\n");
    bool all_pass = true;

    for (int m0 = 0; m0 <= 3; m0++) {
        for (int m1 = 0; m1 <= 3; m1++) {
            for (int m2 = 0; m2 <= 3; m2++) {
                for (int m3 = 0; m3 <= 3; m3++) {
                    for (int m4 = 0; m4 <= 3; m4++) {
                        for (int m5 = 0; m5 <= 3; m5++) {
                            if (m0 == 0 && m1 == 0 && m2 == 0 && m3 == 0 && m4 == 0 && m5 == 0) continue;
                            if (m0 + m1 + m2 + m3 + m4 + m5 > 18) continue;
                            if (!compare_shape(a, b, {m0, m1, m2, m3, m4, m5})) {
                                all_pass = false;
                            }
                        }
                    }
                }
            }
        }
    }
    return all_pass;
}
#endif

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

static void usage(const char* prog) {
    printf("Usage: %s [-v] [-h]\n", prog);
    printf("  -v         Verbose output\n");
    printf("  -h         Show this help\n");
#ifdef WITH_LEAN
    printf("  --lean     Test Lean implementation\n");
    printf("  --compare  Compare C vs Lean implementations\n");
#endif
}

int main(int argc, char* argv[]) {
    bool test_lean = false;
    bool compare_mode = false;

    // Parse arguments
    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "-v") == 0) {
            verbose = true;
        } else if (strcmp(argv[i], "-h") == 0 || strcmp(argv[i], "--help") == 0) {
            usage(argv[0]);
            return 0;
#ifdef WITH_LEAN
        } else if (strcmp(argv[i], "--lean") == 0) {
            test_lean = true;
        } else if (strcmp(argv[i], "--compare") == 0) {
            compare_mode = true;
#endif
        } else {
            fprintf(stderr, "Unknown option: %s\n", argv[i]);
            usage(argv[0]);
            return 1;
        }
    }

#ifdef WITH_LEAN
    // Initialize Lean if needed
    if (test_lean || compare_mode) {
        printf("Initializing Lean runtime...\n");
        if (!init_lean()) {
            return 1;
        }
        printf("Lean runtime initialized.\n\n");
    }

    if (compare_mode) {
        printf("Comparing %s vs %s implementations\n", affine_impl.name, lean_impl.name);
        printf("========================================\n");

        bool all_pass = true;

        all_pass &= compare_exhaustive_2d(affine_impl, lean_impl);
        all_pass &= compare_exhaustive_3d(affine_impl, lean_impl);
        all_pass &= compare_exhaustive_4d(affine_impl, lean_impl);
        // all_pass &= compare_exhaustive_5d(affine_impl, lean_impl);
        // all_pass &= compare_exhaustive_6d(affine_impl, lean_impl);

        printf("========================================\n");
        printf("Results: %d/%d comparisons passed\n", tests_passed, tests_run);

        finalize_lean();

        if (all_pass) {
            printf("ALL COMPARISONS PASSED\n");
            return 0;
        } else {
            printf("SOME COMPARISONS FAILED\n");
            return 1;
        }
    }

    HilbertImpl& impl = test_lean ? lean_impl : affine_impl;
#else
    (void)test_lean;
    (void)compare_mode;
    HilbertImpl& impl = affine_impl;
#endif

    printf("Testing %s implementation\n", impl.name);
    printf("========================================\n");

    bool all_pass = true;

    all_pass &= test_named_shapes(impl);
    all_pass &= test_exhaustive_2d(impl);
    all_pass &= test_exhaustive_3d(impl);
    all_pass &= test_exhaustive_4d(impl);

    printf("========================================\n");
    printf("Results: %d/%d tests passed\n", tests_passed, tests_run);

#ifdef WITH_LEAN
    if (test_lean) {
        finalize_lean();
    }
#endif

    if (all_pass) {
        printf("ALL TESTS PASSED\n");
        return 0;
    } else {
        printf("SOME TESTS FAILED\n");
        return 1;
    }
}
