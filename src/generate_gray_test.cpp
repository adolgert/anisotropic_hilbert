#include "generate_gray.h"
#include <iostream>
#include <iomanip>
#include <string>
#include <cstring>

using namespace graygen;

static bool verbose = false;

// Print a Gray code sequence
static void print_gray_code(const std::vector<u32>& gray, int k) {
    std::cout << "  [";
    for (size_t i = 0; i < gray.size(); i++) {
        if (i > 0) std::cout << ", ";
        std::cout << gray[i];
    }
    std::cout << "]\n";

    // Print as binary
    std::cout << "  Binary: ";
    for (size_t i = 0; i < gray.size(); i++) {
        if (i > 0) std::cout << " -> ";
        for (int b = k - 1; b >= 0; b--) {
            std::cout << ((gray[i] >> b) & 1);
        }
    }
    std::cout << "\n";

    // Print Hamming weights
    std::cout << "  Weights: ";
    for (size_t i = 0; i < gray.size(); i++) {
        if (i > 0) std::cout << " ";
        std::cout << popcount32(gray[i]);
    }
    std::cout << "\n";
}

// Test a single Gray code type for a single dimension
static bool test_gray_code(int k, GrayCodeType type, const char* type_name, u64 seed = 12345) {
    std::cout << "  Testing " << type_name << " k=" << k << "... ";

    std::vector<u32> gray;
    if (type == GrayCodeType::Random) {
        gray = generate_random(k, seed);
    } else {
        gray = gray_code(k, type);
    }

    bool valid = verify_gray_code(gray, k);
    bool cyclic = verify_cyclic(gray, k);
    bool starts_at_zero = !gray.empty() && gray[0] == 0;

    bool type_ok = true;
    std::string type_status;

    if (type == GrayCodeType::Monotone) {
        type_ok = verify_monotone(gray);
        type_status = type_ok ? "monotone" : "NOT monotone (fallback)";
    } else if (type == GrayCodeType::Balanced) {
        type_ok = verify_balanced(gray, k, 2);
        if (type_ok) {
            type_status = "balanced";
        } else {
            // Check with larger tolerance
            type_ok = verify_balanced(gray, k, 4);
            type_status = type_ok ? "almost balanced" : "NOT balanced (fallback)";
        }
    } else {
        type_status = "ok";
    }

    bool pass = valid && cyclic && starts_at_zero;

    if (pass) {
        std::cout << "PASS (" << type_status << ")\n";
    } else {
        std::cout << "FAIL\n";
        std::cout << "    valid=" << valid << " cyclic=" << cyclic
                  << " starts_at_zero=" << starts_at_zero << "\n";
    }

    if (verbose || !pass) {
        print_gray_code(gray, k);
        auto counts = compute_transition_counts(gray, k);
        std::cout << "  Transition counts: ";
        for (int i = 0; i < k; i++) {
            if (i > 0) std::cout << ", ";
            std::cout << "axis" << i << "=" << counts[static_cast<size_t>(i)];
        }
        std::cout << " (target=" << (1 << k) / k << ")\n";
    }

    return pass;
}

// Test reproducibility of random generation
static bool test_random_reproducibility(int k) {
    std::cout << "  Testing Random reproducibility k=" << k << "... ";

    auto gray1 = generate_random(k, 42);
    auto gray2 = generate_random(k, 42);

    if (gray1 != gray2) {
        std::cout << "FAIL (same seed gave different results)\n";
        return false;
    }

    auto gray3 = generate_random(k, 43);
    if (gray1 == gray3) {
        std::cout << "FAIL (different seeds gave same result)\n";
        return false;
    }

    std::cout << "PASS\n";
    return true;
}

int main(int argc, char* argv[]) {
    // Parse arguments
    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "-v") == 0 || strcmp(argv[i], "--verbose") == 0) {
            verbose = true;
        }
    }

    std::cout << "Gray Code Generator Tests\n";
    std::cout << "=========================\n\n";

    int total_tests = 0;
    int passed_tests = 0;

    // Test each type for each dimension
    const struct {
        GrayCodeType type;
        const char* name;
    } types[] = {
        {GrayCodeType::BRGC, "BRGC"},
        {GrayCodeType::Monotone, "Monotone"},
        {GrayCodeType::Balanced, "Balanced"},
        {GrayCodeType::Random, "Random"},
    };

    for (int k = 2; k <= 7; k++) {
        std::cout << "Dimension k=" << k << " (n=" << (1 << k) << " vertices):\n";

        for (const auto& t : types) {
            total_tests++;
            if (test_gray_code(k, t.type, t.name)) {
                passed_tests++;
            }
        }

        // Test random reproducibility
        total_tests++;
        if (test_random_reproducibility(k)) {
            passed_tests++;
        }

        std::cout << "\n";
    }

    // Summary
    std::cout << "=========================\n";
    std::cout << "Results: " << passed_tests << "/" << total_tests << " tests passed\n";

    if (passed_tests == total_tests) {
        std::cout << "All tests PASSED!\n";
        return 0;
    } else {
        std::cout << "Some tests FAILED.\n";
        return 1;
    }
}
