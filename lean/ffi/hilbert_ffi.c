/*
 * hilbert_ffi.c
 *
 * C wrapper for the Lean anisotropic Hilbert curve implementation.
 * Bridges between C arrays and Lean's Array type.
 */

#include <lean/lean.h>
#include <stdint.h>
#include <string.h>

#include "hilbert_ffi.h"

/* Declare the Lean-exported functions from CExport.lean */
extern uint64_t lean_hilbert_encode(uint32_t n_dims, lean_object *coords, lean_object *exponents);
extern lean_object *lean_hilbert_decode(uint32_t n_dims, lean_object *exponents, uint64_t index);

/* Declare module initialization functions */
extern lean_object* initialize_AnisoHilbert_CExport(uint8_t builtin, lean_object* w);

/* Runtime state */
static int g_lean_initialized = 0;

int hilbert_lean_init(void) {
    if (g_lean_initialized) {
        return 0;
    }

    /* Initialize the Lean runtime */
    lean_initialize_runtime_module();

    /* Initialize the AnisoHilbert.CExport module (which transitively initializes dependencies) */
    lean_object* res = initialize_AnisoHilbert_CExport(1 /* builtin */, lean_io_mk_world());

    if (lean_io_result_is_ok(res)) {
        lean_dec_ref(res);
        lean_io_mark_end_initialization();
        g_lean_initialized = 1;
        return 0;
    } else {
        lean_dec_ref(res);
        return -1;
    }
}

void hilbert_lean_finalize(void) {
    if (g_lean_initialized) {
        lean_finalize_thread();
        g_lean_initialized = 0;
    }
}

/*
 * Create a Lean Array UInt32 from a C array.
 * Returns a new Lean object (caller must manage reference).
 */
static lean_object *c_array_to_lean_array(const uint32_t *arr, uint32_t n) {
    lean_object *lean_arr = lean_mk_empty_array();
    for (uint32_t i = 0; i < n; i++) {
        lean_object *val = lean_box_uint32(arr[i]);
        lean_arr = lean_array_push(lean_arr, val);
    }
    return lean_arr;
}

/*
 * Extract values from a Lean Array UInt32 into a C array.
 */
static void lean_array_to_c_array(lean_object *lean_arr, uint32_t *out, uint32_t n) {
    for (uint32_t i = 0; i < n; i++) {
        lean_object *elem = lean_array_get_core(lean_arr, i);
        out[i] = lean_unbox_uint32(elem);
    }
}

uint64_t hilbert_lean_encode(uint32_t n_dims, const uint32_t *coords, const uint32_t *exponents) {
    if (!g_lean_initialized) {
        return 0;
    }

    /* Convert C arrays to Lean arrays */
    lean_object *lean_coords = c_array_to_lean_array(coords, n_dims);
    lean_object *lean_exponents = c_array_to_lean_array(exponents, n_dims);

    /* Call Lean function - it takes ownership of the arrays */
    uint64_t result = lean_hilbert_encode(n_dims, lean_coords, lean_exponents);

    /* Note: lean_hilbert_encode takes ownership of the arrays, so we don't dec_ref them */

    return result;
}

void hilbert_lean_decode(uint32_t n_dims, const uint32_t *exponents, uint64_t index, uint32_t *coords_out) {
    if (!g_lean_initialized) {
        memset(coords_out, 0, n_dims * sizeof(uint32_t));
        return;
    }

    /* Convert exponents to Lean array */
    lean_object *lean_exponents = c_array_to_lean_array(exponents, n_dims);

    /* Call Lean function - it takes ownership of lean_exponents */
    lean_object *result = lean_hilbert_decode(n_dims, lean_exponents, index);

    /* Extract coordinates from result array */
    size_t result_size = lean_array_size(result);
    if (result_size == n_dims) {
        lean_array_to_c_array(result, coords_out, n_dims);
    } else {
        /* Error case: wrong size returned */
        memset(coords_out, 0, n_dims * sizeof(uint32_t));
    }

    /* Note: lean_hilbert_decode takes ownership of lean_exponents, so we don't dec_ref it.
     * We DO need to dec_ref the result since we own it. */
    lean_dec(result);
}
