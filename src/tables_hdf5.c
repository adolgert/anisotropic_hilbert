/*
 * tables_hdf5.c
 *
 * HDF5-based storage and retrieval for Hilbert curve tables.
 */

#define _POSIX_C_SOURCE 200809L  /* For strdup */

#include "tables_hdf5.h"
#include <hdf5.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

#define MAX_NAME_LEN 32
#define MAX_K 8
#define MIN_K 1

/* Context structure */
struct hilbert_tables_ctx {
    hid_t file_id;              /* HDF5 file handle, H5I_INVALID_HID if not open */
    char* filename;             /* For error messages */
    int writable;               /* 1 if opened for writing */

    /* Currently selected table */
    char current_name[MAX_NAME_LEN];
    int current_index;

    /* Cached data for current (name, index, k) */
    int cached_k;               /* Which k is currently loaded (0 = none) */
    uint8_t* gray;              /* [2^k] array */
    uint8_t* gray_rank;
    uint8_t* child_entry;
    uint8_t* child_dir;
};

/* Check if file handle is valid */
static int file_is_valid(hid_t file_id)
{
    return file_id >= 0 && H5Iis_valid(file_id) > 0;
}

/* --------------------------------------------------------------------------
 * Internal helpers
 * -------------------------------------------------------------------------- */

static void free_cache(hilbert_tables_ctx_t* ctx)
{
    if (ctx->gray) { free(ctx->gray); ctx->gray = NULL; }
    if (ctx->gray_rank) { free(ctx->gray_rank); ctx->gray_rank = NULL; }
    if (ctx->child_entry) { free(ctx->child_entry); ctx->child_entry = NULL; }
    if (ctx->child_dir) { free(ctx->child_dir); ctx->child_dir = NULL; }
    ctx->cached_k = 0;
}

/* Build path like "/random/0/3" */
static void build_group_path(char* buf, size_t bufsize,
                             const char* name, int index, int k)
{
    snprintf(buf, bufsize, "/%s/%d/%d", name, index, k);
}

/* Build path like "/random/0/3/gray" */
static void build_dataset_path(char* buf, size_t bufsize,
                               const char* name, int index, int k,
                               const char* dataset)
{
    snprintf(buf, bufsize, "/%s/%d/%d/%s", name, index, k, dataset);
}

/* Check if a group exists */
static int group_exists(hid_t file_id, const char* path)
{
    htri_t exists = H5Lexists(file_id, path, H5P_DEFAULT);
    return exists > 0;
}

/* Create group and all parent groups if needed */
static int create_groups(hid_t file_id, const char* name, int index, int k)
{
    char path[128];
    hid_t gcpl = H5Pcreate(H5P_LINK_CREATE);
    H5Pset_create_intermediate_group(gcpl, 1);

    build_group_path(path, sizeof(path), name, index, k);

    hid_t grp = H5Gcreate2(file_id, path, gcpl, H5P_DEFAULT, H5P_DEFAULT);
    H5Pclose(gcpl);

    if (grp < 0) {
        /* Group might already exist, try to open it */
        grp = H5Gopen2(file_id, path, H5P_DEFAULT);
        if (grp < 0) return -1;
    }
    H5Gclose(grp);
    return 0;
}

/* Write a uint8 array dataset, replacing if it exists */
static int write_dataset(hid_t file_id, const char* path,
                         const uint8_t* data, hsize_t size)
{
    /* Delete existing dataset if present */
    if (H5Lexists(file_id, path, H5P_DEFAULT) > 0) {
        H5Ldelete(file_id, path, H5P_DEFAULT);
    }

    hid_t space = H5Screate_simple(1, &size, NULL);
    if (space < 0) return -1;

    hid_t dset = H5Dcreate2(file_id, path, H5T_NATIVE_UINT8, space,
                            H5P_DEFAULT, H5P_DEFAULT, H5P_DEFAULT);
    if (dset < 0) {
        H5Sclose(space);
        return -1;
    }

    herr_t status = H5Dwrite(dset, H5T_NATIVE_UINT8, H5S_ALL, H5S_ALL,
                             H5P_DEFAULT, data);

    H5Dclose(dset);
    H5Sclose(space);

    return (status < 0) ? -1 : 0;
}

/* Read a uint8 array dataset */
static uint8_t* read_dataset(hid_t file_id, const char* path, hsize_t expected_size)
{
    if (H5Lexists(file_id, path, H5P_DEFAULT) <= 0) {
        return NULL;
    }

    hid_t dset = H5Dopen2(file_id, path, H5P_DEFAULT);
    if (dset < 0) return NULL;

    hid_t space = H5Dget_space(dset);
    if (space < 0) {
        H5Dclose(dset);
        return NULL;
    }

    hsize_t dims[1];
    int ndims = H5Sget_simple_extent_dims(space, dims, NULL);
    H5Sclose(space);

    if (ndims != 1 || dims[0] != expected_size) {
        H5Dclose(dset);
        return NULL;
    }

    uint8_t* data = (uint8_t*)malloc(expected_size);
    if (!data) {
        H5Dclose(dset);
        return NULL;
    }

    herr_t status = H5Dread(dset, H5T_NATIVE_UINT8, H5S_ALL, H5S_ALL,
                            H5P_DEFAULT, data);
    H5Dclose(dset);

    if (status < 0) {
        free(data);
        return NULL;
    }

    return data;
}

/* Load tables for given (name, index, k) into cache */
static int load_tables(hilbert_tables_ctx_t* ctx, int k)
{
    if (k < MIN_K || k > MAX_K) return -1;
    if (ctx->current_name[0] == '\0') return -1;

    free_cache(ctx);

    hsize_t size = (hsize_t)(1u << k);
    char path[128];

    build_dataset_path(path, sizeof(path), ctx->current_name, ctx->current_index, k, "gray");
    ctx->gray = read_dataset(ctx->file_id, path, size);
    if (!ctx->gray) goto fail;

    build_dataset_path(path, sizeof(path), ctx->current_name, ctx->current_index, k, "gray_rank");
    ctx->gray_rank = read_dataset(ctx->file_id, path, size);
    if (!ctx->gray_rank) goto fail;

    build_dataset_path(path, sizeof(path), ctx->current_name, ctx->current_index, k, "child_entry");
    ctx->child_entry = read_dataset(ctx->file_id, path, size);
    if (!ctx->child_entry) goto fail;

    build_dataset_path(path, sizeof(path), ctx->current_name, ctx->current_index, k, "child_dir");
    ctx->child_dir = read_dataset(ctx->file_id, path, size);
    if (!ctx->child_dir) goto fail;

    ctx->cached_k = k;
    return 0;

fail:
    free_cache(ctx);
    return -1;
}

/* --------------------------------------------------------------------------
 * Context Management
 * -------------------------------------------------------------------------- */

hilbert_tables_ctx_t* hilbert_tables_open(const char* filename)
{
    if (!filename) return NULL;

    hilbert_tables_ctx_t* ctx = (hilbert_tables_ctx_t*)calloc(1, sizeof(*ctx));
    if (!ctx) return NULL;

    ctx->file_id = -1;  /* Initialize to invalid */

    /* Suppress HDF5 error output for cleaner error handling */
    H5Eset_auto2(H5E_DEFAULT, NULL, NULL);

    ctx->file_id = H5Fopen(filename, H5F_ACC_RDONLY, H5P_DEFAULT);
    if (ctx->file_id < 0) {
        free(ctx);
        return NULL;
    }

    ctx->filename = strdup(filename);
    ctx->writable = 0;
    ctx->current_index = -1;

    return ctx;
}

hilbert_tables_ctx_t* hilbert_tables_create(const char* filename)
{
    if (!filename) return NULL;

    hilbert_tables_ctx_t* ctx = (hilbert_tables_ctx_t*)calloc(1, sizeof(*ctx));
    if (!ctx) return NULL;

    ctx->file_id = -1;  /* Initialize to invalid */

    /* Suppress HDF5 error output for cleaner error handling */
    H5Eset_auto2(H5E_DEFAULT, NULL, NULL);

    ctx->file_id = H5Fcreate(filename, H5F_ACC_TRUNC, H5P_DEFAULT, H5P_DEFAULT);
    if (ctx->file_id < 0) {
        free(ctx);
        return NULL;
    }

    ctx->filename = strdup(filename);
    ctx->writable = 1;
    ctx->current_index = -1;

    return ctx;
}

hilbert_tables_ctx_t* hilbert_tables_open_rw(const char* filename)
{
    if (!filename) return NULL;

    hilbert_tables_ctx_t* ctx = (hilbert_tables_ctx_t*)calloc(1, sizeof(*ctx));
    if (!ctx) return NULL;

    ctx->file_id = -1;  /* Initialize to invalid */

    /* Suppress HDF5 error output for cleaner error handling */
    H5Eset_auto2(H5E_DEFAULT, NULL, NULL);

    /* Try to open existing file for read/write */
    ctx->file_id = H5Fopen(filename, H5F_ACC_RDWR, H5P_DEFAULT);
    if (ctx->file_id < 0) {
        /* File doesn't exist, create new one */
        ctx->file_id = H5Fcreate(filename, H5F_ACC_TRUNC, H5P_DEFAULT, H5P_DEFAULT);
        if (ctx->file_id < 0) {
            free(ctx);
            return NULL;
        }
    }

    ctx->filename = strdup(filename);
    ctx->writable = 1;
    ctx->current_index = -1;

    return ctx;
}

void hilbert_tables_close(hilbert_tables_ctx_t* ctx)
{
    if (!ctx) return;

    free_cache(ctx);

    if (file_is_valid(ctx->file_id)) {
        H5Fclose(ctx->file_id);
    }
    if (ctx->filename) {
        free(ctx->filename);
    }
    free(ctx);
}

/* --------------------------------------------------------------------------
 * Query Available Tables
 * -------------------------------------------------------------------------- */

/* Callback for counting groups */
typedef struct {
    int count;
} count_info_t;

static herr_t count_callback(hid_t loc_id, const char* name,
                             const H5L_info_t* info, void* opdata)
{
    (void)loc_id;
    (void)name;
    (void)info;
    count_info_t* ci = (count_info_t*)opdata;
    ci->count++;
    return 0;
}

int hilbert_tables_count(hilbert_tables_ctx_t* ctx, const char* name)
{
    if (!ctx || !name) return 0;

    char path[128];
    snprintf(path, sizeof(path), "/%s", name);

    if (!group_exists(ctx->file_id, path)) {
        return 0;
    }

    hid_t grp = H5Gopen2(ctx->file_id, path, H5P_DEFAULT);
    if (grp < 0) return 0;

    count_info_t ci = {0};
    H5Literate(grp, H5_INDEX_NAME, H5_ITER_INC, NULL, count_callback, &ci);

    H5Gclose(grp);
    return ci.count;
}

/* --------------------------------------------------------------------------
 * Select Current Table
 * -------------------------------------------------------------------------- */

int hilbert_tables_select(hilbert_tables_ctx_t* ctx, const char* name, int index)
{
    if (!ctx || !name || index < 0) return -1;

    /* Check that at least one k exists for this name/index */
    char path[128];
    snprintf(path, sizeof(path), "/%s/%d", name, index);

    if (!group_exists(ctx->file_id, path)) {
        return -1;
    }

    /* Update selection */
    strncpy(ctx->current_name, name, MAX_NAME_LEN - 1);
    ctx->current_name[MAX_NAME_LEN - 1] = '\0';
    ctx->current_index = index;

    /* Invalidate cache (will reload on next access) */
    free_cache(ctx);

    return 0;
}

/* --------------------------------------------------------------------------
 * Table Lookup (auto-loads k on demand)
 * -------------------------------------------------------------------------- */

static int ensure_loaded(hilbert_tables_ctx_t* ctx, uint32_t k)
{
    if (!ctx) return -1;
    if (k < MIN_K || k > MAX_K) return -1;
    if (ctx->current_name[0] == '\0' || ctx->current_index < 0) return -1;

    if (ctx->cached_k != (int)k) {
        if (load_tables(ctx, (int)k) < 0) {
            return -1;
        }
    }
    return 0;
}

uint8_t hilbert_gray_ctx(hilbert_tables_ctx_t* ctx, uint32_t k, uint32_t w)
{
    if (ensure_loaded(ctx, k) < 0) return 0;
    if (w >= (1u << k)) return 0;
    return ctx->gray[w];
}

uint8_t hilbert_gray_rank_ctx(hilbert_tables_ctx_t* ctx, uint32_t k, uint32_t g)
{
    if (ensure_loaded(ctx, k) < 0) return 0;
    if (g >= (1u << k)) return 0;
    return ctx->gray_rank[g];
}

uint8_t hilbert_child_entry_ctx(hilbert_tables_ctx_t* ctx, uint32_t k, uint32_t w)
{
    if (ensure_loaded(ctx, k) < 0) return 0;
    if (w >= (1u << k)) return 0;
    return ctx->child_entry[w];
}

uint8_t hilbert_child_dir_ctx(hilbert_tables_ctx_t* ctx, uint32_t k, uint32_t w)
{
    if (ensure_loaded(ctx, k) < 0) return 0;
    if (w >= (1u << k)) return 0;
    return ctx->child_dir[w];
}

/* --------------------------------------------------------------------------
 * Storage API
 * -------------------------------------------------------------------------- */

int hilbert_tables_add(hilbert_tables_ctx_t* ctx,
                       const char* name, int index, int k,
                       const uint8_t* gray,
                       const uint8_t* gray_rank,
                       const uint8_t* child_entry,
                       const uint8_t* child_dir)
{
    if (!ctx || !ctx->writable) return -1;
    if (!name || index < 0) return -1;
    if (k < MIN_K || k > MAX_K) return -1;
    if (!gray || !gray_rank || !child_entry || !child_dir) return -1;

    /* Create group structure */
    if (create_groups(ctx->file_id, name, index, k) < 0) {
        return -1;
    }

    hsize_t size = (hsize_t)(1u << k);
    char path[128];

    build_dataset_path(path, sizeof(path), name, index, k, "gray");
    if (write_dataset(ctx->file_id, path, gray, size) < 0) return -1;

    build_dataset_path(path, sizeof(path), name, index, k, "gray_rank");
    if (write_dataset(ctx->file_id, path, gray_rank, size) < 0) return -1;

    build_dataset_path(path, sizeof(path), name, index, k, "child_entry");
    if (write_dataset(ctx->file_id, path, child_entry, size) < 0) return -1;

    build_dataset_path(path, sizeof(path), name, index, k, "child_dir");
    if (write_dataset(ctx->file_id, path, child_dir, size) < 0) return -1;

    /* Flush to ensure data is written */
    H5Fflush(ctx->file_id, H5F_SCOPE_GLOBAL);

    return 0;
}
