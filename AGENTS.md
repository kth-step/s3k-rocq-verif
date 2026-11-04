# AGENTS.md

Rocq specification and verification of the S3K separation kernel. See `README.md` for background.

## Layout

- `theories/ExecSem/` — specification: executable semantics of S3K (package `rocq-s3k-exec-sem`, logical path `S3K.ExecSem`).
- `theories/Barocq/` — shallow embedding in Rocq of the Barocq implementation (package `rocq-s3k-barocq`, logical path `S3K.Barocq`).
- `theories/Verif/` — refinement proofs of the shallow embedding against the specification (package `rocq-s3k-verif`, logical path `S3K.Verif`).
- `src/` — Barocq sources (`.brc`) of the implementation.

## Dependency rules

The opam packages encode which project parts may depend on which. Keep it that way:

- `ExecSem` and `Barocq` must not depend on each other or on `Verif`.
- `Verif` may depend on both `ExecSem` and `Barocq`.

`theories/Barocq/S3K_ShallowR.v` is generated from `src/` by the Barocq compiler. Do not edit it by hand.

## Conventions

- When Std++ and Rocq's Stdlib both provide a definition, lemma or notation for the same thing, use the Std++ one. Std++ redefines things from Stdlib only deliberately, so its version is the intended one.

## Dependencies

- The `*.opam` files are the authoritative list of dependencies (with versions and `pin-depends`).
- Assume a dedicated opam switch with these dependencies already installed. Do not install, upgrade or pin packages unless asked.
- Of the two packages in the Barocq repository, only `rocq-barocq-lib` is needed to build. `rocq-barocq` (the compiler) is needed only to regenerate `S3K_ShallowR.v`.
- `rocq-barocq` installs only if the build directory of `compcert-brc` is still around. If its install fails for that reason, rebuild `compcert-brc` keeping its build directory, then retry:
  ```
  opam reinstall --keep-build-dir compcert-brc
  opam install rocq-barocq
  ```

## Builds

| Build | Command | Purpose |
|---|---|---|
| Dune | `dune build` | Recommended for agents. Hash-based caching, better job scheduling. Local use only. |
| Root make | `make` | Local development, file list from `_RocqProject`. |
| Per-package make | `make -C theories/<ExecSem\|Barocq\|Verif>` | What the opam packages (and CI) use, file list from each directory's `Make`. |

Notes:

- `dune build` is the recommended default for the edit-check loop. Use a different workflow (e.g. a Rocq MCP server or an IDE-style checker) when the user prefers or has set one up.
- Dune and root make build everything as a single theory `S3K`, so they do **not** enforce the dependency rules above. CI enforces them through the per-package builds, so there is no need to run `make -C theories/...` locally. Instead, do the static checks below before opening a pull request.
- File lists are maintained by hand in two places: `_RocqProject` and each subdirectory's `Make`. When adding, removing or renaming a `.v` file, update both.
- Dune builds every `.v` file under `theories/`. To leave a file out of the Dune build, add an explicit exclusion in `theories/dune`.
- When adding a dependency, update the relevant `*.opam` file(s) and the `(theories ...)` field in `theories/dune`.

## Before opening a pull request

Run these static checks so that CI doesn't fail on something cheap to catch. Each one should print nothing.

```sh
# Dependency rules: ExecSem and Barocq must not import other project parts
grep -nE 'S3K\.(Verif|Barocq)' theories/ExecSem/*.v
grep -nE 'S3K\.(Verif|ExecSem)' theories/Barocq/*.v

# File lists: each Make and _RocqProject must match the .v files on disk
for d in ExecSem Barocq Verif; do
  diff <(cd theories/$d && ls *.v | sort) <(grep '\.v$' theories/$d/Make | sort)
done
diff <(ls theories/*/*.v | sort) <(grep '\.v$' _RocqProject | sort)
```

Also check that any new external library (a new `From <lib> Require`) is listed in the `depends` of the `*.opam` file for the package that uses it.
