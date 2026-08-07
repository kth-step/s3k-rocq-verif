# Specification and verification of S3K using the Rocq Prover
[![Docker CI](https://github.com/kth-step/s3k-rocq-verif/actions/workflows/docker-action.yml/badge.svg)](https://github.com/kth-step/s3k-rocq-verif/actions/workflows/docker-action.yml)

[S3K](https://github.com/kth-step/s3k) is an experimental bare-metal capability-based separation kernel for RISC-V.
This repository is about specification and verification of S3K using the [Rocq Prover](https://rocq-prover.org).
In particular, we take as specification the [HOL4 formalization](https://github.com/kth-step/s3k-verif) of the S3K executable
semantics (ported to Rocq), and verify that an implementation of S3K in the [Barocq](https://gitlab.inria.fr/cchavano/barocq)
programming language is a refinement of this specification.


## Project Structure

### Specification (`theories/ExecSem`)

The executable semantics is ported manually from the [s3k-verif](https://github.com/kth-step/s3k-verif) project
in HOL4, targeting mainly the definitions found in [`src/semantics/execScript.sml`](https://github.com/kth-step/s3k-verif/blob/main/src/semantics/execScript.sml).
We keep the translation as close as possible and depend only on the [std++](https://gitlab.mpi-sws.org/iris/stdpp) library.

### Implementation (`src/` and `theories/Barocq`)

The implementation of the S3K kernel in Barocq is found in `src/`. We use Barocq as the
implementation language because it has a simple, functional formal semantics,
can be compiled to CompCert C and is equipped with a shallow embedding generator. Note
that this implementation on its own is not executable, since it depends on
additional C sources that are currently not included in this repository.

The target of our verification is the Barocq program's shallow embedding inside Rocq (`theories/Barocq/S3K_ShallowR.v`),
automatically generated from source code by the Barocq compiler.
We bundle the Barocq-semantics related dependency in `theories/BarocqComp`.

### Verification (`theories/Verif`)

The verification work is structured as follows:
```txt
 Verif
 ├── axioms.v            # Axioms
 ├── barocq_aux.v        # Barocq helper lemmas
 ├── bridge.v            # Helper definitions bridging the concrete and abstract S3K semantics
 ├── gen_tactics.v       # General tactics
 ├── refine_map.v        # Refinement mappings for S3K datatypes
 ├── refine_tactics.v    # Domain-specific tactics for S3K refinement proofs
 ├── refine_util.v       # Refinement utility definitions
 └── refinements.v       # S3K refinement theorems
```

The proof strategy is to show that the Barocq implementation is a safe forward
simulation for the abstract specification. `refinements.v` contains such forward
simulation theorems. Currently, the correctness of four monitor capability operations
is proved. Extending the verification to cover more kernel operations is work
in progress.

## Build

To build using opam, run `opam install .`.

To build using make, first ensure that you have all dependencies installed, and
then run `make`. 
