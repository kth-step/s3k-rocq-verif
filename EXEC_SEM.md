# ExecSem: Rocq port of the HOL4 executable semantics

This directory ports the executable semantics of S3K from the HOL4
specification in [`s3k-verif`](https://github.com/kth-step/s3k-verif), last compared against
`s3k-verif` commit `a7ec3db`:

| Rocq file  | HOL4 source                    |
|------------|--------------------------------|
| `config.v` | `src/core/configScript.sml`    |
| `proc.v`   | `src/core/procScript.sml`      |
| `cap.v`    | `src/core/capScript.sml`       |
| `sched.v`  | `src/core/schedScript.sml`     |
| `kernel.v` | `src/core/kernelScript.sml`    |
| `exec.v`   | `src/semantics/execScript.sml` |
| `util.v`   | (word conversions; no HOL4 counterpart) |

The port follows the HOL4 definitions one-to-one, keeping their names, argument
order and case structure. The following documents some inevitable semantics
differences between this port and the HOL4 spec, and some notable
representation choices.

## Semantics differences

### Partial functions in HOL4 made total

Some HOL4 functions used in the spec are partial while Rocq functions must be
total, so the port picks a concrete value. Although any HOL4 theorem about
these functions still holds in Rocq.

#### `EL` → `!!!`

HOL4's `EL n l` is defined through `HD`/`TL`, which are unspecified on `[]`, so
`EL n l` is unspecified when `n ≥ LENGTH l`. The port uses Std++'s total lookup
`l !!! n`, which returns the `Inhabited` default when the index is out of range.
For `int64` that default is `Int64.zero` (`int64_inhabited` in `util.v`).

`EL` occurs in two places:

- `proc_reg_get` (`proc.v`): `proc.(pregs) !!! reg`.
- `exec_syscall_retl` (`exec.v`): reading the PC, `proc.(pregs) !!! reg_pc`.

Within the syscall handler, every use is in range:

- `exec_syscall_retl` checks that `length proc.(pregs) = REG_CNT`.
- `proc_get_args` checks that there are at least 20 registers.
- `ptable_reg_get` checks `reg < length proc.(pregs)`.
- `exec_syscall_mon_reg_get` rejects `reg_word ≥ REG_CNT`.

The difference is observable only when `exec_mon_reg_get` is called directly
with `reg ≥ REG_CNT`. However this does not affect the top-level reasoning as
it is only called by `exec_syscall_mon_reg_get` which does the check.

#### `num2<enum>`

For an enumeration datatype, HOL4's `Datatype` generates a bijection with an
initial segment of `num` (`EnumType.sml`): `<ty>2num` and `num2<ty>`. Rocq
generates neither, so the port writes the ones it needs by hand.

In HOL4, `num2pmpreg_t n` is unspecified for `n ≥ 8`. The port maps every such
`n` to `PMP_REG7`. Its only use, `word2pmpreg`, guards it with `n < PMP_CNT`,
so the difference is not observable in the semantics.

#### `MOD` by zero

`exec_sched` computes `t MOD TSLOT_CNT`. HOL4's `MOD` is only specified for a
positive divisor, so `t MOD 0` is unspecified. Rocq's `Nat.modulo` defines
`t mod 0 = t`. In both, `kernel_config` forces `TSLOT_CNT > 0` (see
[Configuration](#configuration)), so the case never arises.

## Representation choices

- **Words → CompCert's `Integers`.** `word64` is `int64`, and `word8` is
  `byte`. The conversions are in `util.v`:

  | HOL4 | Rocq |
  |---|---|
  | `w2n` | `int64_to_nat` (`Z.to_nat ∘ Int64.unsigned`) |
  | `n2w` | `nat_to_int64` (`Int64.repr ∘ Z.of_nat`; wraps modulo 2⁶⁴, like `n2w`) |
  | `w2w : word64 → word8` | `int64_to_byte` (truncation) |
  | `w2w : word8 → word64` | `byte_to_int64` (zero extension) |
  | `≤₊` | `Int64.cmpu Cle` |
  | `>>>`, `<<`, `&&`, `\|\|`, `??` | `>>u₆₄`, `<<₆₄`, `&₆₄`, `\|₆₄`, `^₆₄` (Barocq's `IntopNotations`), and `&₈`, `\|₈` (`util.v`) |

- **`perm_t set` → `gset perm_t`.** HOL4 sets are predicates. The port uses
  Std++'s finite sets, which have decidable `∈`/`⊆` (needed by `decide`) and
  Leibniz equality.
- **Boolean conditions.** HOL4 `if` on a `bool`-valued formula becomes
  `if decide (…)`, or `bool_decide (…)` where a `bool` is stored.

## Renamings

- The `pmpreg_t` constructors `PMPREG0`…`PMPREG7` are `PMP_REG0`…`PMP_REG7`.
- In `exec_mem_derive`, the parameters `mbase`, `msize` and `mperm` are renamed
  to `base`, `size` and `perm`, so that they do not shadow the projections of
  `mem_t`.

