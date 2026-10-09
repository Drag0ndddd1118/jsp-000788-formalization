# JSP-000788 — Lean 4 formalization

A machine-checked Lean 4 formalization and disproof of the question in Erdős Problem #948:

> *Under a finite coloring of the positive integers, can the specified sparse sequence be found whose subset sums omit at least one color?*

Catalog entry JSP-000788 (number theory / Ramsey theory). Erdős and Galvin ([ErGa91]) asked whether there exist a growth rate function $f : \mathbb{N} \to \mathbb{N}$ and an integer $k \ge 1$ such that in every $k$-colouring of $\mathbb{N}$ there exists a strictly increasing sequence $a_1 < a_2 < \cdots$ with $a_n < f(n)$ infinitely often whose non-empty finite subset sums omit at least one colour.

The problem was resolved in the negative: Liam Price and GPT Pro showed that for every growth function $f$ and every $k \ge 1$, there exists a $k$-colouring of $\mathbb{N}$ such that every such sparse sequence has non-empty finite subset sums achieving **every** colour class.

This repository contains the self-contained, machine-checked Lean 4 formalization proving this negative resolution.

## Statement of record — `Challenge.lean`

`Challenge.lean` declares the definitions the problem is phrased with and the proposition `jsp000788Statement`. It proves nothing, so a reviewer has only to read that one file to judge *what* has been claimed.

```lean
def FiniteSums (a : ℕ → ℕ) : Set ℕ :=
  {m | ∃ S : Finset ℕ, S.Nonempty ∧ m = ∑ i ∈ S, a i}

def SmallInfinitelyOften (f a : ℕ → ℕ) : Prop :=
  ∀ N, ∃ n, N ≤ n ∧ a n < f n

def jsp000788Statement : Prop :=
  ¬ ∃ (f : ℕ → ℕ) (k : ℕ), 0 < k ∧
    ∀ c : ℕ → Fin k,
      ∃ a : ℕ → ℕ, StrictMono a ∧ SmallInfinitelyOften f a ∧
        ∃ j : Fin k, ∀ m ∈ FiniteSums a, c m ≠ j
```

## Proof — `Submission.lean`

`Submission.lean` imports `Challenge.lean`, so the proof and the statement refer to the *same* `jsp000788Statement` constant and cannot drift apart. The top-level result is

```lean
theorem jsp_000788_solved : jsp000788Statement
```

The underlying construction builds an explicit greedy-window colouring:
1. **Window function & Greedy clustering** (`Erdos948Colouring.Definitions`, `Greedy`): Defines the window function $G_f$ and the fuel-based greedy window count $\mathrm{greedy}(G, n)$, proving fuel invariance and digit clearing properties.
2. **Pigeonhole block lemma** (`Erdos948Colouring.Blocks`): For any sparse sequence below $f$ infinitely often, extracts consecutive block sums whose binary digits concentrate in a single window beyond any given bound.
3. **Disjoint block assembly** (`Erdos948Colouring.Assembly`): Iterates the block lemma to construct $j + 1$ disjoint, well-separated blocks whose sum attains greedy count $j + 1$.
4. **Main colouring theorem** (`Erdos948Colouring.Main`): Establishes `erdos_948_nat` for countably many colours, descends via modulo arithmetic to `erdos_948` for any $k \ge 1$, and deduces the top-level disproof `erdos_948_closed`.

The file contains no `sorry`, no `admit`, no `axiom`, no `opaque`, no `unsafe`, no `partial`, and no `native_decide`.
`check.py` type-checks the bridge

```lean
example : jsp000788Statement := jsp_000788_solved
```

and audits the axioms of `jsp_000788_solved`.

## Build and check

```sh
lake exe cache get   # Mathlib oleans
lake build
python3 check.py
```

Toolchain: `leanprover/lean4:v4.34.0` (commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`); Mathlib is pinned to `5ed2965256430c3649e86755f9576b54eca72435` (tag `v4.34.0`) in `lake-manifest.json`.

`check.py` runs the build, rejects `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `partial` and `native_decide` in `Submission.lean`, type-checks the bridge above — which can only succeed if the submission proves exactly the proposition that `Challenge.lean` states — and audits `#print axioms jsp_000788_solved`, which reports strictly `[propext, Classical.choice, Quot.sound]`, the three standard axioms of Lean's foundational logic and nothing else. The same audit runs in CI on every push (`.github/workflows/lean_action_ci.yml`).

## Repository layout

| File | Role |
| --- | --- |
| `Challenge.lean` | Statement of record: definitions and the proposition, no proof |
| `Submission.lean` | The proof; imports `Challenge.lean` |
| `Erdos948Colouring/` | Self-contained modular proof development (`Definitions`, `Greedy`, `Blocks`, `Assembly`, `Main`) |
| `check.py` | Build, forbidden-token scan, bridge type-check, axiom audit |
| `.github/workflows/lean_action_ci.yml` | CI: `lean-action` followed by `check.py` |
| `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` | Build configuration and pinned dependencies |

## Attribution

- **Mathematical result.** Liam Price and GPT Pro (negative answer), prompted by Erdős–Galvin [ErGa91], as recorded in the catalog entry. This repository claims no credit for the mathematical discovery.
- **Lean 4 formalization.** Qin Zhao (GitHub: [Drag0ndddd1118](https://github.com/Drag0ndddd1118)), who owns this repository. The formalization development is maintained and packaged with complete type-checked bridges, reproducible toolchain, and CI automation.

## License

Apache License 2.0 — see [LICENSE](LICENSE).
