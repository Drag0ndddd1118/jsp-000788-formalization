/-
  The Justin Sun Prize (孙宇晨奖) — JSP-000788

  **Challenge.lean: the statement of record.**

  This file declares the definitions the problem is phrased with, and the proposition
  `jsp000788Statement`. It proves nothing. `Submission.lean` imports this file, so the proof and
  the statement refer to the *same* constant and the statement cannot drift between them.
  `check.py` type-checks the bridge

      example : jsp000788Statement := jsp_000788_solved

  and audits the axioms the submitted proof depends on. A reviewer has only to read this
  file in order to judge *what* has been claimed.
-/

import Mathlib

namespace JSP000788

/-- Nonempty finite subset sums of a sequence `a : ℕ → ℕ`. -/
def FiniteSums (a : ℕ → ℕ) : Set ℕ :=
  {m | ∃ S : Finset ℕ, S.Nonempty ∧ m = ∑ i ∈ S, a i}

/-- A sequence `a` satisfies `a n < f n` for infinitely many `n`. -/
def SmallInfinitelyOften (f a : ℕ → ℕ) : Prop :=
  ∀ N, ∃ n, N ≤ n ∧ a n < f n

/-- **Statement of record for JSP-000788 (Erdős Problem #948).**

Question: Under a finite coloring of the positive integers, can the specified sparse
sequence be found whose subset sums omit at least one color?

Erdős and Galvin asked whether there exist a growth function `f : ℕ → ℕ` and `k ≥ 1` such that
every `k`-colouring of `ℕ` admits a strictly increasing sequence `a` below `f` infinitely often
whose nonempty finite subset sums miss at least one colour.

The answer is NO (disproved): for every `f` and `k ≥ 1`, there exists a `k`-colouring whose
nonempty finite subset sums for every such sparse sequence cover every colour. Hence no such
pair `(f, k)` exists. -/
def jsp000788Statement : Prop :=
  ¬ ∃ (f : ℕ → ℕ) (k : ℕ), 0 < k ∧
    ∀ c : ℕ → Fin k,
      ∃ a : ℕ → ℕ, StrictMono a ∧ SmallInfinitelyOften f a ∧
        ∃ j : Fin k, ∀ m ∈ FiniteSums a, c m ≠ j

end JSP000788
