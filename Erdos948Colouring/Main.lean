import Erdos948Colouring.Assembly

/-! # Erdős Problem 948 -/

namespace Erdos948

/-- The countable-colour form: for every `f` there is a colouring of `ℕ` with colours in `ℕ`
such that every strictly increasing sequence with `a n < f n` infinitely often has nonempty
finite subset sums of every colour. -/
theorem erdos_948_nat (f : ℕ → ℕ) :
    ∃ c : ℕ → ℕ, ∀ a : ℕ → ℕ, StrictMono a → SmallInfinitelyOften f a →
      ∀ j : ℕ, ∃ m ∈ FiniteSums a, c m = j := by
  refine ⟨colour (Gf f), fun a ha hsmall j => ?_⟩
  obtain ⟨S, hS, hg⟩ := exists_finiteSum_greedy f a ha hsmall j
  exact ⟨∑ i ∈ S, a i, ⟨S, hS, rfl⟩, by simp [colour, hg]⟩

/-- The finite-colour form: for every `f` and every `k ≥ 1` there is a `k`-colouring of `ℕ` such
that every strictly increasing sequence with `a n < f n` infinitely often has nonempty finite
subset sums of every colour. -/
theorem erdos_948 (f : ℕ → ℕ) (k : ℕ) (hk : 0 < k) :
    ∃ c : ℕ → Fin k, ∀ a : ℕ → ℕ, StrictMono a → SmallInfinitelyOften f a →
      ∀ j : Fin k, ∃ m ∈ FiniteSums a, c m = j := by
  obtain ⟨c, hc⟩ := erdos_948_nat f
  refine ⟨fun n => ⟨c n % k, Nat.mod_lt _ hk⟩, fun a ha hsmall j => ?_⟩
  obtain ⟨m, hm, hcm⟩ := hc a ha hsmall j.val
  refine ⟨m, hm, ?_⟩
  ext
  simp [hcm, Nat.mod_eq_of_lt j.isLt]

/-- Erdős Problem 948 in the form asked (Erdős–Galvin): there are no `f` and `k ≥ 1` such that
every `k`-colouring of `ℕ` admits a strictly increasing sequence, below `f` infinitely often, whose
nonempty finite subset sums miss a colour. -/
theorem erdos_948_closed :
    ¬ ∃ (f : ℕ → ℕ) (k : ℕ), 0 < k ∧ ∀ c : ℕ → Fin k, ∃ a : ℕ → ℕ, StrictMono a ∧
      SmallInfinitelyOften f a ∧ ∃ j : Fin k, ∀ m ∈ FiniteSums a, c m ≠ j := by
  rintro ⟨f, k, hk, hbad⟩
  obtain ⟨c, hc⟩ := erdos_948 f k hk
  obtain ⟨a, ha, hsmall, j, hj⟩ := hbad c
  obtain ⟨m, hm, hcm⟩ := hc a ha hsmall j
  exact hj m hm hcm

end Erdos948
