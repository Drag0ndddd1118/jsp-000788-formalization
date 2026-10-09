import Mathlib

/-!
# Erdős Problem 948: colourings whose sparse sequences have finite sums of every colour

Erdős and Galvin asked whether there are `f : ℕ → ℕ` and `k` such that every `k`-colouring of `ℕ`
admits a sequence `a₁ < a₂ < ⋯` with `a n < f n` for infinitely many `n` whose nonempty finite
subset sums miss some colour. The answer is no (2026): for every `f` there is a colouring of `ℕ`
with countably many colours such that every such sequence has finite subset sums of every colour.

The colouring: fix a window function `G`. The colour of `n ≥ 1` is one less than the number of
windows `[v, v + G v]` (`v` the position of the lowest set binary digit of the remaining number)
needed to cover the binary digits of `n` greedily from the bottom.
-/

namespace Erdos948

/-- Nonempty finite subset sums of a sequence. -/
def FiniteSums (a : ℕ → ℕ) : Set ℕ := {m | ∃ S : Finset ℕ, S.Nonempty ∧ m = ∑ i ∈ S, a i}

/-- `a n < f n` for infinitely many `n`. -/
def SmallInfinitelyOften (f a : ℕ → ℕ) : Prop := ∀ N, ∃ n, N ≤ n ∧ a n < f n

/-- Clear the binary digits of `n` below position `t`. -/
def clearLow (n t : ℕ) : ℕ := n / 2 ^ t * 2 ^ t

/-- The top of the window of `n`: `v + G v` where `v` is the position of the lowest set digit. -/
def windowTop (G : ℕ → ℕ) (n : ℕ) : ℕ := padicValNat 2 n + G (padicValNat 2 n)

/-- Fuelled greedy window count. -/
def greedyFuel (G : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, n => if n = 0 then 0 else 1 + greedyFuel G fuel (clearLow n (windowTop G n + 1))

/-- Greedy number of windows `[v, v + G v]` needed to cover the binary digits of `n`
(`n` units of fuel always suffice). -/
def greedy (G : ℕ → ℕ) (n : ℕ) : ℕ := greedyFuel G n n

/-- The colouring with countably many colours: greedy count minus one. -/
def colour (G : ℕ → ℕ) (n : ℕ) : ℕ := greedy G n - 1

/-- A monotone envelope of `f`. -/
def env (f : ℕ → ℕ) (n : ℕ) : ℕ := ∑ i ∈ Finset.range (n + 1), f i

/-- The window function built from `f`. -/
def Gf (f : ℕ → ℕ) (k : ℕ) : ℕ := Nat.log 2 (2 ^ (k + 1) * env f (2 ^ (k + 2))) + 1

end Erdos948
