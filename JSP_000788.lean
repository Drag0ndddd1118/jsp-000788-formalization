import Erdos948

/-- Formal Lean 4 bridge theorem for JSP-000788 (Erdős Problem #948). -/
theorem jsp_000788_solved :
    ¬ (∃ (f : ℕ → ℕ) (k : ℕ), 0 < k ∧
      ∀ colouring : ℤ → Fin k,
        ∃ a : ℕ → ℤ, StrictMono a ∧
          {n | a n < (f n : ℤ)}.Infinite ∧
          ∃ omitted : Fin k, ∀ I : Finset ℕ,
            colouring (∑ i ∈ I, a i) ≠ omitted) :=
  Erdos948.not_erdos_948

#print axioms jsp_000788_solved
-- 'jsp_000788_solved' depends on axioms: [propext, Classical.choice, Quot.sound]
