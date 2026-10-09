import Erdos948Colouring.Greedy
import Erdos948Colouring.Blocks

/-! Assembling `j + 1` disjoint blocks with well-separated windows, so that the sum over their
union of index ranges has greedy count `j + 1`. -/

namespace Erdos948

/-- Iterating `exists_block`: for every `j` there are `j + 1` blocks of consecutive indices, in
increasing order and pairwise disjoint, whose sums sit in increasing, well-separated windows. -/
private theorem exists_blocks (f a : ℕ → ℕ) (ha : StrictMono a)
    (hsmall : SmallInfinitelyOften f a) (j : ℕ) :
    ∃ s t k : Fin (j + 1) → ℕ,
      (∀ i, s i < t i) ∧
      (∀ i i' : Fin (j + 1), i < i' → t i ≤ s i') ∧
      (∀ i, 0 < ∑ l ∈ Finset.Ico (s i) (t i), a l) ∧
      (∀ i, 2 ^ (k i) ∣ ∑ l ∈ Finset.Ico (s i) (t i), a l) ∧
      (∀ i, ∑ l ∈ Finset.Ico (s i) (t i), a l < 2 ^ (k i + Gf f (k i) + 1)) ∧
      (∀ i i' : Fin (j + 1), i < i' →
        k i + Gf f (k i) + Gf f (k i + Gf f (k i)) + 1 ≤ k i') := by
  induction j with
  | zero =>
    obtain ⟨s0, t0, k0, -, hst0, -, hpos0, hdvd0, hlt0⟩ := exists_block a ha f hsmall 0 0
    have hvac : ∀ i i' : Fin 1, ¬ (i < i') := by
      intro i i' h
      rw [Fin.lt_def] at h
      have h1 := i.isLt
      have h2 := i'.isLt
      omega
    exact ⟨fun _ => s0, fun _ => t0, fun _ => k0, fun _ => hst0,
      fun i i' h => absurd h (hvac i i'), fun _ => hpos0, fun _ => hdvd0, fun _ => hlt0,
      fun i i' h => absurd h (hvac i i')⟩
  | succ j ih =>
    obtain ⟨s, t, k, hst, hts, hpos, hdvd, hlt, hsep⟩ := ih
    obtain ⟨s', t', k', hNs', hst', hKk', hpos', hdvd', hlt'⟩ :=
      exists_block a ha f hsmall (t (Fin.last j))
        (k (Fin.last j) + Gf f (k (Fin.last j)) + Gf f (k (Fin.last j) + Gf f (k (Fin.last j))) + 1)
    -- Every old block ends before the new one starts.
    have htmono : ∀ i : Fin (j + 1), t i ≤ s' := by
      intro i
      rcases eq_or_lt_of_le (Fin.le_last i) with h | h
      · exact le_of_eq (congrArg t h) |>.trans hNs'
      · exact ((hts i (Fin.last j) h).trans (hst (Fin.last j)).le).trans hNs'
    -- Every old window is separated from the new one.
    have hsepL : ∀ i : Fin (j + 1),
        k i + Gf f (k i) + Gf f (k i + Gf f (k i)) + 1 ≤ k' := by
      intro i
      have hki : k i ≤ k (Fin.last j) := by
        rcases eq_or_lt_of_le (Fin.le_last i) with h | h
        · exact le_of_eq (congrArg k h)
        · have := hsep i (Fin.last j) h
          omega
      have h1 : Gf f (k i) ≤ Gf f (k (Fin.last j)) := Gf_mono f hki
      have h2 : Gf f (k i + Gf f (k i)) ≤ Gf f (k (Fin.last j) + Gf f (k (Fin.last j))) :=
        Gf_mono f (by omega)
      omega
    refine ⟨Fin.snoc s s', Fin.snoc t t', Fin.snoc k k', ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      induction i using Fin.lastCases with
      | last => simpa using hst'
      | cast p => simpa using hst p
    · intro i i'
      induction i using Fin.lastCases with
      | last =>
        induction i' using Fin.lastCases with
        | last => intro h; exact absurd h (lt_irrefl _)
        | cast q =>
          intro h
          exfalso
          have hq := q.isLt
          rw [Fin.lt_def, Fin.val_last, Fin.val_castSucc] at h
          omega
      | cast p =>
        induction i' using Fin.lastCases with
        | last => intro _; simpa using htmono p
        | cast q =>
          intro h
          rw [Fin.castSucc_lt_castSucc_iff] at h
          simpa using hts p q h
    · intro i
      induction i using Fin.lastCases with
      | last => simpa using hpos'
      | cast p => simpa using hpos p
    · intro i
      induction i using Fin.lastCases with
      | last => simpa using hdvd'
      | cast p => simpa using hdvd p
    · intro i
      induction i using Fin.lastCases with
      | last => simpa using hlt'
      | cast p => simpa using hlt p
    · intro i i'
      induction i using Fin.lastCases with
      | last =>
        induction i' using Fin.lastCases with
        | last => intro h; exact absurd h (lt_irrefl _)
        | cast q =>
          intro h
          exfalso
          have hq := q.isLt
          rw [Fin.lt_def, Fin.val_last, Fin.val_castSucc] at h
          omega
      | cast p =>
        induction i' using Fin.lastCases with
        | last => intro _; simpa using hsepL p
        | cast q =>
          intro h
          rw [Fin.castSucc_lt_castSucc_iff] at h
          simpa using hsep p q h

theorem exists_finiteSum_greedy (f a : ℕ → ℕ) (ha : StrictMono a)
    (hsmall : SmallInfinitelyOften f a) (j : ℕ) :
    ∃ S : Finset ℕ, S.Nonempty ∧ greedy (Gf f) (∑ i ∈ S, a i) = j + 1 := by
  classical
  obtain ⟨s, t, k, hst, hts, hpos, hdvd, hlt, hsep⟩ := exists_blocks f a ha hsmall j
  refine ⟨(Finset.univ : Finset (Fin (j + 1))).biUnion (fun i => Finset.Ico (s i) (t i)), ?_, ?_⟩
  · exact ⟨s 0, Finset.mem_biUnion.2 ⟨0, Finset.mem_univ _, Finset.mem_Ico.2 ⟨le_rfl, hst 0⟩⟩⟩
  · have key : ∀ u v : Fin (j + 1), u < v →
        Disjoint (Finset.Ico (s u) (t u)) (Finset.Ico (s v) (t v)) := by
      intro u v huv
      refine Finset.disjoint_left.2 ?_
      intro l hl hl'
      rw [Finset.mem_Ico] at hl hl'
      have := hts u v huv
      omega
    have hdisj : (↑(Finset.univ : Finset (Fin (j + 1))) : Set (Fin (j + 1))).PairwiseDisjoint
        (fun i => Finset.Ico (s i) (t i)) := by
      intro x _ y _ hxy
      rcases lt_or_gt_of_ne hxy with h | h
      · exact key x y h
      · exact (key y x h).symm
    rw [Finset.sum_biUnion hdisj]
    exact greedy_sum_blocks (Gf f) (Gf_mono f) (j + 1)
      (fun i => ∑ l ∈ Finset.Ico (s i) (t i), a l) k hpos hdvd hlt hsep

end Erdos948
