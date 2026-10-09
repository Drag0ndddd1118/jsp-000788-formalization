import Erdos948Colouring.Definitions

/-! The pigeonhole block lemma: a sparse sequence has a block of consecutive terms, beyond any
given index, whose sum has all binary digits in one window `[k, k + Gf f k]` with `k` beyond any
given bound. -/

namespace Erdos948

/-- A term is at most the envelope (private copy, proved again in `Greedy.lean`). -/
private theorem le_env_aux (f : ℕ → ℕ) (n : ℕ) : f n ≤ env f n := by
  classical
  refine Finset.single_le_sum (f := fun i => f i) (fun i _ => Nat.zero_le _) ?_
  simp

/-- The envelope is monotone (private copy, proved again in `Greedy.lean`). -/
private theorem env_mono_aux (f : ℕ → ℕ) {m n : ℕ} (h : m ≤ n) : env f m ≤ env f n := by
  classical
  unfold env
  exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (Nat.succ_le_succ h))

theorem exists_block (a : ℕ → ℕ) (ha : StrictMono a) (f : ℕ → ℕ)
    (hsmall : SmallInfinitelyOften f a) (N K : ℕ) :
    ∃ s t k : ℕ, N ≤ s ∧ s < t ∧ K ≤ k ∧ 0 < ∑ i ∈ Finset.Ico s t, a i ∧
      2 ^ k ∣ ∑ i ∈ Finset.Ico s t, a i ∧ ∑ i ∈ Finset.Ico s t, a i < 2 ^ (k + Gf f k + 1) := by
  classical
  -- Choose a good index `n`, far enough out.
  obtain ⟨n, hnge, hafn⟩ := hsmall (max (N + 1 + 2 ^ (K + 1)) (2 * N + 4))
  have hn1 : N + 1 + 2 ^ (K + 1) ≤ n := le_trans (le_max_left _ _) hnge
  have hn2 : 2 * N + 4 ≤ n := le_trans (le_max_right _ _) hnge
  have hpK : 0 < 2 ^ (K + 1) := by positivity
  have hdpos : 0 < n - (N + 1) := by omega
  -- The scale `k`.
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = Nat.log 2 (n - (N + 1)) := ⟨_, rfl⟩
  have hkle : 2 ^ k ≤ n - (N + 1) := by
    rw [hk]; exact Nat.pow_log_le_self 2 (by omega)
  have hklt : n - (N + 1) < 2 ^ (k + 1) := by
    rw [hk]; exact Nat.lt_pow_succ_log_self (by norm_num) _
  have hKk : K + 1 ≤ k := by
    rw [hk]; exact Nat.le_log_of_pow_le (by norm_num) (by omega)
  have hpk : 0 < 2 ^ k := by positivity
  -- Pigeonhole on partial sums modulo `2 ^ k`.
  have hcard : (Finset.range (2 ^ k)).card < (Finset.Icc (N + 1) n).card := by
    simp only [Finset.card_range, Nat.card_Icc]
    omega
  have hmaps : Set.MapsTo (fun i => (∑ l ∈ Finset.Ico (N + 1) i, a l) % 2 ^ k)
      ↑(Finset.Icc (N + 1) n) ↑(Finset.range (2 ^ k)) := by
    intro i _
    simp only [Finset.coe_range, Set.mem_Iio]
    exact Nat.mod_lt _ hpk
  obtain ⟨x, hx, y, hy, hxy, hmodxy⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  obtain ⟨s, t, hst, hsmem, htmem, hmod⟩ :
      ∃ s t : ℕ, s < t ∧ s ∈ Finset.Icc (N + 1) n ∧ t ∈ Finset.Icc (N + 1) n ∧
        (∑ l ∈ Finset.Ico (N + 1) s, a l) % 2 ^ k
          = (∑ l ∈ Finset.Ico (N + 1) t, a l) % 2 ^ k := by
    rcases lt_or_gt_of_ne hxy with h | h
    · exact ⟨x, y, h, hx, hy, hmodxy⟩
    · exact ⟨y, x, h, hy, hx, hmodxy.symm⟩
  simp only [Finset.mem_Icc] at hsmem htmem
  -- The block sum is the difference of two partial sums.
  have hsplit : (∑ l ∈ Finset.Ico (N + 1) s, a l) + (∑ l ∈ Finset.Ico s t, a l)
      = ∑ l ∈ Finset.Ico (N + 1) t, a l :=
    Finset.sum_Ico_consecutive a hsmem.1 hst.le
  have hle : (∑ l ∈ Finset.Ico (N + 1) s, a l) ≤ ∑ l ∈ Finset.Ico (N + 1) t, a l := by omega
  have hblock : (∑ l ∈ Finset.Ico s t, a l)
      = (∑ l ∈ Finset.Ico (N + 1) t, a l) - ∑ l ∈ Finset.Ico (N + 1) s, a l := by omega
  refine ⟨s, t, k, by omega, hst, by omega, ?_, ?_, ?_⟩
  · -- Positivity: the block contains the index `s ≥ 1`, and `a s ≥ s`.
    have hmem : s ∈ Finset.Ico s t := Finset.mem_Ico.mpr ⟨le_rfl, hst⟩
    have h1 : a s ≤ ∑ l ∈ Finset.Ico s t, a l :=
      Finset.single_le_sum (f := fun i => a i) (fun i _ => Nat.zero_le _) hmem
    have h2 : s ≤ a s := ha.le_apply
    omega
  · -- Divisibility, from equal residues.
    rw [hblock]
    exact (Nat.modEq_iff_dvd' hle).mp hmod
  · -- The upper bound.
    have hterm : ∀ l ∈ Finset.Ico s t, a l ≤ a n := by
      intro l hl
      rw [Finset.mem_Ico] at hl
      exact ha.monotone (by omega)
    have hb1 : (∑ l ∈ Finset.Ico s t, a l) ≤ (t - s) * a n := by
      have := Finset.sum_le_card_nsmul (Finset.Ico s t) a (a n) hterm
      simpa [Nat.card_Ico, smul_eq_mul] using this
    have hb2 : (t - s) * a n ≤ (n - (N + 1)) * a n :=
      Nat.mul_le_mul (by omega) le_rfl
    have hfpos : 0 < f n := by omega
    have hb3 : (n - (N + 1)) * a n < 2 ^ (k + 1) * f n :=
      lt_of_le_of_lt (Nat.mul_le_mul le_rfl hafn.le) (mul_lt_mul_of_pos_right hklt hfpos)
    -- `n` is below `2 ^ (k + 2)`.
    have hnlt : n < 2 ^ (k + 2) := by
      have hpow : (2 : ℕ) ^ (k + 2) = 2 * 2 ^ (k + 1) := by ring
      omega
    have hb4 : 2 ^ (k + 1) * f n ≤ 2 ^ (k + 1) * env f (2 ^ (k + 2)) :=
      Nat.mul_le_mul le_rfl ((le_env_aux f n).trans (env_mono_aux f hnlt.le))
    have hb5 : 2 ^ (k + 1) * env f (2 ^ (k + 2)) < 2 ^ Gf f k := by
      unfold Gf
      exact Nat.lt_pow_succ_log_self (by norm_num) _
    have hb6 : (2 : ℕ) ^ Gf f k ≤ 2 ^ (k + Gf f k + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    calc (∑ l ∈ Finset.Ico s t, a l) ≤ (t - s) * a n := hb1
      _ ≤ (n - (N + 1)) * a n := hb2
      _ < 2 ^ (k + 1) * f n := hb3
      _ ≤ 2 ^ (k + 1) * env f (2 ^ (k + 2)) := hb4
      _ < 2 ^ Gf f k := hb5
      _ ≤ 2 ^ (k + Gf f k + 1) := hb6

end Erdos948
