import Erdos948Colouring.Definitions

/-! Properties of the greedy window count. -/

namespace Erdos948

theorem clearLow_lt (n t : ℕ) (hn : n ≠ 0) (ht : padicValNat 2 n < t) : clearLow n t < n := by
  have hdvd : ¬ ((2 : ℕ) ^ t ∣ n) := by
    rw [padicValNat_dvd_iff_le hn]
    omega
  have hmod : n % 2 ^ t ≠ 0 := fun h => hdvd (Nat.dvd_of_mod_eq_zero h)
  have key : n / 2 ^ t * 2 ^ t + n % 2 ^ t = n := by
    rw [Nat.mul_comm]; exact Nat.div_add_mod n (2 ^ t)
  unfold clearLow
  omega

theorem greedy_zero (G : ℕ → ℕ) : greedy G 0 = 0 := rfl

/-- The fuelled greedy count does not depend on the amount of fuel, as long as there is
enough of it. -/
theorem greedyFuel_eq_of_le (G : ℕ → ℕ) :
    ∀ n fuel fuel' : ℕ, n ≤ fuel → n ≤ fuel' → greedyFuel G fuel n = greedyFuel G fuel' n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro fuel fuel' h1 h2
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · cases fuel <;> cases fuel' <;> simp [greedyFuel]
    · obtain ⟨f1, rfl⟩ : ∃ f1, fuel = f1 + 1 := ⟨fuel - 1, by omega⟩
      obtain ⟨f2, rfl⟩ : ∃ f2, fuel' = f2 + 1 := ⟨fuel' - 1, by omega⟩
      have hne : n ≠ 0 := by omega
      have hlt : clearLow n (windowTop G n + 1) < n := by
        refine clearLow_lt n _ hne ?_
        unfold windowTop
        omega
      simp only [greedyFuel, hne, ite_false]
      exact congrArg (fun x => 1 + x) (ih _ hlt f1 f2 (by omega) (by omega))

/-- The recursion equation of the greedy count. -/
theorem greedy_eq (G : ℕ → ℕ) (n : ℕ) (hn : n ≠ 0) :
    greedy G n = 1 + greedy G (clearLow n (windowTop G n + 1)) := by
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
  have hlt : clearLow (p + 1) (windowTop G (p + 1) + 1) < p + 1 := by
    refine clearLow_lt _ _ hn ?_
    unfold windowTop
    omega
  show greedyFuel G (p + 1) (p + 1) = 1 + greedy G (clearLow (p + 1) (windowTop G (p + 1) + 1))
  simp only [greedyFuel, hn, ite_false]
  exact congrArg (fun x => 1 + x)
    (greedyFuel_eq_of_le G _ p _ (by omega) le_rfl)

theorem env_mono (f : ℕ → ℕ) : Monotone (env f) := by
  intro a b hab
  unfold env
  refine Finset.sum_le_sum_of_subset ?_
  intro x hx
  simp only [Finset.mem_range] at hx ⊢
  omega

theorem le_env (f : ℕ → ℕ) (n : ℕ) : f n ≤ env f n :=
  Finset.single_le_sum (f := fun i => f i) (fun _ _ => Nat.zero_le _) (Finset.self_mem_range_succ n)

theorem Gf_mono (f : ℕ → ℕ) : Monotone (Gf f) := by
  intro a b hab
  have hle : 2 ^ (a + 1) * env f (2 ^ (a + 2)) ≤ 2 ^ (b + 1) * env f (2 ^ (b + 2)) :=
    Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (by omega))
      (env_mono f (Nat.pow_le_pow_right (by norm_num) (by omega)))
  exact Nat.add_le_add_right (Nat.log_mono_right hle) 1

/-- Characterisation of the 2-adic valuation by divisibility. -/
theorem padicValNat_two_eq_of {n v : ℕ} (hn : n ≠ 0) (h1 : 2 ^ v ∣ n) (h2 : ¬ (2 : ℕ) ^ (v + 1) ∣ n) :
    padicValNat 2 n = v := by
  have hle : v ≤ padicValNat 2 n := (padicValNat_dvd_iff_le hn).1 h1
  have hge : ¬ (v + 1 ≤ padicValNat 2 n) := fun h => h2 ((padicValNat_dvd_iff_le hn).2 h)
  omega

/-- Peeling the lowest block: if `m` occupies the window `[k, k + G k]` and `r` lives above
`k + G k + G (k + G k)`, then the greedy count of `m + r` is one more than that of `r`. -/
theorem greedy_add (G : ℕ → ℕ) (hG : Monotone G) (m r k : ℕ) (hm : 0 < m)
    (hk : 2 ^ k ∣ m) (hmw : m < 2 ^ (k + G k + 1))
    (hr : 2 ^ (k + G k + G (k + G k) + 1) ∣ r) :
    greedy G (m + r) = 1 + greedy G r := by
  have hm0 : m ≠ 0 := hm.ne'
  -- `v` is the position of the lowest set digit of `m`
  have hkv : k ≤ padicValNat 2 m := (padicValNat_dvd_iff_le hm0).1 hk
  have hvm : (2 : ℕ) ^ padicValNat 2 m ∣ m := pow_padicValNat_dvd
  have hvk : padicValNat 2 m ≤ k + G k := by
    rcases Nat.lt_or_ge (k + G k) (padicValNat 2 m) with h | h
    · exfalso
      have h2 : (2 : ℕ) ^ (k + G k + 1) ≤ 2 ^ padicValNat 2 m :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have h3 : (2 : ℕ) ^ padicValNat 2 m ≤ m := Nat.le_of_dvd hm hvm
      omega
    · exact h
  have hGkv : G k ≤ G (padicValNat 2 m) := hG hkv
  have hGvk : G (padicValNat 2 m) ≤ G (k + G k) := hG hvk
  -- the window of `m + r` is the window of `m`
  have hrW : (2 : ℕ) ^ (padicValNat 2 m + G (padicValNat 2 m) + 1) ∣ r :=
    dvd_trans (pow_dvd_pow 2 (by omega)) hr
  have hmW : m < 2 ^ (padicValNat 2 m + G (padicValNat 2 m) + 1) :=
    lt_of_lt_of_le hmw (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hvr : (2 : ℕ) ^ padicValNat 2 m ∣ r := dvd_trans (pow_dvd_pow 2 (by omega)) hrW
  have hv1r : (2 : ℕ) ^ (padicValNat 2 m + 1) ∣ r := dvd_trans (pow_dvd_pow 2 (by omega)) hrW
  have hnotm : ¬ (2 : ℕ) ^ (padicValNat 2 m + 1) ∣ m := pow_succ_padicValNat_not_dvd hm0
  have hsum0 : m + r ≠ 0 := by omega
  have hpv : padicValNat 2 (m + r) = padicValNat 2 m := by
    refine padicValNat_two_eq_of hsum0 (Nat.dvd_add hvm hvr) ?_
    intro h
    exact hnotm ((Nat.dvd_add_left hv1r).1 h)
  have hwt : windowTop G (m + r) = padicValNat 2 m + G (padicValNat 2 m) := by
    unfold windowTop; rw [hpv]
  -- clearing the window of `m + r` leaves exactly `r`
  obtain ⟨s, hs⟩ := hrW
  have hcl : clearLow (m + r) (padicValNat 2 m + G (padicValNat 2 m) + 1) = r := by
    unfold clearLow
    rw [hs, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hmW, Nat.zero_add,
      Nat.mul_comm]
  rw [greedy_eq G (m + r) hsum0, hwt, hcl]

/-- Auxiliary form of `greedy_sum_blocks`, set up for induction on the number of blocks. -/
theorem greedy_sum_blocks_aux (G : ℕ → ℕ) (hG : Monotone G) :
    ∀ (j : ℕ) (m k : Fin j → ℕ), (∀ i, 0 < m i) → (∀ i, 2 ^ (k i) ∣ m i) →
      (∀ i, m i < 2 ^ (k i + G (k i) + 1)) →
      (∀ i i' : Fin j, i < i' → k i + G (k i) + G (k i + G (k i)) + 1 ≤ k i') →
      greedy G (∑ i, m i) = j := by
  intro j
  induction j with
  | zero => intro m k _ _ _ _; simpa using greedy_zero G
  | succ j ih =>
    intro m k hpos hdvd hlt hsep
    rw [Fin.sum_univ_succ]
    have hrdvd : (2 : ℕ) ^ (k 0 + G (k 0) + G (k 0 + G (k 0)) + 1) ∣ ∑ i : Fin j, m i.succ := by
      refine Finset.dvd_sum ?_
      intro i _
      exact dvd_trans (pow_dvd_pow 2 (hsep 0 i.succ (Fin.succ_pos i))) (hdvd i.succ)
    rw [greedy_add G hG _ _ (k 0) (hpos 0) (hdvd 0) (hlt 0) hrdvd,
      ih (fun i => m i.succ) (fun i => k i.succ) (fun i => hpos _) (fun i => hdvd _)
        (fun i => hlt _) (fun i i' h => hsep i.succ i'.succ (Fin.succ_lt_succ_iff.2 h))]
    omega

/-- The greedy count of a sum of `j` blocks with increasing, well-separated windows is `j`. -/
theorem greedy_sum_blocks (G : ℕ → ℕ) (hG : Monotone G) (j : ℕ) (m k : Fin j → ℕ)
    (hpos : ∀ i, 0 < m i) (hdvd : ∀ i, 2 ^ (k i) ∣ m i)
    (hlt : ∀ i, m i < 2 ^ (k i + G (k i) + 1))
    (hsep : ∀ i i' : Fin j, i < i' → k i + G (k i) + G (k i + G (k i)) + 1 ≤ k i') :
    greedy G (∑ i, m i) = j :=
  greedy_sum_blocks_aux G hG j m k hpos hdvd hlt hsep

end Erdos948
