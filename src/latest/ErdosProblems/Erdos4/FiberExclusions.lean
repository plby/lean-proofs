import ErdosProblems.Erdos4.FiberLowerBound

/-!
# Removing primes frozen in other coordinates

Dividing squarefree multiples of a prime by that prime gives an injective
map into the unrestricted harmonic sum. A finite union bound then pays
only the sum of reciprocal prime costs of the occupied coordinates.
-/

open scoped BigOperators

namespace Erdos4.FiberExclusions

open WeightedHarmonic ArithmeticFibers FiberLowerBound IdealProjection

theorem divisor_weight_le {p : ℕ} (hp : p.Prime) (W : ℕ) {n : ℕ} (hpn : p ∣ n) :
    weight W n ≤ ((p : ℝ) - 1)⁻¹ * weight W (n / p) := by
  classical
  by_cases hn : Squarefree n ∧ n.Coprime W
  · have hdvd : n / p ∣ n := Nat.div_dvd_of_dvd hpn
    have hquot : Squarefree (n / p) ∧ (n / p).Coprime W :=
      ⟨hn.1.squarefree_of_dvd hdvd, hn.2.of_dvd_left hdvd⟩
    have hsq : Squarefree (p * (n / p)) := by
      rw [Nat.mul_div_cancel' hpn]
      exact hn.1
    have hphi : Nat.totient n = (p - 1) * Nat.totient (n / p) := by
      calc
        Nat.totient n = Nat.totient (p * (n / p)) :=
          congrArg Nat.totient (Nat.mul_div_cancel' hpn).symm
        _ = _ := by rw [Nat.totient_mul (Nat.coprime_of_squarefree_mul hsq), Nat.totient_prime hp]
    simp only [weight, if_pos hn, if_pos hquot, hphi, Nat.cast_mul,
      Nat.cast_sub hp.one_le, Nat.cast_one, one_div, mul_inv_rev]
    exact le_of_eq (mul_comm _ _)
  · rw [weight, if_neg hn]
    have hh : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
    exact mul_nonneg (inv_nonneg.mpr (by linarith)) (weight_nonneg W (n / p))

theorem sum_weight_eq_mean (W T : ℕ) :
    (∑ n ∈ Finset.Icc 1 T, weight W n) =
      BoundedGaps.Maynard.squarefreeCoprimeInvTotientMean W T := rfl

theorem scaled_le_one {m k : ℝ} (hm : 1 ≤ m) (hk : 0 ≤ k) (R n : ℕ) :
    ProfileSmooth.scaled m k R n ≤ 1 :=
  PrimitiveProfile.profile_le_one hm hk
    (div_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _))

theorem scaled_nonneg {m k : ℝ} (hm : 0 ≤ m) (hk : 0 ≤ k) (R n : ℕ) :
    0 ≤ ProfileSmooth.scaled m k R n :=
  (PrimitiveProfile.profile_pos hm hk
    (div_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _))).le

theorem divisible_sum_le {m k : ℝ} (hm : 1 ≤ m) (hk : 0 ≤ k)
    (W R T : ℕ) (hTR : T ≤ R) {p : ℕ} (hp : p.Prime) :
    (∑ n ∈ (Finset.Icc 1 T).filter (fun n => p ∣ n),
      ProfileSmooth.scaled m k R n * weight W n) ≤
    ((p : ℝ) - 1)⁻¹ * BoundedGaps.Maynard.squarefreeCoprimeInvTotientMean W R := by
  classical
  let S := (Finset.Icc 1 T).filter (fun n => p ∣ n)
  have hdiv : ∀ n ∈ S, p ∣ n := fun n hn => (Finset.mem_filter.mp hn).2
  have hinj : ∀ n ∈ S, ∀ l ∈ S, n / p = l / p → n = l := by
    intro n hn l hl hnl
    rw [← Nat.mul_div_cancel' (hdiv n hn), ← Nat.mul_div_cancel' (hdiv l hl), hnl]
  have himage : S.image (fun n => n / p) ⊆ Finset.Icc 1 R := by
    intro v hv
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hv
    have hbounds := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
    refine Finset.mem_Icc.mpr ⟨?_, (Nat.div_le_self _ _).trans (hbounds.2.trans hTR)⟩
    exact Nat.div_pos (Nat.le_of_dvd (by omega) (hdiv n hn)) hp.pos
  have hsum : (∑ n ∈ S, weight W (n / p)) ≤
      BoundedGaps.Maynard.squarefreeCoprimeInvTotientMean W R := by
    rw [← Finset.sum_image hinj, ← sum_weight_eq_mean]
    exact Finset.sum_le_sum_of_subset_of_nonneg himage (fun v _hv _hnot => weight_nonneg W v)
  have hinv : 0 ≤ ((p : ℝ) - 1)⁻¹ := by
    apply inv_nonneg.mpr
    have hh : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
    linarith
  calc
    (∑ n ∈ S, ProfileSmooth.scaled m k R n * weight W n) ≤ ∑ n ∈ S, weight W n := by
      apply Finset.sum_le_sum
      intro n _hn
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (scaled_le_one hm hk R n) (weight_nonneg W n)
    _ ≤ ∑ n ∈ S, ((p : ℝ) - 1)⁻¹ * weight W (n / p) :=
      Finset.sum_le_sum (fun n hn => divisor_weight_le hp W (hdiv n hn))
    _ = ((p : ℝ) - 1)⁻¹ * ∑ n ∈ S, weight W (n / p) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum hinv

variable {P : Type*} [Fintype P] [DecidableEq P] {k : ℕ}

noncomputable def frozenCost (ell : P → ℕ) (j : Fin k)
    (a : P → Option (Fin k)) : ℝ :=
  ∑ p, if freeze j (a p) = none then 0 else ((ell p : ℝ) - 1)⁻¹

omit [DecidableEq P] in
theorem frozenCost_le_reciprocalMass (ell : P → ℕ) (hell : ∀ p, 1 ≤ ell p)
    (j : Fin k) (a : P → Option (Fin k)) :
    frozenCost ell j a ≤ CoefficientMass.reciprocalMass ell a := by
  apply Finset.sum_le_sum
  intro p _hp
  have hnonneg : 0 ≤ ((ell p : ℝ) - 1)⁻¹ := by
    have hh : (1 : ℝ) ≤ ell p := by exact_mod_cast hell p
    exact inv_nonneg.mpr (by linarith)
  by_cases ha : a p = none
  · simp [ha, freeze]
  · by_cases hf : freeze j (a p) = none <;> simp [ha, hf, hnonneg]

omit [Fintype P] [DecidableEq P] in
open Classical in
theorem admissibleSum_eq (W : ℕ) (m : ℝ) (R T : ℕ)
    (ell : P → ℕ) (j : Fin k) (a : P → Option (Fin k)) :
    admissibleSum W m R T ell j a =
      ∑ n ∈ Finset.Icc 1 T, if AvoidsFrozen ell j a n then
        ProfileSmooth.scaled m k R n * weight W n else 0 := by
  classical
  unfold admissibleSum admissible
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _hn
  by_cases hsq : Squarefree n ∧ n.Coprime W
  · by_cases ha : AvoidsFrozen ell j a n
    · simp [hsq.1, ha, weight, div_eq_mul_inv]
    · simp [ha]
  · have hh : ¬(Squarefree n ∧ n.Coprime W ∧ AvoidsFrozen ell j a n) :=
      fun h => hsq ⟨h.1, h.2.1⟩
    simp [hh, weight, hsq]

/-- The price of all frozen-prime exclusions is bounded by their
reciprocal mass times the unrestricted harmonic sum at the outer cutoff. -/
theorem weightedSum_sub_cost_le {m : ℝ} (hm : 1 ≤ m)
    (W R T : ℕ) (hTR : T ≤ R) (ell : P → ℕ) (hprime : ∀ p, (ell p).Prime)
    (j : Fin k) (a : P → Option (Fin k)) :
    weightedSum W m k R T -
      BoundedGaps.Maynard.squarefreeCoprimeInvTotientMean W R * frozenCost ell j a ≤
    admissibleSum W m R T ell j a := by
  classical
  let w : ℕ → ℝ := fun n => ProfileSmooth.scaled m k R n * weight W n
  have hw : ∀ n, 0 ≤ w n := fun n =>
    mul_nonneg (scaled_nonneg (by linarith) (Nat.cast_nonneg k) R n) (weight_nonneg W n)
  let B : ℝ := ∑ n ∈ Finset.Icc 1 T, if AvoidsFrozen ell j a n then 0 else w n
  have hpoint : ∀ n, (if AvoidsFrozen ell j a n then 0 else w n) ≤
      ∑ p, if freeze j (a p) = none then 0 else if ell p ∣ n then w n else 0 := by
    intro n
    have hterms : ∀ p, 0 ≤
        (if freeze j (a p) = none then 0 else if ell p ∣ n then w n else 0) := by
      intro p
      split_ifs <;> first | exact hw n | exact le_rfl
    by_cases ha : AvoidsFrozen ell j a n
    · rw [if_pos ha]
      exact Finset.sum_nonneg (fun p _hp => hterms p)
    · obtain ⟨p, hp⟩ := not_forall.mp ha
      have hpair := Classical.not_imp.mp hp
      rw [if_neg ha]
      have hh := Finset.single_le_sum (s := Finset.univ)
        (f := fun p => if freeze j (a p) = none then 0 else if ell p ∣ n then w n else 0)
        (fun p _hp => hterms p) (Finset.mem_univ p)
      simpa only [if_neg hpair.2, if_pos hpair.1] using hh
  have hB : B ≤ BoundedGaps.Maynard.squarefreeCoprimeInvTotientMean W R *
      frozenCost ell j a := by
    calc
      B ≤ ∑ n ∈ Finset.Icc 1 T,
          ∑ p, if freeze j (a p) = none then 0 else if ell p ∣ n then w n else 0 :=
        Finset.sum_le_sum (fun n _hn => hpoint n)
      _ = ∑ p, ∑ n ∈ Finset.Icc 1 T,
          if freeze j (a p) = none then 0 else if ell p ∣ n then w n else 0 :=
        Finset.sum_comm
      _ ≤ ∑ p, if freeze j (a p) = none then 0 else
          ((ell p : ℝ) - 1)⁻¹ * BoundedGaps.Maynard.squarefreeCoprimeInvTotientMean W R := by
        apply Finset.sum_le_sum
        intro p _hp
        by_cases hf : freeze j (a p) = none
        · simp [hf]
        · simp only [if_neg hf]
          rw [← Finset.sum_filter]
          exact divisible_sum_le hm (Nat.cast_nonneg k) W R T hTR (hprime p)
      _ = BoundedGaps.Maynard.squarefreeCoprimeInvTotientMean W R * frozenCost ell j a := by
        unfold frozenCost
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _hp
        split_ifs <;> ring
  have hsplit : weightedSum W m k R T = admissibleSum W m R T ell j a + B := by
    rw [admissibleSum_eq]
    unfold weightedSum B
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _hn
    split_ifs <;> simp [w]
  linarith

theorem mean_nonneg (W R : ℕ) :
    0 ≤ BoundedGaps.Maynard.squarefreeCoprimeInvTotientMean W R := by
  rw [← sum_weight_eq_mean]
  exact Finset.sum_nonneg (fun n _hn => weight_nonneg W n)

theorem primeWindow_weightedSum_sub_mass_le {m : ℝ} (hm : 1 ≤ m)
    {R : ℕ} (hR : 2 ≤ R) (K : ℕ) (j : Fin k)
    (a : primeWindow K R → Option (Fin k)) :
    weightedSum (primorial K) m k R
      (R / CutoffSimplex.cofactor (fun p : primeWindow K R => (p : ℕ)) j a) -
      BoundedGaps.Maynard.squarefreeCoprimeInvTotientMean (primorial K) R *
        CoefficientMass.reciprocalMass (fun p : primeWindow K R => (p : ℕ)) a ≤
    IdealAction.fiberSum m R (fun p : primeWindow K R => (p : ℕ)) j a := by
  let ell : primeWindow K R → ℕ := fun p => p
  have hprime : ∀ p, (ell p).Prime := fun p => (mem_primeWindow.mp p.property).1
  have hmass := mul_le_mul_of_nonneg_left
    (frozenCost_le_reciprocalMass ell (fun p => (hprime p).one_le) j a)
    (mean_nonneg (primorial K) R)
  have hexclude := weightedSum_sub_cost_le hm (primorial K) R
    (R / CutoffSimplex.cofactor ell j a) (Nat.div_le_self _ _) ell hprime j a
  have hfiber := primeWindow_admissibleSum_le (by linarith : 0 ≤ m) hR K j a
  change _ ≤ IdealAction.fiberSum m R ell j a
  linarith

end Erdos4.FiberExclusions
