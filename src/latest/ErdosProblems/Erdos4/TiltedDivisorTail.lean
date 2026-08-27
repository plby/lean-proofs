import ErdosProblems.Erdos4.TiltedDivisorMoment

/-! Large common products are controlled by a large prime or an intermediate divisor. -/

open scoped BigOperators

namespace Erdos4.Tilted

open FGKMT

theorem divisor_weight_split (T : Finset ℕ) (hT : ∀ p ∈ T, 0 < p) (a : ℝ) :
    (∏ p ∈ T, a / (p : ℝ) ^ 2) =
      (((∏ p ∈ T, p : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ)) *
        ∏ p ∈ T, (a * (p : ℝ) ^ (-(3 / 2 : ℝ))) := by
  rw [← nat_prod_rpow, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr (hT p hp)
  have hh : (p : ℝ) ^ (-(1 / 2 : ℝ)) * (p : ℝ) ^ (-(3 / 2 : ℝ)) =
      ((p : ℝ) ^ 2)⁻¹ := by
    rw [← Real.rpow_add hp0]
    norm_num [Real.rpow_neg hp0.le]
  calc
    _ = a * ((p : ℝ) ^ 2)⁻¹ := rfl
    _ = _ := by rw [← hh]; ring

theorem divisor_product_tail {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)
    (S : Finset ℕ) (H : Ω → Finset ℕ) {W R X : ℕ} (hW : 0 < W) (hR : 1 ≤ R)
    (hRX : R * R ≤ X) (hS : ∀ p ∈ S, W < p ∧ p ≤ X)
    (hHS : ∀ o, H o ⊆ S) {D a : ℝ} (hD : 0 ≤ D) (ha : 0 ≤ a)
    (hbound : DivisorBound μ S H X D a) :
    μ.prob (fun o => X < ∏ p ∈ H o, p) ≤
      D * (a / R + (R : ℝ) ^ (-(1 / 2 : ℝ)) *
        Real.exp (2 * a * (W : ℝ) ^ (-(1 / 2 : ℝ)))) := by
  classical
  let L := S.filter (fun p => R < p)
  let M := S.powerset.filter (fun T => R < (∏ p ∈ T, p) ∧ (∏ p ∈ T, p) ≤ X)
  let large := fun o => ∃ p ∈ L, p ∈ H o
  let medium := fun o => ∃ T ∈ M, T ⊆ H o
  have hunion : μ.prob (fun o => X < ∏ p ∈ H o, p) ≤ μ.prob large + μ.prob medium := by
    have hsub : μ.prob (fun o => X < ∏ p ∈ H o, p) ≤ μ.prob (fun o => large o ∨ medium o) := by
      apply μ.prob_mono
      intro o ho
      rcases large_prod_has_witness (hHS o) hR hRX ho with hlarge | hmedium
      · obtain ⟨p, hp, hRp, hpH⟩ := hlarge
        exact Or.inl ⟨p, Finset.mem_filter.mpr ⟨hp, hRp⟩, hpH⟩
      · obtain ⟨T, hT, hTH, hRT, hTX⟩ := hmedium
        exact Or.inr ⟨T, Finset.mem_filter.mpr ⟨hT, hRT, hTX⟩, hTH⟩
    apply hsub.trans
    rw [FiniteLaw.prob_eq_mean, FiniteLaw.prob_eq_mean, FiniteLaw.prob_eq_mean, ← μ.mean_add]
    apply μ.mean_mono
    intro o
    by_cases hl : large o <;> by_cases hm : medium o <;> simp [hl, hm]
  have hlarge : μ.prob large ≤ D * a / R := by
    calc
      _ ≤ ∑ p ∈ L, μ.prob (fun o => p ∈ H o) := μ.prob_exists_finset_le L _
      _ ≤ ∑ p ∈ L, D * (a / (p : ℝ) ^ 2) := by
        apply Finset.sum_le_sum
        intro p hp
        have hpS := (Finset.mem_filter.mp hp).1
        have hh := hbound {p} (Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr hpS))
          (Finset.singleton_nonempty p) (by simpa only [Finset.prod_singleton] using (hS p hpS).2)
        simpa only [Finset.singleton_subset_iff, Finset.prod_singleton] using hh
      _ = D * a * ∑ p ∈ L, ((p : ℝ) ^ 2)⁻¹ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        ring
      _ ≤ D * a * (R : ℝ)⁻¹ := mul_le_mul_of_nonneg_left
        (finite_reciprocal_square_tail (by omega) L (fun p hp => (Finset.mem_filter.mp hp).2))
        (mul_nonneg hD ha)
      _ = _ := rfl
  let b := fun p : ℕ => a * (p : ℝ) ^ (-(3 / 2 : ℝ))
  have hb : ∀ p, 0 ≤ b p := fun p => mul_nonneg ha (Real.rpow_nonneg (Nat.cast_nonneg p) _)
  have hEuler : (∑ T ∈ S.powerset, ∏ p ∈ T, b p) ≤
      Real.exp (2 * a * (W : ℝ) ^ (-(1 / 2 : ℝ))) := by
    rw [← Finset.prod_one_add]
    apply (prod_one_add_le_exp_sum S b (fun p _ => hb p)).trans
    apply Real.exp_le_exp.mpr
    calc
      _ = a * ∑ p ∈ S, (p : ℝ) ^ (-(3 / 2 : ℝ)) := (Finset.mul_sum _ _ _).symm
      _ ≤ a * (2 * (W : ℝ) ^ (-(1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left (finite_three_halves_tail hW S (fun p hp => (hS p hp).1)) ha
      _ = _ := by ring
  have hmedium : μ.prob medium ≤ D * ((R : ℝ) ^ (-(1 / 2 : ℝ)) *
      Real.exp (2 * a * (W : ℝ) ^ (-(1 / 2 : ℝ)))) := by
    calc
      _ ≤ ∑ T ∈ M, μ.prob (fun o => T ⊆ H o) := μ.prob_exists_finset_le M _
      _ ≤ ∑ T ∈ M, D * ∏ p ∈ T, (a / (p : ℝ) ^ 2) := by
        apply Finset.sum_le_sum
        intro T hT
        obtain ⟨hTS, hRT, hTX⟩ := Finset.mem_filter.mp hT
        have hTne : T.Nonempty := by
          by_contra hn
          have he : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
          simp only [he, Finset.prod_empty] at hRT
          omega
        exact hbound T hTS hTne hTX
      _ ≤ ∑ T ∈ M, D * ((R : ℝ) ^ (-(1 / 2 : ℝ)) * ∏ p ∈ T, b p) := by
        apply Finset.sum_le_sum
        intro T hT
        obtain ⟨hTS, hRT, hTX⟩ := Finset.mem_filter.mp hT
        have hTpos : ∀ p ∈ T, 0 < p := by
          intro p hp
          exact hW.trans (hS p ((Finset.mem_powerset.mp hTS) hp)).1
        apply mul_le_mul_of_nonneg_left _ hD
        rw [divisor_weight_split T hTpos a]
        apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg (fun p _ => hb p))
        exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast (show 0 < R by omega))
          (Nat.cast_le.mpr hRT.le) (by norm_num)
      _ = D * ((R : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ T ∈ M, ∏ p ∈ T, b p) := by
        simp only [Finset.mul_sum]
      _ ≤ D * ((R : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ T ∈ S.powerset, ∏ p ∈ T, b p) := by
        apply mul_le_mul_of_nonneg_left _ hD
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (Nat.cast_nonneg R) _)
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun T _ _ => Finset.prod_nonneg (fun p _ => hb p))
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hEuler (Real.rpow_nonneg (Nat.cast_nonneg R) _)) hD
  have hh := hunion.trans (add_le_add hlarge hmedium)
  simpa only [mul_add, div_eq_mul_inv, mul_assoc] using hh

end Erdos4.Tilted
