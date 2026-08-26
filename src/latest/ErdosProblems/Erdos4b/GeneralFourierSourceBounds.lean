/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierCoefficientMass

/-!
# Uniform coefficient bounds and the source product support

The fixed compact profiles bound the coefficient independently of all
arithmetic parameters. The first-family simplex support and the
companion support interval give explicit product radii for the mass
estimate, not just bounds on individual divisor coordinates.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

theorem real_abs_moebius_le_one (n : ℕ) : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
  exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))

theorem sourceAnalyticSelbergCoefficient_abs_le
    {ι J : Type*} [Fintype ι] (S : Finset J)
    (F : J → ι → ℝ → ℝ) (G : ℝ → ℝ) (BF : J → ι → ℝ) (BG : ℝ)
    (hBF : ∀ j ∈ S, ∀ i, 0 ≤ BF j i) (_hBG : 0 ≤ BG)
    (hF : ∀ j ∈ S, ∀ i t, |F j i t| ≤ BF j i) (hG : ∀ t, |G t| ≤ BG)
    (LD LE : ℝ) (d e : ι → ℕ) :
    |sourceAnalyticSelbergCoefficient S F G LD LE d e| ≤
      ∑ j ∈ S, ∏ i, BF j i * BG := by
  have hmu : |∏ i, (ArithmeticFunction.moebius (d i) : ℝ) *
      (ArithmeticFunction.moebius (e i) : ℝ)| ≤ 1 := by
    rw [Finset.abs_prod]
    calc
      _ ≤ ∏ _i : ι, (1 : ℝ) := by
        apply Finset.prod_le_prod (fun i hi ↦ abs_nonneg _)
        intro i hi
        rw [abs_mul]
        exact (mul_le_mul (real_abs_moebius_le_one _) (real_abs_moebius_le_one _)
          (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
      _ = _ := Finset.prod_const_one
  unfold sourceAnalyticSelbergCoefficient
  rw [abs_mul]
  calc
    _ ≤ 1 * |∑ j ∈ S, ∏ i, F j i (Real.log (d i) / LD) * G (Real.log (e i) / LE)| :=
      mul_le_mul_of_nonneg_right hmu (abs_nonneg _)
    _ ≤ ∑ j ∈ S, ∏ i, BF j i * BG := by
      rw [one_mul]
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro j hj
      rw [Finset.abs_prod]
      apply Finset.prod_le_prod (fun i hi ↦ abs_nonneg _)
      intro i hi
      rw [abs_mul]
      exact mul_le_mul (hF j hj i _) (hG _) (abs_nonneg _) (hBF j hj i)

theorem exists_uniform_sourceAnalyticSelbergCoefficient_bound
    {ι J : Type*} [Fintype ι] (S : Finset J) (F : J → ι → ℝ → ℝ) (G : ℝ → ℝ)
    (hFcompact : ∀ j i, HasCompactSupport (F j i)) (hFcont : ∀ j i, Continuous (F j i))
    (hGcompact : HasCompactSupport G) (hGcont : Continuous G) :
    ∃ C ≥ 0, ∀ LD LE (d e : ι → ℕ), |sourceAnalyticSelbergCoefficient S F G LD LE d e| ≤ C := by
  choose BF hBF using fun j i ↦ (hFcompact j i).exists_bound_of_continuous (hFcont j i)
  obtain ⟨BG, hBG⟩ := hGcompact.exists_bound_of_continuous hGcont
  have hBF0 (j : J) (i : ι) : 0 ≤ BF j i := (norm_nonneg (F j i 0)).trans (hBF j i 0)
  have hBG0 : 0 ≤ BG := (norm_nonneg (G 0)).trans (hBG 0)
  refine ⟨∑ j ∈ S, ∏ i, BF j i * BG,
    Finset.sum_nonneg (fun j hj ↦ Finset.prod_nonneg (fun i hi ↦ mul_nonneg (hBF0 j i) hBG0)), ?_⟩
  intro LD LE d e
  exact sourceAnalyticSelbergCoefficient_abs_le S F G BF BG (fun j hj ↦ hBF0 j) hBG0
    (fun j hj i t ↦ by simpa only [Real.norm_eq_abs] using hBF j i t)
    (fun t ↦ by simpa only [Real.norm_eq_abs] using hBG t) LD LE d e

theorem nat_prod_le_ceil_exp_of_log_sum
    {ι : Type*} [Fintype ι] (d : ι → ℕ) (hd : ∀ i, 0 < d i)
    {L A : ℝ} (hL : 0 < L) (hsum : (∑ i, Real.log (d i) / L) ≤ A) :
    (∏ i, d i) ≤ ⌈Real.exp (A * L)⌉₊ := by
  have hprodpos : (0 : ℝ) < (∏ i, d i : ℕ) := by
    exact_mod_cast Finset.prod_pos (fun i hi ↦ hd i)
  have hlog : Real.log (∏ i, d i : ℕ) ≤ A * L := by
    rw [Nat.cast_prod, Real.log_prod (fun i hi ↦ by exact_mod_cast (hd i).ne')]
    exact (div_le_iff₀ hL).mp (by simpa only [Finset.sum_div] using hsum)
  have hbound := (Real.log_le_iff_le_exp hprodpos).mp hlog
  exact_mod_cast hbound.trans (Nat.le_ceil (Real.exp (A * L)))

theorem sourceAnalyticSelbergCoefficient_nonzero_product_bounds
    {ι J : Type*} [Fintype ι] (S : Finset J) (F : J → ι → ℝ → ℝ) (G : ℝ → ℝ)
    {LD LE A : ℝ} (hLD : 0 < LD) (hLE : 0 < LE)
    (hFsupport : ∀ j ∈ S, ∀ u : ι → ℝ,
      (∀ i, 0 ≤ u i) → (∀ i, F j i (u i) ≠ 0) → (∑ i, u i) ≤ A)
    (hGsupport : ∀ t, 0 ≤ t → G t ≠ 0 → t ≤ 1)
    (d e : ι → ℕ) (hd : ∀ i, 0 < d i) (he : ∀ i, 0 < e i)
    (hne : sourceAnalyticSelbergCoefficient S F G LD LE d e ≠ 0) :
    (∏ i, d i) ≤ ⌈Real.exp (A * LD)⌉₊ ∧
      (∏ i, e i) ≤ ⌈Real.exp ((Fintype.card ι : ℝ) * LE)⌉₊ := by
  obtain ⟨j, hj, hprod⟩ := Finset.exists_ne_zero_of_sum_ne_zero (mul_ne_zero_iff.mp hne).2
  have hterms (i : ι) :
      F j i (Real.log (d i) / LD) ≠ 0 ∧ G (Real.log (e i) / LE) ≠ 0 :=
    mul_ne_zero_iff.mp ((Finset.prod_ne_zero_iff.mp hprod) i (Finset.mem_univ i))
  have hnonneg (v : ι → ℕ) (hv : ∀ i, 0 < v i) (L : ℝ) (hL : 0 < L) (i : ι) :
      0 ≤ Real.log (v i) / L := div_nonneg (Real.log_nonneg (by exact_mod_cast hv i)) hL.le
  constructor
  · apply nat_prod_le_ceil_exp_of_log_sum d hd hLD
    exact hFsupport j hj _ (hnonneg d hd LD hLD) (fun i ↦ (hterms i).1)
  · apply nat_prod_le_ceil_exp_of_log_sum e he hLE
    calc
      _ ≤ ∑ _i : ι, (1 : ℝ) := Finset.sum_le_sum fun i hi ↦
        hGsupport _ (hnonneg e he LE hLE i) (hterms i).2
      _ = _ := by simp

def sourceSelbergProductMassBound (K : ℕ) (C A LD LE : ℝ) : ℝ :=
  C * ((⌈Real.exp (A * LD)⌉₊ : ℝ) *
      (1 + Real.log (⌈Real.exp (A * LD)⌉₊ : ℝ)) ^ K) *
    ((⌈Real.exp ((K : ℝ) * LE)⌉₊ : ℝ) *
      (1 + Real.log (⌈Real.exp ((K : ℝ) * LE)⌉₊ : ℝ)) ^ K)

theorem sourceAnalyticSelbergCoefficientMass_le
    {J : Type*} (H P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (m : ℕ)
    (S : Finset J) (F : J → H → ℝ → ℝ) (G : ℝ → ℝ)
    {C LD LE A : ℝ} (hC : 0 ≤ C) (hLD : 0 < LD) (hLE : 0 < LE)
    (hbound : ∀ (d e : H → ℕ), |sourceAnalyticSelbergCoefficient S F G LD LE d e| ≤ C)
    (hFsupport : ∀ j ∈ S, ∀ u : H → ℝ,
      (∀ i, 0 ≤ u i) → (∀ i, F j i (u i) ≠ 0) → (∑ i, u i) ≤ A)
    (hGsupport : ∀ t, 0 ≤ t → G t ≠ 0 → t ≤ 1) :
    doubledSelbergCoefficientMass H (cutoffDivisorTupleSupport H P)
      (cutoffCompanionDivisorTupleSupport H P m)
      (sourceAnalyticSelbergCoefficient S F G LD LE) ≤
        sourceSelbergProductMassBound (Fintype.card H) C A LD LE := by
  classical
  apply doubledSelbergCoefficientMass_le_product_radii H _ _ _ _ _ hC
  · exact fun d hd i ↦ cutoffDivisorTupleSupport_coordinate_pos hP hd i
  · exact fun e he i ↦ cutoffDivisorTupleSupport_coordinate_pos hP (Finset.mem_filter.mp he).1 i
  · exact fun d hd e he ↦ hbound d e
  · intro d hd e he hne
    exact sourceAnalyticSelbergCoefficient_nonzero_product_bounds S F G hLD hLE hFsupport
      hGsupport d e (cutoffDivisorTupleSupport_coordinate_pos hP hd)
      (cutoffDivisorTupleSupport_coordinate_pos hP (Finset.mem_filter.mp he).1) hne

theorem sourceAnalyticSelbergEndpointError_abs_le
    {J : Type*} (H P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (W m q T : ℕ) (hW : 0 < W)
    (S : Finset J) (F : J → H → ℝ → ℝ) (G : ℝ → ℝ)
    {C LD LE A : ℝ} (hC : 0 ≤ C) (hLD : 0 < LD) (hLE : 0 < LE)
    (hbound : ∀ (d e : H → ℕ), |sourceAnalyticSelbergCoefficient S F G LD LE d e| ≤ C)
    (hFsupport : ∀ j ∈ S, ∀ u : H → ℝ,
      (∀ i, 0 ≤ u i) → (∀ i, F j i (u i) ≠ 0) → (∑ i, u i) ≤ A)
    (hGsupport : ∀ t, 0 ≤ t → G t ≠ 0 → t ≤ 1) :
    |doubledSelbergGeneralNormalizationError H (cutoffDivisorTupleSupport H P)
      (cutoffCompanionDivisorTupleSupport H P m) (sourceAnalyticSelbergCoefficient S F G LD LE)
      W m q T| ≤
        sourceSelbergProductMassBound (Fintype.card H) C A LD LE ^ 2 *
          (allowedPreSieveResidues W m).card := by
  have hmass := sourceAnalyticSelbergCoefficientMass_le H P hP m S F G
    hC hLD hLE hbound hFsupport hGsupport
  have hmass0 : 0 ≤ doubledSelbergCoefficientMass H (cutoffDivisorTupleSupport H P)
      (cutoffCompanionDivisorTupleSupport H P m) (sourceAnalyticSelbergCoefficient S F G LD LE) :=
    Finset.sum_nonneg fun d hd ↦ Finset.sum_nonneg fun e he ↦ abs_nonneg _
  apply (doubledSelbergGeneralNormalizationError_abs_le_mass H _ _ _ W m q T
    (cutoffDoubledGeneralSupport H P hP m) hW).trans
  exact mul_le_mul_of_nonneg_right
    ((sq_le_sq₀ hmass0 (hmass0.trans hmass)).mpr hmass) (Nat.cast_nonneg _)

end

end Erdos4b
