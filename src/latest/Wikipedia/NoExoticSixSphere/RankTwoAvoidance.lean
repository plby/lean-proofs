import Wikipedia.NoExoticSixSphere.RankOneOperators
import Wikipedia.NoExoticSixSphere.ParametricAvoidance

/-!
# Genuine rank-two factorization and generic avoidance

Every actual operator of rank at most two factors through the ordinary
real plane, including ranks zero and one. The smooth composition map on
these factors parametrizes the low-rank locus. Parametric Sard therefore
excludes that locus when its parameter dimension is sufficiently small.
-/

noncomputable section

open Set Function Module TopologicalSpace
open MeasureTheory MeasureTheory.Measure
open scoped ContDiff

namespace NoExoticSixSphere.OperatorRank

variable {V W : Type}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

omit [FiniteDimensional ℝ W] in
theorem exists_factor_through_plane (L : V →L[ℝ] W) (hr : finrank ℝ L.range ≤ 2) :
    ∃ A : V →L[ℝ] ℝ × ℝ, ∃ B : (ℝ × ℝ) →L[ℝ] W, L = B.comp A := by
  by_cases htwo : finrank ℝ L.range = 2
  · let e : L.range ≃L[ℝ] ℝ × ℝ :=
      ContinuousLinearEquiv.ofFinrankEq (by rw [finrank_prod, finrank_self, htwo])
    refine ⟨e.toContinuousLinearMap.comp L.rangeRestrict,
      L.range.subtypeL.comp e.symm.toContinuousLinearMap, ?_⟩
    ext x
    change L x = (e.symm (e (L.rangeRestrict x)) : W)
    rw [e.symm_apply_apply]
    rfl
  · obtain ⟨ℓ, w, hL⟩ := exists_smulRight_of_rank_le_one L (by omega)
    refine ⟨ℓ.prod 0, (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight w, ?_⟩
    rw [hL]
    rfl

variable {P X : Type}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [MeasurableSpace P] [BorelSpace P]

theorem ae_rank_gt_two_of_submersion (μ : Measure P) [IsAddHaarMeasure μ]
    (D : P × X → V →L[ℝ] W) (U : Opens (P × X)) (hD : ContDiffOn ℝ ∞ D U)
    (hs : ∀ q ∈ U, Surjective (fderiv ℝ D q))
    (hd : finrank ℝ X + 2 * (finrank ℝ V + finrank ℝ W) <
      finrank ℝ V * finrank ℝ W) :
    ∀ᵐ a ∂μ, ∀ x, (a, x) ∈ U → 2 < finrank ℝ (D (a, x)).range := by
  let Z := (V →L[ℝ] ℝ × ℝ) × ((ℝ × ℝ) →L[ℝ] W)
  let G : Z → V →L[ℝ] W := fun z ↦ z.2.comp z.1
  have hG : ContDiff ℝ ∞ G := contDiff_snd.clm_comp contDiff_fst
  have hZ : finrank ℝ Z = 2 * (finrank ℝ V + finrank ℝ W) := by
    simp only [Z, finrank_prod, finrank_operator, finrank_self]
    ring
  have hd' : finrank ℝ X + finrank ℝ Z < finrank ℝ (V →L[ℝ] W) := by
    rw [hZ, finrank_operator]
    exact hd
  apply (ParametricAvoidance.ae_avoids_image_on μ D G U hD hG hs hd').mono
  intro a ha x hx
  by_contra hn
  obtain ⟨A, B, he⟩ := exists_factor_through_plane (D (a, x)) (le_of_not_gt hn)
  exact ha x hx (A, B) he

end NoExoticSixSphere.OperatorRank
