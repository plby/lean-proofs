import Wikipedia.NoExoticSixSphere.GenericThreeSixRestriction
import Wikipedia.NoExoticSixSphere.ParametricAvoidance
import Wikipedia.NoExoticSixSphere.CorankOneSubmersiveFamily

/-!
# Full genericity for submersive parameter-dependent three-to-six operators

No affine parameter formula is assumed. On a coupled open domain the actual
operator map is smooth and submersive. Parametric incidence avoidance excludes
rank at most one, and a countable genuine coordinate cover controls every
rank-two point for the same almost-everywhere set of parameters.
-/

noncomputable section

open Set Function Module TopologicalSpace
open MeasureTheory MeasureTheory.Measure
open scoped ContDiff

namespace NoExoticSixSphere.OperatorRank

open CorankOne CorankOneCoordinates

variable {P X V W : Type}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace P] [BorelSpace P]

theorem ae_rank_gt_one_of_submersion (μ : Measure P) [IsAddHaarMeasure μ]
    (D : P × X → V →L[ℝ] W) (U : Opens (P × X)) (hD : ContDiffOn ℝ ∞ D U)
    (hs : ∀ q ∈ U, Surjective (fderiv ℝ D q))
    (hd : finrank ℝ X + (finrank ℝ V + finrank ℝ W) <
      finrank ℝ V * finrank ℝ W) :
    ∀ᵐ p ∂μ, ∀ x, (p, x) ∈ U → 1 < finrank ℝ (D (p, x)).range := by
  let G : (V →L[ℝ] ℝ) × W → V →L[ℝ] W := fun z ↦ z.1.smulRight z.2
  have hG : ContDiff ℝ ∞ G := contDiff_fst.smulRight contDiff_snd
  have hd' : finrank ℝ X + finrank ℝ ((V →L[ℝ] ℝ) × W) <
      finrank ℝ (V →L[ℝ] W) := by
    simpa only [finrank_prod, finrank_operator, finrank_self, mul_one] using hd
  apply (ParametricAvoidance.ae_avoids_image_on μ D G U hD hG hs hd').mono
  intro p hp x hx
  by_contra hn
  obtain ⟨ℓ, w, he⟩ := exists_smulRight_of_rank_le_one (D (p, x)) (le_of_not_gt hn)
  exact hp x hx (ℓ, w) he

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] in
theorem ae_regular_submersive_coordinates (μ : Measure P) [IsAddHaarMeasure μ]
    (D : P × X → V →L[ℝ] W) (U : Opens (P × X)) (hD : ContDiffOn ℝ ∞ D U)
    (hs : ∀ q ∈ U, Surjective (fderiv ℝ D q)) (c : RankTwoCoordinates V W) :
    ∀ᵐ p ∂μ, ∀ x, (p, x) ∈ U → D (p, x) ∈ CorankOneCoordinates.domain c →
      residual (operatorEquiv c (D (p, x))) = 0 →
        Surjective (fderiv ℝ (fun y ↦ residual (operatorEquiv c (D (p, y)))) x) := by
  let Q := operatorEquiv c
  have hQD : ContDiffOn ℝ ∞ (fun q ↦ Q (D q)) U := Q.contDiff.comp_contDiffOn hD
  have hsQD : ∀ q ∈ U, Surjective (fderiv ℝ (fun q ↦ Q (D q)) q) := by
    intro q hq
    have hd := (hD.contDiffAt (U.isOpen.mem_nhds hq)).differentiableAt (by simp)
    have he := (Q.hasFDerivAt.comp q hd.hasFDerivAt).fderiv
    change Surjective (fderiv ℝ (Q ∘ D) q)
    rw [he]
    exact Q.surjective.comp (hs q hq)
  exact CorankOneSubmersion.ae_regular_family μ (fun q ↦ Q (D q)) U hQD hsQD

theorem ae_regular_three_six_of_submersion (μ : Measure P) [IsAddHaarMeasure μ]
    (D : P × X → V →L[ℝ] W) (U : Opens (P × X)) (hD : ContDiffOn ℝ ∞ D U)
    (hs : ∀ q ∈ U, Surjective (fderiv ℝ D q))
    (hx : finrank ℝ X = 4) (hv : finrank ℝ V = 3) (hw : finrank ℝ W = 6) :
    ∀ᵐ p ∂μ, RegularThreeSixOn (fun x ↦ D (p, x)) {x | (p, x) ∈ U} := by
  let E := EuclideanSpace ℝ (Fin 2)
  let F := EuclideanSpace ℝ (Fin 4)
  have hv' : finrank ℝ V = finrank ℝ E + 1 := by simp [E, hv]
  have hw' : finrank ℝ W = finrank ℝ E + finrank ℝ F := by simp [E, F, hw]
  have hd : finrank ℝ X = finrank ℝ F := by simp [F, hx]
  obtain ⟨C, hC, hcov⟩ := exists_countable_cover hv' hw'
  let : Countable C := hC.to_subtype
  have hc : ∀ᵐ p ∂μ, ∀ c : C, ∀ x, (p, x) ∈ U →
      D (p, x) ∈ CorankOneCoordinates.domain c.val →
        residual (operatorEquiv c.val (D (p, x))) = 0 →
          Surjective (fderiv ℝ (fun y ↦ residual (operatorEquiv c.val (D (p, y)))) x) :=
    ae_all_iff.mpr fun c ↦ ae_regular_submersive_coordinates μ D U hD hs c.val
  have hl := ae_rank_gt_one_of_submersion μ D U hD hs (by rw [hx, hv, hw]; norm_num)
  apply (hc.and hl).mono
  rintro p ⟨hp, hlo⟩
  apply regularOn_of_rank_residual_at (fun x ↦ D (p, x)) {x | (p, x) ∈ U}
    (fun x hxu ↦ (hD.contDiffAt (U.isOpen.mem_nhds hxu)).comp
      (f := fun y ↦ (p, y)) x (contDiff_const.prodMk contDiff_id).contDiffAt) hlo
  intro x hxu hsing
  have hr : finrank ℝ (D (p, x)).range = finrank ℝ E := by
    simpa only [E, finrank_euclideanSpace_fin] using
      (singular_iff_rank_two (D (p, x)) hv (hlo x hxu)).mp hsing
  obtain ⟨c, hcC, hxc⟩ := hcov (D (p, x)) hr
  have hz : residual (operatorEquiv c (D (p, x))) = 0 :=
    (singular_iff_residual_zero hxc).mp
      ((injective_operatorEquiv_iff c (D (p, x))).not.mpr hsing)
  have hsurj := hp ⟨c, hcC⟩ x hxu hxc hz
  exact ⟨c, hxc, hz,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mpr hsurj, hsurj⟩

end NoExoticSixSphere.OperatorRank
