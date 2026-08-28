import Wikipedia.NoExoticSixSphere.ParametricRegularOpen
import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# Generic linear maps avoid a lower-dimensional nonzero smooth family

The parameter is an actual continuous linear map. Evaluation on a nonzero
vector is submersive in that parameter. Parametric Sard and the strict
source-dimension bound therefore exclude every zero for almost every
parameter, simultaneously on a countable collection of open charts.
This supplies the secant and tangent avoidance needed for linear compression.
-/

noncomputable section

open Set Function Module TopologicalSpace MeasureTheory
open MeasureTheory.Measure
open scoped ContDiff

namespace NoExoticSixSphere.GenericLinearAvoidance

variable {D A F : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [FiniteDimensional ℝ D] [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ A] [FiniteDimensional ℝ F] in
theorem evaluation_surjective {v : A} (hv : v ≠ 0) :
    Surjective (fun L : A →L[ℝ] F ↦ L v) := by
  obtain ⟨l, _, hl⟩ := exists_dual_vector ℝ v (norm_ne_zero_iff.mpr hv)
  change l v = ‖v‖ at hl
  intro w
  refine ⟨l.smulRight (‖v‖⁻¹ • w), ?_⟩
  simp only [ContinuousLinearMap.smulRight_apply, hl, smul_smul]
  rw [mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), one_smul]

def family (g : D → A) (q : (A →L[ℝ] F) × D) : F := q.1 (g q.2)

def domain (U : Opens D) : Opens ((A →L[ℝ] F) × D) :=
  ⟨Prod.snd ⁻¹' U, U.isOpen.preimage continuous_snd⟩

omit [FiniteDimensional ℝ D] [FiniteDimensional ℝ A] [FiniteDimensional ℝ F] in
theorem contDiffOn_family (g : D → A) (U : Opens D) (hg : ContDiffOn ℝ ∞ g U) :
    ContDiffOn ℝ ∞ (family (F := F) g) (domain (A := A) (F := F) U) :=
  contDiff_fst.contDiffOn.clm_apply
    (hg.comp contDiff_snd.contDiffOn (fun _ h ↦ h))

omit [FiniteDimensional ℝ D] [FiniteDimensional ℝ A] [FiniteDimensional ℝ F] in
theorem family_derivative_surjective (g : D → A) (U : Opens D)
    (hg : ContDiffOn ℝ ∞ g U) (q : (A →L[ℝ] F) × D)
    (hq : q ∈ domain (A := A) (F := F) U)
    (hne : g q.2 ≠ 0) : Surjective (fderiv ℝ (family (F := F) g) q) := by
  have hD := ((contDiffOn_family (F := F) g U hg).contDiffAt
    ((domain (A := A) (F := F) U).isOpen.mem_nhds hq)).differentiableAt (by simp)
  have hi : HasFDerivAt (fun L : A →L[ℝ] F ↦ (L, q.2))
      (ContinuousLinearMap.inl ℝ (A →L[ℝ] F) D) q.1 :=
    (hasFDerivAt_id q.1).prodMk (hasFDerivAt_const q.2 q.1)
  have he := (hD.hasFDerivAt.comp q.1 hi).fderiv
  have hev : fderiv ℝ (fun L : A →L[ℝ] F ↦ L (g q.2)) q.1 =
      ContinuousLinearMap.apply ℝ F (g q.2) :=
    (ContinuousLinearMap.apply ℝ F (g q.2)).fderiv
  change fderiv ℝ (fun L : A →L[ℝ] F ↦ L (g q.2)) q.1 = _ at he
  rw [hev] at he
  intro w
  obtain ⟨L, hL⟩ := evaluation_surjective (F := F) hne w
  refine ⟨(L, 0), ?_⟩
  have h := congrArg (fun T : (A →L[ℝ] F) →L[ℝ] F ↦ T L) he
  exact h.symm.trans hL

theorem ae_avoids_zero [MeasurableSpace (A →L[ℝ] F)] [BorelSpace (A →L[ℝ] F)]
    (μ : Measure (A →L[ℝ] F)) [IsAddHaarMeasure μ]
    (g : D → A) (U : Opens D) (hg : ContDiffOn ℝ ∞ g U)
    (hne : ∀ x ∈ U, g x ≠ 0) (hd : finrank ℝ D < finrank ℝ F) :
    ∀ᵐ L ∂μ, ∀ x ∈ U, L (g x) ≠ 0 := by
  have h := ParametricRegular.ae_parameters_on μ (family (F := F) g)
    (domain (A := A) (F := F) U) (contDiffOn_family (F := F) g U hg)
    (fun q hq _ ↦ family_derivative_surjective g U hg q hq (hne q.2 hq))
  apply h.mono
  intro L hL x hx hz
  have hs := hL x hx hz
  have hdim := LinearMap.finrank_le_finrank_of_surjective
    (f := (fderiv ℝ (fun y ↦ family g (L, y)) x).toLinearMap) hs
  exact (not_le_of_gt hd) hdim

theorem ae_avoids_zero_countable {ι : Type*} [Countable ι]
    [MeasurableSpace (A →L[ℝ] F)] [BorelSpace (A →L[ℝ] F)]
    (μ : Measure (A →L[ℝ] F)) [IsAddHaarMeasure μ]
    (g : ι → D → A) (U : ι → Opens D) (hg : ∀ i, ContDiffOn ℝ ∞ (g i) (U i))
    (hne : ∀ i x, x ∈ U i → g i x ≠ 0) (hd : finrank ℝ D < finrank ℝ F) :
    ∀ᵐ L ∂μ, ∀ i x, x ∈ U i → L (g i x) ≠ 0 :=
  ae_all_iff.mpr fun i ↦ ae_avoids_zero μ (g i) (U i) (hg i) (hne i) hd

end NoExoticSixSphere.GenericLinearAvoidance
