import Wikipedia.SmoothSixDPoincare.TubularBigonTangentMatching

/-!
# The original native sheet transitions in model-sheet time

The affine time map is explicit, smooth, and has the already checked half-time
derivative. The actual sheet transitions are smooth on their genuine open
chart-overlap domains, including neighborhoods of the two endpoint centers.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.WhitneyPairModel

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

def sheetTimeCoordinates (p : (ℝ × A)) : (ℝ × A) := halfTimeDerivative p + ((1 / 2 : ℝ), 0)

theorem sheetTimeCoordinates_apply (p : (ℝ × A)) :
    sheetTimeCoordinates p = ((p.1 + 1) / 2, p.2) := by
  rw [sheetTimeCoordinates, halfTimeDerivative_apply]
  apply Prod.ext
  · change p.1 / 2 + 1 / 2 = (p.1 + 1) / 2
    ring
  · exact add_zero _

theorem sheetTimeCoordinates_center (t : ℝ) :
    sheetTimeCoordinates (2 * t - 1, (0 : A)) = (t, 0) := by
  rw [sheetTimeCoordinates_apply]
  apply Prod.ext
  · dsimp
    ring
  · rfl

theorem contDiff_sheetTimeCoordinates : ContDiff ℝ ∞ (sheetTimeCoordinates (A := A)) :=
  (halfTimeDerivative (A := A)).contDiff.add contDiff_const

theorem hasFDerivAt_sheetTimeCoordinates (p : (ℝ × A)) :
    HasFDerivAt sheetTimeCoordinates halfTimeDerivative p :=
  halfTimeDerivative.hasFDerivAt.add_const ((1 / 2 : ℝ), (0 : A))

end Wikipedia.SmoothSixDPoincare.WhitneyPairModel

namespace Wikipedia.SmoothSixDPoincare.StripNormalData

open WhitneyPairModel

variable {A B Z E M : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  {S : Set M} {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
  (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞)

def sheetTransitionDomain : Set (ℝ × A) :=
  (ContinuousLinearMap.inl ℝ (ℝ × A) B) ⁻¹' (d.chart.source ∩ d.chart ⁻¹' Ψ.target)

theorem isOpen_sheetTransitionDomain : IsOpen (d.sheetTransitionDomain Ψ) := by
  have hO : IsOpen (d.chart.source ∩ d.chart ⁻¹' Ψ.target) :=
    d.chart.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage
      d.chart.open_source Ψ.open_target
  exact hO.preimage (ContinuousLinearMap.inl ℝ (ℝ × A) B).continuous

theorem contDiffOn_sheetTransition :
    ContDiffOn ℝ ∞ (d.sheetTransition Ψ) (d.sheetTransitionDomain Ψ) := by
  have hfull : ContDiffOn ℝ ∞ (Ψ.symm ∘ d.chart)
      (d.chart.source ∩ d.chart ⁻¹' Ψ.target) :=
    (Ψ.contMDiffOn_invFun.comp (d.chart.contMDiffOn_toFun.mono inter_subset_left)
      (fun _ hp => hp.2)).contDiffOn
  exact hfull.comp (ContinuousLinearMap.inl ℝ (ℝ × A) B).contDiff.contDiffOn (fun _ hp => hp)

def retimedSheetTransition : (ℝ × A) → ((ℝ × ℝ) × Z) := d.sheetTransition Ψ ∘ sheetTimeCoordinates

def retimedDomain : Set (ℝ × A) := sheetTimeCoordinates ⁻¹' d.sheetTransitionDomain Ψ

theorem isOpen_retimedDomain : IsOpen (d.retimedDomain Ψ) :=
  (d.isOpen_sheetTransitionDomain Ψ).preimage contDiff_sheetTimeCoordinates.continuous

theorem contDiffOn_retimedSheetTransition :
    ContDiffOn ℝ ∞ (d.retimedSheetTransition Ψ) (d.retimedDomain Ψ) :=
  (d.contDiffOn_sheetTransition Ψ).comp contDiff_sheetTimeCoordinates.contDiffOn (fun _ hp => hp)

theorem retimedDomain_contains_center {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target) :
    (2 * t - 1, (0 : A)) ∈ d.retimedDomain Ψ := by
  change sheetTimeCoordinates (2 * t - 1, 0) ∈ d.sheetTransitionDomain Ψ
  rw [sheetTimeCoordinates_center]
  exact ⟨d.line ht, htarget⟩

/-- The original native sheet transition has the same full derivative as the adapted model sheet. -/
theorem hasFDerivAt_retimedSheetTransition {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target) :
    HasFDerivAt (d.retimedSheetTransition Ψ)
      ((d.sheetDifferential Ψ t).comp halfTimeDerivative) (2 * t - 1, 0) := by
  have hd : HasFDerivAt (d.sheetTransition Ψ) (d.sheetDifferential Ψ t)
      (sheetTimeCoordinates (2 * t - 1, 0)) := by
    rw [sheetTimeCoordinates_center]
    exact ((d.contDiffAt_sheetTransition Ψ ht htarget).differentiableAt (by simp)).hasFDerivAt
  exact hd.comp (2 * t - 1, (0 : A)) (hasFDerivAt_sheetTimeCoordinates _)

end Wikipedia.SmoothSixDPoincare.StripNormalData
