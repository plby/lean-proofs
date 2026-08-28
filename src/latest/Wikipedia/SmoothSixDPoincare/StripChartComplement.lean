import Wikipedia.SmoothSixDPoincare.SmoothSheetDifferential
import Wikipedia.SmoothSixDPoincare.SmoothComplementQuotient

/-!
# The retained strip chart supplies an actual tangent complement

Differentiate the entire native sheet-chart transition into the tubular
chart. Its normal columns complement the original sheet differential, and
the full splitting is invertible and smooth along the actual chart overlap.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.StripNormalData

variable {A B Z E M : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  {S : Set M} {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
  (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞)

/-- The actual derivative of the entire retained ambient chart transition. -/
def tubularTransitionDerivative (t : ℝ) :
    StripCoordinates.Space A B →L[ℝ] ((ℝ × ℝ) × Z) :=
  fderiv ℝ (Ψ.symm ∘ d.chart) (StripCoordinates.center t)

/-- The complementary columns of that same actual transition. -/
def sheetComplement (t : ℝ) : B →L[ℝ] ((ℝ × ℝ) × Z) :=
  (d.tubularTransitionDerivative Ψ t).comp (ContinuousLinearMap.inr ℝ (ℝ × A) B)

theorem contDiffOn_tubularTransitionDerivative :
    ContDiffOn ℝ ∞ (d.tubularTransitionDerivative Ψ)
      {t | StripCoordinates.center t ∈ d.chart.source ∧
        d.chart (StripCoordinates.center t) ∈ Ψ.target} := by
  intro t ht
  have htransition : ContDiffAt ℝ ∞ (Ψ.symm ∘ d.chart) (StripCoordinates.center t) :=
    ((Ψ.contMDiffOn_invFun.contMDiffAt (Ψ.open_target.mem_nhds ht.2)).comp
      (StripCoordinates.center t)
      (d.chart.contMDiffOn_toFun.contMDiffAt (d.chart.open_source.mem_nhds ht.1))).contDiffAt
  have hc : ContDiff ℝ ∞ (StripCoordinates.center : ℝ → StripCoordinates.Space A B) :=
    (contDiff_id.prodMk contDiff_const).prodMk contDiff_const
  exact ((htransition.fderiv_right (by simp)).comp t hc.contDiffAt).contDiffWithinAt

theorem contDiffOn_sheetComplement :
    ContDiffOn ℝ ∞ (d.sheetComplement Ψ)
      {t | StripCoordinates.center t ∈ d.chart.source ∧
        d.chart (StripCoordinates.center t) ∈ Ψ.target} :=
  (d.contDiffOn_tubularTransitionDerivative Ψ).clm_comp contDiffOn_const

theorem bijective_tubularTransitionDerivative {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target) :
    Bijective (d.tubularTransitionDerivative Ψ t) := by
  unfold tubularTransitionDerivative
  rw [← mfderiv_eq_fderiv, mfderiv_comp (StripCoordinates.center t)
    (Ψ.symm.mdifferentiableAt (by simp) htarget)
    (d.chart.mdifferentiableAt (by simp) (d.line ht))]
  exact (PartialChart.bijective_mfderiv Ψ.symm htarget).comp
    (PartialChart.bijective_mfderiv d.chart (d.line ht))

/-- The sheet columns and complementary columns recover the entire actual chart derivative. -/
theorem sheet_coprod_complement_eq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target) :
    (d.sheetDifferential Ψ t).coprod (d.sheetComplement Ψ t) =
      d.tubularTransitionDerivative Ψ t := by
  rw [d.sheetDifferential_eq Ψ ht htarget]
  apply ContinuousLinearMap.ext
  intro z
  change d.tubularTransitionDerivative Ψ t (z.1, 0) +
    d.tubularTransitionDerivative Ψ t (0, z.2) = d.tubularTransitionDerivative Ψ t z
  rw [← map_add]
  simp

variable [FiniteDimensional ℝ A] [FiniteDimensional ℝ B]

/-- The complement is constructed from the chart, not a supplied frame hypothesis. -/
theorem isInvertible_sheet_coprod_complement {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target) :
    ((d.sheetDifferential Ψ t).coprod (d.sheetComplement Ψ t)).IsInvertible := by
  apply FrameField.isInvertible_coprod_of_bijective
  rw [d.sheet_coprod_complement_eq Ψ ht htarget]
  exact d.bijective_tubularTransitionDerivative Ψ ht htarget

end Wikipedia.SmoothSixDPoincare.StripNormalData
