import Wikipedia.SmoothSixDPoincare.RetimedSheetTransition
import Wikipedia.SmoothSixDPoincare.WhitneySheetCorrection

/-!
# An actual nonlinear correction of the tangent-adapted coordinates

Use the original native sheet transitions, not arbitrary replacement maps.
The correction fixes the whole disk globally, retains the exact invertible
derivative along the bigon, and has both exact sheet restrictions for every
boundary time. Construction and shrinking of its smooth coordinate domain
remain separate from these identities.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.TubularBigon.TangentAdaptedChart

open WhitneyPairModel FrameField

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
  {k : CleanStripPatch (E := E) S T a k₀ k₁}
  {l : CleanStripPatch (E := E) T S b l₀ l₁}
  {tube : TubularBigon (E := E) S T a b k.map l.map h}
  {d : StripNormalData Plane (EuclideanSpace ℝ (Fin 3)) (E := E) S k.map}
  {e : StripNormalData Plane (EuclideanSpace ℝ (Fin 3)) (E := E) T l.map}
  (c : TangentAdaptedChart tube d e)

def shearedCoordinates : Space → ((ℝ × ℝ) × EuclideanSpace ℝ (Fin 4)) :=
  shearedMap c.base c.normal

def correctedCoordinates : Space → ((ℝ × ℝ) × EuclideanSpace ℝ (Fin 4)) :=
  correctedSheetMap c.shearedCoordinates (d.retimedSheetTransition tube.chart)
    (e.retimedSheetTransition tube.chart) h

theorem correctedCoordinates_zero (p : ℝ × ℝ) : c.correctedCoordinates (p, 0) = (p, 0) := by
  rw [correctedCoordinates, correctedSheetMap_zero]
  exact shearedMap_zero c.base c.normal p

theorem hasFDerivAt_shearedCoordinates_zero {p : ℝ × ℝ} (hp : p ∈ bigon h) :
    HasFDerivAt c.shearedCoordinates (shearedBlock (c.base p) (c.normal p)) (p, 0) :=
  hasFDerivAt_shearedMap_zero
    ((c.smooth_base.contDiffAt (c.open_domain.mem_nhds (c.contains hp))).differentiableAt (by simp))
    ((c.smooth_normal.contDiffAt (c.open_domain.mem_nhds (c.contains hp))).differentiableAt
      (by simp))

theorem hasFDerivAt_sheared_lower {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    HasFDerivAt (c.shearedCoordinates ∘ firstSheet)
      ((d.sheetDifferential tube.chart t).comp halfTimeDerivative) (2 * t - 1, 0) := by
  have hd := (c.hasFDerivAt_shearedCoordinates_zero (tube.lowerBoundaryArc_mem_bigon ht)).comp
    (2 * t - 1, (0 : Plane)) (hasFDerivAt_firstSheet (2 * t - 1, 0))
  rwa [lowerBoundaryArc, c.lower_model_tangent ht] at hd

theorem hasFDerivAt_sheared_upper {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    HasFDerivAt (c.shearedCoordinates ∘ secondSheet h)
      ((e.sheetDifferential tube.chart t).comp halfTimeDerivative) (2 * t - 1, 0) := by
  have hd := (c.hasFDerivAt_shearedCoordinates_zero (tube.upperBoundaryArc_mem_bigon ht)).comp
    (2 * t - 1, (0 : Plane)) (hasFDerivAt_secondSheet h (2 * t - 1, 0))
  rwa [c.upper_model_tangent ht] at hd

/-- The actual nonlinear correction retains the full original invertible block derivative. -/
theorem hasFDerivAt_correctedCoordinates_zero {p : ℝ × ℝ} (hp : p ∈ bigon h) :
    HasFDerivAt c.correctedCoordinates (shearedBlock (c.base p) (c.normal p)) (p, 0) := by
  have hpr := bigon_subset_rectangle tube.height_pos hp
  have ht : arcTime p ∈ Icc (0 : ℝ) 1 := by
    change 0 ≤ (p.1 + 1) / 2 ∧ (p.1 + 1) / 2 ≤ 1
    constructor <;> linarith [hpr.1.1, hpr.1.2]
  have htime : 2 * arcTime p - 1 = p.1 := by dsimp [arcTime]; ring
  have hRlo := d.hasFDerivAt_retimedSheetTransition tube.chart ht
    (tube.lower_chart_center_mem_target d ht)
  have hRhi := e.hasFDerivAt_retimedSheetTransition tube.chart ht
    (tube.upper_chart_center_mem_target e ht)
  have hGlo := c.hasFDerivAt_sheared_lower ht
  have hGhi := c.hasFDerivAt_sheared_upper ht
  rw [htime] at hRlo hRhi hGlo hGhi
  exact hasFDerivAt_correctedSheetMap_zero (c.hasFDerivAt_shearedCoordinates_zero hp)
    hRlo hGlo hRhi hGhi

theorem retimed_lower_center_eq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    d.retimedSheetTransition tube.chart (2 * t - 1, 0) =
      c.shearedCoordinates (firstSheet (2 * t - 1, 0)) := by
  change d.sheetTransition tube.chart (sheetTimeCoordinates (2 * t - 1, 0)) =
    shearedMap c.base c.normal ((2 * t - 1, 0), 0)
  rw [sheetTimeCoordinates_center, shearedMap_zero]
  exact (tube.lower_sheetTransition_center_germ d ht).eq_of_nhds

theorem retimed_upper_center_eq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    e.retimedSheetTransition tube.chart (2 * t - 1, 0) =
      c.shearedCoordinates (secondSheet h (2 * t - 1, 0)) := by
  change e.sheetTransition tube.chart (sheetTimeCoordinates (2 * t - 1, 0)) =
    shearedMap c.base c.normal (upperBoundaryArc h t, 0)
  rw [sheetTimeCoordinates_center, shearedMap_zero]
  exact (tube.upper_sheetTransition_center_germ e ht).eq_of_nhds

theorem retimed_lower_center_germ {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (fun s : ℝ => d.retimedSheetTransition tube.chart (s, 0)) =ᶠ[𝓝 (2 * t - 1)]
      (fun s => c.shearedCoordinates (firstSheet (s, 0))) := by
  have hct : ContinuousAt (fun s : ℝ => (s + 1) / 2) (2 * t - 1) := by fun_prop
  have heq : (2 * t - 1 + 1) / 2 = t := by ring
  have htime : Tendsto (fun s : ℝ => (s + 1) / 2) (𝓝 (2 * t - 1)) (𝓝 t) := by
    simpa only [heq] using hct.tendsto
  filter_upwards [(tube.lower_sheetTransition_center_germ d ht).comp_tendsto htime] with s hs
  change d.sheetTransition tube.chart (sheetTimeCoordinates (s, 0)) =
    shearedMap c.base c.normal ((s, 0), 0)
  rw [sheetTimeCoordinates_apply, shearedMap_zero]
  dsimp only [Function.comp_apply] at hs
  rw [hs]
  have hlin : 2 * ((s + 1) / 2) - 1 = s := by ring
  simp only [lowerBoundaryArc, hlin]

theorem retimed_upper_center_germ {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (fun s : ℝ => e.retimedSheetTransition tube.chart (s, 0)) =ᶠ[𝓝 (2 * t - 1)]
      (fun s => c.shearedCoordinates (secondSheet h (s, 0))) := by
  have hct : ContinuousAt (fun s : ℝ => (s + 1) / 2) (2 * t - 1) := by fun_prop
  have heq : (2 * t - 1 + 1) / 2 = t := by ring
  have htime : Tendsto (fun s : ℝ => (s + 1) / 2) (𝓝 (2 * t - 1)) (𝓝 t) := by
    simpa only [heq] using hct.tendsto
  filter_upwards [(tube.upper_sheetTransition_center_germ e ht).comp_tendsto htime] with s hs
  change e.sheetTransition tube.chart (sheetTimeCoordinates (s, 0)) =
    shearedMap c.base c.normal ((s, h * (1 - s ^ 2)), 0)
  rw [sheetTimeCoordinates_apply, shearedMap_zero]
  dsimp only [Function.comp_apply] at hs
  rw [hs]
  have hlin : 2 * ((s + 1) / 2) - 1 = s := by ring
  simp only [upperBoundaryArc, hlin]

/-- The corrected lower restriction is the original native sheet transition,
for every transverse input. -/
theorem correctedCoordinates_lower {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (u : Plane) :
    c.correctedCoordinates (firstSheet (2 * t - 1, u)) =
      d.retimedSheetTransition tube.chart (2 * t - 1, u) :=
  correctedSheetMap_lower _ (c.retimed_lower_center_eq ht)

/-- The upper restriction is exact at the same time, not merely to first order. -/
theorem correctedCoordinates_upper {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (v : Plane) :
    c.correctedCoordinates (secondSheet h (2 * t - 1, v)) =
      e.retimedSheetTransition tube.chart (2 * t - 1, v) :=
  correctedSheetMap_upper _ (c.retimed_upper_center_eq ht)

end Wikipedia.SmoothSixDPoincare.TubularBigon.TangentAdaptedChart
