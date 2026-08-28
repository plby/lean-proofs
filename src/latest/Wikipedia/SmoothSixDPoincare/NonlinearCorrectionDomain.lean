import Wikipedia.SmoothSixDPoincare.TubularBigonNonlinearCorrection

/-!
# A genuine open domain for the nonlinear sheet correction

Every original sheet point and center lies in its actual native chart overlap.
The simultaneous center-matching locus is open and contains all boundary times,
including neighborhoods of both endpoints. The resulting correction domain
contains the entire compact zero section and supports both exact restrictions.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.TubularBigon.TangentAdaptedChart

open WhitneyPairModel FrameField SheetCorrection

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
  {k : CleanStripPatch (E := E) S T a k₀ k₁}
  {l : CleanStripPatch (E := E) T S b l₀ l₁}
  {tube : TubularBigon (E := E) S T a b k.map l.map h}
  {d : StripNormalData Plane (EuclideanSpace ℝ (Fin 3)) (E := E) S k.map}
  {e : StripNormalData Plane (EuclideanSpace ℝ (Fin 3)) (E := E) T l.map}
  (c : TangentAdaptedChart tube d e)

def shearedDomain : Set Space := Prod.fst ⁻¹' c.domain

def lowerCorrectionDomain : Set Sheet :=
  d.retimedDomain tube.chart ∩ firstSheet ⁻¹' c.shearedDomain

def upperCorrectionDomain : Set Sheet :=
  e.retimedDomain tube.chart ∩ secondSheet h ⁻¹' c.shearedDomain

def centerMatchingTimes : Set ℝ := interior {s |
  d.retimedSheetTransition tube.chart (s, 0) = c.shearedCoordinates (firstSheet (s, 0)) ∧
  e.retimedSheetTransition tube.chart (s, 0) = c.shearedCoordinates (secondSheet h (s, 0))}

def nonlinearDomain : Set Space :=
  correctionDomain c.shearedDomain c.lowerCorrectionDomain c.upperCorrectionDomain ∩
    (fun p : Space => p.1.1) ⁻¹' c.centerMatchingTimes

theorem isOpen_shearedDomain : IsOpen c.shearedDomain := c.open_domain.preimage continuous_fst

theorem isOpen_lowerCorrectionDomain : IsOpen c.lowerCorrectionDomain :=
  (d.isOpen_retimedDomain tube.chart).inter
    (c.isOpen_shearedDomain.preimage contDiff_firstSheet.continuous)

theorem isOpen_upperCorrectionDomain : IsOpen c.upperCorrectionDomain :=
  (e.isOpen_retimedDomain tube.chart).inter
    (c.isOpen_shearedDomain.preimage (contDiff_secondSheet h).continuous)

theorem isOpen_nonlinearDomain : IsOpen c.nonlinearDomain :=
  (isOpen_correctionDomain c.isOpen_shearedDomain c.isOpen_lowerCorrectionDomain
    c.isOpen_upperCorrectionDomain).inter (isOpen_interior.preimage (by fun_prop))

theorem contDiffOn_correctedCoordinates :
    ContDiffOn ℝ ∞ c.correctedCoordinates c.nonlinearDomain := by
  have hG : ContDiffOn ℝ ∞ c.shearedCoordinates c.shearedDomain :=
    contDiffOn_shearedMap c.smooth_base c.smooth_normal
  exact (contDiffOn_correctedSheetMap hG
    ((d.contDiffOn_retimedSheetTransition tube.chart).mono inter_subset_left)
    (hG.comp contDiff_firstSheet.contDiffOn (fun _ hp => hp.2))
    ((e.contDiffOn_retimedSheetTransition tube.chart).mono inter_subset_left)
    (hG.comp (contDiff_secondSheet h).contDiffOn (fun _ hp => hp.2))).mono inter_subset_left

theorem centerMatchingTimes_contains {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    2 * t - 1 ∈ c.centerMatchingTimes :=
  mem_interior_iff_mem_nhds.mpr
    ((c.retimed_lower_center_germ ht).and (c.retimed_upper_center_germ ht))

theorem lowerCorrectionDomain_contains_center {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (2 * t - 1, (0 : Plane)) ∈ c.lowerCorrectionDomain := by
  refine ⟨d.retimedDomain_contains_center tube.chart ht
    (tube.lower_chart_center_mem_target d ht), ?_⟩
  exact c.contains (tube.lowerBoundaryArc_mem_bigon ht)

theorem upperCorrectionDomain_contains_center {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (2 * t - 1, (0 : Plane)) ∈ c.upperCorrectionDomain := by
  refine ⟨e.retimedDomain_contains_center tube.chart ht
    (tube.upper_chart_center_mem_target e ht), ?_⟩
  exact c.contains (tube.upperBoundaryArc_mem_bigon ht)

/-- All domain and center-matching requirements hold on the whole original bigon. -/
theorem nonlinearDomain_contains_zero {p : ℝ × ℝ} (hp : p ∈ bigon h) :
    (p, (0 : Plane × Plane)) ∈ c.nonlinearDomain := by
  have hpr := bigon_subset_rectangle tube.height_pos hp
  have ht : arcTime p ∈ Icc (0 : ℝ) 1 := by
    change 0 ≤ (p.1 + 1) / 2 ∧ (p.1 + 1) / 2 ≤ 1
    constructor <;> linarith [hpr.1.1, hpr.1.2]
  have htime : 2 * arcTime p - 1 = p.1 := by dsimp [arcTime]; ring
  have hlo := c.lowerCorrectionDomain_contains_center ht
  have hhi := c.upperCorrectionDomain_contains_center ht
  have hmatch := c.centerMatchingTimes_contains ht
  rw [htime] at hlo hhi hmatch
  exact ⟨⟨c.contains hp, ⟨hlo, hlo⟩, ⟨hhi, hhi⟩⟩, hmatch⟩

theorem lower_native_parameters {q : Sheet} (hq : firstSheet q ∈ c.nonlinearDomain) :
    (sheetTimeCoordinates q, (0 : EuclideanSpace ℝ (Fin 3))) ∈ d.chart.source ∧
      d.chart (sheetTimeCoordinates q, 0) ∈ tube.chart.target :=
  hq.1.2.1.1.1

theorem upper_native_parameters {q : Sheet} (hq : secondSheet h q ∈ c.nonlinearDomain) :
    (sheetTimeCoordinates q, (0 : EuclideanSpace ℝ (Fin 3))) ∈ e.chart.source ∧
      e.chart (sheetTimeCoordinates q, 0) ∈ tube.chart.target :=
  hq.1.2.2.1.1

/-- The lower restriction is exact throughout the open domain, including beyond both endpoints. -/
theorem correctedCoordinates_lower_of_mem_domain {q : Sheet}
    (hq : firstSheet q ∈ c.nonlinearDomain) :
    c.correctedCoordinates (firstSheet q) = d.retimedSheetTransition tube.chart q := by
  have hJ : q.1 ∈ c.centerMatchingTimes := hq.2
  have hm := (show c.centerMatchingTimes ⊆ {s : ℝ |
    d.retimedSheetTransition tube.chart (s, 0) = c.shearedCoordinates (firstSheet (s, 0)) ∧
    e.retimedSheetTransition tube.chart (s, 0) =
      c.shearedCoordinates (secondSheet h (s, 0))} from interior_subset) hJ
  exact correctedSheetMap_lower q hm.1

/-- The upper restriction is exact throughout the same genuine open domain. -/
theorem correctedCoordinates_upper_of_mem_domain {q : Sheet}
    (hq : secondSheet h q ∈ c.nonlinearDomain) :
    c.correctedCoordinates (secondSheet h q) = e.retimedSheetTransition tube.chart q := by
  have hJ : q.1 ∈ c.centerMatchingTimes := hq.2
  have hm := (show c.centerMatchingTimes ⊆ {s : ℝ |
    d.retimedSheetTransition tube.chart (s, 0) = c.shearedCoordinates (firstSheet (s, 0)) ∧
    e.retimedSheetTransition tube.chart (s, 0) =
      c.shearedCoordinates (secondSheet h (s, 0))} from interior_subset) hJ
  exact correctedSheetMap_upper q hm.2

end Wikipedia.SmoothSixDPoincare.TubularBigon.TangentAdaptedChart
