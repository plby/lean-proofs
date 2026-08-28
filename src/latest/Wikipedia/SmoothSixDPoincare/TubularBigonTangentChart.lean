import Wikipedia.SmoothSixDPoincare.TubularBigonAdaptedChart
import Wikipedia.SmoothSixDPoincare.SmoothSheetDifferential
import Wikipedia.SmoothSixDPoincare.ShearedTubularChart

/-!
# An actual tubular chart retaining full transverse sheet tangent vectors

The lower and upper disk components are taken from the original native sheet
differentials. They shear the constructed normal frame without changing its
invertibility. The resulting native chart retains the whole transverse tangent
vectors on both arcs, including their disk components, and fixes the disk.
Exact nonlinear sheet matching is still a separate construction.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.TubularBigon

open WhitneyPairModel FrameField

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
  {k : CleanStripPatch (E := E) S T a k₀ k₁}
  {l : CleanStripPatch (E := E) T S b l₀ l₁}

/-- A genuine chart with full transverse, not only normal, tangent matching. -/
structure TangentAdaptedChart
    (tube : TubularBigon (E := E) S T a b k.map l.map h)
    (d : StripNormalData Plane (EuclideanSpace ℝ (Fin 3)) (E := E) S k.map)
    (e : StripNormalData Plane (EuclideanSpace ℝ (Fin 3)) (E := E) T l.map) where
  base : (ℝ × ℝ) → ((Plane × Plane) →L[ℝ] (ℝ × ℝ))
  normal : (ℝ × ℝ) → ((Plane × Plane) →L[ℝ] EuclideanSpace ℝ (Fin 4))
  domain : Set (ℝ × ℝ)
  open_domain : IsOpen domain
  contains : bigon h ⊆ domain
  smooth_base : ContDiffOn ℝ ∞ base domain
  smooth_normal : ContDiffOn ℝ ∞ normal domain
  normal_invertible : ∀ p ∈ domain, (normal p).IsInvertible
  lower_transverse : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u : Plane,
    shearedBlock (base (2 * t - 1, 0)) (normal (2 * t - 1, 0)) (0, (u, 0)) =
      d.sheetDifferential tube.chart t (0, u)
  upper_transverse : ∀ t ∈ Icc (0 : ℝ) 1, ∀ v : Plane,
    shearedBlock (base (upperBoundaryArc h t)) (normal (upperBoundaryArc h t)) (0, (0, v)) =
      e.sheetDifferential tube.chart t (0, v)
  radius : ℝ
  radius_pos : 0 < radius
  chart : PartialDiffeomorph 𝓘(ℝ, Space) 𝓘(ℝ, E) Space M ∞
  source_contains : bigon h ×ˢ Metric.closedBall 0 radius ⊆ chart.source
  zero_section : ∀ p, chart (p, 0) = tube.map p
  coordinates : ∀ p, chart p = tube.chart (shearedMap base normal p)
  target_subset : chart.target ⊆ tube.chart.target
  transition_derivative : ∀ p ∈ bigon h, HasFDerivAt (tube.chart.symm ∘ chart)
    (shearedBlock (base p) (normal p)) (p, 0)

/-- Construct the tangent-adapted native chart from the actual opposite corner signs. -/
theorem nonempty_tangentAdaptedChart_of_opposite_corner_signs
    (tube : TubularBigon (E := E) S T a b k.map l.map h)
    (d : StripNormalData Plane (EuclideanSpace ℝ (Fin 3)) (E := E) S k.map)
    (e : StripNormalData Plane (EuclideanSpace ℝ (Fin 3)) (E := E) T l.map)
    (hsign : tube.sheetPairDet d e 0 * tube.sheetPairDet d e 1 < 0) :
    Nonempty (TangentAdaptedChart tube d e) := by
  obtain ⟨W, hW, hlo, O, hO, hKO, C, hC, hhi, hframe⟩ :=
    tube.exists_adapted_planar_frame_of_opposite_corner_signs d e hsign
  obtain ⟨Dlo, hDlo, hIDlo, hBlo⟩ := d.exists_open_sheetBaseFrame_domain tube.chart
    (fun t ht => tube.lower_chart_center_mem_target d ht)
  obtain ⟨Dhi, hDhi, hIDhi, hBhi⟩ := e.exists_open_sheetBaseFrame_domain tube.chart
    (fun t ht => tube.upper_chart_center_mem_target e ht)
  have htime (t y : ℝ) : arcTime (2 * t - 1, y) = t := by dsimp [arcTime]; ring
  have htq (t : ℝ) : arcTime (upperBoundaryArc h t) = t := htime t _
  have htimeK : MapsTo arcTime (bigon h) (Icc (0 : ℝ) 1) := by
    intro p hp
    have hpr := bigon_subset_rectangle tube.height_pos hp
    change 0 ≤ (p.1 + 1) / 2 ∧ (p.1 + 1) / 2 ≤ 1
    constructor <;> linarith [hpr.1.1, hpr.1.2]
  let U := O ∩ arcTime ⁻¹' (Dlo ∩ Dhi)
  have hU : IsOpen U := hO.inter ((hDlo.inter hDhi).preimage contDiff_arcTime.continuous)
  have hKU : bigon h ⊆ U :=
    fun p hp => ⟨hKO hp, hIDlo (htimeK hp), hIDhi (htimeK hp)⟩
  let A : (ℝ × ℝ) → ((Plane × Plane) →L[ℝ] (ℝ × ℝ)) := fun p =>
    (d.sheetBaseFrame tube.chart (arcTime p)).coprod (e.sheetBaseFrame tube.chart (arcTime p))
  let N : (ℝ × ℝ) → ((Plane × Plane) →L[ℝ] EuclideanSpace ℝ (Fin 4)) :=
    fun p => (W p).coprod (C p)
  have hA : ContDiffOn ℝ ∞ A U := contDiffOn_coprod
    (hBlo.comp contDiff_arcTime.contDiffOn (fun _ hp => hp.2.1))
    (hBhi.comp contDiff_arcTime.contDiffOn (fun _ hp => hp.2.2))
  have hN : ContDiffOn ℝ ∞ N U :=
    contDiffOn_coprod hW.contDiffOn (hC.mono inter_subset_left)
  have hiN : ∀ p ∈ U, (N p).IsInvertible :=
    fun p hp => isInvertible_coprod_of_bijective _ _ (hframe p hp.1)
  have hlow : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u : Plane,
      shearedBlock (A (2 * t - 1, 0)) (N (2 * t - 1, 0)) (0, (u, 0)) =
        d.sheetDifferential tube.chart t (0, u) := by
    intro t ht u
    have hWt : W (2 * t - 1, 0) = d.normalFrame tube.chart t := by
      have hg := (hlo t ht).eq_of_nhds
      dsimp only [Function.comp_apply] at hg
      rwa [htime] at hg
    rw [d.sheetDifferential_transverse_eq tube.chart ht
      (tube.lower_chart_center_mem_target d ht), shearedBlock_apply]
    simp only [A, N, ContinuousLinearMap.coprod_apply, map_zero, add_zero, zero_add, htime, hWt]
  have hupp : ∀ t ∈ Icc (0 : ℝ) 1, ∀ v : Plane,
      shearedBlock (A (upperBoundaryArc h t)) (N (upperBoundaryArc h t)) (0, (0, v)) =
        e.sheetDifferential tube.chart t (0, v) := by
    intro t ht v
    rw [e.sheetDifferential_transverse_eq tube.chart ht
      (tube.upper_chart_center_mem_target e ht), shearedBlock_apply]
    simp only [A, N, ContinuousLinearMap.coprod_apply, map_zero, zero_add, htq, hhi t ht]
  have hz : bigon h ×ˢ {(0 : EuclideanSpace ℝ (Fin 4))} ⊆ tube.chart.source := by
    rintro ⟨p, z⟩ ⟨hp, hz⟩
    have hz0 : z = 0 := hz
    subst z
    exact tube.source_contains ⟨hp, Metric.mem_closedBall_self tube.radius_pos.le⟩
  obtain ⟨ε, hε, Φ, hsource, hformula, htarget, -, hderiv⟩ :=
    exists_sheared_tubular_chart tube.chart (isCompact_bigon tube.height_pos) hU hKU hz hA hN
      (fun p hp => hiN p (hKU hp))
  refine ⟨{
    base := A
    normal := N
    domain := U
    open_domain := hU
    contains := hKU
    smooth_base := hA
    smooth_normal := hN
    normal_invertible := hiN
    lower_transverse := hlow
    upper_transverse := hupp
    radius := ε
    radius_pos := hε
    chart := Φ
    source_contains := hsource
    zero_section := ?_
    coordinates := hformula
    target_subset := htarget
    transition_derivative := hderiv }⟩
  intro p
  rw [hformula, shearedMap_zero, tube.zero_section]

end Wikipedia.SmoothSixDPoincare.TubularBigon
