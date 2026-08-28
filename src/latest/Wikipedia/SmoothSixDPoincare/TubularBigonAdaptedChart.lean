import Wikipedia.SmoothSixDPoincare.TubularBigonAdaptedFrame
import Wikipedia.SmoothSixDPoincare.ReframedTubularChart

/-!
# Actual tubular coordinates with the constructed adapted normal frame

The chart is obtained by composing the original tubular chart with the
constructed frame change. Its normal derivative columns are the original
sheet normal columns on their respective arcs. This does not yet identify
the full sheet tangent maps or the nonlinear sheet images with the Whitney
model: their disk-tangent components and nonlinear terms remain to handle.
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

/-- A genuine positive-radius chart with a proved normal-frame restriction to both sheets. -/
structure NormalAdaptedChart
    (tube : TubularBigon (E := E) S T a b k.map l.map h)
    (d : StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 3))
      (E := E) S k.map)
    (e : StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 3))
      (E := E) T l.map) where
  first : (ℝ × ℝ) → (EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 4))
  second : (ℝ × ℝ) → (EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 4))
  domain : Set (ℝ × ℝ)
  open_domain : IsOpen domain
  contains : bigon h ⊆ domain
  smooth_first : ContDiff ℝ ∞ first
  smooth_second : ContDiffOn ℝ ∞ second domain
  lower_germ : ∀ t ∈ Icc (0 : ℝ) 1,
    first =ᶠ[𝓝 (2 * t - 1, 0)] (d.normalFrame tube.chart ∘ arcTime)
  upper : ∀ t ∈ Icc (0 : ℝ) 1,
    second (upperBoundaryArc h t) = e.normalFrame tube.chart t
  frame : ∀ p ∈ domain, Bijective ((first p).coprod (second p))
  radius : ℝ
  radius_pos : 0 < radius
  chart : PartialDiffeomorph 𝓘(ℝ, Space) 𝓘(ℝ, E) Space M ∞
  source_contains : bigon h ×ˢ Metric.closedBall 0 radius ⊆ chart.source
  zero_section : ∀ p, chart (p, 0) = tube.map p
  coordinates : ∀ p z, chart (p, z) = tube.chart (p, ((first p).coprod (second p)) z)
  target_subset : chart.target ⊆ tube.chart.target
  transition_derivative : ∀ p ∈ bigon h, HasFDerivAt (tube.chart.symm ∘ chart)
    ((ContinuousLinearMap.id ℝ (ℝ × ℝ)).prodMap ((first p).coprod (second p))) (p, 0)

/-- Construct the entire normal-adapted native chart from the actual opposite corner signs. -/
theorem nonempty_normalAdaptedChart_of_opposite_corner_signs
    (tube : TubularBigon (E := E) S T a b k.map l.map h)
    (d : StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 3))
      (E := E) S k.map)
    (e : StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 3))
      (E := E) T l.map)
    (hsign : tube.sheetPairDet d e 0 * tube.sheetPairDet d e 1 < 0) :
    Nonempty (NormalAdaptedChart tube d e) := by
  obtain ⟨W, hW, hlo, O, hO, hKO, C, hC, hhi, hframe⟩ :=
    tube.exists_adapted_planar_frame_of_opposite_corner_signs d e hsign
  have hz : bigon h ×ˢ {(0 : EuclideanSpace ℝ (Fin 4))} ⊆ tube.chart.source := by
    rintro ⟨p, z⟩ ⟨hp, hz⟩
    have hz0 : z = 0 := hz
    subst z
    exact tube.source_contains ⟨hp, Metric.mem_closedBall_self tube.radius_pos.le⟩
  obtain ⟨ε, hε, Φ, hsource, hformula, htarget, -, hderiv⟩ :=
    exists_reframed_tubular_chart tube.chart (isCompact_bigon tube.height_pos) hO hKO hz
      (contDiffOn_coprod hW.contDiffOn hC)
      (fun p hp => isInvertible_coprod_of_bijective (W p) (C p) (hframe p hp))
  refine ⟨{
    first := W
    second := C
    domain := O
    open_domain := hO
    contains := hKO
    smooth_first := hW
    smooth_second := hC
    lower_germ := hlo
    upper := hhi
    frame := hframe
    radius := ε
    radius_pos := hε
    chart := Φ
    source_contains := hsource
    zero_section := ?_
    coordinates := fun p z => hformula (p, z)
    target_subset := htarget
    transition_derivative := hderiv }⟩
  intro p
  rw [hformula, fiberMap_zero, tube.zero_section]

end Wikipedia.SmoothSixDPoincare.TubularBigon
