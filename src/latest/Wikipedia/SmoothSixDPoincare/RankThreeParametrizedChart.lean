import Wikipedia.SmoothSixDPoincare.RankThreeCorrectionDomain

/-!
# A constructed native chart with exact parametrized sheet restrictions

The simultaneous nonlinear correction has the same invertible zero-section
derivative as the adapted shear. Compactness supplies one genuine native
partial diffeomorphism with a uniform positive radius. Its two model-sheet
restrictions are exactly the original native sheet parametrizations on the
whole open source, not only on the closed arcs or at the tangent level.

This records parametrized inclusion. Recognition of the full original sheet
images after shrinking, and support control for a Whitney move, remain separate.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.TubularBigon

open WhitneyPairModel (bigon isCompact_bigon sheetTimeCoordinates)
open RankThreeWhitneyModel FrameField

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
  {k : CleanStripPatch (E := E) S T a k₀ k₁}
  {l : CleanStripPatch (E := E) T S b l₀ l₁}

/-- The genuine chart has both exact native sheet restrictions and their valid chart parameters. -/
structure RankThreeSheetParametrizedChart
    (tube : TubularBigon (E := E) S T a b k.map l.map h 3)
    (d : StripNormalData Lower (EuclideanSpace ℝ (Fin 3)) (E := E) S k.map)
    (e : StripNormalData Upper (EuclideanSpace ℝ (Fin 2)) (E := E) T l.map) where
  radius : ℝ
  radius_pos : 0 < radius
  chart : PartialDiffeomorph 𝓘(ℝ, Space) 𝓘(ℝ, E) Space M ∞
  source_contains : bigon h ×ˢ Metric.closedBall 0 radius ⊆ chart.source
  zero_section : ∀ p, chart (p, 0) = tube.map p
  target_subset : chart.target ⊆ tube.chart.target
  lower_source : ∀ q : LowerSheet, firstSheet q ∈ chart.source →
    (sheetTimeCoordinates q, (0 : EuclideanSpace ℝ (Fin 3))) ∈ d.chart.source
  upper_source : ∀ q : UpperSheet, secondSheet h q ∈ chart.source →
    (sheetTimeCoordinates q, (0 : EuclideanSpace ℝ (Fin 2))) ∈ e.chart.source
  lower : ∀ q : LowerSheet, firstSheet q ∈ chart.source →
    chart (firstSheet q) = d.chart (sheetTimeCoordinates q, 0)
  upper : ∀ q : UpperSheet, secondSheet h q ∈ chart.source →
    chart (secondSheet h q) = e.chart (sheetTimeCoordinates q, 0)

namespace RankThreeTangentAdaptedChart

variable {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
  {d : StripNormalData Lower (EuclideanSpace ℝ (Fin 3)) (E := E) S k.map}
  {e : StripNormalData Upper (EuclideanSpace ℝ (Fin 2)) (E := E) T l.map}

/-- Construct an actual native chart with both nonlinear restrictions
from the adapted tangents. -/
theorem nonempty_rankThreeSheetParametrizedChart (c : RankThreeTangentAdaptedChart tube d e) :
    Nonempty (RankThreeSheetParametrizedChart tube d e) := by
  have hinj : InjOn c.correctedCoordinates (bigon h ×ˢ {(0 : Lower × Upper)}) := by
    rintro ⟨p, z⟩ ⟨hp, hz⟩ ⟨q, w⟩ ⟨hq, hw⟩ heq
    have hz0 : z = 0 := hz
    have hw0 : w = 0 := hw
    subst z
    subst w
    rw [c.correctedCoordinates_zero, c.correctedCoordinates_zero] at heq
    exact Prod.ext (congrArg (fun v : (ℝ × ℝ) × EuclideanSpace ℝ (Fin 3) => v.1) heq) rfl
  have hlocal : ∀ p ∈ bigon h ×ˢ {(0 : Lower × Upper)},
      IsLocalDiffeomorphAt 𝓘(ℝ, Space) 𝓘(ℝ, (ℝ × ℝ) × EuclideanSpace ℝ (Fin 3)) ∞
        c.correctedCoordinates p := by
    rintro ⟨p, z⟩ ⟨hp, hz⟩
    have hz0 : z = 0 := hz
    subst z
    apply isLocalDiffeomorphAt_of_contMDiffOn
      (D := Space) (E := (ℝ × ℝ) × EuclideanSpace ℝ (Fin 3))
      (M := (ℝ × ℝ) × EuclideanSpace ℝ (Fin 3))
      c.isOpen_nonlinearDomain (c.nonlinearDomain_contains_zero hp)
      c.contDiffOn_correctedCoordinates.contMDiffOn
    rw [mfderiv_eq_fderiv, (c.hasFDerivAt_correctedCoordinates_zero hp).fderiv]
    exact isInvertible_shearedBlock (c.base p) (c.normal p)
      (c.normal_invertible p (c.contains hp))
  have hzeroDomain : bigon h ×ˢ {(0 : Lower × Upper)} ⊆ c.nonlinearDomain := by
    rintro ⟨p, z⟩ ⟨hp, hz⟩
    have hz0 : z = 0 := hz
    subst z
    exact c.nonlinearDomain_contains_zero hp
  obtain ⟨χ, hzeroχ, hχD, hχ⟩ := exists_partialDiffeomorph_near_compact
    ((isCompact_bigon tube.height_pos).prod isCompact_singleton) hinj hlocal
      c.isOpen_nonlinearDomain hzeroDomain
  let Φ := χ.trans tube.chart
  have hzeroΦ : bigon h ×ˢ {(0 : Lower × Upper)} ⊆ Φ.source := by
    rintro ⟨p, z⟩ ⟨hp, hz⟩
    have hz0 : z = 0 := hz
    subst z
    refine ⟨hzeroχ ⟨hp, rfl⟩, ?_⟩
    change χ (p, 0) ∈ tube.chart.source
    rw [hχ, c.correctedCoordinates_zero]
    exact tube.source_contains ⟨hp, Metric.mem_closedBall_self tube.radius_pos.le⟩
  obtain ⟨ε, hε, hsource⟩ := DiskFraming.exists_pos_prod_closedBall_subset
    (isCompact_bigon tube.height_pos) Φ.open_source hzeroΦ
  have hformula (p : Space) : Φ p = tube.chart (c.correctedCoordinates p) := by
    change tube.chart (χ p) = tube.chart (c.correctedCoordinates p)
    rw [hχ]
  refine ⟨{
    radius := ε
    radius_pos := hε
    chart := Φ
    source_contains := hsource
    zero_section := ?_
    target_subset := fun _ hy => hy.1
    lower_source := fun q hq => (c.lower_native_parameters (hχD hq.1)).1
    upper_source := fun q hq => (c.upper_native_parameters (hχD hq.1)).1
    lower := ?_
    upper := ?_ }⟩
  · intro p
    rw [hformula, c.correctedCoordinates_zero, tube.zero_section]
  · intro q hq
    rw [hformula, c.correctedCoordinates_lower_of_mem_domain (hχD hq.1)]
    exact tube.chart.right_inv' (c.lower_native_parameters (hχD hq.1)).2
  · intro q hq
    rw [hformula, c.correctedCoordinates_upper_of_mem_domain (hχD hq.1)]
    exact tube.chart.right_inv' (c.upper_native_parameters (hχD hq.1)).2

end RankThreeTangentAdaptedChart

/-- Opposite actual corner signs construct a genuine chart
with both exact sheet parametrizations. -/
theorem nonempty_rankThreeSheetParametrizedChart_of_opposite_corner_signs
    (tube : TubularBigon (E := E) S T a b k.map l.map h 3)
    (d : StripNormalData Lower (EuclideanSpace ℝ (Fin 3)) (E := E) S k.map)
    (e : StripNormalData Upper (EuclideanSpace ℝ (Fin 2)) (E := E) T l.map)
    (hsign : tube.rankThreeSheetPairDet d e 0 * tube.rankThreeSheetPairDet d e 1 < 0) :
    Nonempty (RankThreeSheetParametrizedChart tube d e) := by
  obtain ⟨c⟩ := tube.nonempty_rankThreeTangentAdaptedChart_of_opposite_corner_signs d e hsign
  exact c.nonempty_rankThreeSheetParametrizedChart

namespace RankThreeSheetParametrizedChart

variable {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
  {d : StripNormalData Lower (EuclideanSpace ℝ (Fin 3)) (E := E) S k.map}
  {e : StripNormalData Upper (EuclideanSpace ℝ (Fin 2)) (E := E) T l.map}
  (c : RankThreeSheetParametrizedChart tube d e)

theorem lower_mem_sheet {q : LowerSheet} (hq : firstSheet q ∈ c.chart.source) :
    c.chart (firstSheet q) ∈ S := by
  rw [c.lower q hq]
  exact (d.sheet _ (c.lower_source q hq)).mpr rfl

theorem upper_mem_sheet {q : UpperSheet} (hq : secondSheet h q ∈ c.chart.source) :
    c.chart (secondSheet h q) ∈ T := by
  rw [c.upper q hq]
  exact (e.sheet _ (c.upper_source q hq)).mpr rfl

end RankThreeSheetParametrizedChart

end Wikipedia.SmoothSixDPoincare.TubularBigon
