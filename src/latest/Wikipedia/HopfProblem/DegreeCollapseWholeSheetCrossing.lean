import Wikipedia.HopfProblem.DegreeCollapseLongitudinalMotionGerms

/-!
# Exactly one intersection between the full original sheets

For two initially disjoint embedded sheets recognized by complementary
planes throughout the tube, the constructed ambient motion produces one
intersection event. This counts the full original sheets, including the
annulus around the selected disk and every point outside the tube.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {U V E H M X Y : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × (U × V)) J (ℝ × (U × V)) M ∞}

theorem LongitudinalTubeMotion.whole_sheet_crossing_iff
    (A : LongitudinalTubeMotion Φ) {f : X → M} {g : Y → M}
    (hfi : Injective f) (hgi : Injective g) (hdisj : Disjoint (range f) (range g))
    (hrecf : ∀ z ∈ Φ.source, Φ z ∈ range f ↔ z.1 = 0 ∧ z.2.2 = 0)
    (hrecg : ∀ z ∈ Φ.source, Φ z ∈ range g ↔ z.1 = 1 ∧ z.2.1 = 0)
    (x₀ : X) (y₀ : Y) (hx₀ : Φ 0 = f x₀) (hy₀ : Φ (1, 0) = g y₀)
    (h0 : (0 : ℝ × (U × V)) ∈ Φ.source) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (x : X) (y : Y) :
    A.family (t, f x) = g y ↔ t = A.time ∧ x = x₀ ∧ y = y₀ := by
  constructor
  · intro he
    have htarget : f x ∈ Φ.target := by
      by_contra hn
      have hxy : f x = g y := (A.fixed_outside_target t (f x) hn).symm.trans he
      exact (disjoint_left.mp hdisj) ⟨x, rfl⟩ ⟨y, hxy.symm⟩
    let z := Φ.symm (f x)
    have hz : z ∈ Φ.source := Φ.map_target htarget
    have hzfx : Φ z = f x := Φ.right_inv htarget
    have hfz := (hrecf z hz).mp ⟨x, hzfx.symm⟩
    let w := longitudinalBlend A.profile A.cutoff Real.smoothTransition (t, z)
    have hw : w ∈ Φ.source := A.model_source t z hz
    have hwgy : Φ w = g y := by
      calc
        Φ w = A.family (t, Φ z) := (A.formula t z hz).symm
        _ = A.family (t, f x) := congrArg (fun p => A.family (t, p)) hzfx
        _ = g y := he
    have hgw := (hrecg w hw).mp ⟨y, hwgy.symm⟩
    have hu : z.2.1 = 0 := hgw.2
    have hz0 : z = 0 := Prod.ext hfz.1 (Prod.ext hu hfz.2)
    have hwaxis : w = (Real.smoothTransition t * A.destination, 0) := by
      dsimp only [w]
      rw [hz0]
      exact A.model_axis t
    have htimevalue : Real.smoothTransition t * A.destination = 1 :=
      (congrArg Prod.fst hwaxis).symm.trans hgw.1
    have htτ : t = A.time := (A.unique_time t ht).mp htimevalue
    have hx : x = x₀ := hfi (hzfx.symm.trans ((congrArg Φ hz0).trans hx₀))
    have hwy : Φ w = g y₀ := by
      rw [hwaxis, htimevalue]
      exact hy₀
    exact ⟨htτ, hx, hgi (hwgy.symm.trans hwy)⟩
  · rintro ⟨ht, hx, hy⟩
    rw [ht, hx, hy]
    calc
      A.family (A.time, f x₀) = A.family (A.time, Φ 0) :=
        congrArg (fun p => A.family (A.time, p)) hx₀.symm
      _ = Φ (1, 0) := A.crossing_axis h0
      _ = g y₀ := hy₀

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
