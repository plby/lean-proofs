import Wikipedia.HopfProblem.DegreeCollapseMinimumDiskChart
import Wikipedia.HopfProblem.DegreeCollapseNativeSublevelDisk
import Wikipedia.SmoothSixDPoincare.MinimumDiskSublevel

/-!
# A whole minimum sublevel with a native smooth disk neighborhood

Compactness puts the complete small sublevel inside the signed Morse chart.
The normalized chart then covers it exactly, by the quadratic height
formula. The closed unit ball remains inside an open smooth source, and
its boundary image is exactly the regular level.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [T2Space M] [CompactSpace M]
  {f : M → ℝ} {p : M}

theorem exists_native_minimum_sublevel_disk (c : SignedMorseChart (E := E) f p)
    (hf : Continuous f) (hunique : ∀ x, f x ≤ f p → x = p)
    {b : ℝ} (hb : f p < b) :
    ∃ a ∈ Ioo (f p) b, Nonempty (NativeSublevelDisk (Module.finrank ℝ E) E f a) := by
  have hglobal : ∀ x, f p ≤ f x := by
    intro x
    by_contra! h
    have heq := hunique x h.le
    rw [heq] at h
    exact lt_irrefl _ h
  have hmin : IsLocalMin f p := Eventually.of_forall hglobal
  obtain ⟨R, hR, hblockR⟩ := c.exists_closed_productBlock
  obtain ⟨ε, hε, hsublevel⟩ := exists_small_sublevel_subset hf hunique
    c.splitChart.open_source c.splitChart_mem_source
  let δ := min ε (b - f p)
  have hδ : 0 < δ := lt_min hε (sub_pos.mpr hb)
  let ρ := min (R / 2) (min 1 (δ / 2))
  have hρ : 0 < ρ := lt_min (half_pos hR) (lt_min zero_lt_one (half_pos hδ))
  have hρR : ρ ≤ R / 2 := min_le_left _ _
  have hρone : ρ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hρδ : ρ ≤ δ / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hρsq : ρ ^ 2 < δ := by nlinarith
  have hsqε : ρ ^ 2 < ε := hρsq.trans_le (min_le_left _ _)
  have hsqb : ρ ^ 2 < b - f p := hρsq.trans_le (min_le_right _ _)
  let Φ := minimumDiskChart c hmin ρ hρ
  have hsource : closedBall (0 : Hemisphere.Ambient (Module.finrank ℝ E)) 1 ⊆ Φ.source := by
    intro v hv
    apply (minimumDiskChart_mem_source c hmin ρ hρ v).mpr
    apply hblockR
    constructor
    · exact mem_closedBall_self hR.le
    · rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hρ,
        LinearIsometryEquiv.norm_map]
      have hvnorm := mem_closedBall_zero_iff.mp hv
      nlinarith
  have hheight (v : Hemisphere.Ambient (Module.finrank ℝ E)) (hv : v ∈ Φ.source) :
      f (Φ v) = f p + ρ ^ 2 * ‖v‖ ^ 2 := minimumDiskChart_height c hmin ρ hρ v hv
  have hball : Φ '' closedBall (0 : Hemisphere.Ambient (Module.finrank ℝ E)) 1 =
      {y : M | f y ≤ f p + ρ ^ 2} := by
    ext y
    constructor
    · rintro ⟨v, hv, rfl⟩
      change f (Φ v) ≤ f p + ρ ^ 2
      rw [hheight v (hsource hv)]
      have hvnorm := mem_closedBall_zero_iff.mp hv
      have hvsq : ‖v‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg v]
      nlinarith [sq_nonneg ρ]
    · intro hy
      have hyS : y ∈ c.splitChart.source := hsublevel (by
        change f y ≤ f p + ρ ^ 2 at hy
        change f y ≤ f p + ε
        linarith)
      have hyT : y ∈ Φ.target := by
        rw [minimumDiskChart_target]
        exact hyS
      let v := Φ.symm y
      have hvS : v ∈ Φ.source := Φ.map_target' hyT
      have hval : Φ v = y := Φ.right_inv' hyT
      have hh := hheight v hvS
      rw [hval] at hh
      have hvnorm : ‖v‖ ≤ 1 := by
        have hvsq : ‖v‖ ^ 2 ≤ 1 := by
          change f y ≤ f p + ρ ^ 2 at hy
          nlinarith [sq_pos_of_pos hρ]
        nlinarith [norm_nonneg v]
      exact ⟨v, mem_closedBall_zero_iff.mpr hvnorm, hval⟩
  refine ⟨f p + ρ ^ 2, ⟨by linarith [sq_pos_of_pos hρ], by linarith⟩,
    ⟨⟨Φ, hsource, hball, ?_⟩⟩⟩
  ext y
  constructor
  · rintro ⟨v, hv, rfl⟩
    change f (Φ v) = f p + ρ ^ 2
    rw [hheight v (hsource (sphere_subset_closedBall hv)),
      mem_sphere_zero_iff_norm.mp hv, one_pow, mul_one]
  · intro hy
    have hyball : y ∈ Φ '' closedBall (0 : Hemisphere.Ambient (Module.finrank ℝ E)) 1 := by
      rw [hball]
      exact hy.le
    obtain ⟨v, hv, rfl⟩ := hyball
    have hh := hheight v (hsource hv)
    have hvnorm : ‖v‖ = 1 := by
      change f (Φ v) = f p + ρ ^ 2 at hy
      have hvsq : ‖v‖ ^ 2 = 1 := by nlinarith [sq_pos_of_pos hρ]
      nlinarith [norm_nonneg v]
    exact ⟨v, mem_sphere_zero_iff_norm.mpr hvnorm, rfl⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
