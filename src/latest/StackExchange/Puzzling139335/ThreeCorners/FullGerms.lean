import StackExchange.Puzzling139335.ThreeCorners.FullBisector
import StackExchange.Puzzling139335.ThreeCorners.Rays

/-!
# Angular germs at full square corners

The full relative square neighborhood at a corner contains a small neighborhood
in the angular support cone determined by its outward bisector. In particular,
both inward rays have initial segments in the set.
-/

open Set Metric

namespace Puzzling139335.ThreeCorners

/-- The angular support cone satisfies the same sharp bisector projection
bound as a supporting right corner. -/
theorem supportCone_bisector_projection {a x : Plane} {θ : ℝ}
    (hx : x ∈ supportCone a θ) :
    inner ℝ (outwardBisector θ) (x - a) ≤ -‖x - a‖ := by
  have hparseval : (inner ℝ (ray θ) (x - a)) ^ 2 +
      (inner ℝ (perpRay θ) (x - a)) ^ 2 = ‖x - a‖ ^ 2 := by
    simpa [Fin.sum_univ_two] using (rayBasis θ).sum_sq_inner_right (x - a)
  have hsum : 0 ≤ inner ℝ (ray θ) (x - a) + inner ℝ (perpRay θ) (x - a) :=
    add_nonneg hx.1 hx.2
  have hprod : 0 ≤ inner ℝ (ray θ) (x - a) * inner ℝ (perpRay θ) (x - a) :=
    mul_nonneg hx.1 hx.2
  have hsq : ‖x - a‖ ^ 2 ≤
      (inner ℝ (ray θ) (x - a) + inner ℝ (perpRay θ) (x - a)) ^ 2 := by
    nlinarith
  have hnorm := (sq_le_sq₀ (norm_nonneg (x - a)) hsum).mp hsq
  rw [outwardBisector, inner_neg_left, inner_add_left]
  linarith

/-- A full square corner contains a full angular germ in the support cone
determined by any of its support-corner witnesses. -/
theorem exists_ball_inter_supportCone_subset {P : Set Plane} {a : Plane}
    (hfull : UnitPairs.IsFullSquareCorner P a) (h : SupportCorner P a)
    {θ : ℝ} (hθ : h.bisector = outwardBisector θ) :
    ∃ ε : ℝ, 0 < ε ∧ ball a ε ∩ supportCone a θ ⊆ P := by
  obtain ⟨f, hfa, _, ε, hε, hnear⟩ := hfull.exists_normalized
  have hmapb : f.linearIsometryEquiv h.bisector = outwardBisector 0 := by
    rw [outwardBisector_zero]
    simpa only [SupportCorner.bisector, SupportCorner.map, map_add] using
      UnitPairs.bisector_eq_of_origin_neighborhood (h.map f) hfa hε hnear
  refine ⟨min ε 1, lt_min hε zero_lt_one, ?_⟩
  rintro x ⟨hball, hcone⟩
  have hmap : f.linearIsometryEquiv (x - a) = f x := by
    simpa only [hfa, vsub_eq_sub, sub_zero] using f.map_vsub x a
  have hnorm : ‖f x‖ = ‖x - a‖ := by
    rw [← hmap, f.linearIsometryEquiv.norm_map]
  have hsmall : ‖f x‖ < min ε 1 := by
    simpa only [dist_eq_norm, ← hnorm] using mem_ball.mp hball
  have hproj : inner ℝ (outwardBisector 0) (f x) ≤ -‖f x‖ := by
    rw [← hmapb, ← hmap, f.linearIsometryEquiv.inner_map_map,
      f.linearIsometryEquiv.norm_map, hθ]
    exact supportCone_bisector_projection hcone
  have hcoords : 0 ≤ f x 0 ∧ 0 ≤ f x 1 := by
    have hc := CornerSupport.Equality.coords_nonneg_of_neg_sum_projection
      (rayBasis 0) (f x)
      (by simpa only [rayBasis_zero, rayBasis_one, outwardBisector] using hproj)
    simpa [Schoenflies.Plane.inner_eq, ray, perpRay] using hc
  have hupper (i : Fin 2) : f x i ≤ 1 := by
    have hi := PiLp.norm_apply_le (f x) i
    rw [Real.norm_eq_abs] at hi
    exact (le_abs_self _).trans (hi.trans (hsmall.le.trans (min_le_right _ _)))
  have hximage : f x ∈ f '' P := by
    apply hnear
    constructor
    · exact mem_ball.mpr (by
        rw [dist_zero_right]
        exact lt_of_lt_of_le hsmall (min_le_left _ _))
    · exact ⟨⟨hcoords.1, hupper 0⟩, ⟨hcoords.2, hupper 1⟩⟩
  obtain ⟨y, hy, hyx⟩ := hximage
  exact f.injective hyx ▸ hy

/-- Both inward rays at a full square corner have initial segments in the set. -/
theorem exists_small_rays_mem {P : Set Plane} {a : Plane}
    (hfull : UnitPairs.IsFullSquareCorner P a) (h : SupportCorner P a)
    {θ : ℝ} (hθ : h.bisector = outwardBisector θ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 ≤ t → t < ε →
      a + t • ray θ ∈ P ∧ a + t • perpRay θ ∈ P := by
  obtain ⟨ε, hε, hnear⟩ := exists_ball_inter_supportCone_subset hfull h hθ
  refine ⟨ε, hε, ?_⟩
  intro t ht htε
  have hball (u : Plane) (hu : ‖u‖ = 1) : a + t • u ∈ ball a ε := by
    apply mem_ball.mpr
    calc
      dist (a + t • u) a = ‖t • u‖ := by
        rw [dist_eq_norm]
        congr 1
        abel
      _ = t := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, hu, mul_one]
      _ < ε := htε
  constructor
  · apply hnear
    refine ⟨hball (ray θ) (norm_ray θ), ?_⟩
    exact (mem_supportCone_iff _ _ _).mpr ⟨t, 0, ht, le_rfl, by simp⟩
  · apply hnear
    refine ⟨hball (perpRay θ) (norm_perpRay θ), ?_⟩
    exact (mem_supportCone_iff _ _ _).mpr ⟨0, t, le_rfl, ht, by simp⟩

end Puzzling139335.ThreeCorners
