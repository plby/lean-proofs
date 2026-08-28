import Wikipedia.NoExoticSixSphere.SphereFourTubeHalfCover

/-!
# Exact maps on the core-complement/open-tube overlap

The punctured open tube projects to `S³ × S³` by normal normalization.
Its map to the exterior is exactly the actual unit boundary map, and
its map to the tube core is exactly the first projection. These are
equalities of continuous maps before passing to singular homology.
-/

noncomputable section

open Function Set ContinuousMap
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.SphereFourTube

open GLOrthonormalization Wikipedia.HopfProblem.DegreeCollapse.TimeCollar

theorem normalClamp_eq_retract (b : Sphere 3) {v : Vector 4}
    (hv : v ≠ 0) (hn : ‖v‖ ≤ 1) : normalClamp v = (SphereRadialRetraction.retract b v).val := by
  simp only [normalClamp, max_eq_left hn, one_div, SphereRadialRetraction.retract,
    dif_neg hv, NormedSpace.normalize]

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [T2Space M]
  (Φ : PartialDiffeomorph ((𝓡 3).prod (𝓡 4)) (𝓡 7) (Sphere 3 × Vector 4) M ∞)

abbrev HalfOverlap (t : M → ℝ) := ↥(halfCoreComplement Φ t ∩ halfOpenTube Φ t)

def overlapLeft (t : M → ℝ) : C(HalfOverlap Φ t, halfCoreComplement Φ t) :=
  ContinuousMap.inclusion inter_subset_left

def overlapRight (t : M → ℝ) : C(HalfOverlap Φ t, halfOpenTube Φ t) :=
  ContinuousMap.inclusion inter_subset_right

theorem overlap_normal_ne_zero (hΦ : Φ.source = univ) (t : M → ℝ) (x : HalfOverlap Φ t) :
    (Φ.symm x.val.val).2 ≠ 0 := by
  intro hz
  exact x.property.1 ((core_mem_iff Φ hΦ x.val.val).mpr
    ⟨halfTube_mem_target Φ hΦ t (overlapRight Φ t x), hz⟩)

theorem overlap_normal_lt_one (hΦ : Φ.source = univ) (t : M → ℝ) (x : HalfOverlap Φ t) :
    ‖(Φ.symm x.val.val).2‖ < 1 := ((mem_openRegion_iff Φ hΦ 1 x.val.val).mp x.property.2).2

def overlapDirection (hΦ : Φ.source = univ) (t : M → ℝ) (b : Sphere 3) :
    C(HalfOverlap Φ t, Sphere 3 × Sphere 3) := by
  let : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨by simp⟩
  let i := (halfTubeInverse Φ hΦ t).comp (overlapRight Φ t)
  have hr : Continuous (fun x : HalfOverlap Φ t ↦ SphereRadialRetraction.retract b (i x).2) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (SphereRadialRetraction.contMDiffAt_retract (n := 3) b
      (overlap_normal_ne_zero Φ hΦ t x)).continuousAt.comp
        (f := fun y : HalfOverlap Φ t ↦ (i y).2) i.continuous.snd.continuousAt
  exact ⟨fun x ↦ ((i x).1, SphereRadialRetraction.retract b (i x).2),
    i.continuous.fst.prodMk hr⟩

theorem overlap_projection (hΦ : Φ.source = univ) (t : M → ℝ) (b : Sphere 3) :
    (halfTubeProjection Φ hΦ t).comp (overlapRight Φ t) =
      ContinuousMap.fst.comp (overlapDirection Φ hΦ t b) := rfl

variable (hΦ : Φ.source = univ) (t τ : C(M, ℝ))
  (hpos : ∀ x ∈ Φ.target, 0 < t x)
  (hhalf : ∀ x, 0 ≤ τ x ↔ 0 ≤ t x ∧ x ∉ openRegion Φ 1)
  (hinner : ∀ p : Sphere 3 × Vector 4, ‖p.2‖ ≤ 3 / 2 → τ (Φ p) = ‖p.2‖ ^ 2 - 1)

include hΦ hpos in
theorem rawRetraction_time_nonneg (x : CoreComplement Φ) (hx : 0 ≤ t x.val) :
    0 ≤ t (rawRetraction Φ x) := by
  classical
  by_cases hxT : x.val ∈ Φ.target
  · rw [rawRetraction, if_pos hxT]
    exact (hpos _ (Φ.toPartialEquiv.map_source (hΦ.symm ▸ mem_univ _))).le
  · simpa only [rawRetraction, if_neg hxT] using hx

def halfComplementRetraction : C(halfCoreComplement Φ t, NonnegativeHalf τ) := by
  let f := forgetHalfCoreComplement Φ t
  refine ⟨fun x ↦ ⟨rawRetraction Φ (f x), (hhalf _).mpr
    ⟨rawRetraction_time_nonneg Φ hΦ t hpos (f x) x.val.property,
      rawRetraction_mem_exterior Φ hΦ (f x)⟩⟩, ?_⟩
  exact ((continuous_rawRetraction Φ hΦ).comp f.continuous).subtype_mk _

include hinner in
theorem unitBoundary_time_zero (p : Sphere 3 × Sphere 3) : τ (Φ (p.1, p.2.val)) = 0 := by
  have hn : ‖p.2.val‖ = 1 := ClosedHemisphere.unit_norm p.2
  rw [hinner (p.1, p.2.val) (by change ‖p.2.val‖ ≤ 3 / 2; rw [hn]; norm_num), hn]
  norm_num

def boundaryInNewHalf : C(Sphere 3 × Sphere 3, NonnegativeHalf τ) :=
  ⟨fun p ↦ ⟨Φ (p.1, p.2.val), (unitBoundary_time_zero Φ τ hinner p).ge⟩,
    ((contMDiff Φ hΦ).continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _⟩

theorem overlap_retraction (b : Sphere 3) :
    (halfComplementRetraction Φ hΦ t τ hpos hhalf).comp (overlapLeft Φ t) =
      (boundaryInNewHalf Φ hΦ τ hinner).comp (overlapDirection Φ hΦ t b) := by
  classical
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  have hxT := halfTube_mem_target Φ hΦ t (overlapRight Φ t x)
  change rawRetraction Φ (forgetHalfCoreComplement Φ t (overlapLeft Φ t x)) =
    Φ ((Φ.symm x.val.val).1, (SphereRadialRetraction.retract b (Φ.symm x.val.val).2).val)
  rw [rawRetraction]
  change (if x.val.val ∈ Φ.target then
    Φ ((Φ.symm x.val.val).1, normalClamp (Φ.symm x.val.val).2) else x.val.val) = _
  change x.val.val ∈ Φ.target at hxT
  rw [if_pos hxT, normalClamp_eq_retract b (overlap_normal_ne_zero Φ hΦ t x)
    (overlap_normal_lt_one Φ hΦ t x).le]

end NoExoticSixSphere.SphereFourTube
