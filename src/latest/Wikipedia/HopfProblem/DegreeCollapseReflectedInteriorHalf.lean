import Wikipedia.HopfProblem.DegreeCollapseReflectedOpenHalf

/-!
# The actual filling half is homotopy equivalent to its strict interior

Within the original constant seam collar, push time t to max(t, ε).
The straight interpolation changes no spatial coordinate, stays in the
actual fiber, and preserves positive time whenever time was positive.
Both inverse homotopies are therefore actual homotopies in the original
half and its actual open interior. No closed theorem is applied to a
boundary atlas, and no homology hypotheses are needed here.
-/

noncomputable section

open Function Set ContinuousMap
open scoped Manifold ContDiff unitInterval

namespace Wikipedia.HopfProblem.DegreeCollapse.ReflectedCylinder

open NoExoticSixSphere SingularMayerVietoris PeriodTorusHigherHomology

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)

def positiveInterior : TopologicalSpace.Opens (Fiber d) :=
  ⟨{p | 0 < p.val.1}, isOpen_lt continuous_const
    (continuous_fst.comp continuous_subtype_val)⟩

def interiorToHalf : C(positiveInterior d, NonnegativeHalf d) :=
  ⟨fun p ↦ ⟨p.val, p.property.le⟩, continuous_subtype_val.subtype_mk _⟩

theorem interiorToHalf_inclusion :
    (halfInclusion d).comp (interiorToHalf d) =
      subtypeInclusion (positiveInterior d : Set (Fiber d)) := rfl

def interiorSlideTime (ε : ℝ) (s : unitInterval) (t : ℝ) : ℝ :=
  (1 - s.val) * t + s.val * max t ε

theorem interiorSlideTime_of_ge (ε : ℝ) (s : unitInterval) (t : ℝ) (ht : ε ≤ t) :
    interiorSlideTime ε s t = t := by
  rw [interiorSlideTime, max_eq_left ht]
  ring

theorem interiorSlideTime_bounds (ε : ℝ) (s : unitInterval) (t : ℝ) :
    t ≤ interiorSlideTime ε s t ∧ interiorSlideTime ε s t ≤ max t ε := by
  have hs0 := s.property.1
  have hs1 := s.property.2
  have ht := le_max_left t ε
  dsimp [interiorSlideTime]
  constructor
  · nlinarith [mul_nonneg hs0 (sub_nonneg.mpr ht)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr ht)]

variable (ε : ℝ) (hε : 0 < ε) (hc : Icc (-ε) ε ⊆ seamCollarTimes d)

include hc in
theorem interiorSlideTime_fiber (s : unitInterval) (p : NonnegativeHalf d) :
    map d (interiorSlideTime ε s p.val.val.1, p.val.val.2) = b := by
  by_cases ht : ε ≤ p.val.val.1
  · rw [interiorSlideTime_of_ge ε s _ ht]
    exact p.val.property
  · have hp : 0 ≤ p.val.val.1 := p.property
    have ht' : p.val.val.1 < ε := lt_of_not_ge ht
    have hb := interiorSlideTime_bounds ε s p.val.val.1
    rw [max_eq_right ht'.le] at hb
    have hs : interiorSlideTime ε s p.val.val.1 ∈ seamCollarTimes d :=
      hc ⟨by linarith, hb.2⟩
    have ho : p.val.val.1 ∈ seamCollarTimes d := hc ⟨by linarith, ht'.le⟩
    exact (map_on_seamCollar d _ hs _).trans
      ((map_on_seamCollar d _ ho _).symm.trans p.val.property)

theorem interiorSlideTime_nonneg (s : unitInterval) (p : NonnegativeHalf d) :
    0 ≤ interiorSlideTime ε s p.val.val.1 :=
  p.property.trans (interiorSlideTime_bounds ε s p.val.val.1).1

theorem interiorSlideTime_pos (s : unitInterval) (p : positiveInterior d) :
    0 < interiorSlideTime ε s p.val.val.1 :=
  p.property.trans_le (interiorSlideTime_bounds ε s p.val.val.1).1

def halfInteriorSlideMap : C(unitInterval × NonnegativeHalf d, NonnegativeHalf d) where
  toFun q := ⟨⟨(interiorSlideTime ε q.1 q.2.val.val.1, q.2.val.val.2),
    interiorSlideTime_fiber d ε hc q.1 q.2⟩, interiorSlideTime_nonneg d ε q.1 q.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · have ht : Continuous (fun q : unitInterval × NonnegativeHalf d ↦ q.2.val.val.1) :=
        continuous_fst.comp (continuous_subtype_val.comp
          (continuous_subtype_val.comp continuous_snd))
      have hs : Continuous (fun q : unitInterval × NonnegativeHalf d ↦ q.1.val) :=
        continuous_subtype_val.comp continuous_fst
      exact ((continuous_const.sub hs).mul ht).add (hs.mul (ht.max continuous_const))
    · exact continuous_snd.comp (continuous_subtype_val.comp
        (continuous_subtype_val.comp continuous_snd))

include hε in
theorem halfInteriorSlideMap_one_positive (p : NonnegativeHalf d) :
    0 < (halfInteriorSlideMap d ε hc (1, p)).val.val.1 := by
  change 0 < interiorSlideTime ε 1 p.val.val.1
  simpa [interiorSlideTime] using hε.trans_le (le_max_right p.val.val.1 ε)

def halfToInterior : C(NonnegativeHalf d, positiveInterior d) :=
  ⟨fun p ↦ ⟨(halfInteriorSlideMap d ε hc (1, p)).val,
    halfInteriorSlideMap_one_positive d ε hε hc p⟩,
    (continuous_subtype_val.comp ((halfInteriorSlideMap d ε hc).continuous.comp
      (continuous_const.prodMk continuous_id))).subtype_mk _⟩

def halfInteriorSlide :
    (ContinuousMap.id (NonnegativeHalf d)).Homotopy
      ((interiorToHalf d).comp (halfToInterior d ε hε hc)) where
  toContinuousMap := halfInteriorSlideMap d ε hc
  map_zero_left p := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (by simp [interiorSlideTime, halfInteriorSlideMap]) rfl
  map_one_left _ := rfl

def interiorHalfSlide :
    (ContinuousMap.id (positiveInterior d)).Homotopy
      ((halfToInterior d ε hε hc).comp (interiorToHalf d)) where
  toFun q := ⟨(halfInteriorSlideMap d ε hc (q.1, interiorToHalf d q.2)).val,
    interiorSlideTime_pos d ε q.1 q.2⟩
  continuous_toFun :=
    (continuous_subtype_val.comp ((halfInteriorSlideMap d ε hc).continuous.comp
      (continuous_fst.prodMk ((interiorToHalf d).continuous.comp continuous_snd)))).subtype_mk _
  map_zero_left p := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (by simp [interiorSlideTime, halfInteriorSlideMap, interiorToHalf]) rfl
  map_one_left _ := rfl

def interiorHalfHomotopyEquiv : positiveInterior d ≃ₕ NonnegativeHalf d where
  toFun := interiorToHalf d
  invFun := halfToInterior d ε hε hc
  left_inv := ⟨(interiorHalfSlide d ε hε hc).symm⟩
  right_inv := ⟨(halfInteriorSlide d ε hε hc).symm⟩

theorem interiorToHalf_homology_bijective (k : ℕ) :
    Bijective (singularHomologyMap (interiorToHalf d) k) := by
  obtain ⟨ε, hε, hc⟩ := exists_seam_width d
  exact (homotopyEquivHomologyEquiv (interiorHalfHomotopyEquiv d ε hε hc) k).bijective

end Wikipedia.HopfProblem.DegreeCollapse.ReflectedCylinder
