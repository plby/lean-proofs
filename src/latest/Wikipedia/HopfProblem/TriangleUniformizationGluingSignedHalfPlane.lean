import Wikipedia.HopfProblem.TriangleUniformizationGluingHalfPlane

/-!
# Folding either orientation of a half-plane boundary map

The prescribed vertex ordering may put the triangle image in either
half-plane. Multiplication by its real orientation sign normalizes the
image to the upper half-plane. The conclusions below concern the original
boundary map and its original reflected fold, not a changed normalization.
-/

noncomputable section

open Set UpperHalfPlane Complex
open scoped Topology MatrixGroups ComplexConjugate ContDiff

namespace Wikipedia.HopfProblem.TriangleUniformizationGluing

open SpecialPeriods SpecialPeriods.Triangle

/-- Half-plane boundary data with either orientation of the original map. -/
structure SignedHalfPlaneMap extends BoundaryMap where
  orientation : ℝ
  orientation_sq : orientation ^ 2 = 1
  injOn : Set.InjOn toFun halfFordRegion
  image_eq : toFun '' halfFordRegion = {w : ℂ | 0 ≤ orientation * w.im}
  interior_positive : ∀ z ∈ halfFordInterior, 0 < orientation * (toFun z).im

instance : CoeFun SignedHalfPlaneMap (fun _ => ℍ → ℂ) := ⟨fun D => D.toFun⟩

namespace SignedHalfPlaneMap

variable (D : SignedHalfPlaneMap)

theorem orientation_ne_zero : D.orientation ≠ 0 := by
  intro h
  have hs := D.orientation_sq
  rw [h] at hs
  norm_num at hs

theorem orientation_coe_ne_zero : (D.orientation : ℂ) ≠ 0 := by
  exact_mod_cast D.orientation_ne_zero

theorem orientation_mul_self : D.orientation * D.orientation = 1 := by
  simpa only [pow_two] using D.orientation_sq

theorem orientation_coe_mul_self : (D.orientation : ℂ) * (D.orientation : ℂ) = 1 := by
  rw [← Complex.ofReal_mul, D.orientation_mul_self, Complex.ofReal_one]

/-- The holomorphic sign change used only to transfer the upper-half-plane proof. -/
def orientationScale (w : ℂ) : ℂ := (D.orientation : ℂ) * w

theorem orientationScale_holomorphic : ContDiff ℂ ω D.orientationScale :=
  contDiff_const.mul contDiff_id

theorem orientationScale_involutive : Function.Involutive D.orientationScale := by
  intro w
  change (D.orientation : ℂ) * ((D.orientation : ℂ) * w) = w
  rw [← mul_assoc, D.orientation_coe_mul_self, one_mul]

theorem orientationScale_injective : Function.Injective D.orientationScale :=
  D.orientationScale_involutive.injective

/-- The original, possibly lower-half-plane-oriented reflected formula. -/
abbrev foldedFordMap : ℍ → ℂ := D.toBoundaryMap.foldedFordMap

theorem foldedFordMap_continuousOn : ContinuousOn D.foldedFordMap fordRegion :=
  D.toBoundaryMap.foldedFordMap_continuousOn

/-- Holomorphic multiplication by the orientation sign gives actual
upper-half-plane data, without altering the source or its boundary. -/
def normalized : HalfPlaneMap where
  toFun := fun z => (D.orientation : ℂ) * D z
  continuousOn := continuousOn_const.mul D.continuousOn
  boundary_real := by
    intro z hz hi
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      add_zero, D.boundary_real z hz hi, mul_zero]
  injOn := by
    intro z hz w hw he
    exact D.injOn hz hw ((mul_right_inj' D.orientation_coe_ne_zero).mp he)
  image_eq := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      have h : D.toFun z ∈ D.toFun '' halfFordRegion := mem_image_of_mem D.toFun hz
      rw [D.image_eq] at h
      simpa only [mem_ofPred_eq, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero] using h
    · intro hw
      have h : (D.orientation : ℂ) * w ∈ D.toFun '' halfFordRegion := by
        rw [D.image_eq]
        simp only [mem_ofPred_eq, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, add_zero]
        rw [← mul_assoc, D.orientation_mul_self, one_mul]
        exact hw
      obtain ⟨z, hz, he⟩ := h
      refine ⟨z, hz, ?_⟩
      change (D.orientation : ℂ) * D.toFun z = w
      rw [he, ← mul_assoc, D.orientation_coe_mul_self, one_mul]
  interior_positive := by
    intro z hz
    simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero] using D.interior_positive z hz

@[simp] theorem normalized_apply (z : ℍ) :
    D.normalized z = (D.orientation : ℂ) * D z := rfl

/-- Real sign multiplication commutes with the actual reflected formula. -/
theorem normalized_foldedFordMap (z : ℍ) :
    D.normalized.foldedFordMap z = (D.orientation : ℂ) * D.foldedFordMap z := by
  simp only [HalfPlaneMap.foldedFordMap, foldedFordMap, BoundaryMap.foldedFordMap]
  split_ifs
  · rfl
  · change conj ((D.orientation : ℂ) * D (rightReflection z)) =
      (D.orientation : ℂ) * conj (D (rightReflection z))
    rw [map_mul, Complex.conj_ofReal]

/-- The original folded map is onto the complex plane for either orientation. -/
theorem foldedFordMap_surjOn : Set.SurjOn D.foldedFordMap fordRegion Set.univ := by
  intro w _
  obtain ⟨z, hz, he⟩ := D.normalized.foldedFordMap_surjOn
    (Set.mem_univ ((D.orientation : ℂ) * w))
  refine ⟨z, hz, ?_⟩
  apply D.orientationScale_injective
  change (D.orientation : ℂ) * D.foldedFordMap z = (D.orientation : ℂ) * w
  rw [← D.normalized_foldedFordMap z]
  exact he

theorem foldedFordMap_image_eq : D.foldedFordMap '' fordRegion = Set.univ :=
  Set.eq_univ_of_forall fun w => D.foldedFordMap_surjOn (Set.mem_univ w)

/-- The exact original-map fibres do not depend on the chosen half-plane orientation. -/
theorem foldedFordMap_eq_iff {z w : ℍ} (hz : z ∈ fordRegion) (hw : w ∈ fordRegion) :
    D.foldedFordMap z = D.foldedFordMap w ↔
      z = w ∨ (w = rightReflection z ∧ z ∉ fordInterior) := by
  have heq : D.normalized.foldedFordMap z = D.normalized.foldedFordMap w ↔
      D.foldedFordMap z = D.foldedFordMap w := by
    rw [D.normalized_foldedFordMap z, D.normalized_foldedFordMap w]
    constructor
    · intro h
      exact D.orientationScale_injective h
    · intro h
      exact congrArg D.orientationScale h
  exact heq.symm.trans (D.normalized.foldedFordMap_eq_iff hz hw)

theorem foldedFordMap_injOn_interior : Set.InjOn D.foldedFordMap fordInterior := by
  intro z hz w hw heq
  rcases (D.foldedFordMap_eq_iff (fordInterior_subset_fordRegion hz)
    (fordInterior_subset_fordRegion hw)).mp heq with he | ⟨_, hi⟩
  · exact he
  · exact (hi hz).elim

/-- Continuous, surjective, exact-fibre properties of the original fold. -/
theorem foldedFordMap_properties :
    ContinuousOn D.foldedFordMap fordRegion ∧
      Set.SurjOn D.foldedFordMap fordRegion Set.univ ∧
      (∀ z ∈ fordRegion, ∀ w ∈ fordRegion,
        D.foldedFordMap z = D.foldedFordMap w ↔
          z = w ∨ (w = rightReflection z ∧ z ∉ fordInterior)) :=
  ⟨D.foldedFordMap_continuousOn, D.foldedFordMap_surjOn,
    fun _ hz _ hw => D.foldedFordMap_eq_iff hz hw⟩

end SignedHalfPlaneMap
end Wikipedia.HopfProblem.TriangleUniformizationGluing
