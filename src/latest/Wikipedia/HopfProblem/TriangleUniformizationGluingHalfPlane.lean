import Wikipedia.HopfProblem.TriangleUniformizationGluingFold

/-!
# A folded half-plane map and its exact fibres on the Ford polygon

An injective boundary map from the closed half-Ford triangle onto the
closed upper half-plane folds onto the whole complex plane. Its only
nontrivial fibres on the Ford polygon are the reflected pairs on the
Ford boundary. No orbit relation is part of the input data.
-/

noncomputable section

open Set UpperHalfPlane Complex
open scoped Topology MatrixGroups ComplexConjugate

namespace Wikipedia.HopfProblem.TriangleUniformizationGluing

open SpecialPeriods SpecialPeriods.Triangle

/-- Actual half-plane boundary data, strengthening the continuous real-boundary map. -/
structure HalfPlaneMap extends BoundaryMap where
  injOn : Set.InjOn toFun halfFordRegion
  image_eq : toFun '' halfFordRegion = {w : ℂ | 0 ≤ w.im}
  interior_positive : ∀ z ∈ halfFordInterior, 0 < (toFun z).im

instance : CoeFun HalfPlaneMap (fun _ => ℍ → ℂ) := ⟨fun D => D.toFun⟩

namespace HalfPlaneMap

variable (D : HalfPlaneMap)

/-- The original reflected formula, without any change of the underlying map. -/
abbrev foldedFordMap : ℍ → ℂ := D.toBoundaryMap.foldedFordMap

theorem im_nonneg {z : ℍ} (hz : z ∈ halfFordRegion) : 0 ≤ (D z).im := by
  have h : D.toFun z ∈ D.toFun '' halfFordRegion := mem_image_of_mem D.toFun hz
  rw [D.image_eq] at h
  exact h

theorem im_eq_zero_iff_not_mem_halfFordInterior {z : ℍ} (hz : z ∈ halfFordRegion) :
    (D z).im = 0 ↔ z ∉ halfFordInterior := by
  constructor
  · intro him hi
    exact (D.interior_positive z hi).ne' him
  · exact D.boundary_real z hz

theorem foldedFordMap_of_left {z : ℍ} (hz : z.re ≤ -(1 / 2)) :
    D.foldedFordMap z = D z :=
  D.toBoundaryMap.foldedFordMap_of_left hz

theorem foldedFordMap_of_right {z : ℍ} (hz : -(1 / 2) < z.re) :
    D.foldedFordMap z = conj (D (rightReflection z)) :=
  D.toBoundaryMap.foldedFordMap_of_right hz

theorem foldedFordMap_continuousOn : ContinuousOn D.foldedFordMap fordRegion :=
  D.toBoundaryMap.foldedFordMap_continuousOn

/-- The upper and reflected lower halves cover every complex value. -/
theorem foldedFordMap_surjOn : Set.SurjOn D.foldedFordMap fordRegion Set.univ := by
  intro w _
  by_cases hw : 0 ≤ w.im
  · have hmem : w ∈ D.toFun '' halfFordRegion := by
      rw [D.image_eq]
      exact hw
    obtain ⟨z, hz, he⟩ := hmem
    refine ⟨z, hz.1, ?_⟩
    change D.toBoundaryMap.foldedFordMap z = w
    rw [D.toBoundaryMap.foldedFordMap_of_left hz.2]
    exact he
  · have hmem : conj w ∈ D.toFun '' halfFordRegion := by
      rw [D.image_eq]
      change 0 ≤ (conj w).im
      rw [Complex.conj_im]
      exact neg_nonneg.mpr (le_of_lt (lt_of_not_ge hw))
    obtain ⟨z, hz, he⟩ := hmem
    refine ⟨rightReflection z, rightReflection_mapsTo_fordRegion hz.1, ?_⟩
    change D.toBoundaryMap.foldedFordMap (rightReflection z) = w
    rw [D.toBoundaryMap.foldedFordMap_reflected z hz, he, conj_conj]

theorem foldedFordMap_image_eq : D.foldedFordMap '' fordRegion = Set.univ :=
  Set.eq_univ_of_forall fun w => D.foldedFordMap_surjOn (Set.mem_univ w)

private theorem rightReflection_mem_halfFordRegion {z : ℍ} (hz : z ∈ fordRegion)
    (hx : -(1 / 2) < z.re) : rightReflection z ∈ halfFordRegion := by
  refine ⟨rightReflection_mapsTo_fordRegion hz, ?_⟩
  change (rightReflection z).re ≤ -(1 / 2)
  rw [rightReflection_re]
  linarith

private theorem cross_fibre {z w : ℍ} (hz : z ∈ halfFordRegion)
    (hw : w ∈ fordRegion) (hwr : -(1 / 2) < w.re)
    (heq : D.foldedFordMap z = D.foldedFordMap w) :
    w = rightReflection z ∧ z ∉ fordInterior := by
  have hrw : rightReflection w ∈ halfFordRegion :=
    rightReflection_mem_halfFordRegion hw hwr
  rw [D.foldedFordMap_of_left hz.2, D.foldedFordMap_of_right hwr] at heq
  have him := congrArg Complex.im heq
  rw [Complex.conj_im] at him
  have hzpos := D.im_nonneg hz
  have hwpos := D.im_nonneg hrw
  have hzreal : (D z).im = 0 := by linarith
  have hwreal : (D (rightReflection w)).im = 0 := by linarith
  have hf : D z = D (rightReflection w) :=
    heq.trans (Complex.conj_eq_iff_im.mpr hwreal)
  have hzw : z = rightReflection w := D.injOn hz hrw hf
  have hwz : w = rightReflection z := by
    rw [hzw, rightReflection_involutive]
  refine ⟨hwz, ?_⟩
  have hnot : z ∉ halfFordInterior :=
    (D.im_eq_zero_iff_not_mem_halfFordInterior hz).mp hzreal
  intro hi
  apply hnot
  refine ⟨hi, ?_⟩
  change z.re < -(1 / 2)
  rw [hzw, rightReflection_re]
  linarith

/-- On the actual Ford polygon the folded map identifies exactly
equal points and the reflected pairs on the Ford boundary. -/
theorem foldedFordMap_eq_iff {z w : ℍ} (hz : z ∈ fordRegion) (hw : w ∈ fordRegion) :
    D.foldedFordMap z = D.foldedFordMap w ↔
      z = w ∨ (w = rightReflection z ∧ z ∉ fordInterior) := by
  constructor
  · intro heq
    by_cases hzl : z.re ≤ -(1 / 2)
    · by_cases hwl : w.re ≤ -(1 / 2)
      · left
        rw [D.foldedFordMap_of_left hzl, D.foldedFordMap_of_left hwl] at heq
        exact D.injOn ⟨hz, hzl⟩ ⟨hw, hwl⟩ heq
      · exact Or.inr (D.cross_fibre ⟨hz, hzl⟩ hw (lt_of_not_ge hwl) heq)
    · have hzr : -(1 / 2) < z.re := lt_of_not_ge hzl
      by_cases hwl : w.re ≤ -(1 / 2)
      · obtain ⟨hzw, hwnot⟩ := D.cross_fibre ⟨hw, hwl⟩ hz hzr heq.symm
        right
        constructor
        · rw [hzw, rightReflection_involutive]
        · rw [hzw, rightReflection_mem_fordInterior_iff]
          exact hwnot
      · have hwr : -(1 / 2) < w.re := lt_of_not_ge hwl
        left
        rw [D.foldedFordMap_of_right hzr, D.foldedFordMap_of_right hwr] at heq
        have hf : D (rightReflection z) = D (rightReflection w) := by
          simpa only [conj_conj] using congrArg (fun u : ℂ => conj u) heq
        exact rightReflection.injective (D.injOn
          (rightReflection_mem_halfFordRegion hz hzr)
          (rightReflection_mem_halfFordRegion hw hwr) hf)
  · rintro (rfl | ⟨rfl, hi⟩)
    · rfl
    · exact (D.toBoundaryMap.foldedFordMap_rightReflection_boundary hz hi).symm

/-- In particular, the fold is injective on the whole strict Ford polygon. -/
theorem foldedFordMap_injOn_interior : Set.InjOn D.foldedFordMap fordInterior := by
  intro z hz w hw heq
  rcases (D.foldedFordMap_eq_iff (fordInterior_subset_fordRegion hz)
    (fordInterior_subset_fordRegion hw)).mp heq with he | ⟨_, hi⟩
  · exact he
  · exact (hi hz).elim

/-- Canonical map properties supplied by the actual half-plane data. -/
theorem foldedFordMap_properties :
    ContinuousOn D.foldedFordMap fordRegion ∧
      Set.SurjOn D.foldedFordMap fordRegion Set.univ ∧
      (∀ z ∈ fordRegion, ∀ w ∈ fordRegion,
        D.foldedFordMap z = D.foldedFordMap w ↔
          z = w ∨ (w = rightReflection z ∧ z ∉ fordInterior)) :=
  ⟨D.foldedFordMap_continuousOn, D.foldedFordMap_surjOn,
    fun _ hz _ hw => D.foldedFordMap_eq_iff hz hw⟩

end HalfPlaneMap
end Wikipedia.HopfProblem.TriangleUniformizationGluing
