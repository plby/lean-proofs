import Wikipedia.NoExoticSixSphere.JamesSphereAttachingSourceQuotient
import Wikipedia.NoExoticSixSphere.JamesSphereClockPerimeterQuotient
import Wikipedia.NoExoticSixSphere.SmoothSphereCubeHomotopy

/-!
# The actual source quotient has the native sphere-cube fibers

Traverse the original clock perimeter in the leading cube coordinate
and use the remaining coordinates for the two original tails. After
collapsing the specified faces, this map is surjective and identifies
exactly the entire native cube boundary. All other fibers are singletons.
-/

noncomputable section

open Set Topology
open scoped unitInterval

namespace NoExoticSixSphere.JamesSphere.AttachingSquare

theorem corner00_val : corner00.val = 0 := by
  funext i
  fin_cases i <;> rfl

theorem clock_zero_iff (t : ClockBoundary) : t.val = 0 ↔ t = corner00 := by
  constructor
  · intro h
    exact Subtype.ext (h.trans corner00_val.symm)
  · rintro rfl
    exact corner00_val

theorem sourceCollapse_eq_point_iff (n : ℕ) (p : fullBoundary n) :
    sourceCollapse n p = sourcePoint n ↔ p ∈ collapsedFaces n := by
  change CollapsedSubspace.quotientMap (collapsedFaces n) p =
    CollapsedSubspace.quotientMap (collapsedFaces n) (fullPoint n) ↔ _
  rw [CollapsedSubspace.quotientMap_eq_iff]
  constructor
  · rintro (rfl | ⟨hp, _⟩)
    · exact (collapsedPoint n).property
    · exact hp
  · intro hp
    exact Or.inr ⟨hp, (collapsedPoint n).property⟩

def cubeSourceBoundary (n : ℕ) : C((Fin (2 * n + 1) → I), fullBoundary n) :=
  ⟨fun u ↦ ⟨((perimeter (u 0)).val, (tailCoordinates n).symm (Fin.tail u)),
      Or.inl (perimeter (u 0)).property⟩,
    (((continuous_subtype_val.comp perimeter.continuous).comp (continuous_apply 0)).prodMk
      ((tailCoordinates n).symm.continuous.comp
        (continuous_pi (fun i ↦ continuous_apply i.succ)))).subtype_mk _⟩

def cubeSourceMap (n : ℕ) : C((Fin (2 * n + 1) → I), SourceQuotient n) :=
  (sourceCollapse n).comp (cubeSourceBoundary n)

theorem cubeSourceMap_eq_point_iff (n : ℕ) (u : Fin (2 * n + 1) → I) :
    cubeSourceMap n u = sourcePoint n ↔ u ∈ Cube.boundary (Fin (2 * n + 1)) := by
  change sourceCollapse n (cubeSourceBoundary n u) = sourcePoint n ↔ _
  rw [sourceCollapse_eq_point_iff]
  change ((perimeter (u 0)).val = 0 ∨
    (tailCoordinates n).symm (Fin.tail u) ∈ tailBoundary n) ↔ _
  rw [clock_zero_iff, perimeter_eq_corner_iff, tailCoordinates_boundary,
    Homeomorph.apply_symm_apply]
  change ((u 0 = 0 ∨ u 0 = 1) ∨ ∃ i : Fin (2 * n), u i.succ = 0 ∨ u i.succ = 1) ↔
    ∃ i, u i = 0 ∨ u i = 1
  rw [Fin.exists_fin_succ]

theorem cubeSourceMap_eq_iff (n : ℕ) (u v : Fin (2 * n + 1) → I) :
    cubeSourceMap n u = cubeSourceMap n v ↔ u = v ∨
      u ∈ Cube.boundary (Fin (2 * n + 1)) ∧ v ∈ Cube.boundary (Fin (2 * n + 1)) := by
  constructor
  · intro h
    by_cases hu : u ∈ Cube.boundary (Fin (2 * n + 1))
    · right
      exact ⟨hu, (cubeSourceMap_eq_point_iff n v).mp
        (h.symm.trans ((cubeSourceMap_eq_point_iff n u).mpr hu))⟩
    · have hnot : cubeSourceBoundary n u ∉ collapsedFaces n := by
        intro hf
        exact hu ((cubeSourceMap_eq_point_iff n u).mp
          ((sourceCollapse_eq_point_iff n _).mpr hf))
      have he := (CollapsedSubspace.quotientMap_eq_iff (collapsedFaces n) _ _).mp h
      have heq : cubeSourceBoundary n u = cubeSourceBoundary n v := he.resolve_right
        (fun hh ↦ hnot hh.1)
      have hclock : perimeter (u 0) = perimeter (v 0) :=
        Subtype.ext (congrArg (fun p : fullBoundary n ↦ p.val.1) heq)
      have htail : Fin.tail u = Fin.tail v := (tailCoordinates n).symm.injective
        (congrArg (fun p : fullBoundary n ↦ p.val.2) heq)
      have hzero : u 0 = v 0 := by
        rcases (perimeter_eq_iff (u 0) (v 0)).mp hclock with ht | ⟨ht, _⟩
        · exact ht
        · exact False.elim (hu ⟨0, ht⟩)
      left
      funext i
      exact Fin.cases hzero (fun j ↦ congrFun htail j) i
  · rintro (rfl | ⟨hu, hv⟩)
    · rfl
    · exact ((cubeSourceMap_eq_point_iff n u).mpr hu).trans
        ((cubeSourceMap_eq_point_iff n v).mpr hv).symm

theorem cubeSourceMap_surjective (n : ℕ) : Function.Surjective (cubeSourceMap n) := by
  intro y
  obtain ⟨p, rfl⟩ := (CollapsedSubspace.isQuotientMap (collapsedFaces n)).surjective y
  rcases p.property with hp | hp
  · obtain ⟨t, ht⟩ := perimeter_surjective ⟨p.val.1, hp⟩
    refine ⟨Fin.cons t (tailCoordinates n p.val.2), ?_⟩
    apply congrArg (sourceCollapse n)
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val ht
    · exact (tailCoordinates n).symm_apply_apply p.val.2
  · refine ⟨0, ?_⟩
    have hzero := (cubeSourceMap_eq_point_iff n 0).mpr
      (SmoothCube.zero_boundary (Nat.succ_pos (2 * n)))
    exact hzero.trans ((sourceCollapse_eq_point_iff n p).mpr (Or.inr hp)).symm

def sourceCube (n : ℕ) :
    GenLoop (Fin (2 * n + 1)) (SourceQuotient n) (sourcePoint n) :=
  ⟨cubeSourceMap n, fun u hu ↦ (cubeSourceMap_eq_point_iff n u).mpr hu⟩

end NoExoticSixSphere.JamesSphere.AttachingSquare
