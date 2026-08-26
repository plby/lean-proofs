import ErdosProblems.Erdos73.UCombPortPaths
import ErdosProblems.Erdos73.UCombPortRegions

/-! Connected disjoint regions for noncrossing ports on both vertical wall boundaries. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {M c r L : ℕ} {U : Type*}

theorem nail_isUCombPort (label : Fin M → U) (hsurj : Function.Surjective label)
    (nails : Fin M → ElementaryWallVertex c r) (leftSide : Fin M → Bool)
    (hmono : StrictMono (twoSidePortRank nails leftSide L))
    (hrows : ∀ i, (nails i).val.1.val ≤ L)
    (hleft : ∀ i, leftSide i = true → (nails i).val.2.val ≤ 1)
    (hright : ∀ i, leftSide i = false → 2 * (c - 1) ≤ (nails i).val.2.val)
    {u : U} {i : Fin M} (hi : label i = u) :
    IsUCombPort (sidePortRows label nails leftSide true u)
      (sidePortRows label nails leftSide false u) L M
      (twoSidePortRank nails leftSide L (portWordFirst label hsurj u))
      (twoSidePortRank nails leftSide L (portWordLast label hsurj u)) (nails i) := by
  have hb := portWord_bounds label hsurj hi
  have hmin := hmono.monotone hb.1
  have hmax := hmono.monotone hb.2
  have hmem (side : Bool) (hh : leftSide i = side) :
      (nails i).val.1.val ∈ sidePortRows label nails leftSide side u :=
    mem_image.mpr ⟨i, mem_filter.mpr ⟨(mem_portWordFiber _ _ _).mpr hi, hh⟩, rfl⟩
  cases hs : leftSide i
  · apply Or.inr
    simp only [twoSidePortRank, hs, Bool.false_eq_true, if_false] at hmin hmax
    exact ⟨hmem false hs, hrows i, hmin, hmax, hright i hs⟩
  · apply Or.inl
    simp only [twoSidePortRank, hs, ite_true] at hmin hmax
    exact ⟨hmem true hs, hrows i, hmin, hmax, hleft i hs⟩

theorem exists_connected_portWordUComb_region (label : Fin M → U)
    (hsurj : Function.Surjective label) (nails : Fin M → ElementaryWallVertex c r)
    (leftSide : Fin M → Bool) (hmono : StrictMono (twoSidePortRank nails leftSide L))
    (hrows : ∀ i, (nails i).val.1.val ≤ L)
    (hleft : ∀ i, leftSide i = true → (nails i).val.2.val ≤ 1)
    (hright : ∀ i, leftSide i = false → 2 * (c - 1) ≤ (nails i).val.2.val)
    (hc : 2 * M + 3 ≤ c) (hr : uCombBase L M < r) (u : U) :
    ∃ T : Finset (ElementaryWallVertex c r),
      (∀ i, label i = u → nails i ∈ T) ∧ T ⊆ portWordUComb label hsurj nails leftSide L u ∧
      ((elementaryWall c r).induce (T : Set (ElementaryWallVertex c r))).Connected := by
  let root := nails (portWordFirst label hsurj u)
  have hroot := nail_isUCombPort label hsurj nails leftSide hmono hrows hleft hright
    (portWordFirst_label label hsurj u)
  have hex (i : portWordFiber label u) := exists_uComb_port_path hroot
    (nail_isUCombPort label hsurj nails leftSide hmono hrows hleft hright
      ((mem_portWordFiber _ _ _).mp i.property))
    (portWordSpine_pos label hsurj u) (portWordSpine_le label hsurj u) hc hr
  choose P hs ht hsub using hex
  let T := insert root (univ.biUnion (fun i => (P i).vertexSet))
  refine ⟨T, ?_, ?_, connected_induce_rooted_pathUnion univ P root (fun i _ => hs i)⟩
  · intro i hi
    let d : portWordFiber label u := ⟨i, (mem_portWordFiber _ _ _).mpr hi⟩
    exact mem_insert_of_mem (mem_biUnion.mpr ⟨d, mem_univ _, ht d ▸ (P d).target_mem_vertexSet⟩)
  · intro w hw
    rcases mem_insert.mp hw with rfl | hw
    · have hh := nail_mem_portWordUComb label hsurj nails leftSide hmono hrows hleft hright
        (portWordFirst label hsurj u)
      rw [portWordFirst_label label hsurj u] at hh
      exact hh
    · obtain ⟨i, _, hi⟩ := mem_biUnion.mp hw
      exact hsub i hi

theorem exists_disjoint_noncrossing_boundary_regions (label : Fin M → U)
    (hsurj : Function.Surjective label) (hNC : NoncrossingPortWord label)
    (nails : Fin M → ElementaryWallVertex c r) (leftSide : Fin M → Bool)
    (hmono : StrictMono (twoSidePortRank nails leftSide L))
    (hrows : ∀ i, (nails i).val.1.val ≤ L)
    (hleft : ∀ i, leftSide i = true → (nails i).val.2.val ≤ 1)
    (hright : ∀ i, leftSide i = false → 2 * (c - 1) ≤ (nails i).val.2.val)
    (hc : 2 * M + 3 ≤ c) (hr : uCombBase L M < r) :
    ∃ R : U → Finset (ElementaryWallVertex c r),
      Pairwise (fun u v => Disjoint (R u) (R v)) ∧
      (∀ i, nails i ∈ R (label i)) ∧
      ∀ u, ((elementaryWall c r).induce (R u : Set (ElementaryWallVertex c r))).Connected := by
  choose R hports hsub hconn using exists_connected_portWordUComb_region
    label hsurj nails leftSide hmono hrows hleft hright hc hr
  refine ⟨R, ?_, fun i => hports (label i) i rfl, hconn⟩
  intro u v huv
  exact (portWordUComb_disjoint hsurj hNC nails leftSide hmono hrows hc huv).mono (hsub u) (hsub v)

end
end Erdos73
