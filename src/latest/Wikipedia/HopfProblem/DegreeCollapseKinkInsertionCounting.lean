import Wikipedia.HopfProblem.DegreeCollapseNativeKinkTransversality
import Wikipedia.HopfProblem.DegreeCollapseDoublePointCounting

/-!
# One actual new unordered double point, with simple fibers preserved

The old and new ordered-pair sets are disjoint because the selected patch
has globally unique original fibers. The quotient by sheet interchange
therefore gains exactly one element. No parity invariance is asserted for
this homotopy through the singular cusp time.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource.KinkPatchData

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization
open SphereSelfIntersections DoublePointCounting

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  {F : Sphere 3 → M} (P : KinkPatchData F)

theorem crossing_fiber (z : Sphere 3)
    (hz : P.insertedMap z = P.insertedMap (P.crossingPoint 1)) :
    z = P.crossingPoint 1 ∨ z = P.crossingPoint (-1) := by
  by_cases he : z = P.crossingPoint 1
  · exact Or.inl he
  have hp := P.sourceSupport_subset (P.crossingPoint_mem_support 1 (by norm_num))
  rcases P.inserted_pair_at_patch hp (Ne.symm he) hz.symm with h | h
  · exact Or.inr h.2
  · exact (P.crossingPoint_ne h.1).elim

theorem onlyDoubleFibers_insertedMap (hf : HasOnlyDoubleFibers F) :
    HasOnlyDoubleFibers P.insertedMap := by
  have hp := P.sourceSupport_subset (P.crossingPoint_mem_support 1 (by norm_num))
  have hm := P.sourceSupport_subset (P.crossingPoint_mem_support (-1) (by norm_num))
  intro x y hxy he z hz
  rcases (P.inserted_pair_iff hxy).mp he with hF | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hx := (P.original_pair_off_patch hxy hF).1
    by_cases hzx : z = x
    · exact Or.inl hzx
    rcases (P.inserted_pair_iff hzx).mp hz with hFz | h | h
    · exact hf x y hxy hF z hFz
    · exact (hx (h.2.symm ▸ hm)).elim
    · exact (hx (h.2.symm ▸ hp)).elim
  · exact P.crossing_fiber z hz
  · exact (P.crossing_fiber z (hz.trans P.inserted_crossing.symm)).symm

theorem disjoint_old_new_pairs : Disjoint (pairs F)
    ({(P.crossingPoint 1, P.crossingPoint (-1)),
      (P.crossingPoint (-1), P.crossingPoint 1)} : Set (Sphere 3 × Sphere 3)) := by
  apply disjoint_left.mpr
  intro p hp hnew
  have hx := (P.original_pair_off_patch hp.1 hp.2).1
  rcases hnew with h | h
  · cases h
    exact hx (P.sourceSupport_subset (P.crossingPoint_mem_support 1 (by norm_num)))
  · cases h
    exact hx (P.sourceSupport_subset (P.crossingPoint_mem_support (-1) (by norm_num)))

theorem finite_inserted_pairs (hfin : (pairs F).Finite) : (pairs P.insertedMap).Finite := by
  rw [P.inserted_pairs]
  exact hfin.union (toFinite _)

theorem unordered_card_insertedMap (hfin : (pairs F).Finite) :
    Nat.card (Unordered P.insertedMap) = Nat.card (Unordered F) + 1 := by
  have hne : (P.crossingPoint 1, P.crossingPoint (-1)) ≠
      (P.crossingPoint (-1), P.crossingPoint 1) :=
    fun h ↦ P.crossingPoint_ne (congrArg Prod.fst h)
  have hn : (pairs P.insertedMap).ncard = (pairs F).ncard + 2 := by
    rw [P.inserted_pairs, ncard_union_eq P.disjoint_old_new_pairs hfin (toFinite _)]
    simp [hne]
  rw [ordered_ncard_eq_twice_unordered P.insertedMap (P.finite_inserted_pairs hfin),
    ordered_ncard_eq_twice_unordered F hfin] at hn
  omega

end Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource.KinkPatchData
