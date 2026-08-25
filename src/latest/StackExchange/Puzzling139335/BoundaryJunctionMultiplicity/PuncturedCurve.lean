import Wikipedia.SchoenfliesTheorem.JordanSeparates

/-!
# A Jordan curve punctured at at most one point

Removing one endpoint of an arc leaves a connected set.  Splitting a Jordan
curve into two arcs at the deleted point and one other point then proves that
deleting at most one point leaves the curve connected and nonempty.
-/

open Set

namespace Schoenflies

/-- An arc remains connected and nonempty after deletion of its left endpoint. -/
theorem IsArcBetween.isConnected_sdiff_left {A : Set Plane} {p q : Plane}
    (hA : IsArcBetween A p q) : IsConnected (A \ {p}) := by
  apply hA.isConnected_diff.subset_closure
  · rintro z ⟨hzA, hzp⟩
    exact ⟨hzA, fun hz => hzp (Or.inl (mem_singleton_iff.mp hz))⟩
  · rintro z ⟨hzA, hzp⟩
    rcases eq_or_ne z q with rfl | hzq
    · exact hA.right_mem_closure_diff
    · apply subset_closure
      refine ⟨hzA, ?_⟩
      simp only [mem_insert_iff, mem_singleton_iff, not_or]
      exact ⟨by simpa only [mem_singleton_iff] using hzp, hzq⟩

/-- An arc remains connected and nonempty after deletion of its right endpoint. -/
theorem IsArcBetween.isConnected_sdiff_right {A : Set Plane} {p q : Plane}
    (hA : IsArcBetween A p q) : IsConnected (A \ {q}) :=
  hA.reverse.isConnected_sdiff_left

/-- Deleting any one point from a Jordan curve leaves a connected nonempty set. -/
theorem IsJordanCurve.isConnected_sdiff_singleton {C : Set Plane}
    (hC : IsJordanCurve C) (p : Plane) : IsConnected (C \ {p}) := by
  by_cases hp : p ∈ C
  · obtain ⟨u, hu, v, hv, huv⟩ := hC.exists_ne
    obtain ⟨q, hq, hpq⟩ : ∃ q ∈ C, p ≠ q := by
      rcases eq_or_ne p u with rfl | hpu
      · exact ⟨v, hv, huv⟩
      · exact ⟨u, hu, hpu⟩
    obtain ⟨A, B, hA, hB, hcover, -⟩ := hC.two_arcs hp hq hpq
    rw [← hcover, union_sdiff_distrib]
    refine IsConnected.union ?_ hA.isConnected_sdiff_left hB.isConnected_sdiff_left
    exact ⟨q, ⟨hA.right_mem, by simpa only [mem_singleton_iff] using hpq.symm⟩,
      ⟨hB.right_mem, by simpa only [mem_singleton_iff] using hpq.symm⟩⟩
  · have heq : C \ {p} = C := by
      ext z
      constructor
      · exact fun hz => hz.1
      · intro hz
        exact ⟨hz, fun heq => hp ((mem_singleton_iff.mp heq) ▸ hz)⟩
    rw [heq]
    exact hC.isConnected

/-- Deleting at most one point from a Jordan curve leaves a connected nonempty set. -/
theorem IsJordanCurve.isConnected_sdiff_subsingleton {C E : Set Plane}
    (hC : IsJordanCurve C) (hE : E.Subsingleton) : IsConnected (C \ E) := by
  rcases hE.eq_empty_or_singleton with rfl | ⟨p, rfl⟩
  · simpa only [sdiff_empty] using hC.isConnected
  · exact hC.isConnected_sdiff_singleton p

end Schoenflies
