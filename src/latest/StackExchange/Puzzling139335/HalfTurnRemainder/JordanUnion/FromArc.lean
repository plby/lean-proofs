import StackExchange.Puzzling139335.HalfTurnRemainder.JordanUnion.FromArc.OuterArcs
import StackExchange.Puzzling139335.HalfTurnRemainder.JordanUnion.FromArc.Filling
import StackExchange.Puzzling139335.JordanCrosscut
import StackExchange.Puzzling139335.JordanCurveRigidity

/-!
# Gluing two Jordan pieces along their intersection arc

For two Jordan regions with disjoint interiors and an arc as their whole
intersection, connectedness of the union's interior and complement identifies
the union as a Jordan region.  The shared arc is an actual Jordan crosscut, and
the two original pieces are exactly the closures of its two named sides.

The connectedness hypotheses are supplied by the remainder construction; no
Jordan-region or crosscut conclusion is assumed for the union.
-/

open Set Schoenflies

namespace Puzzling139335.HalfTurnRemainder.JordanUnion

variable {A D : Set Plane} {p q : Plane}

/-- The union of two Jordan regions is regular closed. -/
theorem closure_interior_union (hA : IsJordanRegion A) (hD : IsJordanRegion D) :
    closure (interior (A ∪ D)) = A ∪ D := by
  apply Subset.antisymm
  · exact (hA.isClosed.union hD.isClosed).closure_subset_iff.mpr interior_subset
  · apply union_subset
    · calc
        A = closure (interior A) := hA.closure_interior.symm
        _ ⊆ closure (interior (A ∪ D)) := closure_mono (interior_mono subset_union_left)
    · calc
        D = closure (interior D) := hD.closure_interior.symm
        _ ⊆ closure (interior (A ∪ D)) := closure_mono (interior_mono subset_union_right)

/-- Gluing along the whole intersection arc produces a Jordan region, with
that arc as a crosscut and the original regions as the two closed sides. -/
theorem glue_of_inter_isArc (hA : IsJordanRegion A) (hD : IsJordanRegion D)
    (hdis : Disjoint (interior A) (interior D))
    (hI : IsArcBetween (A ∩ D) p q)
    (hinterior : IsConnected (interior (A ∪ D)))
    (hcompl : IsConnected (A ∪ D)ᶜ) :
    IsJordanRegion (A ∪ D) ∧ JordanCrosscut (frontier (A ∪ D)) (A ∩ D) p q ∧
      ∃ M N, IsCutPair (frontier (A ∪ D)) p q M N ∧
        IsCutPair (frontier A) p q (A ∩ D) M ∧
        IsCutPair (frontier D) p q (A ∩ D) N ∧
        closure (inside (M ∪ (A ∩ D))) = A ∧
        closure (inside (N ∪ (A ∩ D))) = D := by
  obtain ⟨M, N, hM, hN, houter, hC, hCU⟩ := exists_outer_arcs hA hD hdis hI
  have hfill : A ∪ D = closure (inside (M ∪ N)) :=
    eq_closure_inside_of_frontier_contains_jordan (hA.isClosed.union hD.isClosed)
      (hA.isBounded.union hD.isBounded) (closure_interior_union hA hD)
      hinterior hcompl hC hCU
  have hU : IsJordanRegion (A ∪ D) := ⟨M ∪ N, hC, hfill⟩
  have hfrontier : frontier (A ∪ D) = M ∪ N := by
    rw [hfill, frontier_closure_inside (jordan_curve_theorem hC)]
  have hcross : JordanCrosscut (frontier (A ∪ D)) (A ∩ D) p q := by
    refine ⟨hU.frontier_isJordanCurve, hI, ?_, ?_, ?_⟩
    · rw [hfrontier]
      exact Or.inl hM.snd.left_mem
    · rw [hfrontier]
      exact Or.inl hM.snd.right_mem
    · rintro x ⟨hxI, hxends⟩
      rw [← hU.interior_eq_inside_frontier]
      apply (mem_interior_iff_notMem_frontier (s := A ∪ D) (x := x) (Or.inl hxI.1)).mpr
      rw [hfrontier]
      rintro (hxM | hxN)
      · exact hxends (hM.inter_eq ▸ (show x ∈ (A ∩ D) ∩ M from ⟨hxI, hxM⟩))
      · exact hxends (hN.inter_eq ▸ (show x ∈ (A ∩ D) ∩ N from ⟨hxI, hxN⟩))
  refine ⟨hU, hcross, M, N, ?_, hM, hN, ?_, ?_⟩
  · rw [hfrontier]
    exact houter
  · rw [union_comm, hM.union_eq, ← hA.interior_eq_inside_frontier, hA.closure_interior]
  · rw [union_comm, hN.union_eq, ← hD.interior_eq_inside_frontier, hD.closure_interior]

/-- Region-only wrapper for the gluing theorem. -/
theorem isJordanRegion_union_of_inter_isArc (hA : IsJordanRegion A)
    (hD : IsJordanRegion D) (hdis : Disjoint (interior A) (interior D))
    (hI : IsArcBetween (A ∩ D) p q)
    (hinterior : IsConnected (interior (A ∪ D)))
    (hcompl : IsConnected (A ∪ D)ᶜ) : IsJordanRegion (A ∪ D) :=
  (glue_of_inter_isArc hA hD hdis hI hinterior hcompl).1

/-- The actual intersection is a Jordan crosscut of the actual union. -/
theorem jordanCrosscut_of_inter_isArc (hA : IsJordanRegion A)
    (hD : IsJordanRegion D) (hdis : Disjoint (interior A) (interior D))
    (hI : IsArcBetween (A ∩ D) p q)
    (hinterior : IsConnected (interior (A ∪ D)))
    (hcompl : IsConnected (A ∪ D)ᶜ) :
    JordanCrosscut (frontier (A ∪ D)) (A ∩ D) p q :=
  (glue_of_inter_isArc hA hD hdis hI hinterior hcompl).2.1

/-- Endpoint-free form exposing the actual union and the actual closed pieces.
The endpoints and the two outer arcs are obtained from the intersection arc. -/
theorem glue_of_isArc_inter (hA : IsJordanRegion A) (hD : IsJordanRegion D)
    (hdis : Disjoint (interior A) (interior D)) (hI : IsArc (A ∩ D))
    (hinterior : IsConnected (interior (A ∪ D)))
    (hcompl : IsConnected (A ∪ D)ᶜ) :
    IsJordanRegion (A ∪ D) ∧
      ∃ p q M N, JordanCrosscut (frontier (A ∪ D)) (A ∩ D) p q ∧
        IsCutPair (frontier (A ∪ D)) p q M N ∧
        A = closure (inside (M ∪ (A ∩ D))) ∧
        D = closure (inside (N ∪ (A ∩ D))) := by
  obtain ⟨p, q, hpq⟩ := hI.exists_isArcBetween
  obtain ⟨hU, hcross, M, N, houter, _, _, hsideA, hsideD⟩ :=
    glue_of_inter_isArc hA hD hdis hpq hinterior hcompl
  exact ⟨hU, p, q, M, N, hcross, houter, hsideA.symm, hsideD.symm⟩

end Puzzling139335.HalfTurnRemainder.JordanUnion
