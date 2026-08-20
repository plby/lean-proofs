import ErdosProblems.Erdos733.ST.PolygonalArcInteriorPointCutDataExists
import ErdosProblems.Erdos733.ST.PolygonalArcVertexPointCutDataExists
import Mathlib.Tactic

open Classical
noncomputable section

-- [TABLET NODE: PolygonalArcPointCutDataExists]
lemma PolygonalArcPointCutDataExists
    (Q : PolygonalArc) (c : EuclideanSpace ℝ (Fin 2))
    (hc : c ∈ Q.relativeInterior) :
    Nonempty (PolygonalArcPointCutData Q c) := by
-- BODY
  rw [Q.relativeInterior_eq] at hc
  rcases hc with ⟨hcCarrier, hcEndpoints⟩
  have hcBoth : c ≠ Q.source ∧ c ≠ Q.target := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using hcEndpoints
  have hcSource : c ≠ Q.source := by
    exact hcBoth.1
  have hcTarget : c ≠ Q.target := by
    exact hcBoth.2
  by_cases hcListed : c ∈ Q.vertices
  · rcases List.getElem_of_mem hcListed with ⟨k, hk, hkc⟩
    have hsource0 : Q.vertices[0] = Q.source := by
      have hhead := Q.source_eq_head
      rw [List.head?_eq_getElem?] at hhead
      rw [List.getElem?_eq_getElem (by omega)] at hhead
      exact Option.some.inj hhead
    have hQgetEq (a b : ℕ) (ha : a < Q.vertices.length)
        (hb : b < Q.vertices.length) (hab : a = b) :
        Q.vertices[a]'ha = Q.vertices[b]'hb := by
      subst b
      rfl
    have hkpos : 0 < k := by
      by_contra hnot
      have hk0 : k = 0 := by omega
      apply hcSource
      exact hkc.symm.trans ((hQgetEq k 0 hk (by omega) hk0).trans hsource0)
    have htargetLast : Q.vertices[Q.vertices.length - 1] = Q.target := by
      have hlast := Q.target_eq_last
      rw [List.getLast?_eq_getLast_of_ne_nil (by
        exact List.ne_nil_of_length_pos (by omega))] at hlast
      have hget : Q.vertices.getLast (by
          exact List.ne_nil_of_length_pos (by omega)) = Q.target :=
        Option.some.inj hlast
      simpa [List.getLast_eq_getElem] using hget
    have hknext : k + 1 < Q.vertices.length := by
      by_contra hnot
      have hklast : k = Q.vertices.length - 1 := by omega
      apply hcTarget
      exact hkc.symm.trans
        ((hQgetEq k (Q.vertices.length - 1) hk (by omega) hklast).trans htargetLast)
    simpa only [hkc] using
      PolygonalArcVertexPointCutDataExists Q k hkpos hknext
  · rw [Q.carrier_eq] at hcCarrier
    rcases hcCarrier with ⟨i, hi, hci⟩
    have hleft : Q.vertices[i] ≠ c := by
      intro hEq
      apply hcListed
      rw [← hEq]
      exact List.getElem_mem (by omega)
    have hright : Q.vertices[i + 1] ≠ c := by
      intro hEq
      apply hcListed
      rw [← hEq]
      exact List.getElem_mem hi
    exact PolygonalArcInteriorPointCutDataExists Q i hi c
      (mem_openSegment_of_ne_left_right hleft hright hci)
