/- Finite union bound for choosing a path compatible with many linkages. -/
import ErdosProblems.Erdos73.BoundaryLinkageDeletion

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open Erdos73Infrastructure.SimpleGraph
open scoped BigOperators

def HasProperAvoidingPacking {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (A B Z D : Finset V) (k : ℕ) : Prop :=
  ∃ P : PathPacking G (A \ D) (B \ D), k ≤ P.card ∧
    (∀ r, Disjoint (P.path r).vertexSet D) ∧ P.IsBoundaryProper Z

/-- Choose one path whose deletion retains a specified positive fraction
of each of finitely many proper linkages (qualitative Leaf--Seymour 3.4). -/
theorem exists_path_simultaneously_preserving
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]
    {G : SimpleGraph V} (A B : I → Finset V) {S T Z : Finset V}
    (P : ∀ i, PathPacking G (A i) (B i)) (Q : PathPacking G S T)
    (hP : ∀ i, (P i).IsBoundaryProper Z) (hQ : Q.IsBoundaryProper Z)
    (hAZ : ∀ i, A i ⊆ Z) (hBZ : ∀ i, B i ⊆ Z)
    (g h : ℕ) (hh : 0 < h)
    (hm : ∀ i, qualitativeGrillRows g h ≤ (P i).card)
    (hsize : (∑ i, ((P i).card + 1) * (2 * qualitativeGrillColumns g h)) < Q.card)
    (hgrid : ¬ IsMinor (squareGrid g) G)
    (hbip : ¬ IsMinor (completeBipartiteGraph (Fin h) (Fin h)) G) :
    ∃ q : Q.Index, ∀ i, HasProperAvoidingPacking G (A i) (B i) Z
      (Q.path q).vertexSet ((P i).card / (2 * qualitativeGrillRows g h) + 1) := by
  let good (i : I) (q : Q.Index) := HasProperAvoidingPacking G (A i) (B i) Z
    (Q.path q).vertexSet ((P i).card / (2 * qualitativeGrillRows g h) + 1)
  let bad (i : I) : Finset Q.Index := Finset.univ.filter fun q => ¬ good i q
  have hbad (i : I) : (bad i).card < ((P i).card + 1) * (2 * qualitativeGrillColumns g h) := by
    by_contra hn
    have hbound : ((P i).card + 1) * (2 * qualitativeGrillColumns g h) ≤
        (Q.restrictIndexSet (bad i)).card := by
      rw [PathPacking.restrictIndexSet_card]
      omega
    obtain ⟨q, R, hRcard, hRd, hRprop⟩ := boundaryProper_linkage_avoiding_path
      (P i) (Q.restrictIndexSet (bad i)) (hP i) (fun q => hQ q.val)
      (hAZ i) (hBZ i) g h hh (hm i) hbound hgrid hbip
    have hqbad : ¬ good i q.val := (Finset.mem_filter.mp q.property).2
    exact hqbad ⟨R, hRcard, hRd, hRprop⟩
  let U := Finset.univ.biUnion bad
  have hU : U.card < (Finset.univ : Finset Q.Index).card := by
    calc
      U.card ≤ ∑ i, (bad i).card := Finset.card_biUnion_le
      _ ≤ ∑ i, ((P i).card + 1) * (2 * qualitativeGrillColumns g h) :=
        Finset.sum_le_sum fun i _ => (hbad i).le
      _ < Q.card := hsize
      _ = (Finset.univ : Finset Q.Index).card := (Finset.card_univ).symm
  obtain ⟨q, _, hq⟩ := Finset.exists_mem_notMem_of_card_lt_card hU
  refine ⟨q, fun i => ?_⟩
  by_contra hnot
  exact hq (Finset.mem_biUnion.mpr
    ⟨i, Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnot⟩⟩)

end
end Erdos73
