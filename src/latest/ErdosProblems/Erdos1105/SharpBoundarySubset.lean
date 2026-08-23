import ErdosProblems.Erdos1105.InduceCore
import ErdosProblems.Erdos1105.SharpCorePeeling
import ErdosProblems.Erdos1105.SharpCliqueBoundary

namespace Erdos1105

open SimpleGraph Finset

/-- A sharp clique-core graph contains a boundary-order exceptional join.
The surviving set still contains every vertex of the original core. -/
theorem exists_sharp_boundary_join {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hd : 2 ≤ d) (hn : 2 * d + 3 ≤ Fintype.card V)
    (hclique : G.IsClique (vertexCore G d : Set V))
    (hcard : (vertexCore G d).card = d + 3) (hfree : NoLongCycle G (2 * d + 3))
    (hsharp : G.edgeFinset.card = (vertexCore G d).card.choose 2 +
      d * (Fintype.card V - (vertexCore G d).card)) :
    ∃ U : Finset V, U.card = 2 * d + 3 ∧ vertexCore G d ⊆ U ∧
      ∃ A T : Finset (U : Set V), A.card = d ∧ T.card = 3 ∧ Disjoint A T ∧
        (∀ u, (G.induce (U : Set V)).IsUniversal u → u ∈ A) ∧
        threeCliqueJoin A T ≤ G.induce (U : Set V) := by
  classical
  have hactual := sharp_core_count_actual G d hsharp
  have hcoreEdges : (E767EGApi.edgesInside G (vertexCore G d)).card =
      (vertexCore G d).card.choose 2 := by
    have heq : E767EGApi.edgesInside G univ = G.edgeFinset := by
      simp [E767EGApi.edgesInside]
    rw [heq, card_univ] at hactual
    omega
  obtain ⟨U, _, hUcore, hUcard, hUsharp⟩ := exists_sharp_core_subset G d univ (2 * d + 3)
    (subset_univ _) (by omega) (by simpa only [card_univ] using hn) hactual
  let H := G.induce (U : Set V)
  have himage := vertexCore_induce_image G d U hUcore
  have hHcoreCard : (vertexCore H d).card = d + 3 := by
    rw [← hcard, ← himage, card_image_of_injective _ Subtype.val_injective]
  have hHclique : H.IsClique (vertexCore H d : Set (U : Set V)) := by
    intro v hv w hw hne
    exact hclique (himage ▸ mem_image.mpr ⟨v, hv, rfl⟩)
      (himage ▸ mem_image.mpr ⟨w, hw, rfl⟩) (fun h ↦ hne (Subtype.ext h))
  have hHcard : Fintype.card (U : Set V) = 2 * d + 3 := by
    simpa using hUcard
  have hnot : ¬H.IsHamiltonian := by
    intro h
    obtain ⟨u, p, hp⟩ := h (by omega)
    let f := (Embedding.induce (G := G) (U : Set V))
    have hb := hfree u.val (p.map f.toHom) (hp.isCycle.map f.injective)
    have hlen : (p.map f.toHom).length = p.length := Walk.length_map _ _
    have hbad : 2 * d + 3 < 2 * d + 3 := calc
      _ = p.length := (hp.length_eq.trans hHcard).symm
      _ = (p.map f.toHom).length := hlen.symm
      _ < _ := hb
    exact Nat.lt_irrefl _ hbad
  have hHsharp : H.edgeFinset.card = (vertexCore H d).card.choose 2 +
      d * (Fintype.card (U : Set V) - (vertexCore H d).card) := by
    rw [hHcoreCard, hHcard]
    change (G.induce (U : Set V)).edgeFinset.card = _
    rw [← E767EGApi.card_edgesInside]
    rw [hUsharp, hcoreEdges, hcard]
  obtain ⟨A, T, hA, hT, hAT, huni, hjoin⟩ :=
    sharp_clique_boundary_join H hd hHcard hHclique hHcoreCard hnot hHsharp
  exact ⟨U, hUcard, hUcore, A, T, hA, hT, hAT, huni, hjoin⟩

end Erdos1105

#print axioms Erdos1105.exists_sharp_boundary_join
