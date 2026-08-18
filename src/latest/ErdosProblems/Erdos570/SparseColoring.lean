/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.PathRamsey
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Coloring a connected graph by its cyclomatic excess

A connected finite graph is a spanning tree together with
`e(G) + 1 - v(G)` extra edges.  Giving every endpoint of an extra edge its
own color and two-coloring the remaining forest gives the deliberately crude,
but very useful, bound `χ(G) ≤ 2 + 2 (e(G) + 1 - v(G))`.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos570

open Erdos79

section ExcessColoring

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The vertices incident with an edge in a finite edge set. -/
def edgeEndpoints (E : Finset (Sym2 V)) : Finset V :=
  E.biUnion Sym2.toFinset

@[simp] theorem mem_edgeEndpoints {E : Finset (Sym2 V)} {v : V} :
    v ∈ edgeEndpoints E ↔ ∃ e ∈ E, v ∈ e := by
  simp [edgeEndpoints]

theorem card_edgeEndpoints_le (E : Finset (Sym2 V)) :
    (edgeEndpoints E).card ≤ 2 * E.card := by
  classical
  have hcard (e : Sym2 V) (_he : e ∈ E) : e.toFinset.card ≤ 2 := by
    rw [Sym2.card_toFinset]
    split <;> omega
  calc
    (edgeEndpoints E).card ≤ ∑ e ∈ E, e.toFinset.card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ E, 2 := Finset.sum_le_sum hcard
    _ = 2 * E.card := by simp [mul_comm]

/-- A connected finite graph admits a proper coloring using two colors plus
one private color for every endpoint of an edge outside a spanning tree. -/
theorem exists_coloring_card_le_two_add_twice_excess
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected) :
    ∃ t : ℕ, t ≤ 2 + 2 * (G.edgeFinset.card + 1 - Fintype.card V) ∧
      Nonempty (G.Coloring (Fin t)) := by
  classical
  obtain ⟨T, hTG, hTtree⟩ := hG.exists_isTree_le
  letI : DecidableRel T.Adj := Classical.decRel _
  let E : Finset (Sym2 V) := G.edgeFinset \ T.edgeFinset
  let X : Finset V := edgeEndpoints E
  have hTedge : T.edgeFinset ⊆ G.edgeFinset :=
    SimpleGraph.edgeFinset_mono hTG
  have hEcard : E.card = G.edgeFinset.card + 1 - Fintype.card V := by
    rw [show E = G.edgeFinset \ T.edgeFinset from rfl,
      Finset.card_sdiff_of_subset hTedge]
    have htcard := hTtree.card_edgeFinset
    omega
  have hXcard : X.card ≤ 2 * E.card := card_edgeEndpoints_le E
  obtain ⟨cT⟩ := hTtree.isBipartite
  let color : V → Fin (2 + X.card) := fun v ↦
    if hv : v ∈ X then
      Fin.natAdd 2 (X.equivFin ⟨v, hv⟩)
    else
      Fin.castAdd X.card (cT v)
  have hvalid : ∀ ⦃v w : V⦄, G.Adj v w → color v ≠ color w := by
    intro v w hvw
    have hvwne : v ≠ w := hvw.ne
    by_cases hv : v ∈ X <;> by_cases hw : w ∈ X
    · dsimp only [color]
      rw [dif_pos hv, dif_pos hw]
      intro heq
      have heq' := (Fin.natAdd_inj 2).mp heq
      have hsub := X.equivFin.injective heq'
      exact hvwne (congrArg Subtype.val hsub)
    · dsimp only [color]
      rw [dif_pos hv, dif_neg hw]
      intro heq
      have hval := congrArg Fin.val heq
      simp only [Fin.val_natAdd, Fin.val_castAdd] at hval
      have hcLt : (cT w).val < 2 := (cT w).isLt
      omega
    · dsimp only [color]
      rw [dif_neg hv, dif_pos hw]
      intro heq
      have hval := congrArg Fin.val heq
      simp only [Fin.val_natAdd, Fin.val_castAdd] at hval
      have hcLt : (cT v).val < 2 := (cT v).isLt
      omega
    · dsimp only [color]
      rw [dif_neg hv, dif_neg hw]
      intro heq
      apply cT.valid ?_ ((Fin.castAdd_injective 2 X.card) heq)
      have he : s(v, w) ∈ G.edgeFinset := by
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        exact hvw
      have hnotE : s(v, w) ∉ E := by
        intro heE
        exact hv (mem_edgeEndpoints.mpr
          ⟨s(v, w), heE, by simp⟩)
      have heT : s(v, w) ∈ T.edgeFinset := by
        by_contra hnotT
        exact hnotE (Finset.mem_sdiff.mpr ⟨he, hnotT⟩)
      rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at heT
  refine ⟨2 + X.card, ?_,
    ⟨SimpleGraph.Coloring.mk color (@hvalid)⟩⟩
  rw [hEcard] at hXcard
  omega

/-- Path Ramsey bound depending only on the target order and cyclomatic
excess.  This packages the excess coloring with the iterated Häggkvist bound. -/
theorem pathGraph_isContained_or_compl_of_connected_excess
    {W U : Type*} [Fintype W] [Fintype U]
    [DecidableEq W] {k : ℕ} (hk : 2 ≤ k) (H : SimpleGraph W)
    [DecidableRel H.Adj] (hH : H.Connected)
    (C : SimpleGraph U)
    (hcard : Fintype.card W +
        k * (1 + 2 * (H.edgeFinset.card + 1 - Fintype.card W)) ≤
      Fintype.card U) :
    SimpleGraph.pathGraph k ⊑ C ∨ H ⊑ Cᶜ := by
  classical
  obtain ⟨t, ht, ⟨c⟩⟩ :=
    exists_coloring_card_le_two_add_twice_excess H hH
  apply pathGraph_isContained_or_compl_of_coloring hk H c C
  have ht' : t - 1 ≤ 1 + 2 *
      (H.edgeFinset.card + 1 - Fintype.card W) := by omega
  exact (Nat.add_le_add_left (Nat.mul_le_mul_left k ht') _).trans hcard

/-- Coded exact-order form of the connected-excess path bound. -/
theorem ramseyAt_path_connected_excess
    (H : GraphCode) (hH : H.graph.Connected) {k N : ℕ} (hk : 2 ≤ k)
    (hcard : H.vertexCount +
        k * (1 + 2 * (H.edgeCount + 1 - H.vertexCount)) ≤ N) :
    RamseyAt (pathCode k) H N := by
  classical
  intro C
  letI : DecidableRel H.graph.Adj := Classical.decRel _
  have h := pathGraph_isContained_or_compl_of_connected_excess
    hk H.graph hH C (by
      simpa [GraphCode.edgeCount_eq_card_edgeFinset] using hcard)
  simpa [pathCode] using h

/-- Numeric Ramsey-number form of `ramseyAt_path_connected_excess`. -/
theorem graphRamseyNumber_path_connected_excess_le
    (H : GraphCode) (hH : H.graph.Connected) {k : ℕ} (hk : 2 ≤ k) :
    graphRamseyNumber (pathCode k) H ≤
      H.vertexCount + k * (1 + 2 * (H.edgeCount + 1 - H.vertexCount)) :=
  graphRamseyNumber_le_of_ramseyAt
    (ramseyAt_path_connected_excess H hH hk le_rfl)

end ExcessColoring

end Erdos570
