/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Data.Finset.Powerset

/-!
# A dense finite graph has an induced subgraph of large minimum degree

This is the elementary deletion lemma used in Zhao's proof of Claim 6.10.
We use a minimal vertex set whose induced edge count is still larger than
`k` times its order.  Removing a vertex of degree at most `k` would preserve
that strict inequality, contradicting minimality.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoDenseInducedMinDegree

open Finset SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

private def denseSubsets (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    Finset (Finset V) :=
  (Finset.univ : Finset V).powerset.filter fun U =>
    k * U.card < #(G.induce (U : Set V)).edgeFinset

/-- Deleting one vertex from an induced graph deletes exactly its induced
degree.  This explicit finite-set form is convenient for minimal-subset
arguments. -/
theorem card_edges_induce_erase
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (v : {x // x ∈ U}) :
    #(G.induce ((U.erase v.1 : Finset V) : Set V)).edgeFinset =
      #(G.induce (U : Set V)).edgeFinset -
        (G.induce (U : Set V)).degree v := by
  let H := G.induce (U : Set V)
  let e : {x : {x // x ∈ U} // x ≠ v} ≃ {x // x ∈ U.erase v.1} :=
    { toFun := fun x => ⟨x.1.1, Finset.mem_erase.mpr ⟨by
          intro h
          apply x.2
          exact Subtype.ext h, x.1.2⟩⟩
      invFun := fun x => ⟨⟨x.1, (Finset.mem_erase.mp x.2).2⟩, by
        intro h
        have := congrArg Subtype.val h
        exact (Finset.mem_erase.mp x.2).1 this⟩
      left_inv := fun x => by apply Subtype.ext; apply Subtype.ext; rfl
      right_inv := fun x => by apply Subtype.ext; rfl }
  let iso : H.induce ({v} : Set {x // x ∈ U})ᶜ ≃g
      G.induce ((U.erase v.1 : Finset V) : Set V) :=
    { toEquiv := e
      map_rel_iff' := by
        intro x y
        rfl }
  calc
    #(G.induce ((U.erase v.1 : Finset V) : Set V)).edgeFinset =
        #(H.induce ({v} : Set {x // x ∈ U})ᶜ).edgeFinset :=
      iso.card_edgeFinset_eq.symm
    _ = #(H.deleteIncidenceSet v).edgeFinset :=
      H.card_edgeFinset_induce_compl_singleton v
    _ = #H.edgeFinset - H.degree v :=
      H.card_edgeFinset_deleteIncidenceSet v

/-- Inducing on the literal finite universe does not change the edge count. -/
theorem card_edges_induce_univ
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    #(G.induce ((Finset.univ : Finset V) : Set V)).edgeFinset =
      #G.edgeFinset := by
  let e : {x // x ∈ (Finset.univ : Finset V)} ≃ V :=
    { toFun := fun x => x.1
      invFun := fun x => ⟨x, Finset.mem_univ x⟩
      left_inv := fun x => by apply Subtype.ext; rfl
      right_inv := fun _ => rfl }
  let iso : G.induce ((Finset.univ : Finset V) : Set V) ≃g G :=
    { toEquiv := e
      map_rel_iff' := by
        intro x y
        rfl }
  exact iso.card_edgeFinset_eq

/-- If a finite graph has more than `k |V|` edges, some nonempty induced
subgraph has minimum degree strictly larger than `k`. -/
theorem exists_induced_minDegree_gt_of_mul_card_lt_edges
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (hdense : k * Fintype.card V < #G.edgeFinset) :
    ∃ U : Finset V, U.Nonempty ∧
      ∀ v : {x // x ∈ U}, k < (G.induce (U : Set V)).degree v := by
  classical
  have hcandidates : (denseSubsets G k).Nonempty := by
    refine ⟨Finset.univ, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_powerset.mpr (Finset.subset_univ _)
    · rw [Finset.card_univ, card_edges_induce_univ]
      exact hdense
  obtain ⟨U, hUmem, hminimal⟩ :=
    Finset.exists_min_image (denseSubsets G k) Finset.card hcandidates
  have hUdense : k * U.card < #(G.induce (U : Set V)).edgeFinset :=
    (Finset.mem_filter.mp hUmem).2
  have hUne : U.Nonempty := by
    by_contra h
    have hUempty : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have hedge0 : #(G.induce ((∅ : Finset V) : Set V)).edgeFinset = 0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e
      refine Sym2.inductionOn e ?_
      intro x _y
      have hx : False := by simpa using x.2
      exact hx.elim
    rw [hUempty, Finset.card_empty, Nat.mul_zero, hedge0] at hUdense
    omega
  refine ⟨U, hUne, ?_⟩
  intro v
  by_contra hdegree
  have hdegree' : (G.induce (U : Set V)).degree v ≤ k :=
    Nat.le_of_not_gt hdegree
  let U' := U.erase v.1
  have hcardU' : U'.card = U.card - 1 := by
    simp only [U', Finset.card_erase_of_mem v.2]
  have hedgeU' : #(G.induce (U' : Set V)).edgeFinset =
      #(G.induce (U : Set V)).edgeFinset -
        (G.induce (U : Set V)).degree v := by
    exact card_edges_induce_erase G U v
  have hU'dense : k * U'.card < #(G.induce (U' : Set V)).edgeFinset := by
    rw [hedgeU']
    apply Nat.lt_sub_of_add_lt
    have hcardAdd : U'.card + 1 = U.card := by
      rw [hcardU']
      exact Nat.sub_add_cancel (Finset.one_le_card.mpr hUne)
    have hmulSplit : k * U'.card + k = k * U.card := by
      calc
        k * U'.card + k = k * (U'.card + 1) := by
          rw [Nat.mul_add, Nat.mul_one]
        _ = k * U.card := congrArg (k * ·) hcardAdd
    calc
      k * U'.card + (G.induce (U : Set V)).degree v ≤
          k * U'.card + k := Nat.add_le_add_left hdegree' _
      _ = k * U.card := hmulSplit
      _ < #(G.induce (U : Set V)).edgeFinset := hUdense
  have hU'mem : U' ∈ denseSubsets G k := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),
      hU'dense⟩
  have hmin := hminimal U' hU'mem
  rw [hcardU'] at hmin
  have hvcard : 0 < U.card := Finset.card_pos.mpr hUne
  omega

end Erdos547b.ZhaoDenseInducedMinDegree

#print axioms Erdos547b.ZhaoDenseInducedMinDegree.card_edges_induce_erase
#print axioms Erdos547b.ZhaoDenseInducedMinDegree.card_edges_induce_univ
#print axioms Erdos547b.ZhaoDenseInducedMinDegree.exists_induced_minDegree_gt_of_mul_card_lt_edges
