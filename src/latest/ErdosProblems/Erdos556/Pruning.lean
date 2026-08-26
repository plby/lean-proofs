import ErdosProblems.Erdos556.Basic
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-!
# Low-degree deletion

A minimum-cardinality set satisfying an edge-excess invariant supplies an
induced core. This proves the deletion statement without introducing an
algorithm or assuming the existence of a core.
-/

namespace Erdos556

open SimpleGraph

/-- Deleting a vertex after induction is the same as inducing on the erased set. -/
def induceEraseIso {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (S : Finset V) (v : S) :
    (G.induce (S : Set V)).induce ({v}ᶜ : Set S) ≃g
      G.induce (S.erase v.val : Set V) where
  toEquiv :=
    { toFun := fun x => ⟨x.val.val, Finset.mem_erase.mpr ⟨by
        intro h
        exact x.property (Subtype.ext h), x.val.property⟩⟩
      invFun := fun x => ⟨⟨x.val, (Finset.mem_erase.mp x.property).2⟩, by
        intro h
        exact (Finset.mem_erase.mp x.property).1 (congrArg Subtype.val h)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  map_rel_iff' := by intro x y; rfl

theorem induced_edges_erase_add_degree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (v : S) :
    (G.induce (S.erase v.val : Set V)).edgeFinset.card +
      (G.induce (S : Set V)).degree v = (G.induce (S : Set V)).edgeFinset.card := by
  rw [← (induceEraseIso G S v).card_edgeFinset_eq]
  rw [card_edgeFinset_induce_compl_singleton, card_edgeFinset_deleteIncidenceSet]
  exact Nat.sub_add_cancel ((G.induce (S : Set V)).degree_le_card_edgeFinset v)

/-- Pruning preserves edge excess over `d` times the vertex count and leaves
an induced graph in which every vertex has degree strictly greater than `d`.
The empty induced graph is allowed when the original excess is nonpositive. -/
theorem exists_induced_core {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℝ) :
    ∃ S : Finset V,
      (G.edgeFinset.card : ℝ) - d * Fintype.card V ≤
        ((G.induce (S : Set V)).edgeFinset.card : ℝ) - d * S.card ∧
      ∀ v : S, d < (G.induce (S : Set V)).degree v := by
  classical
  let excess (S : Finset V) : ℝ :=
    ((G.induce (S : Set V)).edgeFinset.card : ℝ) - d * S.card
  let baseline : ℝ := (G.edgeFinset.card : ℝ) - d * Fintype.card V
  let good : Finset (Finset V) := Finset.univ.filter fun S => baseline ≤ excess S
  have huniv : (Finset.univ : Finset V) ∈ good := by
    have he : (G.induce ((Finset.univ : Finset V) : Set V)).edgeFinset.card =
        G.edgeFinset.card := by
      rw [← G.card_filter_edgeFinset_toFinset_subset Finset.univ]
      simp
    simp [good, excess, baseline, he]
  obtain ⟨S, hS, hminimal⟩ := good.exists_min_image Finset.card ⟨_, huniv⟩
  have hgood : baseline ≤ excess S := (Finset.mem_filter.mp hS).2
  refine ⟨S, hgood, ?_⟩
  intro v
  by_contra hdegree
  have hdegree' : ((G.induce (S : Set V)).degree v : ℝ) ≤ d := by
    exact le_of_not_gt hdegree
  let T := S.erase v.val
  have hcard : T.card + 1 = S.card := Finset.card_erase_add_one v.property
  have hedge := induced_edges_erase_add_degree G S v
  have hedgeR : ((G.induce (T : Set V)).edgeFinset.card : ℝ) +
      (G.induce (S : Set V)).degree v = (G.induce (S : Set V)).edgeFinset.card := by
    exact_mod_cast hedge
  have hcardR : (T.card : ℝ) + 1 = S.card := by exact_mod_cast hcard
  have hT : T ∈ good := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    dsimp [excess] at hgood ⊢
    nlinarith
  have hle := hminimal T hT
  omega

/-- Positive edge excess ensures that the pruned core is nonempty and keeps
the same strict edge-density inequality. -/
theorem exists_dense_induced_core {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℝ)
    (hd : d * Fintype.card V < (G.edgeFinset.card : ℝ)) :
    ∃ S : Finset V, S.Nonempty ∧
      d * S.card < ((G.induce (S : Set V)).edgeFinset.card : ℝ) ∧
      ∀ v : S, d < (G.induce (S : Set V)).degree v := by
  obtain ⟨S, hS, hdegree⟩ := exists_induced_core G d
  have he : d * S.card < ((G.induce (S : Set V)).edgeFinset.card : ℝ) := by linarith
  refine ⟨S, ?_, he, hdegree⟩
  by_contra hnonempty
  have hzero : S.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hnonempty)
  have hSCard : Fintype.card (S : Set V) = S.card := by
    calc
      Fintype.card (S : Set V) = (S : Set V).ncard := Nat.card_eq_fintype_card.symm
      _ = S.card := Set.ncard_coe_finset S
  have hb := (G.induce (S : Set V)).card_edgeFinset_le_card_choose_two
  rw [hSCard] at hb
  rw [hzero] at hb
  norm_num only [Nat.choose_zero_succ] at hb
  have hezero : (G.induce (S : Set V)).edgeFinset.card = 0 := Nat.eq_zero_of_le_zero hb
  simp [hzero, hezero] at he

#print axioms exists_induced_core
#print axioms exists_dense_induced_core

end Erdos556
