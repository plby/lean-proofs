/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim68
import ErdosProblems.Erdos547b.Lemma74
import ErdosProblems.Erdos547b.Lemma78Full
import ErdosProblems.Erdos547b.TreeMinDegreeEmbedding

/-!
# The leaf-core completion step in Zhao's Claim 6.10

A tree with many leaves has a small connected leaf-deleted core.  A copy of
that core in a high-minimum-degree induced host extends to the whole tree
because every core vertex lies at a large-degree ambient host vertex.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoClaim610LeafCoreEmbedding

open Finset Fintype SimpleGraph
open Erdos547b.ZhaoClaim68
open Erdos547b.ZhaoLemma78Full74
open Erdos547b.ZhaoTreeMinDegreeEmbedding

universe u v

variable {A : Type u} [Fintype A] [DecidableEq A]
variable {T : SimpleGraph A} [DecidableRel T.Adj]

/-- The unique neighbor of a leaf. -/
noncomputable def leafParent (x : {x // x ∈ graphLeaves T}) : A :=
  Classical.choose (degree_eq_one_iff_existsUnique_adj.mp
    (Finset.mem_filter.mp x.2).2)

theorem leafParent_adj (x : {x // x ∈ graphLeaves T}) :
    T.Adj (leafParent x) x.1 := by
  exact (Classical.choose_spec (degree_eq_one_iff_existsUnique_adj.mp
    (Finset.mem_filter.mp x.2).2)).1.symm

theorem leaf_unique (x : {x // x ∈ graphLeaves T}) (y : A)
    (hxy : T.Adj x.1 y) : y = leafParent x := by
  exact (Classical.choose_spec (degree_eq_one_iff_existsUnique_adj.mp
    (Finset.mem_filter.mp x.2).2)).2 y hxy

/-- In a tree of order at least three, the neighbor of a leaf is not a leaf. -/
theorem leafParent_not_mem (hT : T.IsTree) (hcard : 3 ≤ Fintype.card A)
    (x : {x // x ∈ graphLeaves T}) :
    leafParent x ∉ graphLeaves T := by
  intro hp
  exact not_adj_of_both_degree_one_of_three_le_card T hT
    (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp x.2).2 hcard
    (leafParent_adj x)

/-- The complement of all graph leaves is nonempty once the tree has at
least three vertices. -/
theorem graphLeaves_compl_nonempty (hT : T.IsTree)
    (hcard : 3 ≤ Fintype.card A) :
    ((graphLeaves T : Set A)ᶜ).Nonempty := by
  have hnontrivial : Nontrivial A :=
    Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨x, hx⟩ :=
    @IsTree.exists_vert_degree_one_of_nontrivial A T _ hnontrivial _ hT
  have hxLeaf : x ∈ graphLeaves T := by simp [graphLeaves, hx]
  let xs : {x // x ∈ graphLeaves T} := ⟨x, hxLeaf⟩
  exact ⟨leafParent xs, leafParent_not_mem hT hcard xs⟩

/-- Deleting all leaves from a tree of order at least three leaves a tree. -/
theorem leafCore_isTree (hT : T.IsTree) (hcard : 3 ≤ Fintype.card A) :
    (T.induce ((graphLeaves T : Set A)ᶜ)).IsTree := by
  refine ⟨Erdos547b.connected_induce_compl_of_leaves T
    (graphLeaves T : Set A) hT.connected ?_ (graphLeaves_compl_nonempty hT hcard),
    hT.isAcyclic.induce _⟩
  intro x hx
  exact (Finset.mem_filter.mp hx).2

@[simp] theorem card_leafCore :
    Fintype.card {x : A // x ∉ graphLeaves T} =
      Fintype.card A - #(graphLeaves T) := by
  simpa only [Fintype.card_coe] using
    Fintype.card_subtype_compl (fun x : A ↦ x ∈ graphLeaves T)

/-- The concrete small-core argument: a high-minimum-degree induced host
contains the leaf-deleted core, and ambient large degree then attaches every
leaf by Hall's theorem. -/
theorem isContained_of_leaf_bound_and_induced_minDegree
    {B : Type v} [Fintype B] [DecidableEq B]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (hT : T.IsTree) (hcard : 3 ≤ Fintype.card A)
    (k : ℕ)
    (hleaf : Fintype.card A ≤ k + 1 + #(graphLeaves T))
    (U : Finset B) (hUne : U.Nonempty)
    (hmin : ∀ u : {x // x ∈ U}, k < (G.induce (U : Set B)).degree u)
    (hlarge : ∀ u : {x // x ∈ U},
      Fintype.card A - 1 ≤ G.degree u.1) :
    T.IsContained G := by
  let core := T.induce ((graphLeaves T : Set A)ᶜ)
  have hcoreTree : core.IsTree := leafCore_isTree hT hcard
  have hcoreCard : Fintype.card {x : A // x ∉ graphLeaves T} ≤ k + 1 := by
    rw [card_leafCore]
    omega
  let : Nonempty {x // x ∈ U} := hUne.to_subtype
  have hcoreDegree : ∀ u : {x // x ∈ U},
      Fintype.card {x : A // x ∉ graphLeaves T} - 1 ≤
        (G.induce (U : Set B)).degree u := by
    intro u
    have : Fintype.card {x : A // x ∉ graphLeaves T} - 1 ≤ k := by omega
    exact this.trans (Nat.le_of_lt (hmin u))
  obtain ⟨coreCopy⟩ :=
    exists_copy core (G.induce (U : Set B)) hcoreTree hcoreDegree
  let ambientCoreCopy : core.Copy G :=
    (SimpleGraph.Copy.induce G (U : Set B)).comp coreCopy
  have hparentDegree : ∀ x : {x // x ∈ graphLeaves T},
      Fintype.card A - 1 ≤
        G.degree (ambientCoreCopy ⟨leafParent x,
          leafParent_not_mem hT hcard x⟩) := by
    intro x
    exact hlarge (coreCopy ⟨leafParent x, leafParent_not_mem hT hcard x⟩)
  obtain ⟨fullCopy, -, -⟩ := exists_copy_of_induce_compl_of_leaves
    T G (graphLeaves T) leafParent (leafParent_not_mem hT hcard)
      leafParent_adj leaf_unique ambientCoreCopy hparentDegree
  exact fullCopy.isContained

/-- Nested form used by the host-density argument: `X` is the balanced
large-degree half, and `U` is the dense induced subgraph found inside `X`. -/
theorem isContained_of_leaf_bound_and_twoStage_induced_minDegree
    {B : Type v} [Fintype B] [DecidableEq B]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (hT : T.IsTree) (hcard : 3 ≤ Fintype.card A)
    (k : ℕ)
    (hleaf : Fintype.card A ≤ k + 1 + #(graphLeaves T))
    (X : Finset B) (hlarge : ∀ x ∈ X,
      Fintype.card A - 1 ≤ G.degree x)
    (U : Finset {x // x ∈ X}) (hUne : U.Nonempty)
    (hmin : ∀ u : {x // x ∈ U},
      k < ((G.induce (X : Set B)).induce (U : Set _)).degree u) :
    T.IsContained G := by
  let core := T.induce ((graphLeaves T : Set A)ᶜ)
  have hcoreTree : core.IsTree := leafCore_isTree hT hcard
  have hcoreCard : Fintype.card {x : A // x ∉ graphLeaves T} ≤ k + 1 := by
    rw [card_leafCore]
    omega
  let : Nonempty {x // x ∈ U} := hUne.to_subtype
  have hcoreDegree : ∀ u : {x // x ∈ U},
      Fintype.card {x : A // x ∉ graphLeaves T} - 1 ≤
        ((G.induce (X : Set B)).induce (U : Set _)).degree u := by
    intro u
    have : Fintype.card {x : A // x ∉ graphLeaves T} - 1 ≤ k := by omega
    exact this.trans (Nat.le_of_lt (hmin u))
  obtain ⟨coreCopy⟩ := exists_copy core
    ((G.induce (X : Set B)).induce (U : Set _)) hcoreTree hcoreDegree
  let coreCopyX : core.Copy (G.induce (X : Set B)) :=
    (SimpleGraph.Copy.induce (G.induce (X : Set B)) (U : Set _)).comp coreCopy
  let ambientCoreCopy : core.Copy G :=
    (SimpleGraph.Copy.induce G (X : Set B)).comp coreCopyX
  have hparentDegree : ∀ x : {x // x ∈ graphLeaves T},
      Fintype.card A - 1 ≤
        G.degree (ambientCoreCopy ⟨leafParent x,
          leafParent_not_mem hT hcard x⟩) := by
    intro x
    change Fintype.card A - 1 ≤
      G.degree (coreCopy ⟨leafParent x, leafParent_not_mem hT hcard x⟩).1.1
    exact hlarge _
      (coreCopy ⟨leafParent x, leafParent_not_mem hT hcard x⟩).1.2
  obtain ⟨fullCopy, -, -⟩ := exists_copy_of_induce_compl_of_leaves
    T G (graphLeaves T) leafParent (leafParent_not_mem hT hcard)
      leafParent_adj leaf_unique ambientCoreCopy hparentDegree
  exact fullCopy.isContained

end Erdos547b.ZhaoClaim610LeafCoreEmbedding

#print axioms Erdos547b.ZhaoClaim610LeafCoreEmbedding.isContained_of_leaf_bound_and_induced_minDegree
#print axioms Erdos547b.ZhaoClaim610LeafCoreEmbedding.isContained_of_leaf_bound_and_twoStage_induced_minDegree
