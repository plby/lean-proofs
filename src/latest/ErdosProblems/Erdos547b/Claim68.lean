/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.TreePartition
import ErdosProblems.Erdos547b.Stability
import ErdosProblems.Erdos547b.GallaiEdmonds
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Data.Finset.CastCard
import Mathlib.Tactic

open scoped SimpleGraph Sym2

noncomputable section

namespace Erdos547b.ZhaoClaim68

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition

universe u v

/-! ## Greedy completion of a previously embedded leaf-deleted tree -/

/-- The vertices already used by a copy of the graph induced off `W`. -/
def baseImages {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [DecidableEq β] (W : Finset α)
    {T : SimpleGraph α} {G : SimpleGraph β}
    (f : (T.induce (↑W : Set α)ᶜ).Copy G) : Finset β :=
  Finset.univ.image f

/-- Available images for a deleted leaf: unused neighbors of its parent's image. -/
def leafChoices {α : Type u} {β : Type v} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (W : Finset α) {T : SimpleGraph α} (G : SimpleGraph β)
    [DecidableRel G.Adj]
    (parent : (x : {x // x ∈ W}) → α)
    (hparent : ∀ x, parent x ∉ W)
    (f : (T.induce (↑W : Set α)ᶜ).Copy G)
    (x : {x // x ∈ W}) : Finset β :=
  G.neighborFinset (f ⟨parent x, hparent x⟩) \ baseImages W f

private theorem card_baseImages
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α] [DecidableEq β]
    (W : Finset α) {T : SimpleGraph α} {G : SimpleGraph β}
    (f : (T.induce (↑W : Set α)ᶜ).Copy G) :
    (baseImages W f).card = Fintype.card α - W.card := by
  unfold baseImages
  change (Finset.univ.image (fun x => f x)).card = Fintype.card α - W.card
  have himage : (Finset.univ.image (fun x => f x)).card =
      (Finset.univ : Finset {x // x ∉ W}).card :=
    Finset.card_image_of_injective _ (fun _ _ h => f.injective h)
  rw [himage, Finset.card_univ]
  simpa only [Fintype.card_coe] using
    Fintype.card_subtype_compl (fun x : α => x ∈ W)

private theorem parentImage_mem_baseImages
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α] [DecidableEq β]
    (W : Finset α) {T : SimpleGraph α} {G : SimpleGraph β}
    (parent : (x : {x // x ∈ W}) → α)
    (hparent : ∀ x, parent x ∉ W)
    (f : (T.induce (↑W : Set α)ᶜ).Copy G)
    (x : {x // x ∈ W}) :
    f ⟨parent x, hparent x⟩ ∈ baseImages W f := by
  apply Finset.mem_image.mpr
  exact ⟨⟨parent x, hparent x⟩, Finset.mem_univ _, rfl⟩

private theorem card_leafChoices_ge
    {α : Type u} {β : Type v} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (W : Finset α) {T : SimpleGraph α} (G : SimpleGraph β)
    [DecidableRel G.Adj]
    (parent : (x : {x // x ∈ W}) → α)
    (hparent : ∀ x, parent x ∉ W)
    (f : (T.induce (↑W : Set α)ᶜ).Copy G)
    (hdegree : ∀ x, Fintype.card α - 1 ≤
      G.degree (f ⟨parent x, hparent x⟩))
    (x : {x // x ∈ W}) :
    W.card ≤ (leafChoices W G parent hparent f x).card := by
  let p : β := f ⟨parent x, hparent x⟩
  let N : Finset β := G.neighborFinset p
  let U : Finset β := baseImages W f
  have hpU : p ∈ U := parentImage_mem_baseImages W parent hparent f x
  have hpN : p ∉ N := by
    simp [N, p]
  have hproper : N ∩ U ⊂ U := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨Finset.inter_subset_right, ?_⟩
    intro heq
    have : p ∈ N ∩ U := by rw [heq]; exact hpU
    exact hpN (Finset.mem_inter.mp this).1
  have hinter : (N ∩ U).card + 1 ≤ U.card := by
    have := Finset.card_lt_card hproper
    omega
  have hN : Fintype.card α - 1 ≤ N.card := by
    simpa [N, p] using hdegree x
  have hU : U.card = Fintype.card α - W.card := card_baseImages W f
  have hcardW : W.card ≤ Fintype.card α := Finset.card_le_univ W
  rw [leafChoices, Finset.card_sdiff]
  change W.card ≤ N.card - (U ∩ N).card
  rw [Finset.inter_comm]
  omega

/-- Hall's theorem supplies distinct unused neighbors for all deleted leaves.
The degree threshold is exactly `|V(T)| - 1`; the parent's own occupied image
is not a neighbor, which is the one-unit saving in the count. -/
theorem exists_leafRepresentatives
    {α : Type u} {β : Type v} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (W : Finset α) {T : SimpleGraph α} (G : SimpleGraph β)
    [DecidableRel G.Adj]
    (parent : (x : {x // x ∈ W}) → α)
    (hparent : ∀ x, parent x ∉ W)
    (f : (T.induce (↑W : Set α)ᶜ).Copy G)
    (hdegree : ∀ x, Fintype.card α - 1 ≤
      G.degree (f ⟨parent x, hparent x⟩)) :
    ∃ g : {x // x ∈ W} → β, Function.Injective g ∧
      ∀ x, g x ∈ leafChoices W G parent hparent f x := by
  apply (Finset.all_card_le_biUnion_card_iff_exists_injective
    (leafChoices W G parent hparent f)).mp
  intro s
  by_cases hs : s = ∅
  · simp [hs]
  · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hs
    calc
      s.card ≤ Fintype.card {x // x ∈ W} := Finset.card_le_univ s
      _ = W.card := Fintype.card_coe W
      _ ≤ (leafChoices W G parent hparent f x).card :=
        card_leafChoices_ge W G parent hparent f hdegree x
      _ ≤ (s.biUnion (leafChoices W G parent hparent f)).card := by
        apply Finset.card_le_card
        exact Finset.subset_biUnion_of_mem (leafChoices W G parent hparent f) hx

/-- If a set of independent leaves has been deleted, a copy of the remaining
induced graph extends to a copy of the whole graph whenever every parent image
has degree at least `|V(T)| - 1`.  This formalizes the "add the leaves greedily"
sentence in the proof of Zhao's Claim 6.8. -/
theorem exists_copy_of_induce_compl_of_leaves
    {α : Type u} {β : Type v} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (T : SimpleGraph α) (G : SimpleGraph β) [DecidableRel G.Adj]
    (W : Finset α)
    (parent : (x : {x // x ∈ W}) → α)
    (hparent_not_mem : ∀ x, parent x ∉ W)
    (hparent_adj : ∀ x, T.Adj (parent x) x)
    (hleaf : ∀ x : {x // x ∈ W}, ∀ y, T.Adj x y → y = parent x)
    (f : (T.induce (↑W : Set α)ᶜ).Copy G)
    (hdegree : ∀ x, Fintype.card α - 1 ≤
      G.degree (f ⟨parent x, hparent_not_mem x⟩)) :
    ∃ F : T.Copy G,
      (∀ x : {x // x ∉ W}, F x = f x) ∧
      (∀ x : {x // x ∈ W}, G.Adj (f ⟨parent x, hparent_not_mem x⟩) (F x)) := by
  obtain ⟨g, hginj, hgchoice⟩ :=
    exists_leafRepresentatives W G parent hparent_not_mem f hdegree
  let F0 : α → β := fun x => if hx : x ∈ W then g ⟨x, hx⟩ else f ⟨x, hx⟩
  have hF0_inj : Function.Injective F0 := by
    intro x y hxy
    by_cases hx : x ∈ W
    · by_cases hy : y ∈ W
      · have : (⟨x, hx⟩ : {x // x ∈ W}) = ⟨y, hy⟩ := by
          apply hginj
          simpa [F0, hx, hy] using hxy
        exact congrArg Subtype.val this
      · exfalso
        have hchoice := hgchoice ⟨x, hx⟩
        have hnotbase : g ⟨x, hx⟩ ∉ baseImages W f := by
          exact Finset.mem_sdiff.mp hchoice |>.2
        apply hnotbase
        apply Finset.mem_image.mpr
        exact ⟨⟨y, hy⟩, Finset.mem_univ _, by simpa [F0, hx, hy] using hxy.symm⟩
    · by_cases hy : y ∈ W
      · exfalso
        have hchoice := hgchoice ⟨y, hy⟩
        have hnotbase : g ⟨y, hy⟩ ∉ baseImages W f := by
          exact Finset.mem_sdiff.mp hchoice |>.2
        apply hnotbase
        apply Finset.mem_image.mpr
        exact ⟨⟨x, hx⟩, Finset.mem_univ _, by simpa [F0, hx, hy] using hxy⟩
      · have : (⟨x, hx⟩ : {x // x ∉ W}) = ⟨y, hy⟩ := by
          apply f.injective
          simpa [F0, hx, hy] using hxy
        exact congrArg Subtype.val this
  have hF0_adj : ∀ ⦃x y⦄, T.Adj x y → G.Adj (F0 x) (F0 y) := by
    intro x y hxy
    by_cases hx : x ∈ W
    · have hyeq : y = parent ⟨x, hx⟩ := hleaf ⟨x, hx⟩ y hxy
      subst y
      have hyp : parent ⟨x, hx⟩ ∉ W := hparent_not_mem ⟨x, hx⟩
      have hchoice := Finset.mem_sdiff.mp (hgchoice ⟨x, hx⟩)
      have hadj : G.Adj (f ⟨parent ⟨x, hx⟩, hyp⟩) (g ⟨x, hx⟩) := by
        exact (G.mem_neighborFinset _ _).mp hchoice.1
      simpa [F0, hx, hyp] using hadj.symm
    · by_cases hy : y ∈ W
      · have hxeq : x = parent ⟨y, hy⟩ := hleaf ⟨y, hy⟩ x hxy.symm
        subst x
        have hxp : parent ⟨y, hy⟩ ∉ W := hparent_not_mem ⟨y, hy⟩
        have hchoice := Finset.mem_sdiff.mp (hgchoice ⟨y, hy⟩)
        have hadj : G.Adj (f ⟨parent ⟨y, hy⟩, hxp⟩) (g ⟨y, hy⟩) := by
          exact (G.mem_neighborFinset _ _).mp hchoice.1
        simpa [F0, hy, hxp] using hadj
      · have hinduced : (T.induce (↑W : Set α)ᶜ).Adj
            ⟨x, hx⟩ ⟨y, hy⟩ := by simpa using hxy
        simpa [F0, hx, hy] using f.toHom.map_rel hinduced
  let F : T.Copy G := ⟨⟨F0, fun {_ _} h => hF0_adj h⟩, hF0_inj⟩
  refine ⟨F, ?_, ?_⟩
  · intro x
    simp [F, F0, x.property]
  · intro x
    have hchoice := Finset.mem_sdiff.mp (hgchoice x)
    have hadj : G.Adj (f ⟨parent x, hparent_not_mem x⟩) (g x) :=
      (G.mem_neighborFinset _ _).mp hchoice.1
    simpa [F, F0, x.property] using hadj

/-- The exact finite certificate needed for the leaf-completion step in
Claim 6.8.  Zhao's Lemma 6.5, applied to the reduced-graph cluster matching,
constructs the `coreCopy`; membership in the large clusters supplies
`parentDegree`. -/
structure LeafCompletionCertificate
    {α : Type u} {β : Type v} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (T : SimpleGraph α) (G : SimpleGraph β) [DecidableRel G.Adj]
    (W : Finset α) where
  parent : (x : {x // x ∈ W}) → α
  parent_not_mem : ∀ x, parent x ∉ W
  parent_adj : ∀ x, T.Adj (parent x) x
  leaf_unique : ∀ x : {x // x ∈ W}, ∀ y, T.Adj x y → y = parent x
  coreCopy : (T.induce (↑W : Set α)ᶜ).Copy G
  parentDegree : ∀ x, Fintype.card α - 1 ≤
    G.degree (coreCopy ⟨parent x, parent_not_mem x⟩)

theorem LeafCompletionCertificate.exists_copy
    {α : Type u} {β : Type v} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    {T : SimpleGraph α} {G : SimpleGraph β} [DecidableRel G.Adj]
    {W : Finset α} (C : LeafCompletionCertificate T G W) :
    ∃ F : T.Copy G, True := by
  obtain ⟨F, -, -⟩ := exists_copy_of_induce_compl_of_leaves T G W
    C.parent C.parent_not_mem C.parent_adj C.leaf_unique C.coreCopy C.parentDegree
  exact ⟨F, trivial⟩

theorem LeafCompletionCertificate.isContained
    {α : Type u} {β : Type v} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    {T : SimpleGraph α} {G : SimpleGraph β} [DecidableRel G.Adj]
    {W : Finset α} (C : LeafCompletionCertificate T G W) :
    T.IsContained G := by
  obtain ⟨F, -⟩ := C.exists_copy
  exact F.isContained

/-! ## The level-one leaf classification from Zhao's cut forest -/

/-- The roots of a Zhao forest partition. -/
def partitionRoots {V : Type u} [Fintype V] [DecidableEq V]
    {T : SimpleGraph V} [DecidableRel T.Adj] {r : V} {m : ℕ}
    (P : ZhaoForestPartition T r m) : Finset V :=
  Finset.univ.image P.roots

/-- The parent vertices `p₂, ..., p_cf` of Zhao Definition 6.2. -/
def partitionParents {V : Type u} [Fintype V] [DecidableEq V]
    {T : SimpleGraph V} [DecidableRel T.Adj] {r : V} {m : ℕ}
    (P : ZhaoForestPartition T r m) : Finset V :=
  Finset.univ.image fun j : {j : Fin P.numParts // j.val ≠ 0} =>
    P.parent j.1 j.2

/-- Level one of the rooted cut forest: the cut-forest neighbors of its component roots. -/
def partitionLevelOne {V : Type u} [Fintype V] [DecidableEq V]
    {T : SimpleGraph V} [DecidableRel T.Adj] {r : V} {m : ℕ}
    (P : ZhaoForestPartition T r m) : Finset V :=
  Finset.univ.filter fun v => ∃ i, (T.deleteEdges
    (↑(zhaoCutEdges P.roots P.parent) : Set (Sym2 V))).Adj (P.roots i) v

/-- Leaves of a finite graph, in the convention used in Zhao's paper. -/
def graphLeaves {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter fun v => G.degree v = 1

/-- Zhao's `Leaf₁(F)`. -/
def partitionLevelOneLeaves {V : Type u} [Fintype V] [DecidableEq V]
    {T : SimpleGraph V} [DecidableRel T.Adj] {r : V} {m : ℕ}
    (P : ZhaoForestPartition T r m) : Finset V :=
  partitionLevelOne P ∩ graphLeaves
    (T.deleteEdges (↑(zhaoCutEdges P.roots P.parent) : Set (Sym2 V)))

theorem partitionRoots_card {V : Type u} [Fintype V] [DecidableEq V]
    {T : SimpleGraph V} [DecidableRel T.Adj] {r : V} {m : ℕ}
    (P : ZhaoForestPartition T r m) :
    (partitionRoots P).card = P.numParts := by
  have hinj : Function.Injective P.roots := by
    intro i j hij
    apply P.components.injective
    apply SimpleGraph.ConnectedComponent.eq_of_common_vertex (v := P.roots i)
    · exact P.root_mem i
    · simpa only [hij] using P.root_mem j
  simpa [partitionRoots] using
    Finset.card_image_of_injective (Finset.univ : Finset (Fin P.numParts)) hinj

theorem partitionRoots_disjoint_levelOne
    {V : Type u} [Fintype V] [DecidableEq V]
    {T : SimpleGraph V} [DecidableRel T.Adj] {r : V} {m : ℕ}
    (P : ZhaoForestPartition T r m) :
    Disjoint (partitionRoots P) (partitionLevelOne P) := by
  rw [Finset.disjoint_left]
  intro x hxroot hxlevel
  obtain ⟨i, -, hix⟩ := Finset.mem_image.mp hxroot
  subst x
  obtain ⟨j, hjadj⟩ := (Finset.mem_filter.mp hxlevel).2
  let F := T.deleteEdges (↑(zhaoCutEdges P.roots P.parent) : Set (Sym2 V))
  have hrootj_in_i : P.roots j ∈ (P.components i).supp := by
    have hi : P.roots i ∈ (P.components i).supp := P.root_mem i
    exact (SimpleGraph.ConnectedComponent.mem_supp_congr_adj
      (P.components i) hjadj).mpr hi
  have hcomp : P.components j = P.components i :=
    SimpleGraph.ConnectedComponent.eq_of_common_vertex (P.root_mem j) hrootj_in_i
  have hji : j = i := P.components.injective hcomp
  subst j
  exact (F.loopless.irrefl _ hjadj)

private theorem levelOneLeaf_not_originalLeaf_mem_partitionParents
    {V : Type u} [Fintype V] [DecidableEq V]
    {T : SimpleGraph V} [DecidableRel T.Adj] {r : V} {m : ℕ}
    (P : ZhaoForestPartition T r m) {x : V}
    (hx : x ∈ partitionLevelOneLeaves P) (hxnot : x ∉ graphLeaves T) :
    x ∈ partitionParents P := by
  let cuts : Finset (Sym2 V) := zhaoCutEdges P.roots P.parent
  let F : SimpleGraph V := T.deleteEdges (↑cuts : Set (Sym2 V))
  have hxlevel : x ∈ partitionLevelOne P := Finset.mem_inter.mp hx |>.1
  have hxFleaf : F.degree x = 1 := by
    exact (Finset.mem_filter.mp (Finset.mem_inter.mp hx).2).2
  have hxTnot : T.degree x ≠ 1 := by
    simpa [graphLeaves] using hxnot
  have hle : F.degree x ≤ T.degree x :=
    SimpleGraph.degree_le_of_le (G := F) (H := T) (v := x) (by
      intro a b hab
      exact (SimpleGraph.deleteEdges_adj.mp hab).1)
  have hlt : F.degree x < T.degree x := by omega
  have hproper : F.neighborFinset x ⊂ T.neighborFinset x := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨?_, ?_⟩
    · intro y hy
      have := (F.mem_neighborFinset x y).mp hy
      exact (T.mem_neighborFinset x y).mpr (SimpleGraph.deleteEdges_adj.mp this).1
    · intro heq
      have := congrArg Finset.card heq
      exact (Nat.ne_of_lt hlt) this
  obtain ⟨y, hyT, hyF⟩ := Finset.exists_of_ssubset hproper
  have hTadj : T.Adj x y := (T.mem_neighborFinset x y).mp hyT
  have hnotFadj : ¬F.Adj x y := by simpa using hyF
  have hcut : s(x, y) ∈ cuts := by
    by_contra hnotcut
    exact hnotFadj (SimpleGraph.deleteEdges_adj.mpr ⟨hTadj, hnotcut⟩)
  obtain ⟨j, -, hedge⟩ := Finset.mem_image.mp hcut
  rcases Sym2.eq_iff.mp hedge with hxy | hxy
  · have hxroot : x ∈ partitionRoots P := by
      apply Finset.mem_image.mpr
      exact ⟨j.1, Finset.mem_univ _, hxy.1⟩
    exact False.elim (Finset.disjoint_left.mp (partitionRoots_disjoint_levelOne P)
      hxroot hxlevel)
  · apply Finset.mem_image.mpr
    exact ⟨j, Finset.mem_univ _, hxy.2⟩

/-- The exact combinatorial sentence in the first paragraph of Claim 6.8:
every level-one leaf of the cut forest is either a leaf of the original tree
or one of the recorded parent vertices. -/
theorem partitionLevelOneLeaves_subset_originalLeaves_union_parents
    {V : Type u} [Fintype V] [DecidableEq V]
    {T : SimpleGraph V} [DecidableRel T.Adj] {r : V} {m : ℕ}
    (P : ZhaoForestPartition T r m) :
    partitionLevelOneLeaves P ⊆ graphLeaves T ∪ partitionParents P := by
  intro x hx
  by_cases hleaf : x ∈ graphLeaves T
  · exact Finset.mem_union_left _ hleaf
  · exact Finset.mem_union_right _
      (levelOneLeaf_not_originalLeaf_mem_partitionParents P hx hleaf)

theorem card_partitionParents_le_numParts
    {V : Type u} [Fintype V] [DecidableEq V]
    {T : SimpleGraph V} [DecidableRel T.Adj] {r : V} {m : ℕ}
    (P : ZhaoForestPartition T r m) :
    (partitionParents P).card ≤ P.numParts := by
  rw [partitionParents]
  calc
    (Finset.univ.image fun j : {j : Fin P.numParts // j.val ≠ 0} =>
        P.parent j.1 j.2).card ≤
        (Finset.univ : Finset {j : Fin P.numParts // j.val ≠ 0}).card :=
      Finset.card_image_le
    _ = Fintype.card {j : Fin P.numParts // j.val ≠ 0} := Finset.card_univ
    _ ≤ Fintype.card (Fin P.numParts) :=
      Fintype.card_subtype_le (p := fun j : Fin P.numParts => j.val ≠ 0)
    _ = P.numParts := Fintype.card_fin _

/-- Consequently the non-original part `W₁'` of `Leaf₁(F)` has at most
`c_f` vertices. -/
theorem card_levelOneLeaves_sdiff_originalLeaves_le_numParts
    {V : Type u} [Fintype V] [DecidableEq V]
    {T : SimpleGraph V} [DecidableRel T.Adj] {r : V} {m : ℕ}
    (P : ZhaoForestPartition T r m) :
    (partitionLevelOneLeaves P \ graphLeaves T).card ≤ P.numParts := by
  apply (Finset.card_le_card ?_).trans (card_partitionParents_le_numParts P)
  intro x hx
  have hleaf1 := (Finset.mem_sdiff.mp hx).1
  have hnotleaf := (Finset.mem_sdiff.mp hx).2
  have hu := partitionLevelOneLeaves_subset_originalLeaves_union_parents P hleaf1
  exact (Finset.mem_union.mp hu).resolve_left hnotleaf

/-! ## The numerical conclusion of Claim 6.8 -/

/-- Non-root vertices of the cut forest; its cardinality is Zhao's `||F||`. -/
def partitionNonroots {V : Type u} [Fintype V] [DecidableEq V]
    {T : SimpleGraph V} [DecidableRel T.Adj] {r : V} {m : ℕ}
    (P : ZhaoForestPartition T r m) : Finset V :=
  Finset.univ \ partitionRoots P

theorem card_partitionNonroots_add_numParts
    {V : Type u} [Fintype V] [DecidableEq V]
    {T : SimpleGraph V} [DecidableRel T.Adj] {r : V} {m : ℕ}
    (P : ZhaoForestPartition T r m) :
    (partitionNonroots P).card + P.numParts = Fintype.card V := by
  rw [partitionNonroots, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    partitionRoots_card P]
  exact Nat.sub_add_cancel (by
    rw [← partitionRoots_card P]
    exact Finset.card_le_univ _)

theorem partitionLevelOneLeaves_subset_nonroots
    {V : Type u} [Fintype V] [DecidableEq V]
    {T : SimpleGraph V} [DecidableRel T.Adj] {r : V} {m : ℕ}
    (P : ZhaoForestPartition T r m) :
    partitionLevelOneLeaves P ⊆ partitionNonroots P := by
  intro x hx
  rw [partitionNonroots, Finset.mem_sdiff]
  refine ⟨Finset.mem_univ _, ?_⟩
  intro hxroot
  exact Finset.disjoint_left.mp (partitionRoots_disjoint_levelOne P)
    hxroot (Finset.mem_inter.mp hx).1

/-- Interface between Claim 6.7/Lemma 6.5 and Claim 6.8.  It records the
adjacent large clusters and the cluster matching in the reduced graph, and
the precise consequence of Lemma 6.5 needed here: whenever the set `W₁` of
original level-one leaves reaches Zhao's cutoff, the leaf-deleted tree has an
embedding whose parent images all have the large-vertex degree needed for
leaf completion. -/
structure ReducedMatchingLeafEmbeddingContext
    {V : Type u} {H ι : Type v}
    [Fintype V] [Fintype H] [Fintype ι]
    [DecidableEq V] [DecidableEq H] [DecidableEq ι]
    {T : SimpleGraph V} [DecidableRel T.Adj]
    (G : SimpleGraph H) [DecidableRel G.Adj]
    {r : V} {m n : ℕ} (P : ZhaoForestPartition T r m)
    (d : ℝ) (R : SimpleGraph ι) (M : R.Subgraph) (A B : ι) : Prop where
  matching : M.IsMatching
  adjacentLargeClusters : R.Adj A B
  largeLeavesGiveCore :
    11 * Real.sqrt d * n ≤
        ((partitionLevelOneLeaves P ∩ graphLeaves T).card : ℝ) →
      Nonempty (LeafCompletionCertificate T G
        (partitionLevelOneLeaves P ∩ graphLeaves T))

/-- This is the contradiction at the start of Zhao's proof of Claim 6.8:
if `T` is not contained in the host, the original leaves in level one are
strictly below the cutoff `11 sqrt(d) n`.  The leaf-completion theorem above
discharges the paper's phrase "the vertices in `W₁` can be added greedily". -/
theorem originalLevelOneLeaves_lt_of_reducedMatching
    {V : Type u} {H ι : Type v}
    [Fintype V] [Fintype H] [Fintype ι]
    [DecidableEq V] [DecidableEq H] [DecidableEq ι]
    {T : SimpleGraph V} [DecidableRel T.Adj]
    (G : SimpleGraph H) [DecidableRel G.Adj]
    {r : V} {m n : ℕ} (P : ZhaoForestPartition T r m)
    (d : ℝ) (R : SimpleGraph ι) (M : R.Subgraph) (A B : ι)
    (C : ReducedMatchingLeafEmbeddingContext (n := n) G P d R M A B)
    (hnot : ¬T.IsContained G) :
    ((partitionLevelOneLeaves P ∩ graphLeaves T).card : ℝ) <
      11 * Real.sqrt d * n := by
  by_contra h
  have hlarge : 11 * Real.sqrt d * n ≤
      ((partitionLevelOneLeaves P ∩ graphLeaves T).card : ℝ) := le_of_not_gt h
  obtain ⟨E⟩ := C.largeLeavesGiveCore hlarge
  exact hnot E.isContained

/-- Claim 6.8 with every use of the asymptotic hierarchy exposed as an
explicit real inequality.  Here `partA` and `partB` are the two classes
`F_a - Rt(F_a)` and `F_b - Rt(F_b)`, and `sqrt d * n` is Zhao's error scale.
The preceding lemma supplies the `c_f` term in the level-one-leaf bound. -/
theorem claim6_8
    {V : Type u} [Fintype V] [DecidableEq V]
    {T : SimpleGraph V} [DecidableRel T.Adj] {r : V} {m n : ℕ}
    (P : ZhaoForestPartition T r m)
    (d : ℝ) (hd : 0 ≤ d)
    (hcardT : Fintype.card V = n + 1)
    (partA partB : Finset V)
    (hparts_disjoint : Disjoint partA partB)
    (hparts_union : partA ∪ partB = partitionNonroots P)
    (hmajority : partB.card ≤ partA.card)
    (horiginalLeaves :
      (((partitionLevelOneLeaves P ∩ graphLeaves T).card : ℕ) : ℝ) <
        11 * Real.sqrt d * n)
    (hhierarchyF : 2 * (P.numParts : ℝ) < 1 + Real.sqrt d * n)
    (hhierarchyA : 3 * (P.numParts : ℝ) < 1 + 2 * Real.sqrt d * n) :
    (1 - 12 * Real.sqrt d) * n ≤
        ((partitionNonroots P \ partitionLevelOneLeaves P).card : ℝ) ∧
      (n : ℝ) / 2 - 12 * Real.sqrt d * n <
        ((partA \ partitionLevelOneLeaves P).card : ℝ) := by
  let L1 := partitionLevelOneLeaves P
  let W1 := L1 ∩ graphLeaves T
  let W1' := L1 \ graphLeaves T
  have hW1' : (W1'.card : ℝ) ≤ P.numParts := by
    exact_mod_cast card_levelOneLeaves_sdiff_originalLeaves_le_numParts P
  have hL1decomp : W1 ∪ W1' = L1 := by
    ext x
    simp only [W1, W1', Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    by_cases hxL : x ∈ L1 <;> by_cases hxLeaf : x ∈ graphLeaves T <;> simp_all
  have hL1disj : Disjoint W1 W1' := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact (Finset.mem_sdiff.mp hx').2 (Finset.mem_inter.mp hx).2
  have hL1card : (L1.card : ℝ) = (W1.card : ℝ) + (W1'.card : ℝ) := by
    rw [← hL1decomp, Finset.card_union_of_disjoint hL1disj]
    norm_cast
  have hL1bound : (L1.card : ℝ) < 11 * Real.sqrt d * n + P.numParts := by
    change (L1.card : ℝ) < 11 * Real.sqrt d * n + P.numParts
    rw [hL1card]
    change (W1.card : ℝ) + (W1'.card : ℝ) < _
    change (W1.card : ℝ) < 11 * Real.sqrt d * n at horiginalLeaves
    linarith
  have hnonroots : (partitionNonroots P).card + P.numParts = n + 1 := by
    rw [card_partitionNonroots_add_numParts P, hcardT]
  have hnonrootsR : ((partitionNonroots P).card : ℝ) + P.numParts = n + 1 := by
    exact_mod_cast hnonroots
  have hL1sub : L1 ⊆ partitionNonroots P := partitionLevelOneLeaves_subset_nonroots P
  have htildeF :
      (((partitionNonroots P \ L1).card : ℕ) : ℝ) =
        (partitionNonroots P).card - L1.card := by
    exact Finset.cast_card_sdiff hL1sub
  have hpartsum : partA.card + partB.card = (partitionNonroots P).card := by
    rw [← hparts_union, Finset.card_union_of_disjoint hparts_disjoint]
  have hpartsumR : (partA.card : ℝ) + partB.card = (partitionNonroots P).card := by
    exact_mod_cast hpartsum
  have hmajorityR : (partB.card : ℝ) ≤ partA.card := by exact_mod_cast hmajority
  have hAhalf : ((partitionNonroots P).card : ℝ) / 2 ≤ partA.card := by
    linarith
  have hinter : (L1 ∩ partA).card ≤ L1.card :=
    Finset.card_le_card Finset.inter_subset_left
  have hinterR : ((L1 ∩ partA).card : ℝ) ≤ L1.card := by exact_mod_cast hinter
  have htildeA : (((partA \ L1).card : ℕ) : ℝ) =
      (partA.card : ℝ) - (L1 ∩ partA).card := by
    have heq : partA \ L1 = partA \ (L1 ∩ partA) := by
      ext x
      simp
    rw [heq]
    exact Finset.cast_card_sdiff Finset.inter_subset_right
  constructor
  · rw [htildeF]
    change (1 - 12 * Real.sqrt d) * (n : ℝ) ≤
      (partitionNonroots P).card - L1.card
    linarith only [hnonrootsR, hL1bound, hhierarchyF]
  · rw [htildeA]
    change (n : ℝ) / 2 - 12 * Real.sqrt d * n <
      (partA.card : ℝ) - (L1 ∩ partA).card
    linarith only [hnonrootsR, hL1bound, hAhalf, hinterR, hhierarchyA]

/-- The source-faithful form of Claim 6.8: the reduced-graph matching
context produces the original-leaf bound, the cut-forest classification
adds at most `c_f` new leaves, and the two explicit hierarchy inequalities
give Zhao's two displayed estimates. -/
theorem claim6_8_of_reducedMatching
    {V : Type u} {H ι : Type v}
    [Fintype V] [Fintype H] [Fintype ι]
    [DecidableEq V] [DecidableEq H] [DecidableEq ι]
    {T : SimpleGraph V} [DecidableRel T.Adj]
    (G : SimpleGraph H) [DecidableRel G.Adj]
    {r : V} {m n : ℕ} (P : ZhaoForestPartition T r m)
    (d : ℝ) (hd : 0 ≤ d)
    (R : SimpleGraph ι) (M : R.Subgraph) (A B : ι)
    (C : ReducedMatchingLeafEmbeddingContext (n := n) G P d R M A B)
    (hnot : ¬T.IsContained G)
    (hcardT : Fintype.card V = n + 1)
    (partA partB : Finset V)
    (hparts_disjoint : Disjoint partA partB)
    (hparts_union : partA ∪ partB = partitionNonroots P)
    (hmajority : partB.card ≤ partA.card)
    (hhierarchyF : 2 * (P.numParts : ℝ) < 1 + Real.sqrt d * n)
    (hhierarchyA : 3 * (P.numParts : ℝ) < 1 + 2 * Real.sqrt d * n) :
    (1 - 12 * Real.sqrt d) * n ≤
        ((partitionNonroots P \ partitionLevelOneLeaves P).card : ℝ) ∧
      (n : ℝ) / 2 - 12 * Real.sqrt d * n <
        ((partA \ partitionLevelOneLeaves P).card : ℝ) := by
  apply claim6_8 P d hd hcardT partA partB hparts_disjoint hparts_union
    hmajority
  · exact originalLevelOneLeaves_lt_of_reducedMatching
      G P d R M A B C hnot
  · exact hhierarchyF
  · exact hhierarchyA

end Erdos547b.ZhaoClaim68

#print axioms Erdos547b.ZhaoClaim68.exists_copy_of_induce_compl_of_leaves
#print axioms Erdos547b.ZhaoClaim68.partitionLevelOneLeaves_subset_originalLeaves_union_parents
#print axioms Erdos547b.ZhaoClaim68.claim6_8
#print axioms Erdos547b.ZhaoClaim68.claim6_8_of_reducedMatching
