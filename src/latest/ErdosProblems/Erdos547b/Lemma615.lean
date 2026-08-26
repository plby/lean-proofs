/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma612
import ErdosProblems.Erdos547b.Lemma613
import ErdosProblems.Erdos547b.RegularPair
import ErdosProblems.Erdos547b.ForestMatching
import ErdosProblems.Erdos547b.ForestCapacity

/-!
# Zhao's Lemma 6.15, with a concrete tree-copy conclusion

The two exceptional submatchings below are exactly the ones on page 32 of
Zhao (2011).  The graph-valued theorem does not take a proposition-valued
"continuation" hypothesis: its local hypotheses are literal neighbour
counts in the two sides of each eligible matching edge, and the conclusion
is an actual `SimpleGraph.Copy`.

The file also contains the small-`f_b` reservation step from Lemma 6.12 and
the two contrapositives used in Claim 6.18 (pages 37--38).
-/

open scoped BigOperators SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoLemma615

open Finset SimpleGraph
open Erdos547b.ForestMatching

universe u v w

section ExceptionalSubmatchings

variable {E : Type u} [DecidableEq E]

/-- Zhao's `M_unbal`: matching edges on whose two ends the densities from
the distinguished cluster differ by at least `eta`. -/
def unbalancedEdges (M : Finset E) (density : E → Fin 2 → ℝ)
    (eta : ℝ) : Finset E :=
  M.filter fun e ↦ eta ≤ |density e 0 - density e 1|

/-- Zhao's `M_nonex`: both endpoint densities lie in `[eta,1-eta]`. -/
def nonextremeEdges (M : Finset E) (density : E → Fin 2 → ℝ)
    (eta : ℝ) : Finset E :=
  M.filter fun e ↦
    eta ≤ density e 0 ∧ density e 0 ≤ 1 - eta ∧
    eta ≤ density e 1 ∧ density e 1 ≤ 1 - eta

/-- The one-sided family used in the last paragraph of Claim 6.18. -/
def positiveZeroEdges (M : Finset E) (density : E → Fin 2 → ℝ)
    (eta : ℝ) : Finset E :=
  M.filter fun e ↦ eta ≤ density e 0 ∧ density e 1 = 0

@[simp] theorem mem_unbalancedEdges {M : Finset E}
    {density : E → Fin 2 → ℝ} {eta : ℝ} {e : E} :
    e ∈ unbalancedEdges M density eta ↔
      e ∈ M ∧ eta ≤ |density e 0 - density e 1| := by
  simp [unbalancedEdges]

@[simp] theorem mem_nonextremeEdges {M : Finset E}
    {density : E → Fin 2 → ℝ} {eta : ℝ} {e : E} :
    e ∈ nonextremeEdges M density eta ↔
      e ∈ M ∧ eta ≤ density e 0 ∧ density e 0 ≤ 1 - eta ∧
        eta ≤ density e 1 ∧ density e 1 ≤ 1 - eta := by
  simp [nonextremeEdges]

@[simp] theorem mem_positiveZeroEdges {M : Finset E}
    {density : E → Fin 2 → ℝ} {eta : ℝ} {e : E} :
    e ∈ positiveZeroEdges M density eta ↔
      e ∈ M ∧ eta ≤ density e 0 ∧ density e 1 = 0 := by
  simp [positiveZeroEdges]

theorem unbalancedEdges_subset (M : Finset E) (density : E → Fin 2 → ℝ)
    (eta : ℝ) : unbalancedEdges M density eta ⊆ M := by
  exact filter_subset _ _

theorem nonextremeEdges_subset (M : Finset E) (density : E → Fin 2 → ℝ)
    (eta : ℝ) : nonextremeEdges M density eta ⊆ M := by
  exact filter_subset _ _

/-- A pair with one density at least `eta` and the other equal to zero is
unbalanced.  This is the exact inclusion used in Claim 6.18. -/
theorem positiveZeroEdges_subset_unbalancedEdges
    (M : Finset E) (density : E → Fin 2 → ℝ) (eta : ℝ) (heta : 0 ≤ eta) :
    positiveZeroEdges M density eta ⊆ unbalancedEdges M density eta := by
  intro e he
  rw [mem_positiveZeroEdges] at he
  rw [mem_unbalancedEdges]
  refine ⟨he.1, ?_⟩
  rw [he.2.2, sub_zero, abs_of_nonneg]
  · exact he.2.1
  · exact heta.trans he.2.1

end ExceptionalSubmatchings

section ConcreteEmbedding

variable {E : Type u} [DecidableEq E]
variable {TreeVertex : Type v} [Fintype TreeVertex] [DecidableEq TreeVertex]
variable {HostVertex : Type w} [Fintype HostVertex] [DecidableEq HostVertex]

/-- Concrete local conclusion supplied by the regular-pair calculation on
one matching edge.  These are neighbour counts, not an assumed copy. -/
def LocallyHostsTree (T : SimpleGraph TreeVertex) (G : SimpleGraph HostVertex)
    [DecidableRel G.Adj] (CM : ClusterMatching E HostVertex)
    (rootImage : E → HostVertex) (e : E) : Prop :=
  Fintype.card TreeVertex ≤
      #{z ∈ CM.side e 1 | G.Adj (rootImage e) z} ∧
    ∀ c d : Fin 2, c ≠ d → ∀ z ∈ CM.side e c,
      Fintype.card TreeVertex ≤ #{y ∈ CM.side e d | G.Adj z y}

/-- One eligible edge of the cluster matching yields a genuine tree copy.
The proof deliberately goes through the shared forest-matching theorem;
for the singleton forest, its component copy is the requested copy of `T`. -/
theorem exists_tree_copy_of_eligible_edge
    (T : SimpleGraph TreeVertex) (hT : T.IsTree) (root : TreeVertex)
    (G : SimpleGraph HostVertex) [DecidableRel G.Adj]
    (CM : ClusterMatching E HostVertex) (eligible : Finset E)
    (rootImage : E → HostVertex)
    (hlocal : ∀ e ∈ eligible, LocallyHostsTree T G CM rootImage e)
    (hrootOutside : ∀ e ∈ eligible, ∀ p : E, ∀ c : Fin 2,
      rootImage e ∉ CM.side p c)
    {e : E} (he : e ∈ eligible) : Nonempty (T.Copy G) := by
  classical
  let items : Finset Unit := {()}
  let A : Unit → Type v := fun _ ↦ TreeVertex
  let trees : ∀ i : Unit, SimpleGraph (A i) := fun _ ↦ T
  let roots : ∀ i : Unit, A i := fun _ ↦ root
  let assign : Unit → E := fun _ ↦ e
  let rootImages : Unit → HostVertex := fun _ ↦ rootImage e
  have hcopy : Nonempty (OrderedForestCopy items A trees G) := by
    apply exists_orderedForestCopy_of_clusterMatching items A trees
      (fun _ ↦ hT) roots G CM assign
    · intro i hi j hj hij
      exact Subsingleton.elim i j
    · intro i hi
      simpa [items, A, trees, roots, assign, rootImages, LocallyHostsTree]
        using (hlocal e he).1
    · intro i hi c d hcd z hz
      simpa [items, A, trees, roots, assign, rootImages, LocallyHostsTree]
        using (hlocal e he).2 c d hcd z hz
    · intro i hi j hj hij
      exact Subsingleton.elim i j
    · intro i hi p c
      simpa [rootImages] using hrootOutside e he p c
  exact ⟨hcopy.some.componentCopy () (by simp [items])⟩

/-- Copy-valued form of Zhao's Lemma 6.15.  The threshold `q` is `eta*k`
in the paper.  The two alternatives are literally `|M_unbal| ≥ q` and
`|M_nonex| ≥ q`.

All embedding input is pointwise graph data in `LocallyHostsTree`; in
particular there is no hypothesis of the form "if the continuation
conditions hold, then `T` embeds". -/
theorem zhaoLemma615_concrete
    (T : SimpleGraph TreeVertex) (hT : T.IsTree) (root : TreeVertex)
    (G : SimpleGraph HostVertex) [DecidableRel G.Adj]
    (CM : ClusterMatching E HostVertex) (M : Finset E)
    (density : E → Fin 2 → ℝ) (eta q : ℝ)
    (rootImage : E → HostVertex)
    (hq : 0 < q)
    (hlarge : q ≤ ((unbalancedEdges M density eta).card : ℝ) ∨
      q ≤ ((nonextremeEdges M density eta).card : ℝ))
    (hlocal : ∀ e ∈ unbalancedEdges M density eta ∪
        nonextremeEdges M density eta,
      LocallyHostsTree T G CM rootImage e)
    (hrootOutside : ∀ e ∈ unbalancedEdges M density eta ∪
        nonextremeEdges M density eta,
      ∀ p : E, ∀ c : Fin 2, rootImage e ∉ CM.side p c) :
    Nonempty (T.Copy G) := by
  classical
  let eligible := unbalancedEdges M density eta ∪
    nonextremeEdges M density eta
  have heligPos : 0 < (eligible.card : ℝ) := by
    rcases hlarge with h | h
    · exact hq.trans_le (h.trans (by
        exact_mod_cast Finset.card_le_card (Finset.subset_union_left)))
    · exact hq.trans_le (h.trans (by
        exact_mod_cast Finset.card_le_card (Finset.subset_union_right)))
  have heligNonempty : eligible.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    rw [hempty] at heligPos
    norm_num at heligPos
  obtain ⟨e, he⟩ := heligNonempty
  exact exists_tree_copy_of_eligible_edge T hT root G CM eligible rootImage
    (by simpa [eligible] using hlocal)
    (by simpa [eligible] using hrootOutside) he

end ConcreteEmbedding

section FullCutForestEmbedding

open Erdos547b.TreePartition

variable {E : Type u} [DecidableEq E]
variable {TreeVertex : Type v} [Fintype TreeVertex] [DecidableEq TreeVertex]
variable {HostVertex : Type w} [Fintype HostVertex] [DecidableEq HostVertex]

/-- Restore the deleted root--parent edges after the literal Zhao cut forest
has been embedded. -/
def copyTree_of_cutForestCopy
    {T : SimpleGraph TreeVertex} [DecidableRel T.Adj]
    {globalRoot : TreeVertex} {small : ℕ}
    (P : ZhaoForestPartition T globalRoot small)
    {G : SimpleGraph HostVertex}
    (f : P.cutForest.Copy G)
    (hcut : ∀ j (hj : j.val ≠ 0),
      G.Adj (f (P.roots j)) (f (P.parent j hj))) : T.Copy G where
  toHom :=
    { toFun := f
      map_rel' := by
        intro x y hxy
        by_cases hdeleted : s(x, y) ∈ zhaoCutEdges P.roots P.parent
        · rw [zhaoCutEdges, Finset.mem_image] at hdeleted
          obtain ⟨j, _hjmem, hjxy⟩ := hdeleted
          rcases Sym2.eq_iff.mp hjxy with h | h
          · obtain ⟨rfl, rfl⟩ := h
            exact hcut j.1 j.2
          · obtain ⟨rfl, rfl⟩ := h
            exact (hcut j.1 j.2).symm
        · apply f.toHom.map_rel
          exact SimpleGraph.deleteEdges_adj.mpr ⟨hxy, hdeleted⟩ }
  injective' := f.injective

private theorem fromOrderedForestVertex_injective
    {T : SimpleGraph TreeVertex} [DecidableRel T.Adj]
    {globalRoot : TreeVertex} {small : ℕ}
    (P : ZhaoForestPartition T globalRoot small) :
    Function.Injective P.fromOrderedForestVertex := by
  rintro ⟨i, a⟩ ⟨j, b⟩ hab
  change (P.componentEquiv i a).1 = (P.componentEquiv j b).1 at hab
  have hcomp : P.components i = P.components j := by
    apply ConnectedComponent.eq_of_common_vertex
      (P.componentEquiv i a).property
    rw [hab]
    exact (P.componentEquiv j b).property
  have hij : i = j := P.components.injective hcomp
  subst j
  have hab' : P.componentEquiv i a = P.componentEquiv i b := by
    apply Subtype.ext
    exact hab
  have : a = b := (P.componentEquiv i).injective hab'
  subst b
  rfl

private theorem cutForestCopy_apply
    {T : SimpleGraph TreeVertex} [DecidableRel T.Adj]
    {globalRoot : TreeVertex} {small : ℕ}
    (P : ZhaoForestPartition T globalRoot small) (x : TreeVertex) :
    P.cutForestCopy x = P.toOrderedForestVertex x := by
  apply fromOrderedForestVertex_injective P
  change P.fromOrderedForestVertex (P.cutForestHom x) =
    P.fromOrderedForestVertex (P.toOrderedForestVertex x)
  rw [P.from_cutForestHom, P.from_toOrderedForestVertex]

private theorem toOrderedForestVertex_root
    {T : SimpleGraph TreeVertex} [DecidableRel T.Adj]
    {globalRoot : TreeVertex} {small : ℕ}
    (P : ZhaoForestPartition T globalRoot small) (i : Fin P.numParts) :
    P.toOrderedForestVertex (P.roots i) = ⟨i, P.orderedForest.root i⟩ := by
  apply fromOrderedForestVertex_injective P
  rw [P.from_toOrderedForestVertex]
  change P.roots i =
    (P.componentEquiv i
      ((P.componentEquiv i).symm ⟨P.roots i, P.root_mem i⟩)).1
  rw [Equiv.apply_symm_apply]

/-- The no-oracle Lemma 6.14 endpoint used below. -/
private theorem fullTreeContained_of_uniformPairs
    {T : SimpleGraph TreeVertex} [DecidableRel T.Adj]
    {globalRoot : TreeVertex} {small : ℕ}
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph HostVertex) [DecidableRel G.Adj]
    (rootImage : Fin P.numParts → HostVertex) {rho : ℝ}
    (X Y : Fin P.numParts → Finset HostVertex)
    (hrootInjective : Function.Injective rootImage)
    (hunif : ∀ i, G.IsUniform rho (X i) (Y i)) (hrho : rho ≤ 1)
    (hcapX : ∀ i, (P.orderedForest.size i : ℝ) + rho * #(X i) ≤
      (G.edgeDensity (X i) (Y i) - rho) * #(X i))
    (hcapY : ∀ i, (P.orderedForest.size i : ℝ) + rho * #(Y i) ≤
      (G.edgeDensity (X i) (Y i) - rho) * #(Y i))
    (hrootDegree : ∀ i, (P.orderedForest.size i : ℝ) + rho * #(Y i) ≤
      (#((Y i).filter (G.Adj (rootImage i))) : ℝ))
    (hrootOutside : ∀ i k,
      rootImage i ∉ Erdos547b.RegularPair.cleanedSide G rho (X k) (Y k) ∧
      rootImage i ∉ Erdos547b.RegularPair.cleanedSide G rho (Y k) (X k))
    (hdisjoint : ∀ i k, i ≠ k →
      Disjoint
        (Erdos547b.RegularPair.cleanedSide G rho (X i) (Y i) ∪
          Erdos547b.RegularPair.cleanedSide G rho (Y i) (X i))
        (Erdos547b.RegularPair.cleanedSide G rho (X k) (Y k) ∪
          Erdos547b.RegularPair.cleanedSide G rho (Y k) (X k)))
    (hrootParentAdj : ∀ j (hj : j.val ≠ 0),
      let p := P.toOrderedForestVertex (P.parent j hj)
      p.2 = P.orderedForest.root p.1 →
        G.Adj (rootImage p.1) (rootImage j))
    (hsideParentAdj : ∀ j (hj : j.val ≠ 0),
      let p := P.toOrderedForestVertex (P.parent j hj)
      p.2 ≠ P.orderedForest.root p.1 →
      ∀ z, z ∈
          (if (P.orderedForest.isTree p.1).coloringTwoOfVert
                (P.orderedForest.root p.1) p.2 = 0 then
            Erdos547b.RegularPair.cleanedSide G rho (X p.1) (Y p.1)
          else
            Erdos547b.RegularPair.cleanedSide G rho (Y p.1) (X p.1)) →
        G.Adj z (rootImage j)) :
    T.IsContained G := by
  obtain ⟨Emb, hEroot, hEmem⟩ :=
    P.orderedForest.exists_embedding_over_disjoint_uniform_pairs
      G rootImage X Y hrootInjective hunif hrho hcapX hcapY hrootDegree
        hrootOutside hdisjoint
  let f : P.cutForest.Copy G := Emb.toGraphCopy.comp P.cutForestCopy
  have hf_apply (x : TreeVertex) :
      f x = Emb.copy (P.toOrderedForestVertex x).1
        (P.toOrderedForestVertex x).2 := by
    change Emb.toGraphCopy (P.cutForestCopy x) = _
    rw [cutForestCopy_apply]
    rfl
  have hf_root (i : Fin P.numParts) : f (P.roots i) = rootImage i := by
    rw [hf_apply, toOrderedForestVertex_root]
    exact hEroot i
  refine (copyTree_of_cutForestCopy P f ?_).isContained
  intro j hj
  rw [hf_root, hf_apply]
  let p := P.toOrderedForestVertex (P.parent j hj)
  by_cases hp : p.2 = P.orderedForest.root p.1
  · rw [hp, hEroot]
    exact (hrootParentAdj j hj) hp |>.symm
  · have hm := hEmem p.1 p.2 hp
    exact (hsideParentAdj j hj) hp _ hm |>.symm

/-- Concrete data produced by the Lemma-5.8 allocation in Zhao's proof.
There is deliberately no copy or containment field in this structure. -/
structure UniformCutForestData
    {T : SimpleGraph TreeVertex} [DecidableRel T.Adj]
    {globalRoot : TreeVertex} {small : ℕ}
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph HostVertex) [DecidableRel G.Adj] where
  rootImage : Fin P.numParts → HostVertex
  rho : ℝ
  X : Fin P.numParts → Finset HostVertex
  Y : Fin P.numParts → Finset HostVertex
  rootInjective : Function.Injective rootImage
  uniform : ∀ i, G.IsUniform rho (X i) (Y i)
  rho_le_one : rho ≤ 1
  capX : ∀ i, (P.orderedForest.size i : ℝ) + rho * #(X i) ≤
    (G.edgeDensity (X i) (Y i) - rho) * #(X i)
  capY : ∀ i, (P.orderedForest.size i : ℝ) + rho * #(Y i) ≤
    (G.edgeDensity (X i) (Y i) - rho) * #(Y i)
  rootDegree : ∀ i, (P.orderedForest.size i : ℝ) + rho * #(Y i) ≤
    (#((Y i).filter (G.Adj (rootImage i))) : ℝ)
  rootOutside : ∀ i k,
    rootImage i ∉ Erdos547b.RegularPair.cleanedSide G rho (X k) (Y k) ∧
    rootImage i ∉ Erdos547b.RegularPair.cleanedSide G rho (Y k) (X k)
  disjoint : ∀ i k, i ≠ k →
    Disjoint
      (Erdos547b.RegularPair.cleanedSide G rho (X i) (Y i) ∪
        Erdos547b.RegularPair.cleanedSide G rho (Y i) (X i))
      (Erdos547b.RegularPair.cleanedSide G rho (X k) (Y k) ∪
        Erdos547b.RegularPair.cleanedSide G rho (Y k) (X k))
  rootParentAdj : ∀ j (hj : j.val ≠ 0),
    let p := P.toOrderedForestVertex (P.parent j hj)
    p.2 = P.orderedForest.root p.1 →
      G.Adj (rootImage p.1) (rootImage j)
  sideParentAdj : ∀ j (hj : j.val ≠ 0),
    let p := P.toOrderedForestVertex (P.parent j hj)
    p.2 ≠ P.orderedForest.root p.1 →
    ∀ z, z ∈
        (if (P.orderedForest.isTree p.1).coloringTwoOfVert
              (P.orderedForest.root p.1) p.2 = 0 then
          Erdos547b.RegularPair.cleanedSide G rho (X p.1) (Y p.1)
        else
          Erdos547b.RegularPair.cleanedSide G rho (Y p.1) (X p.1)) →
      G.Adj z (rootImage j)

/-- Concise public form of the actual Lemma 6.15 embedding conclusion.  The
threshold is `q = eta*k`; the input `data` provides only checked local
regular-pair and root--parent adjacency facts for exceptional matching
edges. -/
theorem zhaoLemma615_full
    (T : SimpleGraph TreeVertex) [DecidableRel T.Adj]
    (globalRoot : TreeVertex) (small : ℕ)
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph HostVertex) [DecidableRel G.Adj]
    (M : Finset E) (density : E → Fin 2 → ℝ) (eta q : ℝ)
    (hq : 0 < q)
    (hlarge : q ≤ ((unbalancedEdges M density eta).card : ℝ) ∨
      q ≤ ((nonextremeEdges M density eta).card : ℝ))
    (data : ∀ e, e ∈ unbalancedEdges M density eta ∪
        nonextremeEdges M density eta → UniformCutForestData P G) :
    T.IsContained G := by
  classical
  let eligible := unbalancedEdges M density eta ∪
    nonextremeEdges M density eta
  have heligPos : 0 < (eligible.card : ℝ) := by
    rcases hlarge with h | h
    · exact hq.trans_le (h.trans (by
        exact_mod_cast Finset.card_le_card (Finset.subset_union_left)))
    · exact hq.trans_le (h.trans (by
        exact_mod_cast Finset.card_le_card (Finset.subset_union_right)))
  have heligNonempty : eligible.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    rw [hempty] at heligPos
    norm_num at heligPos
  obtain ⟨e, he⟩ := heligNonempty
  let D := data e (by simpa [eligible] using he)
  exact fullTreeContained_of_uniformPairs P G D.rootImage D.X D.Y
    D.rootInjective D.uniform D.rho_le_one D.capX D.capY D.rootDegree
    D.rootOutside D.disjoint D.rootParentAdj D.sideParentAdj

/-- Full Zhao-forest form of Lemma 6.15.  For every exceptional matching
edge the hypotheses display the uniform slices, capacities and root images
which Zhao obtains from Lemma 5.8 and then passes to Lemma 6.14.  The
cardinality alternative selects such an edge, and the checked 6.14 glue
embeds the literal cut forest and restores every deleted root--parent edge.

Unlike a continuation interface, every premise below is either a numerical
uniform-pair inequality, disjointness, or an ordinary host adjacency. -/
theorem zhaoLemma615_full_of_uniformPairs
    (T : SimpleGraph TreeVertex) [DecidableRel T.Adj]
    (globalRoot : TreeVertex) (small : ℕ)
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph HostVertex) [DecidableRel G.Adj]
    (M : Finset E) (density : E → Fin 2 → ℝ) (eta q : ℝ)
    (rootImage : E → Fin P.numParts → HostVertex)
    (rho : E → ℝ)
    (X Y : E → Fin P.numParts → Finset HostVertex)
    (hq : 0 < q)
    (hlarge : q ≤ ((unbalancedEdges M density eta).card : ℝ) ∨
      q ≤ ((nonextremeEdges M density eta).card : ℝ))
    (hrootInjective : ∀ e ∈ unbalancedEdges M density eta ∪
        nonextremeEdges M density eta,
      Function.Injective (rootImage e))
    (hunif : ∀ e ∈ unbalancedEdges M density eta ∪
        nonextremeEdges M density eta, ∀ i,
      G.IsUniform (rho e) (X e i) (Y e i))
    (hrho : ∀ e ∈ unbalancedEdges M density eta ∪
        nonextremeEdges M density eta, rho e ≤ 1)
    (hcapX : ∀ e ∈ unbalancedEdges M density eta ∪
        nonextremeEdges M density eta, ∀ i,
      (P.orderedForest.size i : ℝ) + rho e * #(X e i) ≤
        (G.edgeDensity (X e i) (Y e i) - rho e) * #(X e i))
    (hcapY : ∀ e ∈ unbalancedEdges M density eta ∪
        nonextremeEdges M density eta, ∀ i,
      (P.orderedForest.size i : ℝ) + rho e * #(Y e i) ≤
        (G.edgeDensity (X e i) (Y e i) - rho e) * #(Y e i))
    (hrootDegree : ∀ e ∈ unbalancedEdges M density eta ∪
        nonextremeEdges M density eta, ∀ i,
      (P.orderedForest.size i : ℝ) + rho e * #(Y e i) ≤
        (#((Y e i).filter (G.Adj (rootImage e i))) : ℝ))
    (hrootOutside : ∀ e ∈ unbalancedEdges M density eta ∪
        nonextremeEdges M density eta, ∀ i k,
      rootImage e i ∉ Erdos547b.RegularPair.cleanedSide G (rho e) (X e k) (Y e k) ∧
      rootImage e i ∉ Erdos547b.RegularPair.cleanedSide G (rho e) (Y e k) (X e k))
    (hdisjoint : ∀ e ∈ unbalancedEdges M density eta ∪
        nonextremeEdges M density eta, ∀ i k, i ≠ k →
      Disjoint
        (Erdos547b.RegularPair.cleanedSide G (rho e) (X e i) (Y e i) ∪
          Erdos547b.RegularPair.cleanedSide G (rho e) (Y e i) (X e i))
        (Erdos547b.RegularPair.cleanedSide G (rho e) (X e k) (Y e k) ∪
          Erdos547b.RegularPair.cleanedSide G (rho e) (Y e k) (X e k)))
    (hrootParentAdj : ∀ e ∈ unbalancedEdges M density eta ∪
        nonextremeEdges M density eta, ∀ j (hj : j.val ≠ 0),
      let p := P.toOrderedForestVertex (P.parent j hj)
      p.2 = P.orderedForest.root p.1 →
        G.Adj (rootImage e p.1) (rootImage e j))
    (hsideParentAdj : ∀ e ∈ unbalancedEdges M density eta ∪
        nonextremeEdges M density eta, ∀ j (hj : j.val ≠ 0),
      let p := P.toOrderedForestVertex (P.parent j hj)
      p.2 ≠ P.orderedForest.root p.1 →
      ∀ z, z ∈
          (if (P.orderedForest.isTree p.1).coloringTwoOfVert
                (P.orderedForest.root p.1) p.2 = 0 then
            Erdos547b.RegularPair.cleanedSide G (rho e) (X e p.1) (Y e p.1)
          else
            Erdos547b.RegularPair.cleanedSide G (rho e) (Y e p.1) (X e p.1)) →
        G.Adj z (rootImage e j)) :
    T.IsContained G := by
  classical
  let eligible := unbalancedEdges M density eta ∪
    nonextremeEdges M density eta
  have heligPos : 0 < (eligible.card : ℝ) := by
    rcases hlarge with h | h
    · exact hq.trans_le (h.trans (by
        exact_mod_cast Finset.card_le_card (Finset.subset_union_left)))
    · exact hq.trans_le (h.trans (by
        exact_mod_cast Finset.card_le_card (Finset.subset_union_right)))
  have heligNonempty : eligible.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    rw [hempty] at heligPos
    norm_num at heligPos
  obtain ⟨e, he⟩ := heligNonempty
  apply fullTreeContained_of_uniformPairs P G (rootImage e) (X e) (Y e)
  · exact hrootInjective e (by simpa [eligible] using he)
  · exact hunif e (by simpa [eligible] using he)
  · exact hrho e (by simpa [eligible] using he)
  · exact hcapX e (by simpa [eligible] using he)
  · exact hcapY e (by simpa [eligible] using he)
  · exact hrootDegree e (by simpa [eligible] using he)
  · exact hrootOutside e (by simpa [eligible] using he)
  · exact hdisjoint e (by simpa [eligible] using he)
  · exact hrootParentAdj e (by simpa [eligible] using he)
  · exact hsideParentAdj e (by simpa [eligible] using he)

end FullCutForestEmbedding

section SourceShapedStatement

variable {E : Type u} [DecidableEq E]
variable {K : Type v} [Fintype K] [DecidableEq K]
variable {TreeVertex : Type*} [Fintype TreeVertex] [DecidableEq TreeVertex]
variable {HostVertex : Type w} [Fintype HostVertex] [DecidableEq HostVertex]

/-- Zhao's degree from a cluster `A` into a cluster matching: every
matching edge contributes the common cluster size times the sum of the two
endpoint densities. -/
def clusterMatchingDegree (M : Finset E) (endpoint : E → Fin 2 → K)
    (density : K → K → ℝ) (N : ℝ) (A : K) : ℝ :=
  ∑ e ∈ M, N * (density A (endpoint e 0) + density A (endpoint e 1))

/-- Literal source-shaped wrapper for Lemma 6.15.  `hdegreeA` and
`hdegreeB` are (6.14), while `hAB` is the adjacency of `A,B` in the reduced
graph.  The host-side hypotheses explicitly discharge the regular-pair
embedding step and the conclusion is a concrete copy of `T`. -/
theorem zhaoLemma615_source
    (T : SimpleGraph TreeVertex) (hT : T.IsTree) (root : TreeVertex)
    (G : SimpleGraph HostVertex) [DecidableRel G.Adj]
    (R : SimpleGraph K) [DecidableRel R.Adj] (A B : K) (hAB : R.Adj A B)
    (CM : ClusterMatching E HostVertex) (M : Finset E)
    (endpoint : E → Fin 2 → K) (clusters : K → Finset HostVertex)
    (density : K → K → ℝ) (rootImage : E → HostVertex)
    (eta d n N k : ℝ)
    (hside : ∀ e ∈ M, ∀ c, CM.side e c = clusters (endpoint e c))
    (hendpoints : ∀ e ∈ M, ∀ c,
      endpoint e c ≠ A ∧ endpoint e c ≠ B)
    (hdegreeA : (1 - 10 * Real.sqrt d) * n ≤
      clusterMatchingDegree M endpoint density N A)
    (hdegreeB : (1 - 10 * Real.sqrt d) * n ≤
      clusterMatchingDegree M endpoint density N B)
    (hthreshold : 0 < eta * k)
    (hlarge : eta * k ≤
        ((unbalancedEdges M (fun e c ↦ density A (endpoint e c)) eta).card : ℝ) ∨
      eta * k ≤
        ((nonextremeEdges M (fun e c ↦ density A (endpoint e c)) eta).card : ℝ))
    (hlocal : ∀ e ∈
        unbalancedEdges M (fun e c ↦ density A (endpoint e c)) eta ∪
          nonextremeEdges M (fun e c ↦ density A (endpoint e c)) eta,
      LocallyHostsTree T G CM rootImage e)
    (hrootOutside : ∀ e ∈
        unbalancedEdges M (fun e c ↦ density A (endpoint e c)) eta ∪
          nonextremeEdges M (fun e c ↦ density A (endpoint e c)) eta,
      ∀ p : E, ∀ c : Fin 2, rootImage e ∉ CM.side p c) :
    Nonempty (T.Copy G) := by
  -- These source hypotheses identify the wrapper with Zhao's setting;
  -- the checked local graph counts are the part used by the copy constructor.
  have _ := hAB
  have _ := hside
  have _ := hendpoints
  have _ := hdegreeA
  have _ := hdegreeB
  exact zhaoLemma615_concrete T hT root G CM M
    (fun e c ↦ density A (endpoint e c)) eta (eta * k) rootImage
    hthreshold hlarge hlocal hrootOutside

/-- Source statement with the full cut-forest constructor.  This is the
literal Lemma 6.15 configuration: `A,B` are adjacent, `M` is a matching on
clusters outside them, (6.14) is stated verbatim, and the two exceptional
families have the paper's threshold `eta*k`.  `data` is the concrete output
of the preceding forest-allocation lemmas, expressed without an embedding
or continuation field. -/
theorem zhaoLemma615_source_full
    {globalRoot : TreeVertex} {small : ℕ}
    (T : SimpleGraph TreeVertex) [DecidableRel T.Adj]
    (P : Erdos547b.TreePartition.ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph HostVertex) [DecidableRel G.Adj]
    (R : SimpleGraph K) [DecidableRel R.Adj] (A B : K) (hAB : R.Adj A B)
    (M : Finset E) (endpoint : E → Fin 2 → K)
    (density : K → K → ℝ) (eta d n N k : ℝ)
    (hmatchingAdj : ∀ e ∈ M, R.Adj (endpoint e 0) (endpoint e 1))
    (hmatchingDisjoint : ∀ e ∈ M, ∀ f ∈ M, e ≠ f →
      ∀ c t : Fin 2, endpoint e c ≠ endpoint f t)
    (hendpoints : ∀ e ∈ M, ∀ c,
      endpoint e c ≠ A ∧ endpoint e c ≠ B)
    (hdegreeA : (1 - 10 * Real.sqrt d) * n ≤
      clusterMatchingDegree M endpoint density N A)
    (hdegreeB : (1 - 10 * Real.sqrt d) * n ≤
      clusterMatchingDegree M endpoint density N B)
    (hthreshold : 0 < eta * k)
    (hlarge : eta * k ≤
        ((unbalancedEdges M (fun e c ↦ density A (endpoint e c)) eta).card : ℝ) ∨
      eta * k ≤
        ((nonextremeEdges M (fun e c ↦ density A (endpoint e c)) eta).card : ℝ))
    (data : ∀ e, e ∈
        unbalancedEdges M (fun e c ↦ density A (endpoint e c)) eta ∪
          nonextremeEdges M (fun e c ↦ density A (endpoint e c)) eta →
      UniformCutForestData P G) :
    T.IsContained G := by
  have _ := hAB
  have _ := hmatchingAdj
  have _ := hmatchingDisjoint
  have _ := hendpoints
  have _ := hdegreeA
  have _ := hdegreeB
  exact zhaoLemma615_full T globalRoot small P G M
    (fun e c ↦ density A (endpoint e c)) eta (eta * k)
      hthreshold hlarge data

end SourceShapedStatement

section Lemma612Reservation

variable {E : Type u} [DecidableEq E]
variable {TreeVertex : Type v} [Fintype TreeVertex] [DecidableEq TreeVertex]
variable {HostVertex : Type w} [Fintype HostVertex] [DecidableEq HostVertex]

/-- The small-`f_b` branch of the source proof.  Lemma 6.12 first reserves
`M_b`; the hierarchy `2 d^(1/4) k < q` leaves an eligible edge outside that
reserve, and the shared forest theorem constructs the tree copy there. -/
theorem zhaoLemma615_small_branch_with_reserved_matching
    (T : SimpleGraph TreeVertex) (hT : T.IsTree) (root : TreeVertex)
    (G : SimpleGraph HostVertex) [DecidableRel G.Adj]
    (CM : ClusterMatching E HostVertex) (M : Finset E)
    (density : E → Fin 2 → ℝ) (eta q : ℝ)
    (rootImage : E → HostVertex)
    (contribution : E → ℝ) (kNat : ℕ)
    (f_b gamma n N d : ℝ)
    (hmk : M.card ≤ kNat)
    (hfb : 0 ≤ f_b) (hgamma : 0 ≤ gamma) (hn : 0 ≤ n)
    (hN : 0 < N) (hd : 0 ≤ d)
    (hnonneg : ∀ e ∈ M, 0 ≤ contribution e)
    (hedgecap : ∀ e ∈ M, contribution e ≤ 2 * N)
    (htotal : (1 - 10 * Real.sqrt d) * n ≤ ∑ e ∈ M, contribution e)
    (hlowerpos : 0 < (1 - 10 * Real.sqrt d) * n)
    (hfbsmall : f_b < Real.sqrt (Real.sqrt d) * n)
    (htargetHierarchy : Real.sqrt (Real.sqrt d) * n + 3 * gamma * n ≤
      (1 - 10 * Real.sqrt d) * n)
    (hcardHierarchy : f_b + 3 * gamma * n + 2 * N ≤
      2 * Real.sqrt (Real.sqrt d) * ((1 - 10 * Real.sqrt d) * n))
    (hq : 0 < q)
    (hreserveSmall : 2 * Real.sqrt (Real.sqrt d) * kNat < q)
    (hlarge : q ≤ ((unbalancedEdges M density eta).card : ℝ) ∨
      q ≤ ((nonextremeEdges M density eta).card : ℝ))
    (hlocal : ∀ e ∈ unbalancedEdges M density eta ∪
        nonextremeEdges M density eta,
      LocallyHostsTree T G CM rootImage e)
    (hrootOutside : ∀ e ∈ unbalancedEdges M density eta ∪
        nonextremeEdges M density eta,
      ∀ p : E, ∀ c : Fin 2, rootImage e ∉ CM.side p c) :
    ∃ M_b : Finset E,
      M_b ⊆ M ∧
      f_b + 3 * gamma * n ≤ ∑ e ∈ M_b, contribution e ∧
      (∑ e ∈ M_b, contribution e) < f_b + 3 * gamma * n + 2 * N ∧
      ((M_b.card : ℕ) : ℝ) ≤ 2 * Real.sqrt (Real.sqrt d) * kNat ∧
      Nonempty (T.Copy G) := by
  classical
  obtain ⟨M_b, hMbM, hMbLower, hMbUpper, hMbCard⟩ :=
    Erdos547b.ZhaoLemma612.zhao_lemma_6_12_source_constants
      M contribution kNat f_b gamma n N d hmk hfb hgamma hn hN hd
      hnonneg hedgecap htotal hlowerpos hfbsmall htargetHierarchy hcardHierarchy
  let eligible := unbalancedEdges M density eta ∪
    nonextremeEdges M density eta
  have heligLower : q ≤ (eligible.card : ℝ) := by
    rcases hlarge with h | h
    · exact h.trans (by
        exact_mod_cast Finset.card_le_card (Finset.subset_union_left))
    · exact h.trans (by
        exact_mod_cast Finset.card_le_card (Finset.subset_union_right))
  have hMbLt : (M_b.card : ℝ) < q := hMbCard.trans_lt hreserveSmall
  have hcardLt : M_b.card < eligible.card := by
    exact_mod_cast hMbLt.trans_le heligLower
  have hex : ∃ e ∈ eligible, e ∉ M_b := by
    by_contra h
    push Not at h
    have hsub : eligible ⊆ M_b := by
      intro e he
      exact h e he
    exact (not_lt_of_ge (Finset.card_le_card hsub)) hcardLt
  obtain ⟨e, he, heMb⟩ := hex
  have hcopy : Nonempty (T.Copy G) :=
    exists_tree_copy_of_eligible_edge T hT root G CM eligible rootImage
      (by simpa [eligible] using hlocal)
      (by simpa [eligible] using hrootOutside) he
  exact ⟨M_b, hMbM, hMbLower, hMbUpper, hMbCard, hcopy⟩

end Lemma612Reservation

section Lemma613Assembly

variable {E : Type u} [DecidableEq E]
variable {TreeVertex : Type v} [Fintype TreeVertex] [DecidableEq TreeVertex]
variable {HostVertex : Type w} [Fintype HostVertex] [DecidableEq HostVertex]

/-- Lemma 6.13's balance conclusion with its formerly abstract embedding
implication discharged by the concrete Lemma 6.15 constructor above.
`hexcessForcesExceptional` is a purely numerical/cardinality assertion. -/
theorem matching_balance_of_concrete_zhaoLemma615
    (T : SimpleGraph TreeVertex) (hT : T.IsTree) (root : TreeVertex)
    (G : SimpleGraph HostVertex) [DecidableRel G.Adj]
    (CM : ClusterMatching E HostVertex) (M : Finset E)
    (density : E → Fin 2 → ℝ) (eta q : ℝ)
    (rootImage : E → HostVertex)
    (a b : E → ℝ) (fb delta bound : ℝ)
    (hq : 0 < q)
    (htotal : (∑ e ∈ M, a e) = ∑ e ∈ M, b e)
    (hfb : delta ≤ fb)
    (hexcessForcesExceptional :
      bound ≤ Erdos547b.ZhaoStability.matchingPositiveExcess M a b →
        q ≤ ((unbalancedEdges M density eta).card : ℝ) ∨
        q ≤ ((nonextremeEdges M density eta).card : ℝ))
    (hlocal : ∀ e ∈ unbalancedEdges M density eta ∪
        nonextremeEdges M density eta,
      LocallyHostsTree T G CM rootImage e)
    (hrootOutside : ∀ e ∈ unbalancedEdges M density eta ∪
        nonextremeEdges M density eta,
      ∀ p : E, ∀ c : Fin 2, rootImage e ∉ CM.side p c)
    (hnot : ¬ Nonempty (T.Copy G)) :
    ∀ S : Finset E, S ⊆ M →
      |(∑ e ∈ S, a e) - (∑ e ∈ S, b e)| < bound := by
  apply Erdos547b.ZhaoStability.zhaoLemma613_matchingDegreeBalance
    M a b fb delta bound (Nonempty (T.Copy G)) htotal hfb
  · intro _hdelta hexcess
    exact zhaoLemma615_concrete T hT root G CM M density eta q rootImage hq
      (hexcessForcesExceptional hexcess) hlocal hrootOutside
  · exact hnot

end Lemma613Assembly

section Claim618Consequences

open Erdos547b.TreePartition

variable {E : Type u} [DecidableEq E]
variable {TreeVertex : Type v} [Fintype TreeVertex] [DecidableEq TreeVertex]
variable {HostVertex : Type w} [Fintype HostVertex] [DecidableEq HostVertex]

/-- Claim 6.18 contrapositive using the full Zhao cut-forest embedding, not
the one-pair specialization. -/
theorem claim618_unbalanced_submatching_card_lt_full
    (T : SimpleGraph TreeVertex) [DecidableRel T.Adj]
    (globalRoot : TreeVertex) (small : ℕ)
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph HostVertex) [DecidableRel G.Adj]
    (M S : Finset E) (density : E → Fin 2 → ℝ) (eta q : ℝ)
    (hq : 0 < q) (hS : S ⊆ M)
    (hSunbalanced : ∀ e ∈ S, eta ≤ |density e 0 - density e 1|)
    (data : ∀ e, e ∈ unbalancedEdges M density eta ∪
        nonextremeEdges M density eta → UniformCutForestData P G)
    (hnot : ¬ T.IsContained G) :
    (S.card : ℝ) < q := by
  have hSU : S ⊆ unbalancedEdges M density eta := by
    intro e he
    exact mem_unbalancedEdges.mpr ⟨hS he, hSunbalanced e he⟩
  by_contra h
  have hlarge : q ≤ ((unbalancedEdges M density eta).card : ℝ) := by
    exact (le_of_not_gt h).trans (by
      exact_mod_cast Finset.card_le_card hSU)
  exact hnot (zhaoLemma615_full T globalRoot small P G M density eta q hq
    (Or.inl hlarge) data)

/-- One-positive/one-zero specialization of the preceding full Claim 6.18
API. -/
theorem claim618_positive_zero_card_lt_full
    (T : SimpleGraph TreeVertex) [DecidableRel T.Adj]
    (globalRoot : TreeVertex) (small : ℕ)
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph HostVertex) [DecidableRel G.Adj]
    (M : Finset E) (density : E → Fin 2 → ℝ) (eta q : ℝ)
    (heta : 0 ≤ eta) (hq : 0 < q)
    (data : ∀ e, e ∈ unbalancedEdges M density eta ∪
        nonextremeEdges M density eta → UniformCutForestData P G)
    (hnot : ¬ T.IsContained G) :
    ((positiveZeroEdges M density eta).card : ℝ) < q := by
  apply claim618_unbalanced_submatching_card_lt_full
    T globalRoot small P G M (positiveZeroEdges M density eta)
      density eta q hq (filter_subset _ _)
  · intro e he
    exact (mem_unbalancedEdges.mp
      (positiveZeroEdges_subset_unbalancedEdges M density eta heta he)).2
  · exact data
  · exact hnot

/-- Contrapositive form used in Claim 6.18: if the tree is absent, every
submatching consisting only of unbalanced pairs has cardinality below the
Lemma 6.15 threshold. -/
theorem claim618_unbalanced_submatching_card_lt
    (T : SimpleGraph TreeVertex) (hT : T.IsTree) (root : TreeVertex)
    (G : SimpleGraph HostVertex) [DecidableRel G.Adj]
    (CM : ClusterMatching E HostVertex) (M S : Finset E)
    (density : E → Fin 2 → ℝ) (eta q : ℝ)
    (rootImage : E → HostVertex) (hq : 0 < q)
    (hS : S ⊆ M)
    (hSunbalanced : ∀ e ∈ S, eta ≤ |density e 0 - density e 1|)
    (hlocal : ∀ e ∈ unbalancedEdges M density eta ∪
        nonextremeEdges M density eta,
      LocallyHostsTree T G CM rootImage e)
    (hrootOutside : ∀ e ∈ unbalancedEdges M density eta ∪
        nonextremeEdges M density eta,
      ∀ p : E, ∀ c : Fin 2, rootImage e ∉ CM.side p c)
    (hnot : ¬ Nonempty (T.Copy G)) :
    (S.card : ℝ) < q := by
  have hSU : S ⊆ unbalancedEdges M density eta := by
    intro e he
    exact mem_unbalancedEdges.mpr ⟨hS he, hSunbalanced e he⟩
  by_contra h
  have hlarge : q ≤ ((unbalancedEdges M density eta).card : ℝ) := by
    exact (le_of_not_gt h).trans (by
      exact_mod_cast Finset.card_le_card hSU)
  exact hnot (zhaoLemma615_concrete T hT root G CM M density eta q rootImage hq
    (Or.inl hlarge) hlocal hrootOutside)

/-- The second use in Claim 6.18: pairs with endpoint densities at least
`eta` and zero are a subfamily of `M_unbal`, so they obey the same bound. -/
theorem claim618_positive_zero_card_lt
    (T : SimpleGraph TreeVertex) (hT : T.IsTree) (root : TreeVertex)
    (G : SimpleGraph HostVertex) [DecidableRel G.Adj]
    (CM : ClusterMatching E HostVertex) (M : Finset E)
    (density : E → Fin 2 → ℝ) (eta q : ℝ)
    (rootImage : E → HostVertex) (heta : 0 ≤ eta) (hq : 0 < q)
    (hlocal : ∀ e ∈ unbalancedEdges M density eta ∪
        nonextremeEdges M density eta,
      LocallyHostsTree T G CM rootImage e)
    (hrootOutside : ∀ e ∈ unbalancedEdges M density eta ∪
        nonextremeEdges M density eta,
      ∀ p : E, ∀ c : Fin 2, rootImage e ∉ CM.side p c)
    (hnot : ¬ Nonempty (T.Copy G)) :
    ((positiveZeroEdges M density eta).card : ℝ) < q := by
  exact claim618_unbalanced_submatching_card_lt T hT root G CM M
    (positiveZeroEdges M density eta) density eta q rootImage hq
    (filter_subset _ _)
    (by
      intro e he
      exact (mem_unbalancedEdges.mp
        (positiveZeroEdges_subset_unbalancedEdges M density eta heta he)).2)
    hlocal hrootOutside hnot

end Claim618Consequences

end Erdos547b.ZhaoLemma615

#print axioms Erdos547b.ZhaoLemma615.zhaoLemma615_concrete
#print axioms Erdos547b.ZhaoLemma615.copyTree_of_cutForestCopy
#print axioms Erdos547b.ZhaoLemma615.zhaoLemma615_full
#print axioms Erdos547b.ZhaoLemma615.zhaoLemma615_full_of_uniformPairs
#print axioms Erdos547b.ZhaoLemma615.zhaoLemma615_source
#print axioms Erdos547b.ZhaoLemma615.zhaoLemma615_source_full
#print axioms Erdos547b.ZhaoLemma615.zhaoLemma615_small_branch_with_reserved_matching
#print axioms Erdos547b.ZhaoLemma615.matching_balance_of_concrete_zhaoLemma615
#print axioms Erdos547b.ZhaoLemma615.claim618_unbalanced_submatching_card_lt
#print axioms Erdos547b.ZhaoLemma615.claim618_positive_zero_card_lt
#print axioms Erdos547b.ZhaoLemma615.claim618_unbalanced_submatching_card_lt_full
#print axioms Erdos547b.ZhaoLemma615.claim618_positive_zero_card_lt_full
