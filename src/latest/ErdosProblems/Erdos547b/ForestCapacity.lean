/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Stability
import ErdosProblems.Erdos547b.RegularPair
import ErdosProblems.Erdos547b.TreePartition

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.RegularPair.OrderedRootedForest

open Finset SimpleGraph

variable {m : ℕ}

/-- The inclusion of one component's vertex type into the vertex type of the
whole ordered forest. -/
def componentEmbedding (F : OrderedRootedForest m) (i : Fin m) :
    Fin (F.size i) ↪ Σ j, Fin (F.size j) where
  toFun a := ⟨i, a⟩
  inj' _ _ h := by simpa using h

/-- The literal simple graph underlying an ordered rooted forest: the
disjoint union of all of its component trees. -/
def graph (F : OrderedRootedForest m) :
    SimpleGraph (Σ i, Fin (F.size i)) :=
  ⨆ i, (F.tree i).map (componentEmbedding F i)

@[simp] theorem graph_adj {F : OrderedRootedForest m}
    (x y : Σ i, Fin (F.size i)) :
    F.graph.Adj x y ↔
      ∃ i, ∃ a b : Fin (F.size i), x = ⟨i, a⟩ ∧ y = ⟨i, b⟩ ∧
        (F.tree i).Adj a b := by
  simp only [graph, iSup_adj, map_adj, componentEmbedding]
  constructor
  · rintro ⟨i, a, b, hab, rfl, rfl⟩
    exact ⟨i, a, b, rfl, rfl, hab⟩
  · rintro ⟨i, a, b, rfl, rfl, hab⟩
    exact ⟨i, a, b, hab, rfl, rfl⟩

/-- A simultaneous ordered-forest embedding is a genuine copy of the
disjoint-union graph of all components. -/
def Embedding.toGraphCopy {F : OrderedRootedForest m} {B : Type*}
    {G : SimpleGraph B} (E : F.Embedding G) : F.graph.Copy G where
  toHom :=
    { toFun := fun z ↦ E.copy z.1 z.2
      map_rel' := by
        intro x y hxy
        rcases (graph_adj x y).mp hxy with ⟨i, a, b, rfl, rfl, hab⟩
        exact (E.copy i).toHom.map_adj hab }
  injective' := E.injective

end Erdos547b.RegularPair.OrderedRootedForest

namespace Erdos547b.TreePartition

open SimpleGraph
open Erdos547b.RegularPair

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small : ℕ}

/-- A canonical finite numbering of the vertices in one component of a Zhao
cut forest. -/
noncomputable def ZhaoForestPartition.componentEquiv
    (P : ZhaoForestPartition T globalRoot small) (i : Fin P.numParts) :
    Fin (Nat.card (↑(P.components i))) ≃ ↑(P.components i) :=
  (Finite.equivFin (↑(P.components i))).symm

/-- The actual ordered rooted forest carried by Zhao's cut edges, with every
connected component reindexed by a finite interval. -/
noncomputable abbrev ZhaoForestPartition.orderedForest
    (P : ZhaoForestPartition T globalRoot small) :
    OrderedRootedForest P.numParts where
  size i := Nat.card (↑(P.components i))
  tree i := (P.components i).toSimpleGraph.comap (P.componentEquiv i)
  isTree i := by
    apply (Iso.comap (P.componentEquiv i) (P.components i).toSimpleGraph).isTree_iff.mpr
    exact (P.component_mTree i).1
  root i := (P.componentEquiv i).symm ⟨P.roots i, P.root_mem i⟩

/-- The spanning cut forest in Zhao Definition 6.2. -/
abbrev ZhaoForestPartition.cutForest
    (P : ZhaoForestPartition T globalRoot small) : SimpleGraph V :=
  T.deleteEdges (↑(zhaoCutEdges P.roots P.parent) : Set (Sym2 V))

/-- The index of the cut-forest component containing a vertex. -/
noncomputable def ZhaoForestPartition.componentIndex
    (P : ZhaoForestPartition T globalRoot small) (v : V) : Fin P.numParts :=
  P.components.symm
    ((T.deleteEdges (↑(zhaoCutEdges P.roots P.parent) : Set (Sym2 V))).connectedComponentMk v)

/-- A vertex, regarded as a member of its indexed cut-forest component. -/
noncomputable def ZhaoForestPartition.vertexInComponent
    (P : ZhaoForestPartition T globalRoot small) (v : V) :
    ↑(P.components (P.componentIndex v)) := by
  refine ⟨v, ?_⟩
  change v ∈ (P.components (P.components.symm
    ((T.deleteEdges (↑(zhaoCutEdges P.roots P.parent) : Set (Sym2 V))).connectedComponentMk v))).supp
  rw [P.components.apply_symm_apply]
  exact ConnectedComponent.connectedComponentMk_mem

/-- The finite coordinate of a vertex inside its cut-forest component. -/
noncomputable def ZhaoForestPartition.componentCoordinate
    (P : ZhaoForestPartition T globalRoot small) (v : V) :
    Fin (P.orderedForest.size (P.componentIndex v)) :=
  (P.componentEquiv (P.componentIndex v)).symm (P.vertexInComponent v)

/-- Canonical encoding of every vertex into the sigma-type underlying the
ordered cut forest. -/
noncomputable def ZhaoForestPartition.toOrderedForestVertex
    (P : ZhaoForestPartition T globalRoot small) (v : V) :
    Σ i, Fin (P.orderedForest.size i) :=
  ⟨P.componentIndex v, P.componentCoordinate v⟩

/-- Forget the component numbering and recover the ambient tree vertex. -/
noncomputable def ZhaoForestPartition.fromOrderedForestVertex
    (P : ZhaoForestPartition T globalRoot small)
    (z : Σ i, Fin (P.orderedForest.size i)) : V :=
  (P.componentEquiv z.1 z.2).1

@[simp] theorem ZhaoForestPartition.componentEquiv_componentCoordinate
    (P : ZhaoForestPartition T globalRoot small) (v : V) :
    P.componentEquiv (P.componentIndex v) (P.componentCoordinate v) =
      P.vertexInComponent v := by
  exact Equiv.apply_symm_apply _ _

@[simp] theorem ZhaoForestPartition.from_toOrderedForestVertex
    (P : ZhaoForestPartition T globalRoot small) (v : V) :
    P.fromOrderedForestVertex (P.toOrderedForestVertex v) = v := by
  change (P.componentEquiv (P.componentIndex v)
    (P.componentCoordinate v)).1 = v
  rw [P.componentEquiv_componentCoordinate]
  rfl

theorem ZhaoForestPartition.toOrderedForestVertex_injective
    (P : ZhaoForestPartition T globalRoot small) :
    Function.Injective P.toOrderedForestVertex := by
  intro x y hxy
  have := congrArg P.fromOrderedForestVertex hxy
  simpa using this

/-- The homomorphism from one literal cut component into its numbered
ordered-forest summand. -/
noncomputable def ZhaoForestPartition.componentCastEquiv
    (P : ZhaoForestPartition T globalRoot small)
    (C : P.cutForest.ConnectedComponent) :
    ↑(P.components (P.components.symm C)) ≃ ↑C where
  toFun x := ⟨x.1, by
    exact x.2.trans (P.components.apply_symm_apply C)⟩
  invFun x := ⟨x.1, by
    exact x.2.trans (P.components.apply_symm_apply C).symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem ZhaoForestPartition.componentCastEquiv_apply_val
    (P : ZhaoForestPartition T globalRoot small)
    (C : P.cutForest.ConnectedComponent)
    (x : ↑(P.components (P.components.symm C))) :
    (P.componentCastEquiv C x).1 = x.1 := rfl

@[simp] theorem ZhaoForestPartition.componentCastEquiv_symm_apply_val
    (P : ZhaoForestPartition T globalRoot small)
    (C : P.cutForest.ConnectedComponent) (x : ↑C) :
    ((P.componentCastEquiv C).symm x).1 = x.1 := rfl

noncomputable def ZhaoForestPartition.numberedComponentEquiv
    (P : ZhaoForestPartition T globalRoot small)
    (C : P.cutForest.ConnectedComponent) :
    Fin (P.orderedForest.size (P.components.symm C)) ≃ ↑C :=
  (P.componentEquiv (P.components.symm C)).trans (P.componentCastEquiv C)

@[simp] theorem ZhaoForestPartition.componentEquiv_numberedComponentEquiv_symm_val
    (P : ZhaoForestPartition T globalRoot small)
    (C : P.cutForest.ConnectedComponent) (x : ↑C) :
    (P.componentEquiv (P.components.symm C)
      ((P.numberedComponentEquiv C).symm x)).1 = x.1 := by
  rw [show P.numberedComponentEquiv C =
    (P.componentEquiv (P.components.symm C)).trans
      (P.componentCastEquiv C) by rfl]
  rw [Equiv.symm_trans_apply]
  calc
    (P.componentEquiv (P.components.symm C)
        ((P.componentEquiv (P.components.symm C)).symm
          ((P.componentCastEquiv C).symm x))).1 =
        ((P.componentCastEquiv C).symm x).1 :=
      congrArg Subtype.val (Equiv.apply_symm_apply
        (P.componentEquiv (P.components.symm C))
        ((P.componentCastEquiv C).symm x))
    _ = x.1 := rfl

noncomputable def ZhaoForestPartition.componentHom
    (P : ZhaoForestPartition T globalRoot small)
    (C : P.cutForest.ConnectedComponent) :
    C.toSimpleGraph →g P.orderedForest.graph := by
  let i : Fin P.numParts := P.components.symm C
  refine
    { toFun := fun x ↦
        ⟨i, (P.numberedComponentEquiv C).symm x⟩
      map_rel' := ?_ }
  intro x y hxy
  rw [RegularPair.OrderedRootedForest.graph_adj]
  refine ⟨i, (P.numberedComponentEquiv C).symm x,
    (P.numberedComponentEquiv C).symm y, rfl, rfl, ?_⟩
  change (P.components i).toSimpleGraph.Adj
    (P.componentEquiv i ((P.numberedComponentEquiv C).symm x))
    (P.componentEquiv i ((P.numberedComponentEquiv C).symm y))
  apply ((P.components i).toSimpleGraph_adj _ _).mpr
  have hcAdj : P.cutForest.Adj x.1 y.1 :=
    (C.toSimpleGraph_adj x.property y.property).mp hxy
  dsimp [i]
  change P.cutForest.Adj
    (P.componentEquiv (P.components.symm C)
      ((P.numberedComponentEquiv C).symm x)).1
    (P.componentEquiv (P.components.symm C)
      ((P.numberedComponentEquiv C).symm y)).1
  rw [P.componentEquiv_numberedComponentEquiv_symm_val,
    P.componentEquiv_numberedComponentEquiv_symm_val]
  exact hcAdj

/-- Canonical homomorphism obtained by gluing the homomorphisms of all cut
components. -/
noncomputable def ZhaoForestPartition.cutForestHom
    (P : ZhaoForestPartition T globalRoot small) :
    P.cutForest →g P.orderedForest.graph :=
  P.cutForest.homOfConnectedComponents P.componentHom

theorem ZhaoForestPartition.componentHom_injective
    (P : ZhaoForestPartition T globalRoot small)
    (C : P.cutForest.ConnectedComponent) :
    Function.Injective (P.componentHom C) := by
  intro x y hxy
  simp only [ZhaoForestPartition.componentHom] at hxy
  change (⟨P.components.symm C, (P.numberedComponentEquiv C).symm x⟩ :
      Σ i, Fin (P.orderedForest.size i)) =
    ⟨P.components.symm C, (P.numberedComponentEquiv C).symm y⟩ at hxy
  have hsnd : (P.numberedComponentEquiv C).symm x =
      (P.numberedComponentEquiv C).symm y := by
    exact eq_of_heq (Sigma.mk.inj_iff.mp hxy).2
  exact (P.numberedComponentEquiv C).symm.injective hsnd

@[simp] theorem ZhaoForestPartition.from_cutForestHom
    (P : ZhaoForestPartition T globalRoot small) (v : V) :
    P.fromOrderedForestVertex (P.cutForestHom v) = v := by
  change P.fromOrderedForestVertex
    (P.componentHom (P.cutForest.connectedComponentMk v)
      ⟨v, ConnectedComponent.connectedComponentMk_mem⟩) = v
  change (P.componentEquiv
    (P.components.symm (P.cutForest.connectedComponentMk v))
    ((P.numberedComponentEquiv (P.cutForest.connectedComponentMk v)).symm
      ⟨v, ConnectedComponent.connectedComponentMk_mem⟩)).1 = v
  rw [P.componentEquiv_numberedComponentEquiv_symm_val]

/-- The canonical reindexing is a genuine graph copy of Zhao's literal cut
forest into the disjoint-union graph of its ordered components. -/
noncomputable def ZhaoForestPartition.cutForestCopy
    (P : ZhaoForestPartition T globalRoot small) :
    P.cutForest.Copy P.orderedForest.graph where
  toHom := P.cutForestHom
  injective' := by
    intro x y hxy
    have := congrArg P.fromOrderedForestVertex hxy
    simpa using this

end Erdos547b.TreePartition

namespace Erdos547b.ZhaoStability

open Finset SimpleGraph
open Erdos547b.RegularPair
open Erdos547b.TreePartition

variable {m : ℕ}

/-- The real ordered-forest regular-pair embedding, viewed through the
capacity interface used in Stability.  The two arbitrary cover graphs in
`ForestCapacityEmbeddingProperty` need no oracle: the checked ordered-forest
embedding has already produced one global injective graph homomorphism. -/
theorem forestCapacityEmbeddingProperty_of_orderedForest_uniformPairs
    {B : Type*} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest m) (G : SimpleGraph B) [DecidableRel G.Adj]
    (rootImage : Fin m → B) {rho : ℝ}
    (X Y : Fin m → Finset B)
    (hrootInjective : Function.Injective rootImage)
    (hunif : ∀ i, G.IsUniform rho (X i) (Y i)) (hrho : rho ≤ 1)
    (hcapX : ∀ i, (F.size i : ℝ) + rho * #(X i) ≤
      (G.edgeDensity (X i) (Y i) - rho) * #(X i))
    (hcapY : ∀ i, (F.size i : ℝ) + rho * #(Y i) ≤
      (G.edgeDensity (X i) (Y i) - rho) * #(Y i))
    (hrootDegree : ∀ i, (F.size i : ℝ) + rho * #(Y i) ≤
      (#((Y i).filter (G.Adj (rootImage i))) : ℝ))
    (hrootOutside : ∀ i k,
      rootImage i ∉ cleanedSide G rho (X k) (Y k) ∧
      rootImage i ∉ cleanedSide G rho (Y k) (X k))
    (hdisjoint : ∀ i k, i ≠ k →
      Disjoint
        (cleanedSide G rho (X i) (Y i) ∪
          cleanedSide G rho (Y i) (X i))
        (cleanedSide G rho (X k) (Y k) ∪
          cleanedSide G rho (Y k) (X k)))
    (capacityA capacityB : ℕ) :
    ForestCapacityEmbeddingProperty F.graph G capacityA capacityB := by
  obtain ⟨E, _hroot, _hmem⟩ :=
    F.exists_embedding_over_disjoint_uniform_pairs G rootImage X Y
      hrootInjective hunif hrho hcapX hcapY hrootDegree hrootOutside hdisjoint
  intro _partA _partB _hcover _hA _hB
  exact ⟨E.toGraphCopy⟩

/-- Reindexing/containment form for an actual cut forest `T`.  The source
copy is purely the checked identification of `T` with the disjoint union of
the ordered components; the host copy itself is constructed by the regular
pair theorem above. -/
theorem forestCapacityEmbeddingProperty_of_cutForest_uniformPairs
    {τ B : Type*} [Fintype B] [DecidableEq B]
    (T : SimpleGraph τ) (F : OrderedRootedForest m)
    (source : T.Copy F.graph)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rootImage : Fin m → B) {rho : ℝ}
    (X Y : Fin m → Finset B)
    (hrootInjective : Function.Injective rootImage)
    (hunif : ∀ i, G.IsUniform rho (X i) (Y i)) (hrho : rho ≤ 1)
    (hcapX : ∀ i, (F.size i : ℝ) + rho * #(X i) ≤
      (G.edgeDensity (X i) (Y i) - rho) * #(X i))
    (hcapY : ∀ i, (F.size i : ℝ) + rho * #(Y i) ≤
      (G.edgeDensity (X i) (Y i) - rho) * #(Y i))
    (hrootDegree : ∀ i, (F.size i : ℝ) + rho * #(Y i) ≤
      (#((Y i).filter (G.Adj (rootImage i))) : ℝ))
    (hrootOutside : ∀ i k,
      rootImage i ∉ cleanedSide G rho (X k) (Y k) ∧
      rootImage i ∉ cleanedSide G rho (Y k) (X k))
    (hdisjoint : ∀ i k, i ≠ k →
      Disjoint
        (cleanedSide G rho (X i) (Y i) ∪
          cleanedSide G rho (Y i) (X i))
        (cleanedSide G rho (X k) (Y k) ∪
          cleanedSide G rho (Y k) (X k)))
    (capacityA capacityB : ℕ) :
    ForestCapacityEmbeddingProperty T G capacityA capacityB := by
  obtain ⟨E, _hroot, _hmem⟩ :=
    F.exists_embedding_over_disjoint_uniform_pairs G rootImage X Y
      hrootInjective hunif hrho hcapX hcapY hrootDegree hrootOutside hdisjoint
  intro _partA _partB _hcover _hA _hB
  exact ⟨E.toGraphCopy.comp source⟩

/-- The concrete matching-allocation output for Zhao's *actual* cut forest.
The source graph is literally `T.deleteEdges (zhaoCutEdges P.roots P.parent)`;
its canonical component numbering is proved above, rather than supplied as
an embedding hypothesis. -/
theorem exists_zhaoCutForestCopy_of_uniformPairs
    {V B : Type*} [Fintype V] [DecidableEq V]
    {T : SimpleGraph V} [DecidableRel T.Adj]
    {globalRoot : V} {small : ℕ}
    (P : ZhaoForestPartition T globalRoot small)
    [Fintype B] [DecidableEq B]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rootImage : Fin P.numParts → B) {rho : ℝ}
    (X Y : Fin P.numParts → Finset B)
    (hrootInjective : Function.Injective rootImage)
    (hunif : ∀ i, G.IsUniform rho (X i) (Y i)) (hrho : rho ≤ 1)
    (hcapX : ∀ i, (P.orderedForest.size i : ℝ) + rho * #(X i) ≤
      (G.edgeDensity (X i) (Y i) - rho) * #(X i))
    (hcapY : ∀ i, (P.orderedForest.size i : ℝ) + rho * #(Y i) ≤
      (G.edgeDensity (X i) (Y i) - rho) * #(Y i))
    (hrootDegree : ∀ i, (P.orderedForest.size i : ℝ) + rho * #(Y i) ≤
      (#((Y i).filter (G.Adj (rootImage i))) : ℝ))
    (hrootOutside : ∀ i k,
      rootImage i ∉ cleanedSide G rho (X k) (Y k) ∧
      rootImage i ∉ cleanedSide G rho (Y k) (X k))
    (hdisjoint : ∀ i k, i ≠ k →
      Disjoint
        (cleanedSide G rho (X i) (Y i) ∪
          cleanedSide G rho (Y i) (X i))
        (cleanedSide G rho (X k) (Y k) ∪
          cleanedSide G rho (Y k) (X k))) :
    Nonempty (P.cutForest.Copy G) := by
  obtain ⟨E, _hroot, _hmem⟩ :=
    P.orderedForest.exists_embedding_over_disjoint_uniform_pairs
      G rootImage X Y hrootInjective hunif hrho hcapX hcapY hrootDegree
        hrootOutside hdisjoint
  exact ⟨E.toGraphCopy.comp P.cutForestCopy⟩

/-- No-oracle constructor for the exact capacity interface used by
`ZhaoStability`: the concrete regular pairs and their disjoint matching
slices first produce an actual copy of Zhao's cut forest. -/
theorem forestCapacityEmbeddingProperty_of_zhaoCutForest_uniformPairs
    {V B : Type*} [Fintype V] [DecidableEq V]
    {T : SimpleGraph V} [DecidableRel T.Adj]
    {globalRoot : V} {small : ℕ}
    (P : ZhaoForestPartition T globalRoot small)
    [Fintype B] [DecidableEq B]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rootImage : Fin P.numParts → B) {rho : ℝ}
    (X Y : Fin P.numParts → Finset B)
    (hrootInjective : Function.Injective rootImage)
    (hunif : ∀ i, G.IsUniform rho (X i) (Y i)) (hrho : rho ≤ 1)
    (hcapX : ∀ i, (P.orderedForest.size i : ℝ) + rho * #(X i) ≤
      (G.edgeDensity (X i) (Y i) - rho) * #(X i))
    (hcapY : ∀ i, (P.orderedForest.size i : ℝ) + rho * #(Y i) ≤
      (G.edgeDensity (X i) (Y i) - rho) * #(Y i))
    (hrootDegree : ∀ i, (P.orderedForest.size i : ℝ) + rho * #(Y i) ≤
      (#((Y i).filter (G.Adj (rootImage i))) : ℝ))
    (hrootOutside : ∀ i k,
      rootImage i ∉ cleanedSide G rho (X k) (Y k) ∧
      rootImage i ∉ cleanedSide G rho (Y k) (X k))
    (hdisjoint : ∀ i k, i ≠ k →
      Disjoint
        (cleanedSide G rho (X i) (Y i) ∪
          cleanedSide G rho (Y i) (X i))
        (cleanedSide G rho (X k) (Y k) ∪
          cleanedSide G rho (Y k) (X k)))
    (capacityA capacityB : ℕ) :
    ForestCapacityEmbeddingProperty P.cutForest G capacityA capacityB := by
  obtain ⟨f⟩ := exists_zhaoCutForestCopy_of_uniformPairs P G rootImage X Y
    hrootInjective hunif hrho hcapX hcapY hrootDegree hrootOutside hdisjoint
  intro _partA _partB _hcover _hA _hB
  exact ⟨f⟩

end Erdos547b.ZhaoStability

#print axioms Erdos547b.RegularPair.OrderedRootedForest.Embedding.toGraphCopy
#print axioms Erdos547b.TreePartition.ZhaoForestPartition.cutForestCopy
#print axioms Erdos547b.ZhaoStability.forestCapacityEmbeddingProperty_of_orderedForest_uniformPairs
#print axioms Erdos547b.ZhaoStability.forestCapacityEmbeddingProperty_of_cutForest_uniformPairs
#print axioms Erdos547b.ZhaoStability.exists_zhaoCutForestCopy_of_uniformPairs
#print axioms Erdos547b.ZhaoStability.forestCapacityEmbeddingProperty_of_zhaoCutForest_uniformPairs
