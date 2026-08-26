/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim68
import ErdosProblems.Erdos547b.Lemma59
import ErdosProblems.Erdos547b.RegularPair
import ErdosProblems.Erdos547b.ForestMatching
import ErdosProblems.Erdos547b.ForestCapacity
import ErdosProblems.Erdos547b.Proposition57

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoLemma614Full

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition

universe u v

namespace ORF

open Erdos547b.RegularPair

/-- The literal roots in the sigma-type graph underlying an ordered forest. -/
def roots {m : ℕ} (F : OrderedRootedForest m) :
    Finset (Σ i, Fin (F.size i)) :=
  Finset.univ.image fun i ↦ ⟨i, F.root i⟩

/-- Union of all two-sided candidate slices used by an ordered forest. -/
def target {m : ℕ} {B : Type*} [DecidableEq B]
    (_F : OrderedRootedForest m) (candidate : Fin m → Fin 2 → Finset B) :
    Finset B :=
  Finset.univ.biUnion fun i ↦ candidate i 0 ∪ candidate i 1

end ORF

/-!
# Zhao's Lemma 6.14: concrete embedding conclusion

The arrows in the printed statement of Lemma 6.14 are *online rooted-forest
embeddings*, not mere numerical inequalities.  The last operation in both
parts of the proof is the same: the deleted root--parent edges are put back.
The first theorem below carries this operation out on the literal cut forest
from Definition 6.2.  In particular, its conclusion is a genuine Mathlib
`Copy T G`; no proposition-valued continuation or assumed embedding theorem
occurs in its hypotheses.
-/

/-- Reinsert the root--parent edges into an already embedded Zhao cut forest.
This is the graph-theoretic conclusion common to both parts of Zhao's Lemma
6.14 and to the invocation in Claim 6.16. -/
def copy_of_cutForestCopy_of_cutAdj
    {V : Type u} {B : Type v} [Fintype V] [DecidableEq V]
    {T : SimpleGraph V} [DecidableRel T.Adj]
    {globalRoot : V} {small : ℕ}
    (P : ZhaoForestPartition T globalRoot small)
    {G : SimpleGraph B}
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

/-- Proposition-valued spelling of the preceding explicit construction. -/
theorem isContained_of_cutForestCopy_of_cutAdj
    {V : Type u} {B : Type v} [Fintype V] [DecidableEq V]
    {T : SimpleGraph V} [DecidableRel T.Adj]
    {globalRoot : V} {small : ℕ}
    (P : ZhaoForestPartition T globalRoot small)
    {G : SimpleGraph B}
    (f : P.cutForest.Copy G)
    (hcut : ∀ j (hj : j.val ≠ 0),
      G.Adj (f (P.roots j)) (f (P.parent j hj))) :
    T.IsContained G :=
  (copy_of_cutForestCopy_of_cutAdj P f hcut).isContained

/-! ## Canonical coordinates of the cut forest -/

theorem fromOrderedForestVertex_injective
    {V : Type u} [Fintype V] [DecidableEq V]
    {T : SimpleGraph V} [DecidableRel T.Adj]
    {globalRoot : V} {small : ℕ}
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

@[simp] theorem cutForestCopy_apply
    {V : Type u} [Fintype V] [DecidableEq V]
    {T : SimpleGraph V} [DecidableRel T.Adj]
    {globalRoot : V} {small : ℕ}
    (P : ZhaoForestPartition T globalRoot small) (x : V) :
    P.cutForestCopy x = P.toOrderedForestVertex x := by
  apply fromOrderedForestVertex_injective P
  change P.fromOrderedForestVertex (P.cutForestHom x) =
    P.fromOrderedForestVertex (P.toOrderedForestVertex x)
  rw [P.from_cutForestHom, P.from_toOrderedForestVertex]

@[simp] theorem toOrderedForestVertex_root
    {V : Type u} [Fintype V] [DecidableEq V]
    {T : SimpleGraph V} [DecidableRel T.Adj]
    {globalRoot : V} {small : ℕ}
    (P : ZhaoForestPartition T globalRoot small) (i : Fin P.numParts) :
    P.toOrderedForestVertex (P.roots i) = ⟨i, P.orderedForest.root i⟩ := by
  apply fromOrderedForestVertex_injective P
  rw [P.from_toOrderedForestVertex]
  change P.roots i =
    (P.componentEquiv i
      ((P.componentEquiv i).symm ⟨P.roots i, P.root_mem i⟩)).1
  rw [Equiv.apply_symm_apply]

/-! ## Constructing the online arrow, rather than assuming it -/

/-- A checked uniform-pair construction of Zhao's online forest arrow.

For every injective assignment of the roots to `rootCluster`, this theorem
constructs a copy of the entire ordered forest with every non-root in its
assigned cleaned pair.  The bad-root set is empty here; hence this is stronger
than the negative-slack arrows used in Lemma 6.14.  Most importantly, the
online/flexible object is *constructed* from cardinal and regularity
hypotheses rather than accepted as an embedding continuation.
-/
theorem exists_flexibleEmbedding_of_uniformPairs
    {m : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : Erdos547b.RegularPair.OrderedRootedForest m)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rootCluster : Finset B) {rho : ℝ}
    (X Y : Fin m → Finset B)
    (hunif : ∀ i, G.IsUniform rho (X i) (Y i)) (hrho : rho ≤ 1)
    (hcapX : ∀ i, (F.size i : ℝ) + rho * #(X i) ≤
      (G.edgeDensity (X i) (Y i) - rho) * #(X i))
    (hcapY : ∀ i, (F.size i : ℝ) + rho * #(Y i) ≤
      (G.edgeDensity (X i) (Y i) - rho) * #(Y i))
    (hrootDegree : ∀ i z, z ∈ rootCluster →
      (F.size i : ℝ) + rho * #(Y i) ≤
        (#((Y i).filter (G.Adj z)) : ℝ))
    (hrootOutside : ∀ z ∈ rootCluster, ∀ i,
      z ∉ Erdos547b.RegularPair.cleanedSide G rho (X i) (Y i) ∧
      z ∉ Erdos547b.RegularPair.cleanedSide G rho (Y i) (X i))
    (hdisjoint : ∀ i k, i ≠ k →
      Disjoint
        (Erdos547b.RegularPair.cleanedSide G rho (X i) (Y i) ∪
          Erdos547b.RegularPair.cleanedSide G rho (Y i) (X i))
        (Erdos547b.RegularPair.cleanedSide G rho (X k) (Y k) ∪
          Erdos547b.RegularPair.cleanedSide G rho (Y k) (X k))) :
    Nonempty (Erdos547b.ZhaoProp57.FlexibleEmbedding
      F.graph G (ORF.roots F) rootCluster
      (ORF.target F (fun i c ↦ if c = 0 then
        Erdos547b.RegularPair.cleanedSide G rho (X i) (Y i)
      else Erdos547b.RegularPair.cleanedSide G rho (Y i) (X i))) 0) := by
  classical
  let candidate : Fin m → Fin 2 → Finset B := fun i c ↦ if c = 0 then
    Erdos547b.RegularPair.cleanedSide G rho (X i) (Y i)
    else Erdos547b.RegularPair.cleanedSide G rho (Y i) (X i)
  refine ⟨
    { bad := fun _ ↦ ∅
      bad_subset := by intro; exact Finset.empty_subset _
      card_bad := by simp
      realize := ?_ }⟩
  intro rootMap hrootMapInj hrootMapMem _hrootGood
  let rootImage : Fin m → B := fun i ↦ rootMap ⟨i, F.root i⟩
  have hriInj : Function.Injective rootImage := by
    intro i j hij
    have hsigma : (⟨i, F.root i⟩ : Σ i, Fin (F.size i)) =
        ⟨j, F.root j⟩ := by
      apply hrootMapInj
      · exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
      · exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
      · exact hij
    exact Sigma.mk.inj_iff.mp hsigma |>.1
  have hriMem (i : Fin m) : rootImage i ∈ rootCluster := by
    apply hrootMapMem
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  obtain ⟨E, hEroot, hEmem⟩ :=
    F.exists_embedding_over_disjoint_uniform_pairs G rootImage X Y
      hriInj hunif hrho hcapX hcapY
      (fun i ↦ hrootDegree i (rootImage i) (hriMem i))
      (fun i k ↦ hrootOutside (rootImage i) (hriMem i) k) hdisjoint
  refine ⟨
    { copy := E.toGraphCopy
      map_root := ?_
      map_nonroot := ?_ }⟩
  · intro r hr
    obtain ⟨i, -, hir⟩ := Finset.mem_image.mp hr
    subst r
    change E.copy i (F.root i) = rootMap ⟨i, F.root i⟩
    exact hEroot i
  · rintro ⟨i, a⟩ hnotroot
    have ha : a ≠ F.root i := by
      intro ha
      apply hnotroot
      subst a
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    have hm := hEmem i a ha
    apply Finset.mem_biUnion.mpr
    refine ⟨i, Finset.mem_univ _, ?_⟩
    by_cases hc : (F.isTree i).coloringTwoOfVert (F.root i) a = 0
    · apply Finset.mem_union_left
      change E.copy i a ∈ Erdos547b.RegularPair.cleanedSide G rho (X i) (Y i)
      simpa [candidate, hc] using hm
    · apply Finset.mem_union_right
      change E.copy i a ∈ Erdos547b.RegularPair.cleanedSide G rho (Y i) (X i)
      simpa [candidate, hc] using hm

/-! ## The regular-pair realization used by both parts -/

/-- Full, no-oracle embedding conclusion of Lemma 6.14.

The regular-pair hypotheses are exactly the finite pointwise conditions used
by the checked ordered-forest theorem.  The last two hypotheses are not an
embedding interface: they are ordinary adjacency statements.  They say that
whichever of the two explicitly displayed cleaned sides contains a parent,
that vertex is adjacent to the prescribed image of the child-component root.
Thus every edge removed in Definition 6.2 is restored below.
-/
theorem lemma6_14_of_uniformPairs
    {V : Type u} {B : Type v} [Fintype V] [DecidableEq V]
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
            Erdos547b.RegularPair.cleanedSide G rho
              (X p.1) (Y p.1)
          else
            Erdos547b.RegularPair.cleanedSide G rho
              (Y p.1) (X p.1)) →
        G.Adj z (rootImage j)) :
    T.IsContained G := by
  obtain ⟨E, hEroot, hEmem⟩ :=
    P.orderedForest.exists_embedding_over_disjoint_uniform_pairs
      G rootImage X Y hrootInjective hunif hrho hcapX hcapY hrootDegree
        hrootOutside hdisjoint
  let f : P.cutForest.Copy G := E.toGraphCopy.comp P.cutForestCopy
  have hf_apply (x : V) :
      f x = E.copy (P.toOrderedForestVertex x).1
        (P.toOrderedForestVertex x).2 := by
    change E.toGraphCopy (P.cutForestCopy x) = _
    rw [cutForestCopy_apply]
    rfl
  have hf_root (i : Fin P.numParts) : f (P.roots i) = rootImage i := by
    rw [hf_apply, toOrderedForestVertex_root]
    exact hEroot i
  apply isContained_of_cutForestCopy_of_cutAdj P f
  intro j hj
  rw [hf_root]
  rw [hf_apply]
  let p := P.toOrderedForestVertex (P.parent j hj)
  by_cases hp : p.2 = P.orderedForest.root p.1
  · rw [hp, hEroot]
    exact (hrootParentAdj j hj) hp |>.symm
  · have hm := hEmem p.1 p.2 hp
    exact (hsideParentAdj j hj) hp _ hm |>.symm

/-! ## The two concrete local constructors used in the source proof -/

/-- Zhao Lemma 5.9(2), in the precise three-layer form used to construct
the root-subforest in Claim 6.16.  Unlike the paper's arrow notation, the
conclusion exposes the actual copy and all three placement assertions. -/
theorem exists_threeLayerRootSubforestCopy
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (F : SimpleGraph A) (G : SimpleGraph B) [DecidableRel G.Adj]
    (roots special : Finset A)
    (hforest : (Erdos547b.ZhaoLemma59.rootedForestCone F roots).IsTree)
    (level : A → ℕ) (hrootLevel : ∀ a ∈ roots, level a = 0)
    (hspecialOdd : ∀ a ∈ special, level a % 2 = 1)
    (A0 C0 M0 : Finset B)
    (hsize : Fintype.card A + 1 ≤ #A0)
    (hcross : ∀ ⦃a b⦄, F.Adj a b →
      ∀ z ∈ (if a ∈ roots then A0
          else if level a = 1 ∨ a ∈ special then C0 else M0),
        Fintype.card A + 1 ≤
          #{w ∈ (if b ∈ roots then A0
            else if level b = 1 ∨ b ∈ special then C0 else M0) |
              G.Adj z w}) :
    ∃ f : F.Copy G,
      (∀ a ∈ roots, f a ∈ A0) ∧
      (∀ a, level a = 1 ∨ a ∈ special → f a ∈ C0) ∧
      (∀ a, a ∉ roots → level a ≠ 1 → a ∉ special → f a ∈ M0) := by
  exact Erdos547b.ZhaoLemma59.lemma5_9_three_layer_candidate_core
    F G roots special hforest level hrootLevel hspecialOdd A0 C0 M0
      hsize hcross

/-- The finite matching-capacity allocation step used in both parts of
Lemma 6.14.  This is the actual bin-packing theorem, not a proposition-valued
"if an allocation exists then embed" continuation. -/
theorem exists_matchingAllocation
    {ι κ : Type*} [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (items : Finset ι) (weight : ι → ℕ) (capacity : κ → ℕ) (slack : ℕ)
    (hsmall : ∀ i ∈ items, weight i ≤ slack)
    (hbudget : (∑ i ∈ items, weight i) + Fintype.card κ * slack ≤
      ∑ j : κ, capacity j) :
    ∃ assign : ι → κ, ∀ j : κ,
      ∑ i ∈ items.filter (assign · = j), weight i ≤ capacity j := by
  exact Erdos547b.ForestMatching.capacity_packing
    items weight capacity slack hsmall hbudget

/-! ## The two displayed residual-capacity calculations in Lemma 6.14 -/

/-- Part 1, equation (6.18): the saving in the exceptional root-subforest
leaves enough `A`-capacity for the rest of that side.  The hierarchy use is
exposed as its exact finite inequality. -/
theorem partOne_remaining_A_capacity
    {E : Type*} [DecidableEq E]
    (M M0 : Finset E) (a : E → ℝ)
    (n f0 f1 eta gamma dSqrt : ℝ)
    (hM0 : M0 ⊆ M)
    (hM : (1 - 10 * dSqrt) * n ≤ ∑ e ∈ M, a e)
    (hM0upper : ∑ e ∈ M0, a e ≤ f0 - eta ^ 3 * n)
    (hforest : f0 + f1 ≤ n)
    (hhierarchy : 10 * dSqrt * n + 3 * gamma * n ≤ eta ^ 3 * n) :
    f1 + 3 * gamma * n ≤ ∑ e ∈ M \ M0, a e := by
  have hsplit := Finset.sum_sdiff hM0 (f := a)
  linarith

/-- Part 2, first paragraph: `deg(A,M_in) ≥ (1-ε1)n` together
with the `ε2 n` saving in `F0` leaves enough capacity for `F1`. -/
theorem partTwo_remaining_A_capacity
    {E : Type*} [DecidableEq E]
    (Min M0 : Finset E) (a : E → ℝ)
    (n f0 f1 epsilon1 epsilon2 gamma : ℝ)
    (hn : 0 ≤ n)
    (hM0 : M0 ⊆ Min)
    (hMin : (1 - epsilon1) * n ≤ ∑ e ∈ Min, a e)
    (hM0upper : ∑ e ∈ M0, a e ≤ f0 - epsilon2 * n)
    (hforest : f0 + f1 ≤ n)
    (hhierarchy : 3 * gamma ≤ epsilon2 - epsilon1) :
    f1 + 3 * gamma * n ≤ ∑ e ∈ Min \ M0, a e := by
  have hsplit := Finset.sum_sdiff hM0 (f := a)
  nlinarith

/-- The leaf-completion alternative that occurs at the start of Claim 6.8
and is reused when a Lemma-6.14 allocation leaves precisely the level-one
leaves unembedded.  The result is again an actual containment conclusion. -/
theorem isContained_of_leafCompletionCertificate
    {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {T : SimpleGraph A} {G : SimpleGraph B} [DecidableRel G.Adj]
    {W : Finset A}
    (C : Erdos547b.ZhaoClaim68.LeafCompletionCertificate T G W) :
    T.IsContained G :=
  C.isContained

end Erdos547b.ZhaoLemma614Full

#print axioms Erdos547b.ZhaoLemma614Full.copy_of_cutForestCopy_of_cutAdj
#print axioms Erdos547b.ZhaoLemma614Full.isContained_of_cutForestCopy_of_cutAdj
#print axioms Erdos547b.ZhaoLemma614Full.exists_flexibleEmbedding_of_uniformPairs
#print axioms Erdos547b.ZhaoLemma614Full.lemma6_14_of_uniformPairs
#print axioms Erdos547b.ZhaoLemma614Full.exists_threeLayerRootSubforestCopy
#print axioms Erdos547b.ZhaoLemma614Full.exists_matchingAllocation
#print axioms Erdos547b.ZhaoLemma614Full.partOne_remaining_A_capacity
#print axioms Erdos547b.ZhaoLemma614Full.partTwo_remaining_A_capacity
#print axioms Erdos547b.ZhaoLemma614Full.isContained_of_leafCompletionCertificate
