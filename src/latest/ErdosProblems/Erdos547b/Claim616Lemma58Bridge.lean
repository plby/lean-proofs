/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim616RootPartitions
import ErdosProblems.Erdos547b.Lemma58GroupedSmallForest

/-!
# Lower Lemma 5.8 output as a supported Claim-6.16 branch embedding

The grouped Lemma-5.8 backend returns an actual
`RootAttachedBranchEmbedding`; it does not choose roots from one common host
cluster.  This is exactly the lower endpoint needed by Claim 6.16: all three
branch families use one already-chosen, parity-aware root map.

This file first forgets a full `RootedTargetEmbedding` outside an arbitrary
support, and then transports the result from `F.restrict s` to the literal
support in `F`.  No copy or containment certificate is supplied by the
caller.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoClaim616Lemma58Bridge

open Finset SimpleGraph
open Erdos547b.ZhaoProp57
open Erdos547b.ZhaoLemma59Part2Full
open Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest
open Erdos547b.ZhaoClaim616RootPartitions
open Erdos547b.ZhaoClaim616RootPartitions.OrderedBranchForest
open Erdos547b.ZhaoLemma58GroupedSmallForest

universe u v

/-- Forget a full rooted-target embedding outside `support`, and retarget
its total root-map function when the two maps agree on supported roots. -/
def supportedRootEmbeddingOfRootedTargetEmbedding
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (F : SimpleGraph A) (G : SimpleGraph B)
    (roots support : Finset A) (target : Finset B)
    (realizedRootImage rootImage : A → B)
    (E : RootedTargetEmbedding F G roots target realizedRootImage)
    (hroot : ∀ ⦃x : A⦄, x ∈ roots → x ∈ support →
      realizedRootImage x = rootImage x) :
    SupportedRootEmbedding F G roots support target rootImage where
  toFun := E.copy
  map_adj := by
    intro x y hxy _ _
    exact E.copy.toHom.map_rel hxy
  injOn := by
    intro x y _ _ hxy
    exact E.copy.injective hxy
  map_root := by
    intro x hxRoot hxSupport
    rw [E.map_root hxRoot]
    exact hroot hxRoot hxSupport
  map_nonroot := by
    intro x _ hxRoot
    exact E.map_nonroot hxRoot

namespace OrderedBranchForest

variable {r b : ℕ}

/-- Canonical total vertex map induced by a shared map on original roots.
Only its values on `Sum.inl` are semantically used as root images; the owner
value on branch coordinates makes the function independent of an embedding
result. -/
def ownerRootImage {B : Type v} (F : OrderedBranchForest r b)
    (rootImage : Fin r → B) : F.Vertex → B
  | Sum.inl q => rootImage q
  | Sum.inr z => rootImage (F.owner z.1)

@[simp] theorem ownerRootImage_root {B : Type v}
    (F : OrderedBranchForest r b) (rootImage : Fin r → B) (q : Fin r) :
    ownerRootImage F rootImage (Sum.inl q) = rootImage q := rfl

/-- Convert one actual lower Lemma-5.8 branch realization on a reindexed
restriction into the literal supported embedding used by the Claim-6.16
three-way merge. -/
noncomputable def supportedRootEmbeddingOfRootAttachedRestrict
    {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (s : Finset (Fin b))
    (q : Finset (Fin r)) (G : SimpleGraph B)
    (rootImage : Fin r → B)
    (endpoint : Fin s.card → Fin 2 → Finset B)
    (orient : Fin s.card → Fin 2 ≃ Fin 2)
    (target : Finset B)
    (E : RootAttachedBranchEmbedding (F.restrict s) G rootImage endpoint orient)
    (hendpoint : ∀ i c, endpoint i c ⊆ target)
    (hrootInjective : Function.Injective rootImage)
    (hrootOutside : ∀ i j c, rootImage i ∉ endpoint j c) :
    SupportedRootEmbedding F.graph G F.roots
      (rootedBranchSupport F q s) target (ownerRootImage F rootImage) := by
  have hrootOutsideCopy : ∀ i j a,
      rootImage i ≠ E.branchEmbedding.copy j a := by
    intro i j a heq
    have hmem := E.map_branch j a
    exact hrootOutside i j
      (orient j (((F.restrict s).branches.isTree j).coloringTwoOfVert
        ((F.restrict s).branches.root j) a)) (heq ▸ hmem)
  let realizedRootImage : (F.restrict s).Vertex → B := fun x =>
    match x with
    | Sum.inl i => rootImage i
    | Sum.inr z => E.branchEmbedding.copy z.1 z.2
  let full : RootedTargetEmbedding (F.restrict s).graph G
      (F.restrict s).roots target realizedRootImage :=
    E.toRootedTargetEmbedding (F.restrict s) G rootImage endpoint orient
      target hendpoint hrootInjective hrootOutsideCopy
  let restrictedRootImage : (F.restrict s).Vertex → B := fun x =>
    ownerRootImage F rootImage
      (Erdos547b.ZhaoClaim616RootPartitions.OrderedBranchForest.restrictVertexMap
        F s x)
  let partial : SupportedRootEmbedding (F.restrict s).graph G
      (F.restrict s).roots
      (rootedBranchSupport (F.restrict s) q Finset.univ)
      target restrictedRootImage :=
    supportedRootEmbeddingOfRootedTargetEmbedding
      (F.restrict s).graph G (F.restrict s).roots
      (rootedBranchSupport (F.restrict s) q Finset.univ)
      target realizedRootImage restrictedRootImage full (by
        intro x hxRoot _
        obtain ⟨i, rfl⟩ := ((F.restrict s).mem_roots_iff x).mp hxRoot
        rfl)
  exact Erdos547b.ZhaoClaim616RootPartitions.OrderedBranchForest.supportedRootEmbeddingOfRestrict
    F s q G (ownerRootImage F rootImage) target partial

/-- Existential composition form matching the output convention of the
lower grouped Lemma-5.8 theorem. -/
theorem exists_supportedRootEmbedding_of_rootAttachedRestrict
    {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (s : Finset (Fin b))
    (q : Finset (Fin r)) (G : SimpleGraph B)
    (rootImage : Fin r → B)
    (endpoint : Fin s.card → Fin 2 → Finset B)
    (orient : Fin s.card → Fin 2 ≃ Fin 2)
    (target : Finset B)
    (hE : Nonempty
      (RootAttachedBranchEmbedding (F.restrict s) G rootImage endpoint orient))
    (hendpoint : ∀ i c, endpoint i c ⊆ target)
    (hrootInjective : Function.Injective rootImage)
    (hrootOutside : ∀ i j c, rootImage i ∉ endpoint j c) :
    Nonempty (SupportedRootEmbedding F.graph G F.roots
      (rootedBranchSupport F q s) target (ownerRootImage F rootImage)) := by
  obtain ⟨E⟩ := hE
  exact ⟨supportedRootEmbeddingOfRootAttachedRestrict
    F s q G rootImage endpoint orient target E hendpoint hrootInjective
      hrootOutside⟩

end OrderedBranchForest

end Erdos547b.ZhaoClaim616Lemma58Bridge

#print axioms Erdos547b.ZhaoClaim616Lemma58Bridge.OrderedBranchForest.supportedRootEmbeddingOfRootAttachedRestrict
#print axioms Erdos547b.ZhaoClaim616Lemma58Bridge.OrderedBranchForest.exists_supportedRootEmbedding_of_rootAttachedRestrict
