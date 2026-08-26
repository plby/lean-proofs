/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim616Lemma58Bridge
import ErdosProblems.Erdos547b.Claim616RootPartitions

/-!
# Concrete three-way lower-realization merge for Zhao Claim 6.16

This module specializes the generic root-dependent-reservoir merge to the
literal selected `F₀`, residual `F₁`, and minor `F_b` supports.  All three
lower branch realizations use one already-chosen map on the Zhao partition
roots.  No common root cluster, copy premise, or continuation is introduced.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoClaim616Lemma58Merge

open Finset SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoProp57
open Erdos547b.ZhaoClaim68BranchAdapter
open Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616ResidualAllocation
open Erdos547b.ZhaoClaim616RootPartitions
open Erdos547b.ZhaoClaim616RootPartitions.OrderedBranchForest
open Erdos547b.ZhaoClaim616Lemma58Bridge
open Erdos547b.ZhaoClaim616Lemma58Bridge.OrderedBranchForest
open Erdos547b.ZhaoLemma59Part2Full

universe u v

/-- Extend the coordinatewise A/B reservoir assignment to the reconstructed
branch-forest vertex type.  Only values at original roots are used by the
merge proof. -/
def vertexRootReservoir {r b : ℕ} {B : Type v}
    (F : OrderedBranchForest r b) (rootReservoir : Fin r → Finset B) :
    F.Vertex → Finset B
  | Sum.inl i => rootReservoir i
  | Sum.inr z => rootReservoir (F.owner z.1)

@[simp] theorem vertexRootReservoir_root {r b : ℕ} {B : Type v}
    (F : OrderedBranchForest r b) (rootReservoir : Fin r → Finset B)
    (i : Fin r) :
    vertexRootReservoir F rootReservoir (Sum.inl i) = rootReservoir i := rfl

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small target slack : ℕ}

/-- The actual lower realizations of `F₀`, `F₁`, and `F_b` merge into the
full reconstructed branch forest.  Isolated roots are handled by
`selected_F1_supportPartition`'s explicit `isolatedMajorRootIndices`; no
additional root-allocation premise is needed. -/
theorem exists_rootedTargetEmbedding_of_three_lower_realizations
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (G : SimpleGraph B)
    (rootImage : Fin P.numParts → B)
    (rootReservoir : Fin P.numParts → Finset B)
    (targetSelected targetF1 targetFb : Finset B)
    (hrootInjective : Function.Injective rootImage)
    (hrootMem : ∀ i, rootImage i ∈ rootReservoir i)
    (hrootSelected : ∀ i, Disjoint (rootReservoir i) targetSelected)
    (hrootF1 : ∀ i, Disjoint (rootReservoir i) targetF1)
    (hrootFb : ∀ i, Disjoint (rootReservoir i) targetFb)
    (hselectedF1 : Disjoint targetSelected targetF1)
    (hmajorFb : Disjoint (targetSelected ∪ targetF1) targetFb)
    (hSelected : Nonempty (SupportedRootEmbedding
      (branchForest P).graph G (branchForest P).roots
      (selectedSupport P S) targetSelected
      (ownerRootImage (branchForest P) rootImage)))
    (hF1 : Nonempty (SupportedRootEmbedding
      (branchForest P).graph G (branchForest P).roots
      (F1Support P S) targetF1
      (ownerRootImage (branchForest P) rootImage)))
    (hFb : Nonempty (SupportedRootEmbedding
      (branchForest P).graph G (branchForest P).roots
      (FbSupport P) targetFb
      (ownerRootImage (branchForest P) rootImage))) :
    Nonempty (RootedTargetEmbedding (branchForest P).graph G
      (branchForest P).roots
      ((targetSelected ∪ targetF1) ∪ targetFb)
      (ownerRootImage (branchForest P) rootImage)) := by
  obtain ⟨eSelected⟩ := hSelected
  obtain ⟨eF1⟩ := hF1
  obtain ⟨eFb⟩ := hFb
  have hrootInjectiveVertex :
      ∀ ⦃x y : (branchForest P).Vertex⦄,
        x ∈ (branchForest P).roots → y ∈ (branchForest P).roots →
        ownerRootImage (branchForest P) rootImage x =
          ownerRootImage (branchForest P) rootImage y → x = y := by
    intro x y hx hy hxy
    obtain ⟨i, rfl⟩ := ((branchForest P).mem_roots_iff x).mp hx
    obtain ⟨j, rfl⟩ := ((branchForest P).mem_roots_iff y).mp hy
    apply congrArg Sum.inl
    apply hrootInjective
    simpa using hxy
  have hrootMemVertex :
      ∀ ⦃x : (branchForest P).Vertex⦄,
        x ∈ (branchForest P).roots →
        ownerRootImage (branchForest P) rootImage x ∈
          vertexRootReservoir (branchForest P) rootReservoir x := by
    intro x hx
    obtain ⟨i, rfl⟩ := ((branchForest P).mem_roots_iff x).mp hx
    exact hrootMem i
  have hrootSelectedVertex :
      ∀ ⦃x : (branchForest P).Vertex⦄,
        x ∈ (branchForest P).roots →
        Disjoint (vertexRootReservoir (branchForest P) rootReservoir x)
          targetSelected := by
    intro x hx
    obtain ⟨i, rfl⟩ := ((branchForest P).mem_roots_iff x).mp hx
    exact hrootSelected i
  have hrootF1Vertex :
      ∀ ⦃x : (branchForest P).Vertex⦄,
        x ∈ (branchForest P).roots →
        Disjoint (vertexRootReservoir (branchForest P) rootReservoir x)
          targetF1 := by
    intro x hx
    obtain ⟨i, rfl⟩ := ((branchForest P).mem_roots_iff x).mp hx
    exact hrootF1 i
  have hrootFbVertex :
      ∀ ⦃x : (branchForest P).Vertex⦄,
        x ∈ (branchForest P).roots →
        Disjoint (vertexRootReservoir (branchForest P) rootReservoir x)
          targetFb := by
    intro x hx
    obtain ⟨i, rfl⟩ := ((branchForest P).mem_roots_iff x).mp hx
    exact hrootFb i
  exact merge_three_supportedRootEmbeddings_of_rootReservoir
    (branchForest P).graph G (branchForest P).roots
    (majorSupport P) (selectedSupport P S) (F1Support P S) (FbSupport P)
    targetSelected targetF1 targetFb
    (ownerRootImage (branchForest P) rootImage)
    (vertexRootReservoir (branchForest P) rootReservoir)
    (selected_F1_supportPartition P S) (major_Fb_rootPartition P)
    hrootInjectiveVertex hrootMemVertex hrootSelectedVertex hrootF1Vertex
    hrootFbVertex hselectedF1 hmajorFb eSelected eF1 eFb

/-- Copy-valued projection of the concrete three-way merge. -/
theorem exists_branchForestCopy_of_three_lower_realizations
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (G : SimpleGraph B)
    (rootImage : Fin P.numParts → B)
    (rootReservoir : Fin P.numParts → Finset B)
    (targetSelected targetF1 targetFb : Finset B)
    (hrootInjective : Function.Injective rootImage)
    (hrootMem : ∀ i, rootImage i ∈ rootReservoir i)
    (hrootSelected : ∀ i, Disjoint (rootReservoir i) targetSelected)
    (hrootF1 : ∀ i, Disjoint (rootReservoir i) targetF1)
    (hrootFb : ∀ i, Disjoint (rootReservoir i) targetFb)
    (hselectedF1 : Disjoint targetSelected targetF1)
    (hmajorFb : Disjoint (targetSelected ∪ targetF1) targetFb)
    (hSelected : Nonempty (SupportedRootEmbedding
      (branchForest P).graph G (branchForest P).roots
      (selectedSupport P S) targetSelected
      (ownerRootImage (branchForest P) rootImage)))
    (hF1 : Nonempty (SupportedRootEmbedding
      (branchForest P).graph G (branchForest P).roots
      (F1Support P S) targetF1
      (ownerRootImage (branchForest P) rootImage)))
    (hFb : Nonempty (SupportedRootEmbedding
      (branchForest P).graph G (branchForest P).roots
      (FbSupport P) targetFb
      (ownerRootImage (branchForest P) rootImage))) :
    Nonempty ((branchForest P).graph.Copy G) := by
  obtain ⟨E⟩ := exists_rootedTargetEmbedding_of_three_lower_realizations
    P S G rootImage rootReservoir targetSelected targetF1 targetFb
    hrootInjective hrootMem hrootSelected hrootF1 hrootFb hselectedF1
    hmajorFb hSelected hF1 hFb
  exact ⟨E.copy⟩

end Erdos547b.ZhaoClaim616Lemma58Merge

#print axioms Erdos547b.ZhaoClaim616Lemma58Merge.exists_rootedTargetEmbedding_of_three_lower_realizations
#print axioms Erdos547b.ZhaoClaim616Lemma58Merge.exists_branchForestCopy_of_three_lower_realizations
