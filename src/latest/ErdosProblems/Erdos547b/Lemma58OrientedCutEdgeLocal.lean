/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma58OrientedCutForestReconstruction
import ErdosProblems.Erdos547b.Lemma58CanonicalThresholdStep

/-!
# Edge-local cleaning for literal oriented cut parents

The global deleted set on an endpoint contains only roots whose literal cut
parent is assigned to that endpoint.  The canonical threshold constructor
then returns a certified embedding with the precomputed orientation.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoLemma58OrientedCutEdgeLocal

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.RegularPair
open Erdos547b.ZhaoClaim68
open Erdos547b.ZhaoClaim68BranchAdapter
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616HierarchyClassification
open Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma58MatchingAssembly
open Erdos547b.ZhaoLemma58OwnerForbiddenCertificate
open Erdos547b.ZhaoLemma58CutForestReconstruction
open Erdos547b.ZhaoLemma58OrientedCutForestReconstruction
open Erdos547b.ZhaoLemma58OwnerLocalStep
open Erdos547b.ZhaoLemma58CanonicalThresholdStep

universe u v

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small : ℕ}

/-- The exact endpoint-level union of all orientation-sensitive cut-parent
bad sets. -/
def orientedGlobalCutParentBad
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rootImage : Fin P.numParts → B)
    {k : ℕ}
    (assign : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B)
    (orient : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin 2 ≃ Fin 2)
    (e : Fin k) (c : Fin 2) : Finset B :=
  (endpoint e c).filter fun x ↦
    ∃ j : Fin P.numParts, ∃ hj : j.val ≠ 0,
      ∃ hnonroot : P.parent j hj ∉ partitionRoots P,
        let z := literalBranchCoordinate P (P.parent j hj) hnonroot
        assign z.1 = e ∧
          orient z.1
              ((branchForest P).branches.isTree z.1 |>.coloringTwoOfVert
                ((branchForest P).branches.root z.1) z.2) = c ∧
          ¬ G.Adj (rootImage j) x

@[simp] theorem mem_orientedGlobalCutParentBad
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rootImage : Fin P.numParts → B)
    {k : ℕ}
    (assign : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B)
    (orient : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin 2 ≃ Fin 2)
    (e : Fin k) (c : Fin 2) (x : B) :
    x ∈ orientedGlobalCutParentBad P G rootImage assign endpoint orient e c ↔
      x ∈ endpoint e c ∧
      ∃ j : Fin P.numParts, ∃ hj : j.val ≠ 0,
        ∃ hnonroot : P.parent j hj ∉ partitionRoots P,
          let z := literalBranchCoordinate P (P.parent j hj) hnonroot
          assign z.1 = e ∧
            orient z.1
                ((branchForest P).branches.isTree z.1 |>.coloringTwoOfVert
                  ((branchForest P).branches.root z.1) z.2) = c ∧
            ¬ G.Adj (rootImage j) x := by
  rw [orientedGlobalCutParentBad, Finset.mem_filter]

theorem orientedCutParentBad_subset_global
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rootImage : Fin P.numParts → B)
    {k : ℕ}
    (assign : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B)
    (orient : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin 2 ≃ Fin 2)
    (e : Fin k) (q : Fin P.numParts) (c : Fin 2) :
    orientedCutParentBad P G rootImage assign endpoint orient e q c ⊆
      orientedGlobalCutParentBad P G rootImage assign endpoint orient e c := by
  intro x hx
  obtain ⟨hxEndpoint, j, hj, hnonroot, _howner, hedge, hside, hnonadj⟩ :=
    (mem_orientedCutParentBad P G rootImage assign endpoint orient
      e q c x).mp hx
  exact (mem_orientedGlobalCutParentBad P G rootImage assign endpoint orient
    e c x).mpr ⟨hxEndpoint, j, hj, hnonroot, hedge, hside, hnonadj⟩

/-- Local fiber orientation obtained by restricting a literal global branch
orientation. -/
def restrictedOrient
    {b k : ℕ} (assign : Fin b → Fin k)
    (orient : Fin b → Fin 2 ≃ Fin 2) (e : Fin k) :
    Fin (matchingFiber assign e).card → Fin 2 ≃ Fin 2 :=
  fun i ↦ orient (OrderedBranchForest.selectedEquiv
    (matchingFiber assign e) i)

/-- A canonical threshold step, cleaned by a global bad set, gives a
certified local embedding with exactly the prescribed restricted
orientation. -/
theorem exists_certifiedOwnerDynamicEmbedding_of_canonicalThreshold
    {b r : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (externalParent : Fin b → B)
    (whole endpoint : Fin 2 → Finset B)
    (owner : Fin b → Fin r)
    (bad : Fin r → Fin 2 → Finset B)
    (globalBad : Fin 2 → Finset B)
    (rho density : ℝ)
    (D : ActualThresholdStepData F G externalParent whole
      (fun c ↦ endpoint c \ globalBad c) rho density)
    (expected : Fin b → Fin 2 ≃ Fin 2)
    (horient : canonicalStepOrientation F G externalParent whole
      (fun c ↦ endpoint c \ globalBad c) rho density D = expected)
    (hbadGlobal : ∀ q c, bad q c ⊆ globalBad c) :
    Nonempty {E : CertifiedOwnerDynamicEmbedding F G externalParent endpoint
        owner bad // E.orient = expected} := by
  obtain ⟨E⟩ :=
    Erdos547b.ZhaoLemma58CanonicalThresholdStep.ActualThresholdStepData.realize_canonical
      F G externalParent whole (fun c ↦ endpoint c \ globalBad c)
      rho density D
  let Ewide : DynamicAttachedForestEmbedding F G externalParent
      (canonicalStepOrientation F G externalParent whole
        (fun c ↦ endpoint c \ globalBad c) rho density D) endpoint := {
    embedding := E.embedding
    attach := E.attach
    map_side := by
      intro i a
      exact (Finset.mem_sdiff.mp (E.map_side i a)).1
  }
  let Ecert : CertifiedOwnerDynamicEmbedding F G externalParent endpoint
      owner bad := {
    orient := canonicalStepOrientation F G externalParent whole
      (fun c ↦ endpoint c \ globalBad c) rho density D
    embedding := Ewide
    avoids := by
      intro i a
      have hm := E.map_side i a
      have hnotGlobal := (Finset.mem_sdiff.mp hm).2
      exact fun hbad ↦ hnotGlobal (hbadGlobal (owner i) _ hbad)
  }
  exact ⟨⟨Ecert, horient⟩⟩

end Erdos547b.ZhaoLemma58OrientedCutEdgeLocal

#print axioms Erdos547b.ZhaoLemma58OrientedCutEdgeLocal.exists_certifiedOwnerDynamicEmbedding_of_canonicalThreshold
