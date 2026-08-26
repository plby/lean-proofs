/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma58CombinedResidual
import ErdosProblems.Erdos547b.Lemma58CutForestReconstruction

/-!
# Edge-local realization alternatives for the cut-aware Lemma 5.8 backend

Parts 1 and 2 orient the complete forest assigned to one matching edge at
once.  Splitting such an edge by outer-tree owner would incorrectly repay the
edge capacity for every owner.  We therefore clean that full edge fiber by
the union of all cut-parent bad sets and invoke one concrete local step.

Part 3 genuinely chooses an Appendix orientation separately below each outer
root, so it retains the checked owner-by-owner recursion.  `CutEdgeLocalData`
packages precisely these two alternatives.  Its realization theorem returns
the common certified object used by matching-fiber assembly, but neither
constructor contains an embedding or copy result.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoLemma58CutEdgeLocal

open Finset Fintype SimpleGraph
open Erdos547b.RegularPair
open Erdos547b.TreePartition
open Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma58DynamicBatchAppend
open Erdos547b.ZhaoLemma58ChosenOwnerBatches
open Erdos547b.ZhaoLemma58OwnerLocalStep
open Erdos547b.ZhaoLemma58OwnerForbidden
open Erdos547b.ZhaoLemma58OwnerForbiddenCertificate
open Erdos547b.ZhaoLemma58CutForestReconstruction
open Erdos547b.ZhaoLemma54ThresholdOrientation
open Erdos547b.ZhaoLemma54ThresholdNumerics

universe u v

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small : ℕ}

/-- All endpoint vertices which fail one of the internal cut-parent
adjacencies, independent of the owner of the current branch. -/
def globalCutParentBad
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rootImage : Fin P.numParts → B)
    {k : ℕ} (endpoint : Fin k → Fin 2 → Finset B)
    (e : Fin k) (c : Fin 2) : Finset B :=
  (endpoint e c).filter fun x ↦
    ∃ j : CutIndex P,
      P.parent j.1 j.2 ≠ P.roots (P.parentPart j.1 j.2) ∧
      ¬ G.Adj (rootImage j.1) x

@[simp] theorem mem_globalCutParentBad
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rootImage : Fin P.numParts → B)
    {k : ℕ} (endpoint : Fin k → Fin 2 → Finset B)
    (e : Fin k) (c : Fin 2) (x : B) :
    x ∈ globalCutParentBad P G rootImage endpoint e c ↔
      x ∈ endpoint e c ∧
      ∃ j : CutIndex P,
        P.parent j.1 j.2 ≠ P.roots (P.parentPart j.1 j.2) ∧
        ¬ G.Adj (rootImage j.1) x := by
  simp [globalCutParentBad]

theorem cutParentBad_subset_global
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rootImage : Fin P.numParts → B)
    {k : ℕ} (endpoint : Fin k → Fin 2 → Finset B)
    (e : Fin k) (q : Fin P.numParts) (c : Fin 2) :
    cutParentBad P G rootImage endpoint e q c ⊆
      globalCutParentBad P G rootImage endpoint e c := by
  intro x hx
  obtain ⟨hxEndpoint, j, hj, _howner, hnonroot, hnonadj⟩ :=
    (mem_cutParentBad P G rootImage endpoint e q c x).mp hx
  have hnonroot' :
      P.parent j hj ≠ P.roots (P.parentPart j hj) := by
    rw [_howner]
    exact hnonroot
  exact (mem_globalCutParentBad P G rootImage endpoint e c x).mpr
    ⟨hxEndpoint, ⟨⟨j, hj⟩, by simpa using hnonroot', hnonadj⟩⟩

/-- The global bad set is covered by one non-neighbour set for every cut
index. -/
theorem card_globalCutParentBad_le_numParts_mul
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rootImage : Fin P.numParts → B)
    {k : ℕ} (endpoint : Fin k → Fin 2 → Finset B)
    (e : Fin k) (c : Fin 2) (loss : ℕ)
    (htypical : ∀ j : CutIndex P,
      #(cutRootNonneighbors P G rootImage endpoint e c j) ≤ loss) :
    #(globalCutParentBad P G rootImage endpoint e c) ≤
      P.numParts * loss := by
  classical
  have hsub : globalCutParentBad P G rootImage endpoint e c ⊆
      (Finset.univ : Finset (CutIndex P)).biUnion
        (cutRootNonneighbors P G rootImage endpoint e c) := by
    intro x hx
    obtain ⟨hxEndpoint, j, _hnonroot, hnonadj⟩ :=
      (mem_globalCutParentBad P G rootImage endpoint e c x).mp hx
    apply Finset.mem_biUnion.mpr
    refine ⟨j, Finset.mem_univ _, ?_⟩
    exact Finset.mem_filter.mpr ⟨hxEndpoint, hnonadj⟩
  calc
    #(globalCutParentBad P G rootImage endpoint e c) ≤
        #((Finset.univ : Finset (CutIndex P)).biUnion
          (cutRootNonneighbors P G rootImage endpoint e c)) :=
      Finset.card_le_card hsub
    _ ≤ ∑ j : CutIndex P,
        #(cutRootNonneighbors P G rootImage endpoint e c j) := by
      simpa only [Finset.sum_attach, Finset.sum_filter] using
        (Finset.card_biUnion_le
          (s := (Finset.univ : Finset (CutIndex P)))
          (t := cutRootNonneighbors P G rootImage endpoint e c))
    _ ≤ ∑ _j : CutIndex P, loss := by
      exact Finset.sum_le_sum fun j _ ↦ htypical j
    _ = Fintype.card (CutIndex P) * loss := by simp
    _ ≤ P.numParts * loss := by
      apply Nat.mul_le_mul_right loss
      calc
        Fintype.card (CutIndex P) ≤ Fintype.card (Fin P.numParts) :=
          Fintype.card_le_of_injective Subtype.val Subtype.val_injective
        _ = P.numParts := Fintype.card_fin _

/-- Canonical scalar loss used by a full-fiber Parts-1/2 invocation. -/
def globalCutLossBound
    (P : ZhaoForestPartition T globalRoot small)
    (permanentBound rootLoss : Fin 2 → ℕ) (c : Fin 2) : ℕ :=
  permanentBound c + P.numParts * rootLoss c

/-- Permanent endpoint removal plus global cut-parent cleaning is bounded by
the canonical full-fiber loss. -/
theorem card_combinedDeleted_global_le
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rootImage : Fin P.numParts → B)
    {k : ℕ} (whole endpoint : Fin k → Fin 2 → Finset B)
    (e : Fin k) (permanentBound rootLoss : Fin 2 → ℕ)
    (hpermanent : ∀ c,
      #(whole e c \ endpoint e c) ≤ permanentBound c)
    (htypical : ∀ c (j : CutIndex P),
      #(cutRootNonneighbors P G rootImage endpoint e c j) ≤ rootLoss c)
    (c : Fin 2) :
    #(Erdos547b.ZhaoLemma58CombinedResidual.combinedDeleted
        (whole e) (endpoint e) (fun _ ↦ ∅)
        (globalCutParentBad P G rootImage endpoint e) c) ≤
      globalCutLossBound P permanentBound rootLoss c := by
  have hused (d : Fin 2) : #((∅ : Finset B)) ≤ 0 := by simp
  have hbad (d : Fin 2) :
      #(globalCutParentBad P G rootImage endpoint e d) ≤
        P.numParts * rootLoss d :=
    card_globalCutParentBad_le_numParts_mul P G rootImage endpoint e d
      (rootLoss d) (htypical d)
  have h :=
    Erdos547b.ZhaoLemma58CombinedResidual.card_combinedDeleted_le_of_bounds
      (whole e) (endpoint e) (fun _ ↦ (∅ : Finset B))
      (globalCutParentBad P G rootImage endpoint e)
      permanentBound (fun _ ↦ 0) (fun d ↦ P.numParts * rootLoss d)
      hpermanent hused hbad c
  simpa only [globalCutLossBound, Nat.add_zero] using h

/-- The two source-faithful ways to realize one matching-edge fiber. -/
inductive CutEdgeLocalData
    {b r : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (F : OrderedRootedForest b)
    (Gpair Gtarget : SimpleGraph B)
    [DecidableRel Gpair.Adj] [DecidableRel Gtarget.Adj]
    (externalParent : Fin b → B)
    (whole endpoint : Fin 2 → Finset B)
    (owner : Fin b → Fin r)
    (bad : Fin r → Fin 2 → Finset B)
    (globalBad : Fin 2 → Finset B)
    (rho density : ℝ) : Type (max 0 v)
  /-- Parts 1/2: one orientation and one capacity payment for the whole
  matching-edge fiber. -/
  | global : OwnerLocalStepData F Gpair externalParent whole
      (fun c ↦ endpoint c \ globalBad c) rho density →
      CutEdgeLocalData P F Gpair Gtarget externalParent whole endpoint owner
        bad globalBad rho density
  /-- Part 3: separate adaptive Appendix choices below each outer root. -/
  | owners :
      (∀ n (hn : n < r)
        (Eprefix : ChosenPartialDynamicEmbedding F Gpair externalParent
          endpoint (ownerPrefix Finset.univ owner n)),
        Nonempty (OwnerLocalStepData
          (selectedForest F
            (ownerBatch Finset.univ owner ⟨n, hn⟩)) Gpair
          (fun i ↦ externalParent
            (Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest.selectedEquiv
              (ownerBatch Finset.univ owner ⟨n, hn⟩) i))
          whole
          (ownerCleanedLive (fun c ↦ endpoint c \ Eprefix.used c)
            (bad ⟨n, hn⟩)) rho density)) →
      CutEdgeLocalData P F Gpair Gtarget externalParent whole endpoint owner
        bad globalBad rho density

/-- Build the full-fiber Parts-1/2 alternative from exact combined-deletion
bounds.  There is no previous owner image in this branch: the full edge fiber
is oriented and embedded in one invocation, so only permanent endpoint
removal and the global cut-parent bad set are charged. -/
noncomputable def CutEdgeLocalData.thresholdOfCombinedBounds
    {b r : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (F : OrderedRootedForest b)
    (Gpair Gtarget : SimpleGraph B)
    [DecidableRel Gpair.Adj] [DecidableRel Gtarget.Adj]
    (externalParent : Fin b → B)
    (whole endpoint : Fin 2 → Finset B)
    (owner : Fin b → Fin r)
    (bad : Fin r → Fin 2 → Finset B)
    (globalBad : Fin 2 → Finset B)
    (rho density ratio dx dy gamma epsilon N : ℝ) (slack : ℕ)
    (lowSide highSide : Fin 2)
    (Dsource : Erdos547b.ZhaoLemma54ThresholdSourceNumerics.ClassifiedThresholdOwnerNumerics
      F ratio dx dy gamma epsilon N slack)
    (hsides : highSide ≠ lowSide)
    (hendpoint : ∀ c, endpoint c ⊆ whole c)
    (hglobalSub : ∀ c, globalBad c ⊆ endpoint c)
    (hunif : Gpair.IsUniform rho (whole 0) (whole 1))
    (hwholeDisjoint : Disjoint (whole 0) (whole 1))
    (hdensity : density ≤ Gpair.edgeDensity (whole 0) (whole 1))
    (hfactor : 0 ≤ density - rho)
    (lossBound : Fin 2 → ℕ)
    (hloss : ∀ c,
      #(Erdos547b.ZhaoLemma58CombinedResidual.combinedDeleted whole endpoint
          (fun _ ↦ ∅) globalBad c) ≤ lossBound c)
    (htotal : ∀ c,
      lossBound c +
          Erdos547b.ZhaoLemma54ThresholdSourceNumerics.thresholdHighBudget
            dy gamma N +
          Erdos547b.ZhaoLemma54ThresholdSourceNumerics.thresholdReserve
            rho #(whole c) ≤ #(whole c))
    (heligible : ∀ i c,
      lossBound c +
          (1 +
            Erdos547b.ZhaoLemma54ThresholdSourceNumerics.thresholdReserve
              rho #(whole c) +
            Erdos547b.ZhaoLemma58ThresholdResidualCapacity.thresholdNeed
              (Erdos547b.ZhaoLemma54ThresholdSourceNumerics.thresholdLowBudget
                dx gamma N)
              (Erdos547b.ZhaoLemma54ThresholdSourceNumerics.thresholdHighBudget
                dy gamma N) lowSide c) ≤
        #((whole c).filter (Gpair.Adj (externalParent i))))
    (hcomponent : ∀ i c,
      (F.size i : ℝ) + rho * (#(whole c) : ℝ) + 1 ≤
        (density - rho) *
          ((#(whole c) : ℝ) - lossBound c -
            Erdos547b.ZhaoLemma54ThresholdSourceNumerics.thresholdHighBudget
              dy gamma N)) :
    CutEdgeLocalData P F Gpair Gtarget externalParent whole endpoint owner
      bad globalBad rho density := by
  let D :=
    Erdos547b.ZhaoLemma58CombinedResidual.thresholdOwnerLocalStepDataOfCombinedBounds
      F Gpair externalParent whole endpoint (fun _ ↦ ∅) globalBad rho density
      ratio dx dy gamma epsilon N slack lowSide highSide Dsource hsides
      hendpoint (fun _ ↦ Finset.empty_subset _) hglobalSub hunif
      hwholeDisjoint hdensity hfactor lossBound hloss htotal heligible
      hcomponent
  apply CutEdgeLocalData.global
  change OwnerLocalStepData F Gpair externalParent whole
    (ownerCleanedLive endpoint globalBad) rho density
  simpa only [Finset.sdiff_empty] using D

/-- Canonical maximal-cutoff form of `thresholdOfCombinedBounds`.  Its
parent-degree premise ranges only over the endpoint actually chosen for each
branch root, so it remains applicable when the unused low endpoint has zero
source density. -/
noncomputable def CutEdgeLocalData.thresholdOfCanonicalCombinedBounds
    {b r : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (F : OrderedRootedForest b)
    (Gpair Gtarget : SimpleGraph B)
    [DecidableRel Gpair.Adj] [DecidableRel Gtarget.Adj]
    (externalParent : Fin b → B)
    (whole endpoint : Fin 2 → Finset B)
    (owner : Fin b → Fin r)
    (bad : Fin r → Fin 2 → Finset B)
    (globalBad : Fin 2 → Finset B)
    (rho density ratio dx dy gamma epsilon N : ℝ) (slack : ℕ)
    (lowSide highSide : Fin 2)
    (Dsource : Erdos547b.ZhaoLemma54ThresholdSourceNumerics.ClassifiedThresholdOwnerNumerics
      F ratio dx dy gamma epsilon N slack)
    (hsides : highSide ≠ lowSide)
    (hendpoint : ∀ c, endpoint c ⊆ whole c)
    (hglobalSub : ∀ c, globalBad c ⊆ endpoint c)
    (hunif : Gpair.IsUniform rho (whole 0) (whole 1))
    (hwholeDisjoint : Disjoint (whole 0) (whole 1))
    (hdensity : density ≤ Gpair.edgeDensity (whole 0) (whole 1))
    (hfactor : 0 ≤ density - rho)
    (lossBound : Fin 2 → ℕ)
    (hloss : ∀ c,
      #(Erdos547b.ZhaoLemma58CombinedResidual.combinedDeleted whole endpoint
          (fun _ ↦ ∅) globalBad c) ≤ lossBound c)
    (htotal : ∀ c,
      lossBound c +
          Erdos547b.ZhaoLemma54ThresholdSourceNumerics.thresholdHighBudget
            dy gamma N +
          Erdos547b.ZhaoLemma54ThresholdSourceNumerics.thresholdReserve
            rho #(whole c) ≤ #(whole c))
    (heligible : ∀ (base : Fin b → Fin 2 ≃ Fin 2)
      (hbase : ∀ t c,
        2 * sideLoadPrefix F base t c ≤ prefixOrder F t + slack),
      let O := actualThresholdSwitchOrientation F slack
        (Erdos547b.ZhaoLemma54ThresholdSourceNumerics.thresholdLowBudget
          dx gamma N)
        (Erdos547b.ZhaoLemma54ThresholdSourceNumerics.thresholdHighBudget
          dy gamma N)
        lowSide highSide Dsource.small hsides
        (Dsource.suffix_display highSide) base hbase
      ∀ i,
        let c := branchRootSide F O.orient i
        lossBound c +
            (1 +
              Erdos547b.ZhaoLemma54ThresholdSourceNumerics.thresholdReserve
                rho #(whole c) +
              sideLoadBefore F O.orient i c) ≤
          #((whole c).filter (Gpair.Adj (externalParent i))))
    (hcomponent : ∀ i c,
      (F.size i : ℝ) + rho * (#(whole c) : ℝ) + 1 ≤
        (density - rho) *
          ((#(whole c) : ℝ) - lossBound c -
            Erdos547b.ZhaoLemma54ThresholdSourceNumerics.thresholdHighBudget
              dy gamma N)) :
    CutEdgeLocalData P F Gpair Gtarget externalParent whole endpoint owner
      bad globalBad rho density := by
  let D :=
    Erdos547b.ZhaoLemma58CombinedResidual.thresholdOwnerLocalStepDataOfCanonicalCombinedBounds
      F Gpair externalParent whole endpoint (fun _ ↦ ∅) globalBad rho density
      ratio dx dy gamma epsilon N slack lowSide highSide Dsource hsides
      hendpoint (fun _ ↦ Finset.empty_subset _) hglobalSub hunif
      hwholeDisjoint hdensity hfactor lossBound hloss htotal heligible
      hcomponent
  apply CutEdgeLocalData.global
  change OwnerLocalStepData F Gpair externalParent whole
    (ownerCleanedLive endpoint globalBad) rho density
  simpa only [Finset.sdiff_empty] using D

/-- Realize either local-data alternative and retain the owner-specific bad
avoidance needed by cut reconstruction. -/
theorem CutEdgeLocalData.realize
    {b r : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (F : OrderedRootedForest b)
    (Gpair Gtarget : SimpleGraph B)
    [DecidableRel Gpair.Adj] [DecidableRel Gtarget.Adj]
    (externalParent : Fin b → B)
    (whole endpoint : Fin 2 → Finset B)
    (owner : Fin b → Fin r)
    (bad : Fin r → Fin 2 → Finset B)
    (globalBad : Fin 2 → Finset B)
    (rho density : ℝ)
    (hendpoint : ∀ c, endpoint c ⊆ whole c)
    (hwholeDisjoint : Disjoint (whole 0) (whole 1))
    (hbadGlobal : ∀ q c, bad q c ⊆ globalBad c)
    (D : CutEdgeLocalData P F Gpair Gtarget externalParent whole endpoint
      owner bad globalBad rho density) :
    Nonempty (CertifiedOwnerDynamicEmbedding
      F Gpair externalParent endpoint owner bad) := by
  classical
  cases D with
  | global D =>
      obtain ⟨orient, ⟨E⟩⟩ := D.realize F Gpair externalParent whole
        (fun c ↦ endpoint c \ globalBad c) rho density
      let Ewide : DynamicAttachedForestEmbedding F Gpair externalParent
          orient endpoint := {
        embedding := E.embedding
        attach := E.attach
        map_side := by
          intro i a
          exact (Finset.mem_sdiff.mp (E.map_side i a)).1
      }
      refine ⟨{
        orient := orient
        embedding := Ewide
        avoids := ?_
      }⟩
      intro i a
      have hm := E.map_side i a
      have hnotGlobal := (Finset.mem_sdiff.mp hm).2
      exact fun hbad ↦ hnotGlobal (hbadGlobal (owner i) _ hbad)
  | owners hdata =>
      exact exists_certifiedDynamicEmbedding_of_ownerLocalStepsWithForbidden
        F Gpair externalParent whole endpoint hendpoint hwholeDisjoint owner
        rho density bad hdata

end Erdos547b.ZhaoLemma58CutEdgeLocal

#print axioms Erdos547b.ZhaoLemma58CutEdgeLocal.CutEdgeLocalData.realize
#print axioms Erdos547b.ZhaoLemma58CutEdgeLocal.CutEdgeLocalData.thresholdOfCanonicalCombinedBounds
