/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichGlobalRootSidePlan
import ErdosProblems.Erdos547b.Lemma58GlobalFixedOrientationPlan

/-!
# Mixed fixed/Appendix target plans

The Part-3 recursion uses adaptive orientations only on exceptional physical
edges.  On every ordinary edge, the complete-fiber Part-1 orientation is
fixed once and must remain fixed in all earlier owner batches.  This module
records that distinction directly in the coordinate-side plan.  Root
cleaning is unchanged because it reads coordinate sides only at literal cut
parents, where the maximal physical root-side set is retained.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim615RichPartThreeTargetPlan

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest
open Erdos547b.ZhaoClaim615SourceSelection
open Erdos547b.ZhaoClaim615CoordinateSourceAllocation
open Erdos547b.ZhaoClaim615RichHierarchicalAllocation
open Erdos547b.ZhaoClaim615RichPhysicalEdgeFamilies
open Erdos547b.ZhaoClaim615RichPhysicalMatching
open Erdos547b.ZhaoClaim615RichDynamicApplication
open Erdos547b.ZhaoClaim615RichDynamicHostLayout
open Erdos547b.ZhaoClaim615RichCoordinatePairFacts
open Erdos547b.ZhaoClaim615RichDynamicRootTargetPlan
open Erdos547b.ZhaoClaim615RichDynamicPlannedRootCleaning
open Erdos547b.ZhaoClaim615RichGlobalRootSidePlan
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoLemma58GlobalFixedOrientationPlan
open Erdos547b.ZhaoLemma58GlobalOwnerOnlineState
open Erdos547b.ZhaoLemma58GlobalPlannedOnlineState
open Erdos547b.ZhaoLemma58MatchingAssembly
open Erdos547b.ZhaoLemma58DynamicBatchAppend

universe u v w

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small : ℕ}

variable {Bv : Type v} {I : Type w}
variable [Fintype Bv] [DecidableEq Bv] [Fintype I] [DecidableEq I]
variable (Pcluster : ClusterAssignment Bv I)
variable (Gdegree : SimpleGraph Bv) [DecidableRel Gdegree.Adj]
variable (threshold quota : ℕ)
variable (R : SimpleGraph I) [DecidableRel R.Adj]
variable (miss : ℕ)
variable
  (Q : RichClaim61Certificate Pcluster Gdegree threshold quota R
    (largeClustersAtLeast Pcluster Gdegree threshold quota) miss)
variable (sourceDensity : EvenPadding I → EvenPadding I → ℝ)

variable {L : Finset (EvenPadding I)} {eta N targetB cap : ℝ}
variable {which : ExceptionalCase} {count cardBound : ℕ}
variable (E0 : SelectedExceptionalEdges Q sourceDensity L eta which count)
variable
  (Mb : PreliminaryReservedEdges Q sourceDensity L N targetB cap cardBound)

variable (P : ZhaoForestPartition T globalRoot small)
variable {available : Finset
  (ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)} {target slack : ℕ}
variable (S : SelectedF0 P available target slack)
variable {cap0 : K0 Q sourceDensity E0 → ℕ}
variable {cap1 : K1 Q sourceDensity E0 Mb → ℕ}
variable {capb : Kb Q sourceDensity Mb → ℕ}
variable
  (A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb cap0 cap1 capb)

/-- Root sides remain maximal.  Adaptive edges retain their full admissible
side set, while ordinary edges retain exactly the side prescribed by the
complete-fiber orientation at every coordinate, including cut parents. -/
noncomputable def partThreeRootTargetPlan
    (Dside : PhysicalRootSidePlan Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb)
    (orient : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P →
      Fin 2 ≃ Fin 2)
    (adaptive : PhysicalIndex Q sourceDensity E0 Mb → Prop) : RootTargetPlan P := by
  classical
  let assign := richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
    (threshold := threshold) (quota := quota) (R := R) (miss := miss)
    (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
    (P := P) (S := S) (A := A)
  refine {
    branchRootSides := fun j ↦ Dside.sides (assign j)
    coordinateSides := ?_
  }
  intro z
  exact if adaptive (assign z.1) then Dside.sides (assign z.1)
    else {globalFixedCoordinateSide (branchForest P) assign orient z}

@[simp] theorem partThreeRootTargetPlan_branchRootSides
    (Dside : PhysicalRootSidePlan Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb)
    (orient : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P →
      Fin 2 ≃ Fin 2)
    (adaptive : PhysicalIndex Q sourceDensity E0 Mb → Prop)
    (j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P) :
    (partThreeRootTargetPlan Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A Dside orient adaptive).branchRootSides j =
      Dside.sides (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A) j) := rfl

theorem partThreeRootTargetPlan_coordinateSides_adaptive
    (Dside : PhysicalRootSidePlan Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb)
    (orient : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P →
      Fin 2 ≃ Fin 2)
    (adaptive : PhysicalIndex Q sourceDensity E0 Mb → Prop)
    (z : Σ j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P,
      Fin ((branchForest P).branches.size j))
    (hz : adaptive (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
      (threshold := threshold) (quota := quota) (R := R) (miss := miss)
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A) z.1)) :
    (partThreeRootTargetPlan Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A Dside orient adaptive).coordinateSides z =
      Dside.sides (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A) z.1) := by
  simp only [partThreeRootTargetPlan, hz, if_true]

theorem partThreeRootTargetPlan_coordinateSides_fixed
    (Dside : PhysicalRootSidePlan Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb)
    (orient : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P →
      Fin 2 ≃ Fin 2)
    (adaptive : PhysicalIndex Q sourceDensity E0 Mb → Prop)
    (z : Σ j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P,
      Fin ((branchForest P).branches.size j))
    (hadaptive : ¬ adaptive (richAssign (Pcluster := Pcluster)
      (Gdegree := Gdegree) (threshold := threshold) (quota := quota) (R := R)
      (miss := miss) (Q := Q) (sourceDensity := sourceDensity) (E0 := E0)
      (Mb := Mb) (P := P) (S := S) (A := A) z.1)) :
    (partThreeRootTargetPlan Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A Dside orient adaptive).coordinateSides z =
      {globalFixedCoordinateSide (branchForest P)
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A)) orient z} := by
  simp only [partThreeRootTargetPlan, hadaptive, if_false]

/-- The mixed plan asks for no root-cleaning target beyond the maximal
physical root-side plan.  On an ordinary cut coordinate, admissibility of the
fixed side follows from the cut-parent parity theorem. -/
theorem richPlannedRootTargets_partThree_subset_rootSide
    (hT : T.IsTree)
    (Dside : PhysicalRootSidePlan Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb)
    (orient : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P →
      Fin 2 ≃ Fin 2)
    (adaptive : PhysicalIndex Q sourceDensity E0 Mb → Prop)
    (hroot : ∀ j, orient j 0 ∈ Dside.sides
      (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A) j))
    (q : Fin P.numParts) :
    richPlannedRootTargets Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A
          (partThreeRootTargetPlan Pcluster Gdegree threshold quota R miss Q
            sourceDensity E0 Mb P S A Dside orient adaptive) q ⊆
      richPlannedRootTargets Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A
          (richRootSideTargetPlan Pcluster Gdegree threshold quota R miss Q
            sourceDensity E0 Mb P S A Dside) q := by
  classical
  have howned :
      plannedOwnedBranchTargets Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A
            (partThreeRootTargetPlan Pcluster Gdegree threshold quota R miss Q
              sourceDensity E0 Mb P S A Dside orient adaptive) q =
        plannedOwnedBranchTargets Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A
            (richRootSideTargetPlan Pcluster Gdegree threshold quota R miss Q
              sourceDensity E0 Mb P S A Dside) q := by
    rfl
  have hcut :
      plannedNonrootCutParentTargets Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A
            (partThreeRootTargetPlan Pcluster Gdegree threshold quota R miss Q
              sourceDensity E0 Mb P S A Dside orient adaptive) q ⊆
        plannedNonrootCutParentTargets Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A
            (richRootSideTargetPlan Pcluster Gdegree threshold quota R miss Q
              sourceDensity E0 Mb P S A Dside) q := by
    unfold plannedNonrootCutParentTargets
    split <;> rename_i hq
    · intro t ht
      obtain ⟨z, hz, ht⟩ := Finset.mem_biUnion.mp ht
      apply Finset.mem_biUnion.mpr
      refine ⟨z, hz, ?_⟩
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp ht
      apply Finset.mem_image.mpr
      refine ⟨c, ?_, rfl⟩
      have hzcut : isCutParentCoordinate P z :=
        ⟨q, hq, (Finset.mem_filter.mp hz).2⟩
      by_cases ha : adaptive (richAssign (Pcluster := Pcluster)
          (Gdegree := Gdegree) (threshold := threshold) (quota := quota)
          (R := R) (miss := miss) (Q := Q) (sourceDensity := sourceDensity)
          (E0 := E0) (Mb := Mb) (P := P) (S := S) (A := A) z.1)
      · simpa only [partThreeRootTargetPlan, ha, if_true,
          richRootSideTargetPlan, hzcut, if_true] using hc
      · have hfixed : c = globalFixedCoordinateSide (branchForest P)
            (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
              (threshold := threshold) (quota := quota) (R := R)
              (miss := miss) (Q := Q) (sourceDensity := sourceDensity)
              (E0 := E0) (Mb := Mb) (P := P) (S := S) (A := A)) orient z := by
          simpa only [partThreeRootTargetPlan, ha, if_false,
            Finset.mem_singleton] using hc
        rw [hfixed]
        simpa only [globalFixedCoordinateSide, richRootSideTargetPlan, hzcut,
          if_true] using
          orientation_coordinate_mem_rootSidePlan Pcluster Gdegree threshold
            quota R miss Q sourceDensity E0 Mb P S A hT Dside orient hroot z
    · simp
  unfold richPlannedRootTargets
  rw [howned]
  intro t ht
  rw [Finset.mem_insert] at ht ⊢
  rcases ht with rfl | ht
  · exact Or.inl rfl
  · exact Or.inr ((Finset.union_subset_union_right hcut) ht)

/-- The maximal root-side cleaning certificate transports to the mixed plan:
the latter has a subset of the old targets, hence no larger rounded loss. -/
theorem rootCleaningFactsOfPartThreeTargetPlan
    (hT : T.IsTree)
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rootRho rootDensity : ℝ)
    (H : ReducedPairRealization Pcluster R G rootRho rootDensity)
    (Dside : PhysicalRootSidePlan Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb)
    (orient : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P →
      Fin 2 ≃ Fin 2)
    (adaptive : PhysicalIndex Q sourceDensity E0 Mb → Prop)
    (hrootRho : 0 ≤ rootRho)
    (hroot : ∀ j, orient j 0 ∈ Dside.sides
      (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A) j))
    (F : RichPlannedRootCleaningFacts Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A G rootRho rootDensity H
        (richRootSideTargetPlan Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A Dside)) :
    RichPlannedRootCleaningFacts Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A G rootRho rootDensity H
        (partThreeRootTargetPlan Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A Dside orient adaptive) := by
  let oldPlan := richRootSideTargetPlan Pcluster Gdegree threshold quota R miss
    Q sourceDensity E0 Mb P S A Dside
  let newPlan := partThreeRootTargetPlan Pcluster Gdegree threshold quota R miss
    Q sourceDensity E0 Mb P S A Dside orient adaptive
  have htargets : ∀ q,
      richPlannedRootTargets Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A newPlan q ⊆
        richPlannedRootTargets Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A oldPlan q := by
    intro q
    exact richPlannedRootTargets_partThree_subset_rootSide Pcluster Gdegree
      threshold quota R miss Q sourceDensity E0 Mb P S A hT Dside orient
      adaptive hroot q
  have hloss : ∀ q,
      richPlannedRootLoss Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A rootRho newPlan q ≤
        richPlannedRootLoss Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A rootRho oldPlan q := by
    intro q
    unfold richPlannedRootLoss
    apply Nat.ceil_mono
    apply mul_le_mul_of_nonneg_right
    · exact_mod_cast Finset.card_le_card (htargets q)
    · exact mul_nonneg hrootRho (Nat.cast_nonneg _)
  refine {
    pair_adj := ?_
    root_large := F.root_large
    target_large := ?_
    root_budget := ?_
    root_link_margin := ?_
  }
  · intro q t ht
    apply F.pair_adj q t
    exact htargets q ht
  · intro q t ht
    apply F.target_large q t
    exact htargets q ht
  · intro q
    exact (Nat.add_le_add_left (hloss q) P.numParts).trans (F.root_budget q)
  · intro j hj hroot
    have hlossReal :
        (richPlannedRootLoss Pcluster Gdegree threshold quota R miss Q
            sourceDensity E0 Mb P S A rootRho newPlan j : ℝ) ≤
          richPlannedRootLoss Pcluster Gdegree threshold quota R miss Q
            sourceDensity E0 Mb P S A rootRho oldPlan j := by
      exact_mod_cast hloss j
    have hbase := F.root_link_margin j hj hroot
    linarith

private theorem fiberCoordinateSide_eq_fixed_of_eq
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    {k : ℕ}
    (assign : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P → Fin k)
    (endpoint : Fin k → Fin 2 → Finset Bv)
    (rootCandidate : Fin P.numParts → Finset Bv)
    (orient : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P →
      Fin 2 ≃ Fin 2)
    (n : ℕ)
    (state : OnlineOwnerPrefixState (branchForest P) G assign endpoint
      rootCandidate n)
    (e : Fin k) (j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)
    (hj : assign j = e) (a : Fin ((branchForest P).branches.size j))
    (hside : onlineCoordinateSide P G assign endpoint rootCandidate n state j a =
      globalFixedCoordinateSide (branchForest P) assign orient ⟨j, a⟩) :
    ((state.edgeState e).orient (fiberIndex assign e j hj))
        ((onlineFiberForest (branchForest P) assign e).isTree
            (fiberIndex assign e j hj) |>.coloringTwoOfVert
          ((onlineFiberForest (branchForest P) assign e).root
            (fiberIndex assign e j hj))
          (fiberVertex (branchForest P) assign e j hj a)) =
      orient j (((branchForest P).branches.isTree j).coloringTwoOfVert
        ((branchForest P).branches.root j) a) := by
  subst e
  convert hside using 1
  all_goals
    simp only [onlineCoordinateSide, globalFixedCoordinateSide, fiberIndex,
      fiberVertex, assignmentIndex, assignmentVertex]
    try rfl

/-- On an ordinary physical edge the mixed plan forces every processed
coordinate to use the global complete-fiber orientation.  Consequently the
literal used set of the reparented synchronized state is bounded by the exact
fixed prefix load, even though other physical edges may be adaptive. -/
theorem PlannedCutOnlineOwnerPrefixState.card_reparented_used_le_partThreeFixedPrefix
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (Dside : PhysicalRootSidePlan Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb)
    (orient : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P →
      Fin 2 ≃ Fin 2)
    (adaptive : PhysicalIndex Q sourceDensity E0 Mb → Prop)
    (endpoint : PhysicalIndex Q sourceDensity E0 Mb → Fin 2 → Finset Bv)
    (rootCandidate : Fin P.numParts → Finset Bv)
    (n : ℕ) (hn : n < P.numParts)
    (state : PlannedCutOnlineOwnerPrefixState P G
      (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A)) endpoint rootCandidate
      (partThreeRootTargetPlan Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A Dside orient adaptive).coordinateSides n)
    (z : Bv) (e : PhysicalIndex Q sourceDensity E0 Mb)
    (hadaptive : ¬ adaptive e) (c : Fin 2) :
    #((reparentedEdgeState (branchForest P) G
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A)) endpoint rootCandidate n hn
        state.state.state z e).used c) ≤
      globalFixedPrefixLoad (branchForest P)
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A)) orient e n c := by
  classical
  let assign := richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
    (threshold := threshold) (quota := quota) (R := R) (miss := miss)
    (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
    (P := P) (S := S) (A := A)
  change #((state.state.state.edgeState e).used c) ≤ _
  apply card_edgeState_used_le_fixedPrefixLoad_of_orient_eq
  intro i hi a
  let fiberEquiv := OrderedBranchForest.selectedEquiv (matchingFiber assign e)
  obtain ⟨sj, hisj⟩ := fiberEquiv.symm.surjective i
  subst i
  let j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P := sj.1
  have hjassign : assign j = e := by
    exact (mem_matchingFiber assign e j).mp sj.2
  have howner : ((branchForest P).owner j).val < n := by
    simpa only [assign, onlineFiberOwner, fiberEquiv,
      Equiv.apply_symm_apply, j]
      using (Finset.mem_filter.mp hi).2
  let aGlobal : Fin ((branchForest P).branches.size j) :=
    ⟨a.val, by
      simpa only [assign, onlineFiberForest, OrderedBranchForest.restrict_size,
        fiberEquiv, Equiv.apply_symm_apply, j] using a.isLt⟩
  have hindex : fiberIndex assign e j hjassign = fiberEquiv.symm sj := by
    apply (OrderedBranchForest.selectedEquiv (matchingFiber assign e)).injective
    apply Subtype.ext
    simp only [fiberIndex, Equiv.apply_symm_apply, fiberEquiv, j]
  have hcolor := fiberVertex_coloring (branchForest P) assign e j hjassign aGlobal
  have hmem := state.coordinate_side_mem j howner aGlobal
  have hnot : ¬ adaptive (assign j) := by simpa only [hjassign] using hadaptive
  have hside : onlineCoordinateSide P G assign endpoint rootCandidate n
      state.state.state j aGlobal =
        globalFixedCoordinateSide (branchForest P) assign orient ⟨j, aGlobal⟩ := by
    apply Finset.mem_singleton.mp
    simpa only [assign, partThreeRootTargetPlan, hnot, if_false] using hmem
  have hside' :
      ((state.state.state.edgeState e).orient (fiberIndex assign e j hjassign))
          ((onlineFiberForest (branchForest P) assign e).isTree
              (fiberIndex assign e j hjassign) |>.coloringTwoOfVert
            ((onlineFiberForest (branchForest P) assign e).root
              (fiberIndex assign e j hjassign))
            (fiberVertex (branchForest P) assign e j hjassign aGlobal)) =
        orient j (((branchForest P).branches.isTree j).coloringTwoOfVert
          ((branchForest P).branches.root j) aGlobal) := by
    exact fiberCoordinateSide_eq_fixed_of_eq P G assign endpoint rootCandidate
      orient n state.state.state e j hjassign aGlobal hside
  have htargetColor :
      ((onlineFiberForest (branchForest P) assign e).isTree
          (fiberEquiv.symm sj) |>.coloringTwoOfVert
        ((onlineFiberForest (branchForest P) assign e).root
          (fiberEquiv.symm sj)) a) =
      ((onlineFiberForest (branchForest P) assign e).isTree
          (fiberIndex assign e j hjassign) |>.coloringTwoOfVert
        ((onlineFiberForest (branchForest P) assign e).root
          (fiberIndex assign e j hjassign))
        (fiberVertex (branchForest P) assign e j hjassign aGlobal)) := by
    apply onlineFiber_coloring_eq_of_index_eq (branchForest P) assign e
      (fiberEquiv.symm sj) (fiberIndex assign e j hjassign) hindex.symm
    rfl
  have hlocalColor := htargetColor.trans hcolor
  have horient := congrArg (state.state.state.edgeState e).orient hindex
  calc
    ((state.state.state.edgeState e).orient (fiberEquiv.symm sj))
        ((onlineFiberForest (branchForest P) assign e).isTree
          (fiberEquiv.symm sj) |>.coloringTwoOfVert
          ((onlineFiberForest (branchForest P) assign e).root
            (fiberEquiv.symm sj)) a) =
      ((state.state.state.edgeState e).orient
        (fiberIndex assign e j hjassign))
        ((onlineFiberForest (branchForest P) assign e).isTree
          (fiberEquiv.symm sj) |>.coloringTwoOfVert
          ((onlineFiberForest (branchForest P) assign e).root
            (fiberEquiv.symm sj)) a) := by rw [horient]
    _ = ((state.state.state.edgeState e).orient
        (fiberIndex assign e j hjassign))
        ((onlineFiberForest (branchForest P) assign e).isTree
          (fiberIndex assign e j hjassign) |>.coloringTwoOfVert
          ((onlineFiberForest (branchForest P) assign e).root
            (fiberIndex assign e j hjassign))
          (fiberVertex (branchForest P) assign e j hjassign aGlobal)) := by
      exact congrArg _ htargetColor
    _ = orient j (((branchForest P).branches.isTree j).coloringTwoOfVert
        ((branchForest P).branches.root j) aGlobal) := hside'
    _ = (globalFixedFiberOrientation (branchForest P) assign orient e
        (fiberEquiv.symm sj))
        ((onlineFiberForest (branchForest P) assign e).isTree
          (fiberEquiv.symm sj) |>.coloringTwoOfVert
          ((onlineFiberForest (branchForest P) assign e).root
            (fiberEquiv.symm sj)) a) := by
      rw [hlocalColor]
      simp only [globalFixedFiberOrientation, fiberEquiv,
        Equiv.apply_symm_apply, j]

end Erdos547b.ZhaoClaim615RichPartThreeTargetPlan

#print axioms Erdos547b.ZhaoClaim615RichPartThreeTargetPlan.richPlannedRootTargets_partThree_subset_rootSide
#print axioms Erdos547b.ZhaoClaim615RichPartThreeTargetPlan.rootCleaningFactsOfPartThreeTargetPlan
#print axioms Erdos547b.ZhaoClaim615RichPartThreeTargetPlan.PlannedCutOnlineOwnerPrefixState.card_reparented_used_le_partThreeFixedPrefix
