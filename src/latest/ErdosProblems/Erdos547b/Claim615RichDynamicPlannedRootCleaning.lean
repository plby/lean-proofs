/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichDynamicRootTargetPlan
import ErdosProblems.Erdos547b.Claim615RichDynamicRootCleaning

/-!
# Regularity cleaning for fixed/adaptive root-target plans

Before a Lemma 5.8 fiber is realized, a threshold fiber already has a fixed
root side while an Appendix fiber may still choose either side.  The target
list in `Claim615RichDynamicRootTargetPlan` records exactly that distinction.
This module proves the corresponding regularity union bound without choosing
the adaptive orientations and without deleting non-neighbours of a fixed
root from an entire matching endpoint.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim615RichDynamicPlannedRootCleaning

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoRoundedScales
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoClaim616HierarchyAttachments
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoClaim615SourceSelection
open Erdos547b.ZhaoClaim615CoordinateSourceAllocation
open Erdos547b.ZhaoClaim615RichHierarchicalAllocation
open Erdos547b.ZhaoClaim615RichPhysicalEdgeFamilies
open Erdos547b.ZhaoClaim615RichPhysicalMatching
open Erdos547b.ZhaoClaim615RichDynamicHostLayout
open Erdos547b.ZhaoClaim615RichDynamicApplication
open Erdos547b.ZhaoClaim615RichDynamicRootLayout
open Erdos547b.ZhaoClaim615RichDynamicRootTargets
open Erdos547b.ZhaoClaim615RichDynamicRootTargetPlan
open Erdos547b.ZhaoClaim615RichDynamicRootCleaning
open Erdos547b.ZhaoClaim615RichCoordinatePairFacts
open Erdos547b.ZhaoLemma58RootCandidateCleaning
open Erdos547b.ZhaoLemma58RootSkeleton

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
variable
  (E0 : SelectedExceptionalEdges Q sourceDensity L eta which count)
variable
  (Mb : PreliminaryReservedEdges Q sourceDensity L N targetB cap cardBound)

variable (P : ZhaoForestPartition T globalRoot small)
variable {available : Finset
  (ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)}
variable {target slack : ℕ}
variable (S : SelectedF0 P available target slack)
variable {cap0 : K0 Q sourceDensity E0 → ℕ}
variable {cap1 : K1 Q sourceDensity E0 Mb → ℕ}
variable {capb : Kb Q sourceDensity Mb → ℕ}
variable
  (A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb
    cap0 cap1 capb)

/-- Upward-rounded regularity loss for the fixed/adaptive target plan of one
distinguished root. -/
def richPlannedRootLoss
    (rho : ℝ) (plan : RootTargetPlan P) (q : Fin P.numParts) : ℕ :=
  upperScale
    ((#(richPlannedRootTargets Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A plan q) : ℝ) *
      (rho * #(rootWhole Pcluster Gdegree threshold quota R miss Q P q)))

/-- Honest reduced-pair and scalar facts for cleaning every planned target.
The record does not choose an orientation for adaptive fibers. -/
structure RichPlannedRootCleaningFacts
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rho density : ℝ)
    (H : ReducedPairRealization Pcluster R G rho density)
    (plan : RootTargetPlan P) : Prop where
  pair_adj : ∀ q t,
    t ∈ richPlannedRootTargets Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A plan q →
    (padGraph R).Adj
      (richRootCluster Pcluster Gdegree threshold quota R miss Q P q)
      (richTargetCluster Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb t)
  root_large : ∀ q,
    rho * #(rootWhole Pcluster Gdegree threshold quota R miss Q P q) ≤ quota
  target_large : ∀ q t,
    t ∈ richPlannedRootTargets Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A plan q →
    rho * #(richTargetWhole Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb t) ≤
      #(richTargetRaw Pcluster Gdegree threshold quota R miss Q sourceDensity
        E0 Mb t)
  root_budget : ∀ q,
    P.numParts + richPlannedRootLoss Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A rho plan q ≤ quota
  root_link_margin : ∀ j (hj : j.val ≠ 0)
    (_hroot : P.parent j hj = P.roots (P.parentPart j hj)),
    (P.numParts : ℝ) +
        richPlannedRootLoss Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A rho plan j ≤
      (density - rho) * quota

/-- Planned targets are reduced-adjacent when every allowed physical side is
adjacent at its actual owner and at every literal non-root cut parent. -/
theorem richPlannedRootTarget_pair_adj_of_source
    (plan : RootTargetPlan P)
    (hbranch : ∀ j c, c ∈ plan.branchRootSides j →
      (padGraph R).Adj
        (richRootCluster Pcluster Gdegree threshold quota R miss Q P
          ((branchForest P).owner j))
        (richTargetCluster Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb
          (Sum.inr (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
            (threshold := threshold) (quota := quota) (R := R) (miss := miss)
            (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
            (P := P) (S := S) (A := A) j, c))))
    (hcut : ∀ q (hq : q.val ≠ 0)
      (z : Σ j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P,
        Fin ((branchForest P).branches.size j)),
      (partitionBranchEquivNonroots P z).1 = P.parent q hq →
      ∀ c, c ∈ plan.coordinateSides z →
      (padGraph R).Adj
        (richRootCluster Pcluster Gdegree threshold quota R miss Q P q)
        (richTargetCluster Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb
          (Sum.inr (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
            (threshold := threshold) (quota := quota) (R := R) (miss := miss)
            (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
            (P := P) (S := S) (A := A) z.1, c))))
    (q : Fin P.numParts)
    (t : RichRootTarget Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb)
    (ht : t ∈ richPlannedRootTargets Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A plan q) :
    (padGraph R).Adj
      (richRootCluster Pcluster Gdegree threshold quota R miss Q P q)
      (richTargetCluster Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb t) := by
  rw [richPlannedRootTargets, Finset.mem_insert] at ht
  rcases ht with ht | ht
  · subst t
    let s := componentReservoirSide P q
    change (padGraph R).Adj
      (Sum.inl (if s = 0 then Q.A else Q.B))
      (Sum.inl (if otherSide s = 0 then Q.A else Q.B))
    by_cases hs : s = 0
    · rw [hs]
      simpa [otherSide] using Q.adj
    · have hs1 : s = 1 := by
        apply Fin.ext
        have hslt := s.isLt
        omega
      rw [hs1]
      simpa [otherSide] using Q.adj.symm
  · rcases Finset.mem_union.mp ht with ht | ht
    · obtain ⟨j, hj, ht⟩ := Finset.mem_biUnion.mp ht
      have howner := (Finset.mem_filter.mp hj).2
      rw [plannedCoordinateTargets] at ht
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp ht
      rw [← howner]
      exact hbranch j c hc
    · rw [plannedNonrootCutParentTargets] at ht
      by_cases hq : q.val ≠ 0
      · rw [dif_pos hq] at ht
        obtain ⟨z, hz, ht⟩ := Finset.mem_biUnion.mp ht
        rw [plannedCoordinateTargets] at ht
        obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp ht
        exact hcut q hq z (Finset.mem_filter.mp hz).2 c hc
      · rw [dif_neg hq] at ht
        simp at ht

/-- Construct the planned cleaning certificate from source adjacency and
uniform scalar bounds for the two kinds of target sets. -/
theorem RichPlannedRootCleaningFacts.of_source
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rho density : ℝ)
    (H : ReducedPairRealization Pcluster R G rho density)
    (plan : RootTargetPlan P)
    (hbranch : ∀ j c, c ∈ plan.branchRootSides j →
      (padGraph R).Adj
        (richRootCluster Pcluster Gdegree threshold quota R miss Q P
          ((branchForest P).owner j))
        (richTargetCluster Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb
          (Sum.inr (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
            (threshold := threshold) (quota := quota) (R := R) (miss := miss)
            (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
            (P := P) (S := S) (A := A) j, c))))
    (hcut : ∀ q (hq : q.val ≠ 0)
      (z : Σ j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P,
        Fin ((branchForest P).branches.size j)),
      (partitionBranchEquivNonroots P z).1 = P.parent q hq →
      ∀ c, c ∈ plan.coordinateSides z →
      (padGraph R).Adj
        (richRootCluster Pcluster Gdegree threshold quota R miss Q P q)
        (richTargetCluster Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb
          (Sum.inr (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
            (threshold := threshold) (quota := quota) (R := R) (miss := miss)
            (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
            (P := P) (S := S) (A := A) z.1, c))))
    (hrootLarge : ∀ side,
      rho * #(rootWholeSide Pcluster Gdegree threshold quota R miss Q side) ≤
        quota)
    (hendpointLarge : ∀ e c,
      rho * #(richWhole Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb e c) ≤
        #(richEndpoint Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb e c))
    (hbudget : ∀ q,
      P.numParts + richPlannedRootLoss Pcluster Gdegree threshold quota R miss
        Q sourceDensity E0 Mb P S A rho plan q ≤ quota)
    (hlink : ∀ j (hj : j.val ≠ 0)
      (_hroot : P.parent j hj = P.roots (P.parentPart j hj)),
      (P.numParts : ℝ) +
          richPlannedRootLoss Pcluster Gdegree threshold quota R miss Q
            sourceDensity E0 Mb P S A rho plan j ≤
        (density - rho) * quota) :
    RichPlannedRootCleaningFacts Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A G rho density H plan where
  pair_adj := richPlannedRootTarget_pair_adj_of_source Pcluster Gdegree
    threshold quota R miss Q sourceDensity E0 Mb P S A plan hbranch hcut
  root_large := fun q ↦ hrootLarge (componentReservoirSide P q)
  target_large := by
    intro q t ht
    rcases t with side | ec
    · simpa [richTargetWhole, richTargetRaw, card_rootRawSide] using
        hrootLarge side
    · exact hendpointLarge ec.1 ec.2
  root_budget := hbudget
  root_link_margin := hlink

namespace RichPlannedRootCleaningFacts

/-- Cleaning against the plan is stronger than cleaning against any later
orientation covered by that plan. -/
theorem rootCandidate_planned_subset_oriented
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rho : ℝ)
    (plan : RootTargetPlan P)
    (orient : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P →
      Fin 2 ≃ Fin 2)
    (hrootSide : ∀ j,
      orient j
          ((branchForest P).branches.isTree j |>.coloringTwoOfVert
            ((branchForest P).branches.root j)
            ((branchForest P).branches.root j)) ∈ plan.branchRootSides j)
    (hcutSide : ∀ q (hq : q.val ≠ 0)
      (z : Σ j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P,
        Fin ((branchForest P).branches.size j)),
      (partitionBranchEquivNonroots P z).1 = P.parent q hq →
      orient z.1
          ((branchForest P).branches.isTree z.1 |>.coloringTwoOfVert
            ((branchForest P).branches.root z.1) z.2) ∈
        plan.coordinateSides z)
    (q : Fin P.numParts) :
    rootCandidate G rho
        (rootWhole Pcluster Gdegree threshold quota R miss Q P)
        (rootRaw Pcluster Gdegree threshold quota R miss Q P)
        (richPlannedRootTargets Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A plan)
        (richTargetWhole Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb)
        (richTargetRaw Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb) q ⊆
      rootCandidate G rho
        (rootWhole Pcluster Gdegree threshold quota R miss Q P)
        (rootRaw Pcluster Gdegree threshold quota R miss Q P)
        (richRootTargets Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A orient)
        (richTargetWhole Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb)
        (richTargetRaw Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb) q := by
  have htargets := richRootTargets_subset_planned Pcluster Gdegree threshold
    quota R miss Q sourceDensity E0 Mb P S A plan orient hrootSide
      hcutSide q
  intro z hz
  rw [rootCandidate] at hz ⊢
  refine Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hz).1, ?_⟩
  intro hzBad
  apply (Finset.mem_sdiff.mp hz).2
  rw [rootTargetBad] at hzBad ⊢
  obtain ⟨t, ht, hzt⟩ := Finset.mem_biUnion.mp hzBad
  exact Finset.mem_biUnion.mpr ⟨t, htargets ht, hzt⟩

/-- The literal bad-root set is bounded by the rounded planned-target union
loss. -/
theorem rootTargetBad_le
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rho density : ℝ)
    (H : ReducedPairRealization Pcluster R G rho density)
    (plan : RootTargetPlan P)
    (F : RichPlannedRootCleaningFacts Pcluster Gdegree threshold quota R miss
      Q sourceDensity E0 Mb P S A G rho density H plan)
    (q : Fin P.numParts) :
    #(rootTargetBad G rho
        (rootWhole Pcluster Gdegree threshold quota R miss Q P)
        (rootRaw Pcluster Gdegree threshold quota R miss Q P)
        (richPlannedRootTargets Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A plan)
        (richTargetWhole Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb)
        (richTargetRaw Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb) q) ≤
      richPlannedRootLoss Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A rho plan q := by
  have hreal := card_rootTargetBad_le G rho
    (rootWhole Pcluster Gdegree threshold quota R miss Q P)
    (rootRaw Pcluster Gdegree threshold quota R miss Q P)
    (richPlannedRootTargets Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A plan)
    (richTargetWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
      E0 Mb)
    (richTargetRaw Pcluster Gdegree threshold quota R miss Q sourceDensity
      E0 Mb) q
    (by
      intro t ht
      have hp := H.pair_of_adj
        (richRootCluster Pcluster Gdegree threshold quota R miss Q P q)
        (richTargetCluster Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb t) (F.pair_adj q t ht)
      simpa only [rootWhole_eq_padCluster, richTargetWhole_eq_padCluster]
        using hp.1)
    (rootRaw_subset Pcluster Gdegree threshold quota R miss Q P q)
    (fun t _ ↦ richTargetRaw_subset_whole Pcluster Gdegree threshold quota R
      miss Q sourceDensity E0 Mb t)
    (by simpa only [card_rootRaw] using F.root_large q)
    (F.target_large q)
  have hceil := le_upperScale_cast
    ((#(richPlannedRootTargets Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A plan q) : ℝ) *
      (rho * #(rootWhole Pcluster Gdegree threshold quota R miss Q P q)))
  exact_mod_cast hreal.trans hceil

/-- Every vertex surviving the planned root cleaning has the expected
density-gap degree into each literal planned raw target. -/
theorem target_degree
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rho density : ℝ)
    (H : ReducedPairRealization Pcluster R G rho density)
    (plan : RootTargetPlan P)
    (F : RichPlannedRootCleaningFacts Pcluster Gdegree threshold quota R miss
      Q sourceDensity E0 Mb P S A G rho density H plan)
    (q : Fin P.numParts) (z : Bv)
    (hz : z ∈ rootCandidate G rho
      (rootWhole Pcluster Gdegree threshold quota R miss Q P)
      (rootRaw Pcluster Gdegree threshold quota R miss Q P)
      (richPlannedRootTargets Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A plan)
      (richTargetWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
        E0 Mb)
      (richTargetRaw Pcluster Gdegree threshold quota R miss Q sourceDensity
        E0 Mb) q)
    (t : RichRootTarget Pcluster Gdegree threshold quota R miss Q sourceDensity
      E0 Mb)
    (ht : t ∈ richPlannedRootTargets Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A plan q) :
    (density - rho) *
        #(richTargetRaw Pcluster Gdegree threshold quota R miss Q sourceDensity
          E0 Mb t) ≤
      #((richTargetRaw Pcluster Gdegree threshold quota R miss Q sourceDensity
        E0 Mb t).filter (G.Adj z)) := by
  have hp := H.pair_of_adj
    (richRootCluster Pcluster Gdegree threshold quota R miss Q P q)
    (richTargetCluster Pcluster Gdegree threshold quota R miss Q sourceDensity
      E0 Mb t) (F.pair_adj q t ht)
  have hp' : density ≤ G.edgeDensity
      (rootWhole Pcluster Gdegree threshold quota R miss Q P q)
      (richTargetWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
        E0 Mb t) := by
    simpa only [rootWhole_eq_padCluster, richTargetWhole_eq_padCluster] using hp.2
  calc
    (density - rho) *
        #(richTargetRaw Pcluster Gdegree threshold quota R miss Q sourceDensity
          E0 Mb t) ≤
      (G.edgeDensity
          (rootWhole Pcluster Gdegree threshold quota R miss Q P q)
          (richTargetWhole Pcluster Gdegree threshold quota R miss Q
            sourceDensity E0 Mb t) - rho) *
        #(richTargetRaw Pcluster Gdegree threshold quota R miss Q sourceDensity
          E0 Mb t) := by
        exact mul_le_mul_of_nonneg_right (sub_le_sub_right hp' rho)
          (Nat.cast_nonneg _)
    _ ≤ #((richTargetRaw Pcluster Gdegree threshold quota R miss Q sourceDensity
          E0 Mb t).filter (G.Adj z)) :=
      rootCandidate_target_degree G rho
        (rootWhole Pcluster Gdegree threshold quota R miss Q P)
        (rootRaw Pcluster Gdegree threshold quota R miss Q P)
        (richPlannedRootTargets Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A plan)
        (richTargetWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
          E0 Mb)
        (richTargetRaw Pcluster Gdegree threshold quota R miss Q sourceDensity
          E0 Mb) q z hz t ht

/-- The distinguished root-to-root cut link remains available in every
plan because its opposite distinguished target is always inserted. -/
theorem rootLink
    (hT : T.IsTree)
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rho density : ℝ)
    (H : ReducedPairRealization Pcluster R G rho density)
    (plan : RootTargetPlan P)
    (F : RichPlannedRootCleaningFacts Pcluster Gdegree threshold quota R miss
      Q sourceDensity E0 Mb P S A G rho density H plan)
    (j : Fin P.numParts) (hj : j.val ≠ 0)
    (hroot : P.parent j hj = P.roots (P.parentPart j hj)) :
    ∃ t ∈ richPlannedRootTargets Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A plan (P.parentPart j hj),
      richTargetRaw Pcluster Gdegree threshold quota R miss Q sourceDensity
          E0 Mb t = rootRaw Pcluster Gdegree threshold quota R miss Q P j ∧
      (P.numParts : ℝ) +
          richPlannedRootLoss Pcluster Gdegree threshold quota R miss Q
            sourceDensity E0 Mb P S A rho plan j ≤
        (G.edgeDensity
            (rootWhole Pcluster Gdegree threshold quota R miss Q P
              (P.parentPart j hj))
            (richTargetWhole Pcluster Gdegree threshold quota R miss Q
              sourceDensity E0 Mb t) - rho) *
          #(richTargetRaw Pcluster Gdegree threshold quota R miss Q
            sourceDensity E0 Mb t) := by
  let t : RichRootTarget Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb :=
    Sum.inl (otherSide (componentReservoirSide P (P.parentPart j hj)))
  refine ⟨t, ?_, ?_, ?_⟩
  · simp [t, richPlannedRootTargets]
  · exact richTargetRaw_opposite_eq_child Pcluster Gdegree threshold quota R
      miss Q sourceDensity E0 Mb P hT j hj hroot
  · have hsides := componentReservoirSide_ne_of_cutRoot
      (P := P) hT j hj hroot
    have hpair := rootWholeSide_pair_of_ne Pcluster Gdegree threshold quota R
      miss Q G rho density H (componentReservoirSide P (P.parentPart j hj))
      (componentReservoirSide P j) hsides
    have hmargin := F.root_link_margin j hj hroot
    have hcard :
        #(richTargetRaw Pcluster Gdegree threshold quota R miss Q sourceDensity
          E0 Mb t) = quota := by
      simp [t, richTargetRaw, card_rootRawSide]
    have hwhole :
        richTargetWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
            E0 Mb t =
          rootWholeSide Pcluster Gdegree threshold quota R miss Q
            (componentReservoirSide P j) := by
      simp [t, richTargetWhole, otherSide_eq_of_ne _ _ hsides]
    rw [hcard, hwhole]
    calc
      (P.numParts : ℝ) +
          richPlannedRootLoss Pcluster Gdegree threshold quota R miss Q
            sourceDensity E0 Mb P S A rho plan j ≤
          (density - rho) * quota := hmargin
      _ ≤ (G.edgeDensity
              (rootWhole Pcluster Gdegree threshold quota R miss Q P
                (P.parentPart j hj))
              (rootWholeSide Pcluster Gdegree threshold quota R miss Q
                (componentReservoirSide P j)) - rho) * quota := by
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg quota)
        exact sub_le_sub_right hpair.2 rho

/-- The planned cleaning facts construct the injective distinguished-root
skeleton before adaptive matching-fiber orientations are chosen. -/
theorem exists_plannedRootSkeletonEmbedding
    (hT : T.IsTree)
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rho density : ℝ)
    (H : ReducedPairRealization Pcluster R G rho density)
    (plan : RootTargetPlan P)
    (F : RichPlannedRootCleaningFacts Pcluster Gdegree threshold quota R miss
      Q sourceDensity E0 Mb P S A G rho density H plan) :
    Nonempty (RootSkeletonEmbedding P G
      (rootCandidate G rho
        (rootWhole Pcluster Gdegree threshold quota R miss Q P)
        (rootRaw Pcluster Gdegree threshold quota R miss Q P)
        (richPlannedRootTargets Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A plan)
        (richTargetWhole Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb)
        (richTargetRaw Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb))) := by
  refine exists_rootSkeletonEmbedding_of_targetCleaningWithLinks P G rho
    (rootWhole Pcluster Gdegree threshold quota R miss Q P)
    (rootRaw Pcluster Gdegree threshold quota R miss Q P)
    (richPlannedRootTargets Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A plan)
    (richTargetWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
      E0 Mb)
    (richTargetRaw Pcluster Gdegree threshold quota R miss Q sourceDensity
      E0 Mb)
    (richPlannedRootLoss Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A rho plan) ?_ ?_ ?_
  · exact F.rootTargetBad_le Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A G rho density H plan
  · intro q
    simpa only [card_rootRaw] using F.root_budget q
  · exact F.rootLink Pcluster Gdegree threshold quota R miss Q sourceDensity
      E0 Mb P S A hT G rho density H plan

end RichPlannedRootCleaningFacts

end Erdos547b.ZhaoClaim615RichDynamicPlannedRootCleaning

#print axioms Erdos547b.ZhaoClaim615RichDynamicPlannedRootCleaning.richPlannedRootTarget_pair_adj_of_source
#print axioms Erdos547b.ZhaoClaim615RichDynamicPlannedRootCleaning.RichPlannedRootCleaningFacts.of_source
#print axioms Erdos547b.ZhaoClaim615RichDynamicPlannedRootCleaning.RichPlannedRootCleaningFacts.rootCandidate_planned_subset_oriented
#print axioms Erdos547b.ZhaoClaim615RichDynamicPlannedRootCleaning.RichPlannedRootCleaningFacts.rootTargetBad_le
#print axioms Erdos547b.ZhaoClaim615RichDynamicPlannedRootCleaning.RichPlannedRootCleaningFacts.target_degree
#print axioms Erdos547b.ZhaoClaim615RichDynamicPlannedRootCleaning.RichPlannedRootCleaningFacts.rootLink
#print axioms Erdos547b.ZhaoClaim615RichDynamicPlannedRootCleaning.RichPlannedRootCleaningFacts.exists_plannedRootSkeletonEmbedding
