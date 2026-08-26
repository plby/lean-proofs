/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichDynamicRootTargets

/-!
# Regularity cleaning of the exact dynamic root targets

This module turns reduced-graph adjacency of the finite target list into the
literal root-candidate loss used by the full cut-aware backend.  The loss is
the upward-rounded regularity union bound for the actual targets of each
root.  Root-to-root cut links use the concrete opposite distinguished target
and are packaged with their density estimate in the sharp link API.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim615RichDynamicRootCleaning

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
open Erdos547b.ZhaoClaim615RichDynamicRootApplication
open Erdos547b.ZhaoClaim615RichDynamicRootTargets
open Erdos547b.ZhaoClaim615RichCoordinatePairFacts
open Erdos547b.ZhaoLemma58RootCandidateCleaning
open Erdos547b.ZhaoLemma58CutForestReconstruction
open Erdos547b.ZhaoLemma58FullCutTree

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

/-- Padded reduced vertex containing one distinguished component root. -/
def richRootCluster (q : Fin P.numParts) : EvenPadding I :=
  Sum.inl (if componentReservoirSide P q = 0 then Q.A else Q.B)

/-- Padded reduced vertex represented by one exact root target. -/
def richTargetCluster :
    RichRootTarget Pcluster Gdegree threshold quota R miss Q sourceDensity
      E0 Mb → EvenPadding I
  | Sum.inl side => Sum.inl (if side = 0 then Q.A else Q.B)
  | Sum.inr (e, c) =>
      matchingEdgeEndpoint (indexedPhysicalEdge Q sourceDensity E0 Mb e).1 c

theorem rootWhole_eq_padCluster (q : Fin P.numParts) :
    rootWhole Pcluster Gdegree threshold quota R miss Q P q =
      padCluster (clusterVertices Pcluster)
        (richRootCluster Pcluster Gdegree threshold quota R miss Q P q) := by
  unfold rootWhole rootWholeSide richRootCluster
  rfl

theorem richTargetWhole_eq_padCluster
    (t : RichRootTarget Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb) :
    richTargetWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
        E0 Mb t =
      padCluster (clusterVertices Pcluster)
        (richTargetCluster Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb t) := by
  rcases t with side | ec
  · rfl
  · rfl

theorem richTargetRaw_subset_whole
    (t : RichRootTarget Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb) :
    richTargetRaw Pcluster Gdegree threshold quota R miss Q sourceDensity
        E0 Mb t ⊆
      richTargetWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
        E0 Mb t := by
  rcases t with side | ec
  · exact rootRawSide_subset Pcluster Gdegree threshold quota R miss Q side
  · exact endpoint_subset_whole
      (Pcluster := Pcluster) (Gdegree := Gdegree)
      (threshold := threshold) (quota := quota) (R := R) (miss := miss)
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      ec.1 ec.2

/-- Upward-rounded regularity loss for the exact target list of one root. -/
def richRootLoss
    (rho : ℝ)
    (orient : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P →
      Fin 2 ≃ Fin 2)
    (q : Fin P.numParts) : ℕ :=
  upperScale
    ((#(richRootTargets Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A orient q) : ℝ) *
      (rho * #(rootWhole Pcluster Gdegree threshold quota R miss Q P q)))

/-- Honest source/regularity facts needed to clean all distinguished roots. -/
structure RichRootCleaningFacts
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rho density : ℝ)
    (H : ReducedPairRealization Pcluster R G rho density)
    (orient : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P →
      Fin 2 ≃ Fin 2) : Prop where
  pair_adj : ∀ q t,
    t ∈ richRootTargets Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A orient q →
    (padGraph R).Adj
      (richRootCluster Pcluster Gdegree threshold quota R miss Q P q)
      (richTargetCluster Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb t)
  root_large : ∀ q,
    rho * #(rootWhole Pcluster Gdegree threshold quota R miss Q P q) ≤ quota
  target_large : ∀ q t,
    t ∈ richRootTargets Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A orient q →
    rho * #(richTargetWhole Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb t) ≤
      #(richTargetRaw Pcluster Gdegree threshold quota R miss Q sourceDensity
        E0 Mb t)
  root_budget : ∀ q,
    P.numParts + richRootLoss Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A rho orient q ≤ quota
  root_link_margin : ∀ j (hj : j.val ≠ 0)
    (_hroot : P.parent j hj = P.roots (P.parentPart j hj)),
    (P.numParts : ℝ) +
        richRootLoss Pcluster Gdegree threshold quota R miss Q sourceDensity
          E0 Mb P S A rho orient j ≤
      (density - rho) * quota

/-- The exact target list is reduced-adjacent once the owned branch-root
targets and the literal non-root cut-parent targets are. -/
theorem richRootTarget_pair_adj_of_source
    (orient : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P →
      Fin 2 ≃ Fin 2)
    (hbranch : ∀ j,
      (padGraph R).Adj
        (richRootCluster Pcluster Gdegree threshold quota R miss Q P
          ((branchForest P).owner j))
        (richTargetCluster Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb
          (branchRootTarget Pcluster Gdegree threshold quota R miss Q
            sourceDensity E0 Mb P S A orient j)))
    (hcut : ∀ q (hq : q.val ≠ 0)
      (z : Σ j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P,
        Fin ((branchForest P).branches.size j)),
      (partitionBranchEquivNonroots P z).1 = P.parent q hq →
      (padGraph R).Adj
        (richRootCluster Pcluster Gdegree threshold quota R miss Q P q)
        (richTargetCluster Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb
          (coordinateTarget Pcluster Gdegree threshold quota R miss Q
            sourceDensity E0 Mb P S A orient z)))
    (q : Fin P.numParts)
    (t : RichRootTarget Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb)
    (ht : t ∈ richRootTargets Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A orient q) :
    (padGraph R).Adj
      (richRootCluster Pcluster Gdegree threshold quota R miss Q P q)
      (richTargetCluster Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb t) := by
  rw [richRootTargets, Finset.mem_insert] at ht
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
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ht
      have howner := (Finset.mem_filter.mp hj).2
      rw [← howner]
      exact hbranch j
    · rw [nonrootCutParentTargets] at ht
      by_cases hq : q.val ≠ 0
      · rw [dif_pos hq] at ht
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp ht
        exact hcut q hq z (Finset.mem_filter.mp hz).2
      · rw [dif_neg hq] at ht
        simp at ht

/-- Package the cleaning record from the two genuine source-adjacency
families and uniform scalar size bounds for distinguished and matching
targets. -/
theorem RichRootCleaningFacts.of_source
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rho density : ℝ)
    (H : ReducedPairRealization Pcluster R G rho density)
    (orient : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P →
      Fin 2 ≃ Fin 2)
    (hbranch : ∀ j,
      (padGraph R).Adj
        (richRootCluster Pcluster Gdegree threshold quota R miss Q P
          ((branchForest P).owner j))
        (richTargetCluster Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb
          (branchRootTarget Pcluster Gdegree threshold quota R miss Q
            sourceDensity E0 Mb P S A orient j)))
    (hcut : ∀ q (hq : q.val ≠ 0)
      (z : Σ j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P,
        Fin ((branchForest P).branches.size j)),
      (partitionBranchEquivNonroots P z).1 = P.parent q hq →
      (padGraph R).Adj
        (richRootCluster Pcluster Gdegree threshold quota R miss Q P q)
        (richTargetCluster Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb
          (coordinateTarget Pcluster Gdegree threshold quota R miss Q
            sourceDensity E0 Mb P S A orient z)))
    (hrootLarge : ∀ side,
      rho * #(rootWholeSide Pcluster Gdegree threshold quota R miss Q side) ≤
        quota)
    (hendpointLarge : ∀ e c,
      rho * #(richWhole Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb e c) ≤
        #(richEndpoint Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb e c))
    (hbudget : ∀ q,
      P.numParts + richRootLoss Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A rho orient q ≤ quota)
    (hlink : ∀ j (hj : j.val ≠ 0)
      (_hroot : P.parent j hj = P.roots (P.parentPart j hj)),
      (P.numParts : ℝ) +
          richRootLoss Pcluster Gdegree threshold quota R miss Q sourceDensity
            E0 Mb P S A rho orient j ≤
        (density - rho) * quota) :
    RichRootCleaningFacts Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A G rho density H orient where
  pair_adj := richRootTarget_pair_adj_of_source Pcluster Gdegree threshold
    quota R miss Q sourceDensity E0 Mb P S A orient hbranch hcut
  root_large := fun q ↦ hrootLarge (componentReservoirSide P q)
  target_large := by
    intro q t ht
    rcases t with side | ec
    · simpa [richTargetWhole, richTargetRaw, card_rootRawSide] using
        hrootLarge side
    · exact hendpointLarge ec.1 ec.2
  root_budget := hbudget
  root_link_margin := hlink

namespace RichRootCleaningFacts

theorem rootTargetBad_le
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rho density : ℝ)
    (H : ReducedPairRealization Pcluster R G rho density)
    (orient : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P →
      Fin 2 ≃ Fin 2)
    (F : RichRootCleaningFacts Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A G rho density H orient)
    (q : Fin P.numParts) :
    #(rootTargetBad G rho
        (rootWhole Pcluster Gdegree threshold quota R miss Q P)
        (rootRaw Pcluster Gdegree threshold quota R miss Q P)
        (richRootTargets Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A orient)
        (richTargetWhole Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb)
        (richTargetRaw Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb) q) ≤
      richRootLoss Pcluster Gdegree threshold quota R miss Q sourceDensity
        E0 Mb P S A rho orient q := by
  have hreal := card_rootTargetBad_le G rho
    (rootWhole Pcluster Gdegree threshold quota R miss Q P)
    (rootRaw Pcluster Gdegree threshold quota R miss Q P)
    (richRootTargets Pcluster Gdegree threshold quota R miss Q sourceDensity
      E0 Mb P S A orient)
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
    (by
      simpa only [card_rootRaw] using F.root_large q)
    (F.target_large q)
  have hceil := le_upperScale_cast
    ((#(richRootTargets Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A orient q) : ℝ) *
      (rho * #(rootWhole Pcluster Gdegree threshold quota R miss Q P q)))
  exact_mod_cast hreal.trans hceil

theorem rootLink
    (hT : T.IsTree)
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rho density : ℝ)
    (H : ReducedPairRealization Pcluster R G rho density)
    (orient : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P →
      Fin 2 ≃ Fin 2)
    (F : RichRootCleaningFacts Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A G rho density H orient)
    (j : Fin P.numParts) (hj : j.val ≠ 0)
    (hroot : P.parent j hj = P.roots (P.parentPart j hj)) :
    ∃ t ∈ richRootTargets Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A orient (P.parentPart j hj),
      richTargetRaw Pcluster Gdegree threshold quota R miss Q sourceDensity
          E0 Mb t = rootRaw Pcluster Gdegree threshold quota R miss Q P j ∧
      (P.numParts : ℝ) +
          richRootLoss Pcluster Gdegree threshold quota R miss Q sourceDensity
            E0 Mb P S A rho orient j ≤
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
  refine ⟨t, oppositeRootTarget_mem Pcluster Gdegree threshold quota R miss Q
    sourceDensity E0 Mb P S A orient (P.parentPart j hj), ?_, ?_⟩
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
          richRootLoss Pcluster Gdegree threshold quota R miss Q sourceDensity
            E0 Mb P S A rho orient j ≤
          (density - rho) * quota := hmargin
      _ ≤ (G.edgeDensity
              (rootWhole Pcluster Gdegree threshold quota R miss Q P
                (P.parentPart j hj))
              (rootWholeSide Pcluster Gdegree threshold quota R miss Q
                (componentReservoirSide P j)) - rho) * quota := by
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg quota)
        exact sub_le_sub_right hpair.2 rho

end RichRootCleaningFacts

/-- Apply the complete rich root-cleaning package to the cut-aware dynamic
backend.  Root loss, target lists, and root/root links are all constructed
internally from `RichRootCleaningFacts`. -/
theorem exists_treeCopy_of_richRootCleaningFacts
    (hT : T.IsTree)
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (hdisjoint : Disjoint E0.selected Mb.selected)
    (rho density : ℝ)
    (H : ReducedPairRealization Pcluster R G rho density)
    (orient : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P →
      Fin 2 ≃ Fin 2)
    (F : RichRootCleaningFacts Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A G rho density H orient)
    (edgeRho edgeDensity : PhysicalIndex Q sourceDensity E0 Mb → ℝ)
    (hdata : ∀ rootImage : Fin P.numParts → Bv,
      (∀ q, rootImage q ∈ rootCandidate G rho
        (rootWhole Pcluster Gdegree threshold quota R miss Q P)
        (rootRaw Pcluster Gdegree threshold quota R miss Q P)
        (richRootTargets Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A orient)
        (richTargetWhole Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb)
        (richTargetRaw Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb) q) →
      CutEdgeData P G G rootImage
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A))
        (richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
          E0 Mb)
        (richEndpoint Pcluster Gdegree threshold quota R miss Q sourceDensity
          E0 Mb)
        edgeRho edgeDensity) :
    Nonempty (T.Copy G) := by
  refine exists_treeCopy_of_richTargetCleanedRoots Pcluster Gdegree threshold
    quota R miss Q sourceDensity E0 Mb P S A G hdisjoint rho
    (richRootTargets Pcluster Gdegree threshold quota R miss Q sourceDensity
      E0 Mb P S A orient)
    (richTargetWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
      E0 Mb)
    (richTargetRaw Pcluster Gdegree threshold quota R miss Q sourceDensity
      E0 Mb)
    (richRootLoss Pcluster Gdegree threshold quota R miss Q sourceDensity E0
      Mb P S A rho orient) ?_ ?_ ?_ edgeRho edgeDensity ?_
  · exact F.rootTargetBad_le Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A G rho density H orient
  · exact F.root_budget
  · exact F.rootLink Pcluster Gdegree threshold quota R miss Q sourceDensity
      E0 Mb P S A hT G rho density H orient
  · exact hdata

end Erdos547b.ZhaoClaim615RichDynamicRootCleaning

#print axioms Erdos547b.ZhaoClaim615RichDynamicRootCleaning.RichRootCleaningFacts.rootTargetBad_le
#print axioms Erdos547b.ZhaoClaim615RichDynamicRootCleaning.RichRootCleaningFacts.rootLink
#print axioms Erdos547b.ZhaoClaim615RichDynamicRootCleaning.richRootTarget_pair_adj_of_source
#print axioms Erdos547b.ZhaoClaim615RichDynamicRootCleaning.RichRootCleaningFacts.of_source
#print axioms Erdos547b.ZhaoClaim615RichDynamicRootCleaning.exists_treeCopy_of_richRootCleaningFacts
