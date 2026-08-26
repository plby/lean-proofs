/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourcePendingOwnerStep
import ErdosProblems.Erdos547b.SourceResidualRootPacking
import ErdosProblems.Erdos547b.Claim616CoordinateCutAttachmentParity
import ErdosProblems.Erdos547b.Lemma58GlobalCutOnline

/-!
# Actual reservoir degrees of pending cut-parent images

Root-colour vertices of a pending branch inherit positive source support
from the plan. Their images survive permanent cleanup, giving the required
reservoir degree. The recorded partition cut parent has this colour, and
literal branch-list transport preserves it.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourcePendingParentDegree

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceEmbeddingHost
open Erdos547b.ZhaoSourceActualChunkEmbedding Erdos547b.ZhaoSourceParentCleanup
open Erdos547b.ZhaoSourceRootExclusions Erdos547b.ZhaoSourceActualPendingPlan
open Erdos547b.ZhaoSourceResidualRootPacking Erdos547b.ZhaoLemma58DynamicBatchAppend
open Erdos547b.ZhaoLemma58ThresholdResidualCapacity

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)

private theorem source_support_rootCluster
    (S : CleanSourceWitness W Q) (s : Fin 2) (x : EvenPadding (Index W))
    (hpos : 0 < rootDensity W S (Sum.inl (rootCluster W Q s)) x) :
    (padGraph (reduced W)).Adj (Sum.inl (rootCluster W Q s)) x := by
  rcases rootCluster_cases W Q s with hA | hB
  · rw [hA] at hpos ⊢
    exact (CleanSourceWitness.source_rows W S).supportA x hpos
  · rw [hB] at hpos ⊢
    exact (CleanSourceWitness.source_rows W S).supportB x hpos

/-- Every root-colour branch image in the actual pending plan is an
eligible future cut parent toward the same distinguished root reservoir. -/
theorem degree_at_rootColor
    {S : CleanSourceWitness W Q} {s : Fin 2} {e : MatchingEdge Q.claim67.M}
    {b : ℕ} {F : OrderedRootedForest b}
    (P : ActualPendingPlan W Q S (rootCluster W Q s) e F)
    (parent : Fin b → Fin hostN) (selected : Finset (Fin b))
    (E : PartialDynamicAttachedForestEmbedding F (embeddingHost W) parent P.orient
      (residualSide (edgeWhole W Q e) (deleted W Q e)) selected)
    (i : Fin b) (hi : i ∈ selected) (a : Fin (F.size i))
    (hcolor : (F.isTree i).coloringTwoOfVert (F.root i) a = 0) :
    ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (sourceQuota W : ℝ) ≤
      (#((reservoir W Q s).filter
        ((embeddingHost W).Adj (E.forestCopy.componentCopy i hi a))) : ℝ) := by
  have hmem := E.map_side i hi a
  rw [hcolor] at hmem
  have hadj := source_support_rootCluster W Q S s _ (P.root_positive i)
  exact parent_degree_into_reservoir W Q e (P.orient i 0) s
    (E.forestCopy.componentCopy i hi a) hmem hadj.symm

open Erdos547b.TreePartition Erdos547b.ZhaoClaim68
open Erdos547b.ZhaoClaim617BranchCount Erdos547b.ZhaoClaim616HierarchyClassification
open Erdos547b.ZhaoClaim616CoordinateCutAttachmentParity
open Erdos547b.ZhaoClaim616HierarchyCoordinateSide
open Erdos547b.ZhaoLemma58GlobalCutOnline

/-- The original recorded non-root cut parent has colour zero in its
literal branch, independently of all host graph choices. -/
theorem cutParent_coordinate_color_zero
    {U : Type*} [Fintype U] [DecidableEq U]
    {T : SimpleGraph U} [DecidableRel T.Adj] (hT : T.IsTree)
    {globalRoot : U} {small : ℕ} (TP : ZhaoForestPartition T globalRoot small)
    (n : Fin TP.numParts) (hn : n.val ≠ 0)
    (hnotroot : TP.parent n hn ≠ TP.roots (TP.parentPart n hn)) :
    let z := cutParentBranchCoordinate TP n hn hnotroot
    ((branchForest TP).branches.isTree z.1).coloringTwoOfVert
      ((branchForest TP).branches.root z.1) z.2 = 0 := by
  let z := cutParentBranchCoordinate TP n hn hnotroot
  have hclass : literalSourceClass TP (TP.parent n hn) = Sum.inr z.1 := by
    rw [← cutParentBranchCoordinate_value TP n hn hnotroot]
    exact literalSourceClass_partitionBranchEquivNonroots TP z
  have hzero := cutParent_canonicalBranchSide_zero hT TP n hn z.1 hclass
  change ((branchForest TP).branches.isTree z.1).coloringTwoOfVert
    ((branchForest TP).branches.root z.1) z.2 = 0
  rw [← canonicalBranchSide_partitionBranchCoordinate hT TP z.1 z.2,
    cutParentBranchCoordinate_value TP n hn hnotroot]
  exact hzero

/-- Transporting a literal branch index transports its rooted colouring. -/
theorem coloring_cast_index {b : ℕ} (F : OrderedRootedForest b)
    {i j : Fin b} (h : i = j) (a : Fin (F.size j)) :
    (F.isTree i).coloringTwoOfVert (F.root i) (Fin.cast (congrArg F.size h.symm) a) =
      (F.isTree j).coloringTwoOfVert (F.root j) a := by
  subst i
  rfl

/-- Root-colour membership survives the actual packed-list indexing. -/
theorem listForest_color_zero {b : ℕ} (F : OrderedRootedForest b)
    (items : List (Fin b)) (i : Fin items.length) (j : Fin b)
    (hij : items[i.val] = j) (a : Fin (F.size j))
    (hcolor : (F.isTree j).coloringTwoOfVert (F.root j) a = 0) :
    ((listForest F items).isTree i).coloringTwoOfVert ((listForest F items).root i)
      (Fin.cast (congrArg F.size hij.symm) a) = 0 := by
  exact (coloring_cast_index F hij a).trans hcolor

open Erdos547b.ZhaoClaim68BranchAdapter

/-- The degree premise for the next cut root, evaluated at the actual
recorded parent coordinate in the current pending chunk. -/
theorem degree_at_recorded_cutParent
    {U : Type*} [Fintype U] [DecidableEq U]
    {T : SimpleGraph U} [DecidableRel T.Adj] (hT : T.IsTree)
    {globalRoot : U} {small : ℕ} (TP : ZhaoForestPartition T globalRoot small)
    (n : Fin TP.numParts) (hn : n.val ≠ 0)
    (hnotroot : TP.parent n hn ≠ TP.roots (TP.parentPart n hn))
    {S : CleanSourceWitness W Q} {s : Fin 2} {e : MatchingEdge Q.claim67.M}
    (items : List (Fin (Fintype.card (ChildKey TP.orderedForest))))
    (P : ActualPendingPlan W Q S (rootCluster W Q s) e
      (listForest (branchForest TP).branches items))
    (parent : Fin items.length → Fin hostN) (selected : Finset (Fin items.length))
    (E : PartialDynamicAttachedForestEmbedding (listForest (branchForest TP).branches items)
      (embeddingHost W) parent P.orient
      (residualSide (edgeWhole W Q e) (deleted W Q e)) selected)
    (i : Fin items.length) (hi : i ∈ selected)
    (hindex : items[i.val] = (cutParentBranchCoordinate TP n hn hnotroot).1) :
    let z := cutParentBranchCoordinate TP n hn hnotroot
    let a := Fin.cast (congrArg (branchForest TP).branches.size hindex.symm) z.2
    ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (sourceQuota W : ℝ) ≤
      (#((reservoir W Q s).filter
        ((embeddingHost W).Adj (E.forestCopy.componentCopy i hi a))) : ℝ) := by
  apply degree_at_rootColor W Q P parent selected E i hi
  exact listForest_color_zero (branchForest TP).branches items i _ hindex _
    (cutParent_coordinate_color_zero hT TP n hn hnotroot)

end Erdos547b.ZhaoSourcePendingParentDegree

#print axioms Erdos547b.ZhaoSourcePendingParentDegree.degree_at_rootColor
#print axioms Erdos547b.ZhaoSourcePendingParentDegree.cutParent_coordinate_color_zero
#print axioms Erdos547b.ZhaoSourcePendingParentDegree.coloring_cast_index
#print axioms Erdos547b.ZhaoSourcePendingParentDegree.listForest_color_zero
#print axioms Erdos547b.ZhaoSourcePendingParentDegree.degree_at_recorded_cutParent
