/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceMatchingFamilyState
import ErdosProblems.Erdos547b.SourcePendingParentDegree

/-!
# Reconnection degrees on the actual family placement

Positive source support survives both completed and active placements.
Thus every root-colour image has the permanent-cleanup degree bound,
without reconstructing a pending plan or changing the stored copy.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceMatchingParentDegree

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoSourceMatchingFamilyState Erdos547b.ZhaoSourceOriginalBranchPlacement
open Erdos547b.ZhaoSourcePendingParentDegree
open Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceEmbeddingHost
open Erdos547b.ZhaoSourceMatchingGeometry Erdos547b.ZhaoSourceMatchingParentCleanup
open Erdos547b.ZhaoSourceParentCleanup (reservoir rootCluster)
open Erdos547b.ZhaoSourceRootExclusions Erdos547b.ZhaoLemma58ThresholdResidualCapacity

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)
variable (S : CleanSourceWitness W Q) (P : (padGraph (reduced W)).Subgraph) (s : Fin 2)

/-- The degree bound uses the original-index placement and its inherited
support. It is independent of whether the branch is completed or active. -/
theorem placement_rootColor_degree
    {b : ℕ} (F : OrderedRootedForest b) (selected : Finset (Fin b))
    (parent : Fin b → Fin hostN)
    (E : BranchPlacement F (embeddingHost W) selected parent
      (fun e => residualSide (pairWhole W P e) (deleted W Q P e)))
    (hpositive : ∀ i, 0 < rootDensity W S (Sum.inl (rootCluster W Q s))
      (pairVertex W P (E.edge i) (E.orient i 0)))
    (i : Fin b) (hi : i ∈ selected) (a : Fin (F.size i))
    (hcolor : (F.isTree i).coloringTwoOfVert (F.root i) a = 0) :
    ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (sourceQuota W : ℝ) ≤
      (#((reservoir W Q s).filter
        ((embeddingHost W).Adj (E.forestCopy.componentCopy i hi a))) : ℝ) := by
  have hmem := E.map_side i hi a
  rw [hcolor] at hmem
  have hpos := hpositive ⟨i, hi⟩
  have hadj : (padGraph (reduced W)).Adj (Sum.inl (rootCluster W Q s))
      (pairVertex W P (E.edge ⟨i, hi⟩) (E.orient ⟨i, hi⟩ 0)) := by
    rcases rootCluster_cases W Q s with hA | hB
    · rw [hA] at hpos ⊢
      exact (CleanSourceWitness.source_rows W S).supportA _ hpos
    · rw [hB] at hpos ⊢
      exact (CleanSourceWitness.source_rows W S).supportB _ hpos
  exact parent_degree_into_reservoir W Q P (E.edge ⟨i, hi⟩) (E.orient ⟨i, hi⟩ 0) s
    (E.forestCopy.componentCopy i hi a) hmem hadj.symm

/-- Apply permanent cleanup to the literal image stored in a family state. -/
theorem family_rootColor_degree
    {b r : ℕ} (F : OrderedRootedForest b) (owner : Fin b → Fin r)
    {all : Finset (MatchingEdge P)} {family : List (Fin b)}
    {rootImage : Fin r → Fin hostN} {stage : ℕ}
    (A : FamilyState W Q S P (rootCluster W Q s) F owner all family rootImage stage)
    (i : Fin b) (hi : i ∈ family.toFinset.filter (fun i => (owner i).val < stage))
    (a : Fin (F.size i)) (hcolor : (F.isTree i).coloringTwoOfVert (F.root i) a = 0) :
    ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (sourceQuota W : ℝ) ≤
      (#((reservoir W Q s).filter ((embeddingHost W).Adj
        ((A.currentPlacement W Q S P (rootCluster W Q s) F owner).forestCopy.componentCopy i hi a))) : ℝ) :=
  placement_rootColor_degree W Q S P s F _ _ (A.currentPlacement W Q S P (rootCluster W Q s) F owner)
    (A.current_root_positive W Q S P (rootCluster W Q s) F owner) i hi a hcolor

end Erdos547b.ZhaoSourceMatchingParentDegree

#print axioms Erdos547b.ZhaoSourceMatchingParentDegree.placement_rootColor_degree
#print axioms Erdos547b.ZhaoSourceMatchingParentDegree.family_rootColor_degree
