/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceExceptionalRowBounds
import ErdosProblems.Erdos547b.SourceTwoSideFamilyAdvance

/-!
# Exchange the two actual distinguished roots

The matching, physical source graph and physical density table are retained.
Only the two reservoir tags are reversed. This realizes the swapped
alternative of the finite raw-discrepancy allocation lemma.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceSwappedRootRows

open Finset SimpleGraph
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceParentCleanup
open Erdos547b.ZhaoSourceExceptionalRowBounds Erdos547b.ZhaoSourceTwoSideFamilyAdvance
open Erdos547b.ZhaoRichClaim61Lemma611 Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoClaim616

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)

def swapCertificate : Certificate W where
  A := Q.B
  B := Q.A
  adj := Q.adj.symm
  A_mem := Q.B_mem
  B_mem := Q.A_mem
  A₀ := Q.B₀
  B₀ := Q.A₀
  A₀_subset := Q.B₀_subset
  B₀_subset := Q.A₀_subset
  A₀_card := Q.B₀_card
  B₀_card := Q.A₀_card
  A₀_high := Q.B₀_high
  B₀_high := Q.A₀_high
  claim67 := Q.claim67
  A_in_claim67O := Q.B_in_claim67O
  B_in_claim67O := Q.A_in_claim67O
  matching_edge_meets_large := Q.matching_edge_meets_large

def swapSource : CleanSourceWitness W (swapCertificate W Q) where
  source := S.source
  zA := S.zB
  zB := S.zA
  zA_mem := S.zB_mem
  zB_mem := S.zA_mem
  distinct := S.distinct.symm
  extraLoss := S.extraLoss
  source_le := S.source_le
  degree_loss := S.degree_loss
  extraLoss_small := S.extraLoss_small
  upperA := fun j hjB hjA => S.upperB j hjA hjB
  upperB := fun j hjB hjA => S.upperA j hjA hjB

theorem rootCluster_swap (s : Fin 2) :
    rootCluster W (swapCertificate W Q) s = rootCluster W Q (otherSide s) := by
  fin_cases s <;> rfl

/-- Physical rows are unchanged, even though their two tags are exchanged. -/
theorem rootDensity_swap : rootDensity W (swapSource W Q S) = rootDensity W S := by
  funext C x
  have hAB : (Sum.inl Q.A : EvenPadding (Index W)) ≠ Sum.inl Q.B :=
    fun h => Q.adj.ne (Sum.inl.inj h)
  dsimp only [rootDensity, swapSource, swapCertificate, twoRootSourceDensity]
  by_cases hA : C = Sum.inl Q.A
  · have hB : C ≠ Sum.inl Q.B := by simpa only [hA] using hAB
    simp only [if_pos hA, if_neg hB]
  · by_cases hB : C = Sum.inl Q.B
    · simp only [if_pos hB, if_neg hA]
    · simp only [if_neg hA, if_neg hB]

theorem sideWeight_swap (s : Fin 2) (e : Erdos547b.ZhaoLemma611Full.MatchingEdge Q.claim67.M) :
    sideWeight W (swapCertificate W Q) (swapSource W Q S) s e =
      sideWeight W Q S (otherSide s) e := by
  change rowWeight W (swapSource W Q S) (Sum.inl (rootCluster W (swapCertificate W Q) s)) e = _
  rw [rootCluster_swap]
  dsimp only [rowWeight]
  rw [rootDensity_swap]
  rfl

theorem awayEdges_swap : awayEdges W (swapCertificate W Q) = awayEdges W Q := by
  change Erdos547b.ZhaoLemma611Full.allMatchingEdges Q.claim67.M \
      incidentCoverEdges Q.claim67.M (padFinset (large W)) {Sum.inl Q.B, Sum.inl Q.A} =
    Erdos547b.ZhaoLemma611Full.allMatchingEdges Q.claim67.M \
      incidentCoverEdges Q.claim67.M (padFinset (large W)) {Sum.inl Q.A, Sum.inl Q.B}
  rw [Finset.pair_comm (Sum.inl Q.B) (Sum.inl Q.A)]

end Erdos547b.ZhaoSourceSwappedRootRows

#print axioms Erdos547b.ZhaoSourceSwappedRootRows.swapCertificate
#print axioms Erdos547b.ZhaoSourceSwappedRootRows.swapSource
#print axioms Erdos547b.ZhaoSourceSwappedRootRows.rootDensity_swap
#print axioms Erdos547b.ZhaoSourceSwappedRootRows.sideWeight_swap
#print axioms Erdos547b.ZhaoSourceSwappedRootRows.awayEdges_swap
