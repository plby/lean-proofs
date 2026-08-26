/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceLargeExceptionalForcing
import ErdosProblems.Erdos547b.SourceSwappedRootRows

/-!
# Physical exceptional rows and source parity under root exchange

Exchange the actual root certificate to inspect either physical row while
leaving the source parity unchanged. A small canonical minor family cannot
be the parity carrying the required balanced mass.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceExceptionalRootExchange

open Finset SimpleGraph Erdos547b.TreePartition
open Erdos547b.ZhaoSourceLargeExceptionalForcing Erdos547b.ZhaoSourceSwappedRootRows
open Erdos547b.ZhaoSourceExceptionalFamilies Erdos547b.ZhaoSourceExceptionalNumerics
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceParentCleanup
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceActualChunkEmbedding
open Erdos547b.ZhaoClaim615SourceSelection Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoSourceTwoSideFamilyAdvance Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoLemma615

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)

theorem sideDensity_swap (s : Fin 2) (e : MatchingEdge Q.claim67.M) (c : Fin 2) :
    sideDensity W (swapCertificate W Q) (swapSource W Q S) s e c =
      sideDensity W Q S (otherSide s) e c := by
  change rootDensity W (swapSource W Q S)
      (Sum.inl (rootCluster W (swapCertificate W Q) s)) (edgeVertex W (swapCertificate W Q) e c) = _
  rw [rootCluster_swap, rootDensity_swap]
  rfl

theorem unbalancedAway_swap (s : Fin 2) :
    unbalancedAway W (swapCertificate W Q) (swapSource W Q S) s =
      unbalancedAway W Q S (otherSide s) := by
  unfold unbalancedAway unbalancedEdges
  rw [awayEdges_swap]
  apply Finset.filter_congr
  intro e _
  rw [sideDensity_swap W Q S s e 0, sideDensity_swap W Q S s e 1]

theorem nonextremeAway_swap (s : Fin 2) :
    nonextremeAway W (swapCertificate W Q) (swapSource W Q S) s =
      nonextremeAway W Q S (otherSide s) := by
  unfold nonextremeAway nonextremeEdges
  rw [awayEdges_swap]
  apply Finset.filter_congr
  intro e _
  rw [sideDensity_swap W Q S s e 0, sideDensity_swap W Q S s e 1]

variable {U : Type*} [Fintype U] [DecidableEq U]
variable {T : SimpleGraph U} [DecidableRel T.Adj]
variable {globalRoot : U} {small : ℕ}
variable (P : ZhaoForestPartition T globalRoot small)

theorem balancedSide_eq_zero_of_smallMinor
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (q : ℕ) (s : Fin 2)
    (hminor : (branchMass P (sideBranches P 1) : ℝ) < (fourthRoot α : ℝ) * q)
    (hmass : (α : ℝ) / 32 * q ≤ (branchMass P (balancedSideBranches P s ((α : ℝ) / 16)) : ℝ)) :
    s = 0 := by
  fin_cases s
  · rfl
  · exfalso
    change (α : ℝ) / 32 * q ≤
      (branchMass P (balancedSideBranches P 1 ((α : ℝ) / 16)) : ℝ) at hmass
    have hp := parameter_pos hα
    have hu := parameter_upper_bounds hα hα1
    have hg := parameter_gates hα hα1
    have he3 : eta α ^ 3 ≤ eta α := pow_succ_le_self hp.2.2.1.le hg.2.1 2
    have htQ : 32 * fourthRoot α ≤ α := by
      linarith only [hu.2.2.2.1, he3, hg.2.2.1, hp.2.2.1]
    have htR : (32 : ℝ) * (fourthRoot α : ℝ) ≤ α := by exact_mod_cast htQ
    have htq := mul_le_mul_of_nonneg_right htR (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
    have hmassNat : branchMass P (balancedSideBranches P 1 ((α : ℝ) / 16)) ≤
        branchMass P (sideBranches P 1) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => Nat.zero_le _)
    have hmassLe : (branchMass P (balancedSideBranches P 1 ((α : ℝ) / 16)) : ℝ) ≤
        branchMass P (sideBranches P 1) := by exact_mod_cast hmassNat
    nlinarith only [hminor, hmass, hmassLe, htq]

end Erdos547b.ZhaoSourceExceptionalRootExchange

#print axioms Erdos547b.ZhaoSourceExceptionalRootExchange.unbalancedAway_swap
#print axioms Erdos547b.ZhaoSourceExceptionalRootExchange.nonextremeAway_swap
#print axioms Erdos547b.ZhaoSourceExceptionalRootExchange.balancedSide_eq_zero_of_smallMinor
