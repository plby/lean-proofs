/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim616RichCoordinateCapacitySplitApplication
import ErdosProblems.Erdos547b.RichClaim61Lemma611
import ErdosProblems.Erdos547b.Lemma611RootAccess
import ErdosProblems.Erdos547b.Claim616RichCoordinateMbOrientation

/-!
# Coordinate facts extracted from the rich Lemma 6.11 output

These are the exact source-degree and root-adjacency facts needed by the
capacity-split coordinate application.  No host embedding or result is an
input.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim616RichCoordinateOutputFacts

open Finset SimpleGraph
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoLemma611CapacitySplit
open Erdos547b.ZhaoLemma611RootAccess
open Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoClaim616RichCoordinateMbOrientation
open Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoQuantitativeLargeClusters

universe u v

variable {B : Type u} {I : Type v}
variable [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]
variable (Pcluster : ClusterAssignment B I)
variable (Gdegree : SimpleGraph B) [DecidableRel Gdegree.Adj]
variable (threshold quota : ℕ) (R0 : SimpleGraph I) [DecidableRel R0.Adj]
variable (miss : ℕ)
variable
  (Q : RichClaim61Certificate Pcluster Gdegree threshold quota R0
    (largeClustersAtLeast Pcluster Gdegree threshold quota) miss)
variable (sourceDensity : EvenPadding I → EvenPadding I → ℝ)
variable (N eta targetA targetB fb cutoff : ℝ)
variable (lowerV1 upperV1 upperV2 mbEdgesBound mbBound : ℕ)
variable (lowerA lowerB exceptionalBound : ℝ)
variable
  (O : RichLemma611Output Pcluster Gdegree threshold quota R0 miss Q
    sourceDensity N eta targetA targetB fb cutoff lowerV1 upperV1 upperV2
    mbEdgesBound mbBound lowerA lowerB exceptionalBound)

/-- The clean `M_in` endpoints are all adjacent to the distinguished
`A`-cluster in the literal padded reduced graph. -/
theorem rich_V1_adj_A
    (heta : 0 < eta) (hetaHalf : eta < 1 / 2) :
    ∀ x ∈ O.D.V1, (padGraph R0).Adj (Sum.inl Q.A) x :=
  V1_adj_distinguished_of_min_subset_clean O.D O.min_subset_clean heta
    hetaHalf O.sourceDensityAdjA

/-- The exact `M_in \ M₀` subtraction is strictly positive under the
displayed residual-mass and `M₀` scalar margins. -/
theorem rich_remaining_sourceDegree_pos
    (C : Finset (EvenPadding I))
    (n f0 f1 epsilon1 epsilon2 gamma : ℝ)
    (hn : 0 ≤ n)
    (hMinTarget : (1 - epsilon1) * n ≤ targetA)
    (hdensityOne : ∀ e ∈ reservedMinEdges O.D C, ∀ c,
      sourceDensity (Sum.inl Q.A)
        (orientedEndpoint Q.claim67.M
          (padFinset (largeClustersAtLeast Pcluster Gdegree threshold quota))
          e c) ≤ 1)
    (hMzeroScalar : 2 * N * C.card ≤ f0 - epsilon2 * n)
    (hforest : f0 + f1 ≤ n)
    (hhierarchy : 3 * gamma ≤ epsilon2 - epsilon1)
    (hpositive : 0 < f1 + 3 * gamma * n)
    (hN : 0 ≤ N) :
    0 < sourceDegree Q.claim67.M
      (padFinset (largeClustersAtLeast Pcluster Gdegree threshold quota))
      sourceDensity N (Sum.inl Q.A) (remainingMinEdges O.D C) := by
  have hMin : (1 - epsilon1) * n ≤
      sourceDegree Q.claim67.M
        (padFinset (largeClustersAtLeast Pcluster Gdegree threshold quota))
        sourceDensity N (Sum.inl Q.A) O.D.minEdges := by
    calc
      (1 - epsilon1) * n ≤ targetA := hMinTarget
      _ = O.D.targetA := O.targetA_eq.symm
      _ ≤ sourceDegree Q.claim67.M
          (padFinset (largeClustersAtLeast Pcluster Gdegree threshold quota))
          sourceDensity N (Sum.inl Q.A) O.D.minEdges :=
        O.D.degreeA_target_lower.le
  have hMzero : sourceDegree Q.claim67.M
      (padFinset (largeClustersAtLeast Pcluster Gdegree threshold quota))
      sourceDensity N (Sum.inl Q.A) (reservedMinEdges O.D C) ≤
        f0 - epsilon2 * n :=
    (reserved_A_capacity_upper O.D C sourceDensity N (Sum.inl Q.A) hN
      hdensityOne).trans hMzeroScalar
  exact hpositive.trans_le
    (remaining_A_capacity O.D C sourceDensity N (Sum.inl Q.A) n f0 f1
      epsilon1 epsilon2 gamma hn hMin hMzero hforest hhierarchy)

/-- The small-`f_b` capacity certificate makes the reserved matching degree
strictly positive whenever its target is positive. -/
theorem rich_reserved_sourceDegree_pos
    (hsmall : fb < cutoff) (htargetB : 0 < targetB) :
    0 < sourceDegree Q.claim67.M
      (padFinset (largeClustersAtLeast Pcluster Gdegree threshold quota))
      sourceDensity N (Sum.inl Q.B) O.D.mbEdges :=
  htargetB.trans_le (O.reservedCapacity.small_lower hsmall)

/-- Every literal reserved edge has a B-facing adjacent endpoint in the
small-`f_b` branch. -/
theorem rich_reservedRootSide_adj_B
    (hN : 0 < N) (hsmall : fb < cutoff)
    (e : {e : MatchingEdge Q.claim67.M // e ∈ O.D.mbEdges}) :
    (padGraph R0).Adj (Sum.inl Q.B)
      (matchingEdgeEndpoint e.1.1
        (reservedRootSide Pcluster Gdegree threshold quota R0 miss Q
          sourceDensity N eta targetA targetB fb cutoff lowerV1 upperV1 upperV2
          mbEdgesBound mbBound lowerA lowerB exceptionalBound O e)) := by
  exact reservedRootSide_adj_B Pcluster Gdegree threshold quota R0 miss Q
    sourceDensity N eta targetA targetB fb cutoff lowerV1 upperV1 upperV2
    mbEdgesBound mbBound lowerA lowerB exceptionalBound O hN hsmall e

end Erdos547b.ZhaoClaim616RichCoordinateOutputFacts

#print axioms Erdos547b.ZhaoClaim616RichCoordinateOutputFacts.rich_remaining_sourceDegree_pos
#print axioms Erdos547b.ZhaoClaim616RichCoordinateOutputFacts.rich_reserved_sourceDegree_pos
#print axioms Erdos547b.ZhaoClaim616RichCoordinateOutputFacts.rich_reservedRootSide_adj_B
