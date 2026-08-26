/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim616RichCoordinateAllocation
import ErdosProblems.Erdos547b.RichClaim61Lemma611

/-!
# B-facing orientation for literal coordinate reserved edges

This is the current `ReservedEdge D` version of the optional-matching
orientation.  It has no dependency on the obsolete hierarchical host-pool
modules.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim616RichCoordinateMbOrientation

open Finset SimpleGraph
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoClaim616RichCoordinateAllocation
open Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoQuantitativeLargeClusters

universe u v

/-- Choose the first raw endpoint when it has positive source density, and
the second endpoint otherwise. -/
def positiveRawSide
    {K : Type u} [Fintype K] [DecidableEq K]
    {R : SimpleGraph K} (M : R.Subgraph)
    (sourceDensity : K → K → ℝ) (Broot : K)
    (e : MatchingEdge M) : Fin 2 :=
  if 0 < sourceDensity Broot (matchingEdgeEndpoint e.1 0) then 0 else 1

/-- A positive singleton contribution supplies a positive raw endpoint. -/
theorem density_positive_at_positiveRawSide
    {K : Type u} [Fintype K] [DecidableEq K]
    {R : SimpleGraph K} (M : R.Subgraph) (L : Finset K)
    (sourceDensity : K → K → ℝ) (N : ℝ) (Broot : K)
    (e : MatchingEdge M) (hN : 0 < N)
    (hpositive : 0 < sourceDegree M L sourceDensity N Broot {e}) :
    0 < sourceDensity Broot
      (matchingEdgeEndpoint e.1
        (positiveRawSide M sourceDensity Broot e)) := by
  have hcontribution :
      0 < N * (sourceDensity Broot (orientedEndpoint M L e 0) +
        sourceDensity Broot (orientedEndpoint M L e 1)) := by
    simpa [sourceDegree_eq_sum] using hpositive
  have hsum : 0 < sourceDensity Broot (orientedEndpoint M L e 0) +
      sourceDensity Broot (orientedEndpoint M L e 1) := by
    rcases (mul_pos_iff.mp hcontribution) with h | h
    · exact h.2
    · exact False.elim ((not_lt_of_ge hN.le) h.1)
  have hrawSum : 0 < sourceDensity Broot (matchingEdgeEndpoint e.1 0) +
      sourceDensity Broot (matchingEdgeEndpoint e.1 1) := by
    by_cases hlarge : e.1.out.1 ∈ L
    · simpa [orientedEndpoint, rawEndpoint, matchingEdgeEndpoint, hlarge]
        using hsum
    · simpa [orientedEndpoint, rawEndpoint, matchingEdgeEndpoint, hlarge,
        add_comm] using hsum
  by_cases hfirst :
      0 < sourceDensity Broot (matchingEdgeEndpoint e.1 0)
  · simpa [positiveRawSide, hfirst] using hfirst
  · have hsecond :
        0 < sourceDensity Broot (matchingEdgeEndpoint e.1 1) := by
      linarith [le_of_not_gt hfirst]
    simpa [positiveRawSide, hfirst] using hsecond

section Rich

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

/-- Literal B-facing side of one current coordinate `ReservedEdge`. -/
def reservedRootSide (e : ReservedEdge O.D) : Fin 2 :=
  positiveRawSide Q.claim67.M sourceDensity (Sum.inl Q.B) e.1

theorem reservedRootSide_density_pos
    (hN : 0 < N) (hsmall : fb < cutoff) (e : ReservedEdge O.D) :
    0 < sourceDensity (Sum.inl Q.B)
      (matchingEdgeEndpoint e.1.1
        (reservedRootSide Pcluster Gdegree threshold quota R0 miss Q
          sourceDensity N eta targetA targetB fb cutoff lowerV1 upperV1 upperV2
          mbEdgesBound mbBound lowerA lowerB exceptionalBound O e)) := by
  apply density_positive_at_positiveRawSide Q.claim67.M
    (padFinset (largeClustersAtLeast Pcluster Gdegree threshold quota))
    sourceDensity N (Sum.inl Q.B) e.1 hN
  exact O.reservedCapacity.small_singleton_pos hsmall e.1 e.2

/-- The chosen literal reserved endpoint is adjacent to the distinguished
B cluster in the padded reduced graph. -/
theorem reservedRootSide_adj_B
    (hN : 0 < N) (hsmall : fb < cutoff) (e : ReservedEdge O.D) :
    (padGraph R0).Adj (Sum.inl Q.B)
      (matchingEdgeEndpoint e.1.1
        (reservedRootSide Pcluster Gdegree threshold quota R0 miss Q
          sourceDensity N eta targetA targetB fb cutoff lowerV1 upperV1 upperV2
          mbEdgesBound mbBound lowerA lowerB exceptionalBound O e)) :=
  O.sourceDensityAdjB _
    (reservedRootSide_density_pos Pcluster Gdegree threshold quota R0 miss Q
      sourceDensity N eta targetA targetB fb cutoff lowerV1 upperV1 upperV2
      mbEdgesBound mbBound lowerA lowerB exceptionalBound O hN hsmall e)

end Rich

end Erdos547b.ZhaoClaim616RichCoordinateMbOrientation

#print axioms Erdos547b.ZhaoClaim616RichCoordinateMbOrientation.reservedRootSide_adj_B
