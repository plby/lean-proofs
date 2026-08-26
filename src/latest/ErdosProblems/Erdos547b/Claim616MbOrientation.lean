/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim616HierarchicalHostPools
import ErdosProblems.Erdos547b.RichClaim61Lemma611

/-!
# Canonical B-facing orientation of the optional matching

The decreasing-prefix construction of `M_b` now retains that every selected
edge has positive singleton `B`-degree.  This module turns that literal
positive sum into a canonical raw endpoint and then applies the symmetric
`B`-row reduced-adjacency conclusion of the rich Lemma 6.11 package.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim616MbOrientation

open Finset SimpleGraph
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoClaim616HierarchicalHostPools
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoQuantitativeLargeClusters

universe u v

/-- Choose the first raw endpoint when it has positive `B`-density, and the
second raw endpoint otherwise. -/
def positiveRawSide
    {K : Type u} [Fintype K] [DecidableEq K]
    {R : SimpleGraph K} {L : Finset K}
    (M : R.Subgraph) (density : K → K → ℝ) (B : K)
    (e : MatchingEdge M) : Fin 2 :=
  if 0 < density B (matchingEdgeEndpoint e.1 0) then 0 else 1

/-- A positive singleton source degree supplies a positive raw endpoint.
This is independent of whether the canonical large-endpoint orientation
swaps the two raw endpoints. -/
theorem density_positive_at_positiveRawSide
    {K : Type u} [Fintype K] [DecidableEq K]
    {R : SimpleGraph K} {L : Finset K}
    (M : R.Subgraph) (density : K → K → ℝ) (N : ℝ) (B : K)
    (e : MatchingEdge M) (hN : 0 < N)
    (hpositive : 0 < sourceDegree M L density N B {e}) :
    0 < density B
      (matchingEdgeEndpoint e.1 (positiveRawSide M density B e)) := by
  have hcontribution :
      0 < N * (density B (orientedEndpoint M L e 0) +
        density B (orientedEndpoint M L e 1)) := by
    simpa [sourceDegree_eq_sum] using hpositive
  have hsum : 0 < density B (orientedEndpoint M L e 0) +
      density B (orientedEndpoint M L e 1) := by
    rcases (mul_pos_iff.mp hcontribution) with h | h
    · exact h.2
    · exact False.elim ((not_lt_of_ge hN.le) h.1)
  have hrawSum : 0 < density B (matchingEdgeEndpoint e.1 0) +
      density B (matchingEdgeEndpoint e.1 1) := by
    by_cases hlarge : e.1.out.1 ∈ L
    · simpa [orientedEndpoint, rawEndpoint, matchingEdgeEndpoint, hlarge]
        using hsum
    · simpa [orientedEndpoint, rawEndpoint, matchingEdgeEndpoint, hlarge,
        add_comm] using hsum
  by_cases hfirst : 0 < density B (matchingEdgeEndpoint e.1 0)
  · simpa [positiveRawSide, hfirst] using hfirst
  · have hsecond : 0 < density B (matchingEdgeEndpoint e.1 1) := by
      linarith [le_of_not_gt hfirst]
    simpa [positiveRawSide, hfirst] using hsecond

section Rich

variable {Bv : Type u} {I : Type v}
variable [Fintype Bv] [DecidableEq Bv] [Fintype I] [DecidableEq I]
variable (Pcluster : ClusterAssignment Bv I)
variable (Gdegree : SimpleGraph Bv) [DecidableRel Gdegree.Adj]
variable (threshold quota : ℕ) (R0 : SimpleGraph I) [DecidableRel R0.Adj]
variable (miss : ℕ)
variable
  (Q : RichClaim61Certificate Pcluster Gdegree threshold quota R0
    (largeClustersAtLeast Pcluster Gdegree threshold quota) miss)
variable (density : EvenPadding I → EvenPadding I → ℝ)
variable (N eta targetA targetB fb cutoff : ℝ)
variable (lowerV1 upperV1 upperV2 mbEdgesBound mbBound : ℕ)
variable (lowerA lowerB exceptionalBound : ℝ)
variable
  (O : RichLemma611Output Pcluster Gdegree threshold quota R0 miss Q density
    N eta targetA targetB fb cutoff lowerV1 upperV1 upperV2 mbEdgesBound
    mbBound lowerA lowerB exceptionalBound)

/-- The literal raw endpoint orientation used for `F_b` branches. -/
def mbRootSide
    (e : Fin O.D.Mb.edgeSet.toFinite.toFinset.card) : Fin 2 :=
  positiveRawSide Q.claim67.M density (Sum.inl Q.B)
    (mbOriginalEdge O.D e)

/-- Every indexed `M_b` edge is oriented toward a genuinely positive
`B`-density endpoint.  In the large-`f_b` branch the indexed edge type is
empty, so the conclusion follows from the stored `M_b = ∅` identity. -/
theorem mbRootSide_density_pos
    (hN : 0 < N)
    (e : Fin O.D.Mb.edgeSet.toFinite.toFinset.card) :
    0 < density (Sum.inl Q.B)
      (matchingEdgeEndpoint (mbOriginalEdge O.D e).1
        (mbRootSide Pcluster Gdegree threshold quota R0 miss Q density N eta
          targetA targetB fb cutoff lowerV1 upperV1 upperV2 mbEdgesBound
          mbBound lowerA lowerB exceptionalBound O e)) := by
  apply density_positive_at_positiveRawSide Q.claim67.M density N
    (Sum.inl Q.B) (mbOriginalEdge O.D e) hN
  by_cases hsmall : fb < cutoff
  · exact O.reservedCapacity.small_singleton_pos hsmall
      (mbOriginalEdge O.D e) (mbOriginalEdge_mem_mbEdges O.D e)
  · have hempty := O.reservedCapacity.large_empty hsmall
    exact False.elim (by
      have he := mbOriginalEdge_mem_mbEdges O.D e
      rw [hempty] at he
      simpa using he)

/-- The B-facing endpoint of every actual `M_b` edge is adjacent in the
literal rich reduced graph. -/
theorem mbRootSide_adj_B
    (hN : 0 < N)
    (e : Fin O.D.Mb.edgeSet.toFinite.toFinset.card) :
    (padGraph R0).Adj (Sum.inl Q.B)
      (matchingEdgeEndpoint (mbOriginalEdge O.D e).1
        (mbRootSide Pcluster Gdegree threshold quota R0 miss Q density N eta
          targetA targetB fb cutoff lowerV1 upperV1 upperV2 mbEdgesBound
          mbBound lowerA lowerB exceptionalBound O e)) :=
  O.sourceDensityAdjB _
    (mbRootSide_density_pos Pcluster Gdegree threshold quota R0 miss Q density
      N eta targetA targetB fb cutoff lowerV1 upperV1 upperV2 mbEdgesBound
      mbBound lowerA lowerB exceptionalBound O hN e)

/-- Equality-only transport of the canonical B-attachment fact.  The rich
Claim 6.1 adapter uses this with `padGraph_regularityReducedGraph`; no graph
isomorphism or duplicated decomposition is introduced. -/
theorem mbRootSide_adj_B_of_eq
    (S : SimpleGraph (EvenPadding I))
    (hEq : padGraph R0 = S)
    (hN : 0 < N)
    (e : Fin O.D.Mb.edgeSet.toFinite.toFinset.card) :
    S.Adj (Sum.inl Q.B)
      (matchingEdgeEndpoint (mbOriginalEdge O.D e).1
        (mbRootSide Pcluster Gdegree threshold quota R0 miss Q density N eta
          targetA targetB fb cutoff lowerV1 upperV1 upperV2 mbEdgesBound
          mbBound lowerA lowerB exceptionalBound O e)) := by
  rw [← hEq]
  exact mbRootSide_adj_B Pcluster Gdegree threshold quota R0 miss Q density N
    eta targetA targetB fb cutoff lowerV1 upperV1 upperV2 mbEdgesBound mbBound
    lowerA lowerB exceptionalBound O hN e

end Rich

section PaddedRegularity

variable {Bv : Type u} {I : Type v}
variable [Fintype Bv] [DecidableEq Bv] [Fintype I] [DecidableEq I]
variable (Gdegree Hregular : SimpleGraph Bv)
variable [DecidableRel Gdegree.Adj] [DecidableRel Hregular.Adj]
variable (Pcluster : ClusterAssignment Bv I) (cluster : I → Finset Bv)
variable (epsilon reducedDensity : ℚ)
variable [DecidableRel
  (regularityReducedGraph Hregular cluster epsilon reducedDensity).Adj]
variable (threshold quota miss : ℕ)
variable
  (Q : RichClaim61Certificate Pcluster Gdegree threshold quota
    (regularityReducedGraph Hregular cluster epsilon reducedDensity)
    (largeClustersAtLeast Pcluster Gdegree threshold quota) miss)
variable (density : EvenPadding I → EvenPadding I → ℝ)
variable (N eta targetA targetB fb cutoff : ℝ)
variable (lowerV1 upperV1 upperV2 mbEdgesBound mbBound : ℕ)
variable (lowerA lowerB exceptionalBound : ℝ)
variable
  (O : RichLemma611Output Pcluster Gdegree threshold quota
    (regularityReducedGraph Hregular cluster epsilon reducedDensity) miss Q
    density N eta targetA targetB fb cutoff lowerV1 upperV1 upperV2
    mbEdgesBound mbBound lowerA lowerB exceptionalBound)

/-- The canonical `M_b` root endpoint is adjacent to the distinguished
`B` cluster in the definitionally concrete padded regularity reduced graph. -/
theorem mbRootSide_adj_B_paddedRegularity
    (hreducedDensity : 0 < reducedDensity)
    (hN : 0 < N)
    (e : Fin O.D.Mb.edgeSet.toFinite.toFinset.card) :
    (regularityReducedGraph Hregular (padCluster cluster) epsilon
      reducedDensity).Adj (Sum.inl Q.B)
        (matchingEdgeEndpoint (mbOriginalEdge O.D e).1
          (mbRootSide Pcluster Gdegree threshold quota
            (regularityReducedGraph Hregular cluster epsilon reducedDensity)
            miss Q density N eta targetA targetB fb cutoff lowerV1 upperV1
            upperV2 mbEdgesBound mbBound lowerA lowerB exceptionalBound O e)) := by
  apply mbRootSide_adj_B_of_eq Pcluster Gdegree threshold quota
    (regularityReducedGraph Hregular cluster epsilon reducedDensity) miss Q
    density N eta targetA targetB fb cutoff lowerV1 upperV1 upperV2
    mbEdgesBound mbBound lowerA lowerB exceptionalBound O
    (regularityReducedGraph Hregular (padCluster cluster) epsilon reducedDensity)
    (padGraph_regularityReducedGraph Hregular cluster epsilon reducedDensity
      hreducedDensity) hN e

end PaddedRegularity

end Erdos547b.ZhaoClaim616MbOrientation

#print axioms Erdos547b.ZhaoClaim616MbOrientation.mbRootSide_adj_B
#print axioms Erdos547b.ZhaoClaim616MbOrientation.mbRootSide_adj_B_paddedRegularity
