/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim616

/-! Canonical `M₀`/`M₁` capacity split for Lemma 6.14(2). -/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoLemma611CapacitySplit

open Finset SimpleGraph
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616

universe u

variable {K : Type u} [Fintype K] [DecidableEq K]
variable {R : SimpleGraph K} [DecidableRel R.Adj]
variable {L O : Finset K} {miss lowerV1 upperV1 upperV2 mbBound : ℕ}
variable {C67 : Claim67Certificate R L miss}
variable {degreeA : Finset (MatchingEdge C67.M) → ℝ}
variable
  (D : MatchingDecomposition L O miss C67 lowerV1 upperV1 upperV2 mbBound
    degreeA)

/-- Zhao's `M₀`, typed in the original matching so source degree applies
definitionally. -/
abbrev reservedMinEdges (C : Finset K) : Finset (MatchingEdge C67.M) :=
  Erdos547b.ZhaoClaim616.MatchingDecomposition.MzeroEdges D C

/-- Zhao's `M₁ = M_in \ M₀`. -/
abbrev remainingMinEdges (C : Finset K) : Finset (MatchingEdge C67.M) :=
  Erdos547b.ZhaoClaim616.MatchingDecomposition.MoneEdges D C

abbrev reservedMin (C : Finset K) : R.Subgraph :=
  Erdos547b.ZhaoClaim616.MatchingDecomposition.Mzero D C
abbrev remainingMin (C : Finset K) : R.Subgraph :=
  Erdos547b.ZhaoClaim616.MatchingDecomposition.Mone D C

theorem reservedMinEdges_subset (C : Finset K) :
    reservedMinEdges D C ⊆ D.minEdges :=
  Erdos547b.ZhaoClaim616.MatchingDecomposition.MzeroEdges_subset_minEdges D C

theorem remainingMinEdges_subset (C : Finset K) :
    remainingMinEdges D C ⊆ D.minEdges :=
  Finset.sdiff_subset

theorem card_reservedMinEdges_le (C : Finset K) :
    (reservedMinEdges D C).card ≤ C.card :=
  Erdos547b.ZhaoClaim616.MatchingDecomposition.Mzero_edge_card_le D C

/-- This is the only source-set premise: `C ⊆ D.V1`, exactly as produced
by Claim 6.16. -/
theorem C_subset_reservedMin_support
    (C : Finset K) (hC : C ⊆ D.V1) :
    C ⊆ matchingSupport (reservedMin D C) :=
  Erdos547b.ZhaoClaim616.MatchingDecomposition.C_subset_Mzero_support D C hC

theorem reservedMin_isMatching (C : Finset K) :
    (reservedMin D C).IsMatching :=
  Erdos547b.ZhaoClaim616.MatchingDecomposition.Mzero_isMatching D C

theorem remainingMin_isMatching (C : Finset K) :
    (remainingMin D C).IsMatching :=
  Erdos547b.ZhaoClaim616.MatchingDecomposition.Mone_isMatching D C

theorem reserved_remaining_support_disjoint (C : Finset K) :
    Disjoint (matchingSupport (reservedMin D C))
      (matchingSupport (remainingMin D C)) :=
  Erdos547b.ZhaoClaim616.MatchingDecomposition.Mzero_Mone_support_disjoint D C

/-- With `|C|=rhoK`, this is the `M₀` upper bound before (6.23). -/
theorem reserved_A_capacity_upper
    (C : Finset K) (density : K → K → ℝ) (N : ℝ) (A : K)
    (hN : 0 ≤ N)
    (hdensity : ∀ e ∈ reservedMinEdges D C, ∀ c,
      density A (orientedEndpoint C67.M L e c) ≤ 1) :
    sourceDegree C67.M L density N A (reservedMinEdges D C) ≤
      2 * N * C.card :=
  Erdos547b.ZhaoClaim616.MatchingDecomposition.Mzero_sourceDegree_le
    D C density N A hN hdensity

/-- Literal capacity subtraction on the genuine residual submatching. -/
theorem remaining_A_capacity
    (C : Finset K) (density : K → K → ℝ) (N : ℝ) (A : K)
    (n f0 f1 epsilon1 epsilon2 gamma : ℝ)
    (hn : 0 ≤ n)
    (hMin : (1 - epsilon1) * n ≤
      sourceDegree C67.M L density N A D.minEdges)
    (hMzero : sourceDegree C67.M L density N A (reservedMinEdges D C) ≤
      f0 - epsilon2 * n)
    (hforest : f0 + f1 ≤ n)
    (hhierarchy : 3 * gamma ≤ epsilon2 - epsilon1) :
    f1 + 3 * gamma * n ≤
      sourceDegree C67.M L density N A (remainingMinEdges D C) :=
  Erdos547b.ZhaoClaim616.MatchingDecomposition.Mone_sourceDegree_lower
    D C density N A n f0 f1 epsilon1 epsilon2 gamma hn hMin hMzero
      hforest hhierarchy

/-- Actual `B`-degree capacity stored by the Lemma-6.11 constructor. -/
theorem reserved_B_capacity
    (degreeB : Finset (MatchingEdge C67.M) → ℝ)
    (targetB N fb cutoff : ℝ) (mbEdgesBound : ℕ)
    (H : OptionalReservedCapacity D degreeB targetB N fb cutoff mbEdgesBound)
    (hsmall : fb < cutoff) :
    targetB ≤ degreeB D.mbEdges :=
  H.small_lower hsmall

end Erdos547b.ZhaoLemma611CapacitySplit

#print axioms Erdos547b.ZhaoLemma611CapacitySplit.C_subset_reservedMin_support
#print axioms Erdos547b.ZhaoLemma611CapacitySplit.remaining_A_capacity
