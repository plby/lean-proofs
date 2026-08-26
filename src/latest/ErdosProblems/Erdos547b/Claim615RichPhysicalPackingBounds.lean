/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichPhysicalEdgeFamilies
import ErdosProblems.Erdos547b.Section6EventualParameters

/-!
# Deletion bounds for the physical Claim-6.15 edge families

The exceptional and reserved families are chosen before the Lemma-6.11
matching decomposition.  Their removal from the full Claim-6.7 matching is
therefore controlled directly by the per-edge source-degree cap.  This file
records that elementary estimate once, in the literal `sourceDegree` notation
used by both physical exceptional cases.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim615RichPhysicalPackingBounds

open Finset SimpleGraph
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoClaim615RichHierarchicalAllocation
open Erdos547b.ZhaoRoundedScales
open Erdos547b.ZhaoSection6EventualParameters

universe u

variable {K : Type u} [Fintype K] [DecidableEq K]
variable {R : SimpleGraph K} [DecidableRel R.Adj]

/-- Deleting two finite edge families costs at most `2*N` per edge.  The
families need not be disjoint; using the sum of their cardinalities is the
uniform estimate needed before the physical Claim-6.15 package is built. -/
theorem sourceDegree_le_sdiff_union_add
    (M : R.Subgraph) (L : Finset K) (density : K → K → ℝ)
    (N : ℝ) (C : K) (E B : Finset (MatchingEdge M))
    (hN : 0 ≤ N)
    (hE : E ⊆ allMatchingEdges M) (hB : B ⊆ allMatchingEdges M)
    (hcap : ∀ e : MatchingEdge M,
      N * (density C (orientedEndpoint M L e 0) +
        density C (orientedEndpoint M L e 1)) ≤ 2 * N) :
    sourceDegree M L density N C (allMatchingEdges M) ≤
      sourceDegree M L density N C (allMatchingEdges M \ (E ∪ B)) +
        ((E.card + B.card : ℕ) : ℝ) * (2 * N) := by
  let contribution := fun e : MatchingEdge M ↦
    N * (density C (orientedEndpoint M L e 0) +
      density C (orientedEndpoint M L e 1))
  have hU : E ∪ B ⊆ allMatchingEdges M := Finset.union_subset hE hB
  have hsplit :
      (∑ e ∈ allMatchingEdges M, contribution e) =
        (∑ e ∈ allMatchingEdges M \ (E ∪ B), contribution e) +
          ∑ e ∈ E ∪ B, contribution e := by
    simpa only [add_comm] using
      (Finset.sum_sdiff hU (f := contribution)).symm
  have hcard : (E ∪ B).card ≤ E.card + B.card := Finset.card_union_le E B
  have hdeleted :
      (∑ e ∈ E ∪ B, contribution e) ≤
        ((E.card + B.card : ℕ) : ℝ) * (2 * N) := by
    calc
      (∑ e ∈ E ∪ B, contribution e) ≤
          ∑ _e ∈ E ∪ B, 2 * N := by
            exact Finset.sum_le_sum fun e _he ↦ hcap e
      _ = (((E ∪ B).card : ℕ) : ℝ) * (2 * N) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((E.card + B.card : ℕ) : ℝ) * (2 * N) := by
            apply mul_le_mul_of_nonneg_right
            · exact_mod_cast hcard
            · positivity
  rw [sourceDegree_eq_sum, sourceDegree_eq_sum, hsplit]
  linarith

/-- Strict total source degree beyond the two deletion costs leaves a
strictly positive physical remainder. -/
theorem sourceDegree_sdiff_union_pos
    (M : R.Subgraph) (L : Finset K) (density : K → K → ℝ)
    (N : ℝ) (C : K) (E B : Finset (MatchingEdge M))
    (hN : 0 ≤ N)
    (hE : E ⊆ allMatchingEdges M) (hB : B ⊆ allMatchingEdges M)
    (hcap : ∀ e : MatchingEdge M,
      N * (density C (orientedEndpoint M L e 0) +
        density C (orientedEndpoint M L e 1)) ≤ 2 * N)
    (htotal : ((E.card + B.card : ℕ) : ℝ) * (2 * N) <
      sourceDegree M L density N C (allMatchingEdges M)) :
    0 < sourceDegree M L density N C
      (allMatchingEdges M \ (E ∪ B)) := by
  have h := sourceDegree_le_sdiff_union_add M L density N C E B hN hE hB hcap
  linarith

universe v w

variable {Bv : Type v} {I : Type w}
variable [Fintype Bv] [DecidableEq Bv] [Fintype I] [DecidableEq I]
variable {Pcluster : ClusterAssignment Bv I}
variable {Gdegree : SimpleGraph Bv} [DecidableRel Gdegree.Adj]
variable {threshold quota : ℕ} {R0 : SimpleGraph I} [DecidableRel R0.Adj]
variable {miss : ℕ}

/-- The preceding deletion lemma specialized to the two actual physical
families.  Their subset facts are part of the selected-edge records, so the
caller only supplies the numerical strict surplus. -/
theorem physicalRemaining_sourceDegree_pos
    (Q : RichClaim61Certificate Pcluster Gdegree threshold quota R0
      (largeClustersAtLeast Pcluster Gdegree threshold quota) miss)
    (density : EvenPadding I → EvenPadding I → ℝ)
    {L : Finset (EvenPadding I)} {eta N targetB cap : ℝ}
    {which : ExceptionalCase} {count cardBound : ℕ}
    (E0 : SelectedExceptionalEdges Q density L eta which count)
    (Mb : PreliminaryReservedEdges Q density L N targetB cap cardBound)
    (hN : 0 ≤ N)
    (hcap : ∀ e : MatchingEdge Q.claim67.M,
      N * (density (Sum.inl Q.A) (orientedEndpoint Q.claim67.M L e 0) +
        density (Sum.inl Q.A) (orientedEndpoint Q.claim67.M L e 1)) ≤ 2 * N)
    (htotal : ((E0.selected.card + Mb.selected.card : ℕ) : ℝ) * (2 * N) <
      sourceDegree Q.claim67.M L density N (Sum.inl Q.A)
        (allMatchingEdges Q.claim67.M)) :
    0 < sourceDegree Q.claim67.M L density N (Sum.inl Q.A)
      (allMatchingEdges Q.claim67.M \ (E0.selected ∪ Mb.selected)) := by
  apply sourceDegree_sdiff_union_pos Q.claim67.M L density N (Sum.inl Q.A)
    E0.selected Mb.selected hN
  · intro e he
    have hef := E0.selected_subset he
    cases which <;> simpa [exceptionalFamily] using
      (Finset.mem_filter.mp hef).1
  · exact Mb.selected_subset
  · exact hcap
  · exact htotal

/-- Eventual-scale specialization.  The selected exceptional family has the
paper's half-threshold size and the preliminary reserved family has at most
`claim617Q` edges; the already proved Lemma-6.11 deletion inequality then
leaves a positive A-row on the physical remainder. -/
theorem physicalRemaining_sourceDegree_pos_eventual
    {beta : ℚ} (hbeta : 0 < beta) (hbetaOne : beta ≤ 1 / 4)
    {reducedK : ℕ}
    (Q : RichClaim61Certificate Pcluster Gdegree threshold quota R0
      (largeClustersAtLeast Pcluster Gdegree threshold quota) miss)
    (density : EvenPadding I → EvenPadding I → ℝ)
    {L : Finset (EvenPadding I)} {N targetB cap : ℝ} {cardBound : ℕ}
    {which : ExceptionalCase}
    (E0 : SelectedExceptionalEdges Q density L (eta beta : ℝ) which
      (upperScale (((eta beta : ℝ) * reducedK) / 2)))
    (Mb : PreliminaryReservedEdges Q density L N targetB cap cardBound)
    (hMb : Mb.selected.card ≤ claim617Q beta reducedK)
    {n : ℝ} (hN : 0 < N) (hn : 0 ≤ n)
    (hcluster : N ≤ 3 * (sigma beta : ℝ) * n)
    (hcover : (reducedK : ℝ) * N ≤ n + N)
    (hcap : ∀ e : MatchingEdge Q.claim67.M,
      N * (density (Sum.inl Q.A) (orientedEndpoint Q.claim67.M L e 0) +
        density (Sum.inl Q.A) (orientedEndpoint Q.claim67.M L e 1)) ≤ 2 * N)
    (hdegree : (1 - 10 * Real.sqrt (lemma611D beta)) * n + 4 * N ≤
      sourceDegree Q.claim67.M L density N (Sum.inl Q.A)
        (allMatchingEdges Q.claim67.M)) :
    0 < sourceDegree Q.claim67.M L density N (Sum.inl Q.A)
      (allMatchingEdges Q.claim67.M \ (E0.selected ∪ Mb.selected)) := by
  have heta0 : (0 : ℝ) < (eta beta : ℝ) := by
    exact_mod_cast eta_pos hbeta
  have hcountLe : E0.selected.card ≤ auxiliaryScale beta reducedK := by
    rw [E0.selected_card]
    have hhalfNonneg : 0 ≤ (eta beta : ℝ) * reducedK / 2 := by positivity
    have hcountCast :
        (upperScale (((eta beta : ℝ) * reducedK) / 2) : ℝ) <
          (eta beta : ℝ) * reducedK / 2 + 1 :=
      upperScale_cast_lt_add_one hhalfNonneg
    have hauxCast : (eta beta : ℝ) * reducedK ≤
        (auxiliaryScale beta reducedK : ℝ) :=
      le_upperScale_cast _
    have hreal :
        (upperScale (((eta beta : ℝ) * reducedK) / 2) : ℝ) <
          (auxiliaryScale beta reducedK : ℝ) + 1 := by
      nlinarith
    have hnat : upperScale (((eta beta : ℝ) * reducedK) / 2) <
        auxiliaryScale beta reducedK + 1 := by
      exact_mod_cast hreal
    omega
  have hcards : E0.selected.card + Mb.selected.card ≤
      auxiliaryScale beta reducedK + claim617Q beta reducedK := by omega
  have hcardsReal : ((E0.selected.card + Mb.selected.card : ℕ) : ℝ) ≤
      auxiliaryScale beta reducedK + claim617Q beta reducedK := by
    exact_mod_cast hcards
  have htargetNonneg : 0 ≤ lemma611TargetA beta n :=
    lemma611TargetA_nonneg hbeta hbetaOne hn
  have hdelete := lemma611_deletion_numeric hbeta hbetaOne hN hn hcluster hcover
  have hsurplus :
      ((E0.selected.card + Mb.selected.card : ℕ) : ℝ) * (2 * N) <
        (1 - 10 * Real.sqrt (lemma611D beta)) * n + 4 * N := by
    have hmul := mul_le_mul_of_nonneg_right hcardsReal
      (show 0 ≤ 2 * N by positivity)
    have hetaTerm : 0 ≤ 3 * (eta beta : ℝ) * N * reducedK := by positivity
    nlinarith
  apply physicalRemaining_sourceDegree_pos Q density E0 Mb hN.le hcap
  exact hsurplus.trans_le hdegree

end Erdos547b.ZhaoClaim615RichPhysicalPackingBounds

#print axioms Erdos547b.ZhaoClaim615RichPhysicalPackingBounds.sourceDegree_le_sdiff_union_add
#print axioms Erdos547b.ZhaoClaim615RichPhysicalPackingBounds.sourceDegree_sdiff_union_pos
#print axioms Erdos547b.ZhaoClaim615RichPhysicalPackingBounds.physicalRemaining_sourceDegree_pos
#print axioms Erdos547b.ZhaoClaim615RichPhysicalPackingBounds.physicalRemaining_sourceDegree_pos_eventual
