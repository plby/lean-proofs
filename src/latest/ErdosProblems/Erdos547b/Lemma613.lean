/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Stability
import ErdosProblems.Erdos547b.GallaiEdmonds
import Mathlib

/-!
# The matching degree-balance core of Zhao's Lemma 6.13

For a cluster matching `M`, write `a e` and `b e` for the contributions of
the matching edge `e` to `deg(A, M)` and `deg(B, M)`.  Zhao splits `M` into
`M⁺ = {e : a e > b e}` and its complement.  When the total contributions at
`A` and `B` agree, the excess on `M⁺` is the largest possible absolute
difference on any submatching.  This file proves that assertion for arbitrary
finite weighted families and then specializes it to the edge set of a genuine
Mathlib matching.

The final theorem is the precise logical degree-balance implication used in
Lemma 6.13: if the remaining (embedding) part of the lemma turns an excess at
least `bound` into the target copy, then absence of the target copy forces
every submatching to have degree difference strictly below `bound`.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoStability

open SimpleGraph

section FiniteWeightedFamily

variable {E : Type*} [DecidableEq E]

/-- Zhao's `M⁺`: those matching edges whose contribution at `A` is larger. -/
def matchingPositivePart (M : Finset E) (a b : E → ℝ) : Finset E :=
  M.filter fun e => b e < a e

/-- The total positive excess `a⁺ - b⁺` on Zhao's `M⁺`. -/
def matchingPositiveExcess (M : Finset E) (a b : E → ℝ) : ℝ :=
  ∑ e ∈ matchingPositivePart M a b, (a e - b e)

@[simp] theorem mem_matchingPositivePart {M : Finset E} {a b : E → ℝ} {e : E} :
    e ∈ matchingPositivePart M a b ↔ e ∈ M ∧ b e < a e := by
  simp [matchingPositivePart]

theorem matchingPositivePart_subset (M : Finset E) (a b : E → ℝ) :
    matchingPositivePart M a b ⊆ M := by
  intro e he
  exact (mem_matchingPositivePart.mp he).1

theorem sum_difference_le_matchingPositiveExcess
    (M S : Finset E) (a b : E → ℝ) (hS : S ⊆ M) :
    (∑ e ∈ S, a e) - (∑ e ∈ S, b e) ≤ matchingPositiveExcess M a b := by
  classical
  rw [← Finset.sum_sub_distrib]
  have hsplit :
      (∑ e ∈ S, (a e - b e)) =
        (∑ e ∈ S.filter (fun e => b e < a e), (a e - b e)) +
          ∑ e ∈ S.filter (fun e => ¬ b e < a e), (a e - b e) := by
    rw [← Finset.sum_filter_add_sum_filter_not S (fun e => b e < a e)]
  rw [hsplit]
  calc
    (∑ e ∈ S.filter (fun e => b e < a e), (a e - b e)) +
          ∑ e ∈ S.filter (fun e => ¬ b e < a e), (a e - b e)
        ≤ (∑ e ∈ S.filter (fun e => b e < a e), (a e - b e)) + 0 := by
          gcongr
          exact Finset.sum_nonpos fun e he => sub_nonpos.mpr (le_of_not_gt (Finset.mem_filter.mp he).2)
    _ = ∑ e ∈ S.filter (fun e => b e < a e), (a e - b e) := by simp
    _ ≤ ∑ e ∈ matchingPositivePart M a b, (a e - b e) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro e he
        have heS := (Finset.mem_filter.mp he).1
        have hepos := (Finset.mem_filter.mp he).2
        exact mem_matchingPositivePart.mpr ⟨hS heS, hepos⟩
      · intro e he_big _
        exact sub_nonneg.mpr (le_of_lt (mem_matchingPositivePart.mp he_big).2)
    _ = matchingPositiveExcess M a b := rfl

/-- If the total `A`- and `B`-degrees agree, every submatching's absolute
degree difference is at most the excess on `M⁺`. -/
theorem abs_sum_difference_le_matchingPositiveExcess
    (M S : Finset E) (a b : E → ℝ) (hS : S ⊆ M)
    (htotal : (∑ e ∈ M, a e) = ∑ e ∈ M, b e) :
    |(∑ e ∈ S, a e) - (∑ e ∈ S, b e)| ≤ matchingPositiveExcess M a b := by
  classical
  apply abs_le.mpr
  constructor
  · have hcomp := sum_difference_le_matchingPositiveExcess
      M (M \ S) a b (Finset.sdiff_subset)
    have hdecompA : (∑ e ∈ M, a e) = (∑ e ∈ S, a e) + ∑ e ∈ M \ S, a e := by
      have h := Finset.sum_sdiff hS (f := a)
      linarith
    have hdecompB : (∑ e ∈ M, b e) = (∑ e ∈ S, b e) + ∑ e ∈ M \ S, b e := by
      have h := Finset.sum_sdiff hS (f := b)
      linarith
    linarith
  · exact sum_difference_le_matchingPositiveExcess M S a b hS

/-- The positive part itself attains the upper bound.  Thus the preceding
bound is sharp, matching Zhao's identity
`a⁺ - b⁺ = max_{M' ⊆ M} |deg(A,M') - deg(B,M')|`. -/
theorem matchingPositivePart_attains_excess (M : Finset E) (a b : E → ℝ) :
    (∑ e ∈ matchingPositivePart M a b, a e) -
        (∑ e ∈ matchingPositivePart M a b, b e) =
      matchingPositiveExcess M a b := by
  simp only [matchingPositiveExcess, ← Finset.sum_sub_distrib]

/-- Exact maximum characterization of Zhao's positive excess. -/
theorem matchingPositiveExcess_isGreatest_abs_difference
    (M : Finset E) (a b : E → ℝ)
    (htotal : (∑ e ∈ M, a e) = ∑ e ∈ M, b e) :
    IsGreatest
      {x : ℝ | ∃ S : Finset E, S ⊆ M ∧
        x = |(∑ e ∈ S, a e) - (∑ e ∈ S, b e)|}
      (matchingPositiveExcess M a b) := by
  constructor
  · refine ⟨matchingPositivePart M a b, matchingPositivePart_subset M a b, ?_⟩
    rw [matchingPositivePart_attains_excess]
    have hnonneg : 0 ≤ matchingPositiveExcess M a b := by
      apply Finset.sum_nonneg
      intro e he
      exact sub_nonneg.mpr (le_of_lt (mem_matchingPositivePart.mp he).2)
    exact (abs_of_nonneg hnonneg).symm
  · rintro x ⟨S, hS, rfl⟩
    exact abs_sum_difference_le_matchingPositiveExcess M S a b hS htotal

/-- The matching-degree conclusion of Zhao's Lemma 6.13.  `target` is the
statement `T ⊂ G`; `hlarge_excess_embeds` is precisely the preceding part of
Zhao's proof (the application of Lemma 6.5 after the ratio-ordering argument).
The conclusion is the strict degree balance for every submatching. -/
theorem zhaoLemma613_matchingDegreeBalance
    (M : Finset E) (a b : E → ℝ) (fb delta bound : ℝ) (target : Prop)
    (htotal : (∑ e ∈ M, a e) = ∑ e ∈ M, b e)
    (hfb : delta ≤ fb)
    (hlarge_excess_embeds :
      delta ≤ fb → bound ≤ matchingPositiveExcess M a b → target)
    (hnot_target : ¬ target) :
    ∀ S : Finset E, S ⊆ M →
      |(∑ e ∈ S, a e) - (∑ e ∈ S, b e)| < bound := by
  have hexcess_lt : matchingPositiveExcess M a b < bound := by
    by_contra h
    exact hnot_target (hlarge_excess_embeds hfb (le_of_not_gt h))
  intro S hS
  exact lt_of_le_of_lt
    (abs_sum_difference_le_matchingPositiveExcess M S a b hS htotal)
    hexcess_lt

/-- Zhao's published constants in Lemma 6.13.  The weights are already the
unnormalized quantities contributing to `deg(A, M)` and `deg(B, M)`; hence
both total degrees are `(1 - 10 √d)n`, the forest-side lower bound is
`d^(1/4)n`, and the asserted discrepancy bound is `15 d^(1/4)n`.

As above, the hypothesis `hlarge_excess_embeds` is the separately proved
embedding implication obtained in the paper from Lemma 6.5 Part 1. -/
theorem zhaoLemma613_matchingDegreeBalance_exactScale
    (M : Finset E) (a b : E → ℝ) (d : ℝ) (n : ℕ) (fb : ℝ) (target : Prop)
    (htotalA : (∑ e ∈ M, a e) = (1 - 10 * Real.sqrt d) * n)
    (htotalB : (∑ e ∈ M, b e) = (1 - 10 * Real.sqrt d) * n)
    (hfb : Real.rpow d (1 / 4 : ℝ) * n ≤ fb)
    (hlarge_excess_embeds :
      Real.rpow d (1 / 4 : ℝ) * n ≤ fb →
      15 * (Real.rpow d (1 / 4 : ℝ) * n) ≤ matchingPositiveExcess M a b →
      target)
    (hnot_target : ¬ target) :
    ∀ S : Finset E, S ⊆ M →
      |(∑ e ∈ S, a e) - (∑ e ∈ S, b e)| <
        15 * (Real.rpow d (1 / 4 : ℝ) * n) := by
  apply zhaoLemma613_matchingDegreeBalance M a b fb
    (Real.rpow d (1 / 4 : ℝ) * n)
    (15 * (Real.rpow d (1 / 4 : ℝ) * n)) target
  · exact htotalA.trans htotalB.symm
  · exact hfb
  · exact hlarge_excess_embeds
  · exact hnot_target

end FiniteWeightedFamily

section GenuineMatching

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The ambient edge finset of a finite subgraph.  Unlike `M.coe.edgeFinset`,
this keeps edges in `Sym2 V`, which is the natural type for cluster weights. -/
def subgraphEdgeFinset (M : G.Subgraph) : Finset (Sym2 V) := by
  classical
  exact Finset.univ.filter fun e => e ∈ M.edgeSet

@[simp] theorem mem_subgraphEdgeFinset {M : G.Subgraph} {e : Sym2 V} :
    e ∈ subgraphEdgeFinset M ↔ e ∈ M.edgeSet := by
  simp [subgraphEdgeFinset]

theorem subgraphEdgeFinset_mono {M N : G.Subgraph} (hNM : N ≤ M) :
    subgraphEdgeFinset N ⊆ subgraphEdgeFinset M := by
  intro e he
  rw [mem_subgraphEdgeFinset] at he ⊢
  exact Subgraph.edgeSet_mono hNM he

/-- Degree of a cluster at a genuine Mathlib matching, from per-edge weights. -/
def matchingWeightedDegree (M : G.Subgraph) (w : Sym2 V → ℝ) : ℝ :=
  ∑ e ∈ subgraphEdgeFinset M, w e

/-- Zhao's Lemma 6.13 degree-balance conclusion, specialized to a genuine
subgraph matching. -/
theorem zhaoLemma613_for_isMatching
    (M : G.Subgraph) (_hM : M.IsMatching) (a b : Sym2 V → ℝ)
    (fb delta bound : ℝ) (target : Prop)
    (htotal : matchingWeightedDegree M a = matchingWeightedDegree M b)
    (hfb : delta ≤ fb)
    (hlarge_excess_embeds : delta ≤ fb →
      bound ≤ matchingPositiveExcess (subgraphEdgeFinset M) a b → target)
    (hnot_target : ¬ target) :
    ∀ N : G.Subgraph, N.IsMatching → N ≤ M →
      |matchingWeightedDegree N a - matchingWeightedDegree N b| < bound := by
  intro N _hN hNM
  exact zhaoLemma613_matchingDegreeBalance (subgraphEdgeFinset M) a b
    fb delta bound target htotal hfb hlarge_excess_embeds hnot_target
    (subgraphEdgeFinset N) (subgraphEdgeFinset_mono hNM)

end GenuineMatching

end Erdos547b.ZhaoStability

#print axioms Erdos547b.ZhaoStability.matchingPositiveExcess_isGreatest_abs_difference
#print axioms Erdos547b.ZhaoStability.zhaoLemma613_matchingDegreeBalance
#print axioms Erdos547b.ZhaoStability.zhaoLemma613_matchingDegreeBalance_exactScale
#print axioms Erdos547b.ZhaoStability.zhaoLemma613_for_isMatching
