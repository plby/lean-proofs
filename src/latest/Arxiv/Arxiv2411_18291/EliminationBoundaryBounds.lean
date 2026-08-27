import Arxiv.Arxiv2411_18291.SharpEliminationCounts
import Arxiv.Arxiv2411_18291.IndexedCliqueDegrees
import Arxiv.Arxiv2411_18291.CoefficientReduction

/-!
# Elimination boundary bounds without a repetition cap

On old edges, the remaining cliques are bounded by the two indexed root
families. New edges occur at most twice. Consequently balanced root degrees
give a constant boundary-degree loss even for large elimination groups.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {I W V : Type*} [Fintype I] [Fintype W] [Fintype V]
variable [DecidableEq W] [DecidableEq V] {q r : ℕ}
variable {S : ExchangeSystem W q (r + 1)} {N : Block W q} {e₀ : Block W (r + 1)}
variable {B : Hypergraph V (r + 1)} {P Q : I → Block V q} {θ : ℝ}

theorem EliminationFamily.boundary_le_indexed_roots (F : EliminationFamily S N B P Q θ)
    (hpair : IsEliminationPair S N e₀) (e : Block V (r + 1)) :
    boundary (r + 1) (indicator F.cliques) e ≤
      (familyDegree P e.val : ℤ) + (familyDegree Q e.val : ℤ) + 2 * indicator F.graph e := by
  rw [boundary_indicator]
  by_cases heB : e ∈ B
  · have h : ((F.cliques.filter fun R => e.val ⊆ R.val).card : ℤ) ≤
        (familyDegree P e.val : ℤ) + (familyDegree Q e.val : ℤ) := by
      exact_mod_cast F.clique_count_original_sharp hpair e heB
    rw [indicator_apply_of_mem (show e ∈ F.graph from mem_union_left _ heB)]
    omega
  · by_cases heG : e ∈ F.graph
    · have h : ((F.cliques.filter fun R => e.val ⊆ R.val).card : ℤ) ≤ 2 := by
        exact_mod_cast F.clique_count_outside hpair e heB
      rw [indicator_apply_of_mem heG]
      have hp : (0 : ℤ) ≤ familyDegree P e.val := Nat.cast_nonneg _
      have hq : (0 : ℤ) ≤ familyDegree Q e.val := Nat.cast_nonneg _
      omega
    · have hz : boundary (r + 1) (indicator F.cliques) e = 0 :=
        boundary_zero_outside_support F.cliques F.graph (indicator F.cliques)
          (fun R hR => indicator_apply_of_notMem hR) (F.cliques_support hpair) e heG
      rw [boundary_indicator] at hz
      rw [hz, indicator_apply_of_notMem heG, mul_zero, add_zero]
      positivity

theorem clique_boundary_bounded_of_indexed_roots
    (D : Finset (Block V q)) (G : Hypergraph V (r + 1)) {A : ℝ}
    (hG : IsGraphBounded G θ)
    (hroot : ∀ e : Block V (r + 1), boundary (r + 1) (indicator D) e ≤
      (familyDegree P e.val : ℤ) + (familyDegree Q e.val : ℤ) + 2 * indicator G e)
    (hP : ∀ T : Block V r, (familyDegree P T.val : ℝ) ≤ A * Fintype.card V)
    (hQ : ∀ T : Block V r, (familyDegree Q T.val : ℝ) ≤ A * Fintype.card V) :
    IsCliqueFamilyBounded r D (2 * ((q - r : ℕ) : ℝ) * A + 2 * θ) := by
  let JP : Block V (r + 1) → ℤ := ∑ i, indicator (cliqueEdges (r + 1) (P i))
  let JQ : Block V (r + 1) → ℤ := ∑ i, indicator (cliqueEdges (r + 1) (Q i))
  have hpoint (e : Block V (r + 1)) : boundary (r + 1) (indicator D) e ≤
      JP e + JQ e + 2 * indicator G e := by
    simpa only [JP, JQ, sum_clique_indicators_apply] using hroot e
  intro T
  have hdeg := degree_mono_int hpoint T.val
  have hsum : degree (fun e => JP e + JQ e + 2 * indicator G e) T.val =
      degree JP T.val + degree JQ T.val + 2 * degree (indicator G) T.val := by
    unfold degree
    rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro e _
    split_ifs <;> ring
  have hpdeg : degree JP T.val = ((q - r : ℕ) : ℤ) * familyDegree P T.val :=
    degree_sum_clique_indicators P T
  have hqdeg : degree JQ T.val = ((q - r : ℕ) : ℤ) * familyDegree Q T.val :=
    degree_sum_clique_indicators Q T
  rw [hsum, hpdeg, hqdeg, degree_indicator] at hdeg
  have hreal : ((degree (boundary (r + 1) (indicator D)) T.val : ℤ) : ℝ) ≤
      ((q - r : ℕ) : ℝ) * familyDegree P T.val +
        ((q - r : ℕ) : ℝ) * familyDegree Q T.val +
          2 * ((G.filter fun e => T.val ⊆ e.val).card : ℝ) := by exact_mod_cast hdeg
  have hp := mul_le_mul_of_nonneg_left (hP T) (Nat.cast_nonneg (q - r) : (0 : ℝ) ≤ _)
  have hq := mul_le_mul_of_nonneg_left (hQ T) (Nat.cast_nonneg (q - r) : (0 : ℝ) ≤ _)
  have hgraph := hG T
  change ((G.filter fun e => T.val ⊆ e.val).card : ℝ) < θ * Fintype.card V at hgraph
  nlinarith only [hreal, hp, hq, hgraph]
theorem EliminationFamily.cliques_bounded_from_degrees (F : EliminationFamily S N B P Q θ)
    (hpair : IsEliminationPair S N e₀) {A : ℝ}
    (hP : ∀ T : Block V r, (familyDegree P T.val : ℝ) ≤ A * Fintype.card V)
    (hQ : ∀ T : Block V r, (familyDegree Q T.val : ℝ) ≤ A * Fintype.card V) :
    IsCliqueFamilyBounded r F.cliques (2 * ((q - r : ℕ) : ℝ) * A + 2 * θ) :=
  clique_boundary_bounded_of_indexed_roots F.cliques F.graph F.bounded
    (F.boundary_le_indexed_roots hpair) hP hQ

end Arxiv2411_18291
