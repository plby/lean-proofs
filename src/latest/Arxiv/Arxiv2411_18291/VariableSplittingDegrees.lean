import Arxiv.Arxiv2411_18291.VariableSplittingMultiplicity
import Arxiv.Arxiv2411_18291.IndexedCliqueDegrees

/-! # Boundary degrees after splitting without a maximum multiplicity factor

The root-capacity degree and the simple output-graph degree enter additively.
This retains sparsity when individual old edges have growing multiplicity.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {q r : ℕ} {S : ExchangeSystem W q (r + 1)} {D : Finset (Block V q)}
variable {B : Hypergraph V (r + 1)} {C : Block V q → ℕ} {θ : ℝ}

theorem VariableSplittingFamily.boundary_le_roots (F : VariableSplittingFamily S D B C θ)
    (e : Block V (r + 1)) :
    boundary (r + 1) (indicator F.cliques) e ≤
      (familyDegree (fun s : VariableCliqueSlots D C => s.1.val) e.val : ℤ) +
        2 * indicator F.graph e := by
  by_cases heB : e ∈ B
  · have hroot : boundary (r + 1) (indicator F.cliques) e ≤
        (familyDegree (fun s : VariableCliqueSlots D C => s.1.val) e.val : ℤ) := by
      rw [boundary_indicator, variableCliqueSlots_degree]
      exact_mod_cast F.clique_count_original e heB
    have hnonneg : 0 ≤ indicator F.graph e := by unfold indicator; split_ifs <;> norm_num
    linarith only [hroot, hnonneg]
  · by_cases heG : e ∈ F.graph
    · rw [indicator_apply_of_mem heG, mul_one]
      have htwo : boundary (r + 1) (indicator F.cliques) e ≤ 2 := by
        rw [boundary_indicator]
        exact_mod_cast F.clique_count_outside e heB
      have hnonneg : (0 : ℤ) ≤ familyDegree
          (fun s : VariableCliqueSlots D C => s.1.val) e.val := Nat.cast_nonneg _
      linarith only [htwo, hnonneg]
    · have hzero : F.cliques.filter (fun Q => e.val ⊆ Q.val) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro Q hQ
        obtain ⟨hQ, heQ⟩ := mem_filter.mp hQ
        exact heG (F.cliques_support
          (mem_biUnion.mpr ⟨Q, hQ, (mem_cliqueEdges _ _).mpr heQ⟩))
      rw [boundary_indicator, hzero, card_empty, Nat.cast_zero,
        indicator_apply_of_notMem heG, mul_zero, add_zero]
      exact Nat.cast_nonneg _

theorem VariableSplittingFamily.boundary_degree_le (F : VariableSplittingFamily S D B C θ)
    (T : Block V r) :
    degree (boundary (r + 1) (indicator F.cliques)) T.val ≤
      2 * ((q - r : ℕ) : ℤ) * cliqueCapacityDegree D C T.val +
        2 * degree (indicator F.graph) T.val := by
  let P : VariableCliqueSlots D C → Block V q := fun s => s.1.val
  have hroot : degree (fun e : Block V (r + 1) => (familyDegree P e.val : ℤ)) T.val =
      2 * ((q - r : ℕ) : ℤ) * cliqueCapacityDegree D C T.val := by
    have heq : (fun e : Block V (r + 1) => (familyDegree P e.val : ℤ)) =
        ∑ s, indicator (cliqueEdges (r + 1) (P s)) := by
      funext e
      exact (sum_clique_indicators_apply P e).symm
    rw [heq, degree_sum_clique_indicators, variableCliqueSlots_degree]
    push_cast
    ring
  have hsum : degree (fun e : Block V (r + 1) =>
      (familyDegree P e.val : ℤ) + 2 * indicator F.graph e) T.val =
        degree (fun e : Block V (r + 1) => (familyDegree P e.val : ℤ)) T.val +
          2 * degree (indicator F.graph) T.val := by
    unfold degree
    rw [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro e _
    split_ifs <;> ring
  have hh := degree_mono_int (F.boundary_le_roots) T.val
  change degree (boundary (r + 1) (indicator F.cliques)) T.val ≤
    degree (fun e : Block V (r + 1) =>
      (familyDegree P e.val : ℤ) + 2 * indicator F.graph e) T.val at hh
  rw [hsum, hroot] at hh
  exact hh

theorem VariableSplittingFamily.cliques_bounded (F : VariableSplittingFamily S D B C θ)
    {θC : ℝ} (hC : IsCliqueCapacityBounded r D C θC) :
    IsCliqueFamilyBounded r F.cliques (2 * (q - r : ℕ) * θC + 2 * θ) := by
  intro T
  have hle : ((degree (boundary (r + 1) (indicator F.cliques)) T.val : ℤ) : ℝ) ≤
      2 * (q - r : ℕ) * (cliqueCapacityDegree D C T.val : ℝ) +
        2 * ((degree (indicator F.graph) T.val : ℤ) : ℝ) := by
    exact_mod_cast F.boundary_degree_le T
  have hroot := mul_le_mul_of_nonneg_left (hC T).le
    (by positivity : (0 : ℝ) ≤ 2 * (q - r : ℕ))
  have hgraph : ((degree (indicator F.graph) T.val : ℤ) : ℝ) < θ * Fintype.card V := by
    simpa only [degree_indicator, Int.cast_natCast, VariableSplittingFamily.graph]
      using F.bounded T
  have hg := mul_lt_mul_of_pos_left hgraph (by norm_num : (0 : ℝ) < 2)
  apply hle.trans_lt
  have hh := add_lt_add_of_le_of_lt hroot hg
  rw [show (2 * (q - r : ℕ) : ℝ) * (θC * Fintype.card V) +
      2 * (θ * Fintype.card V) =
        (2 * (q - r : ℕ) * θC + 2 * θ) * Fintype.card V by ring] at hh
  exact hh

end Arxiv2411_18291
