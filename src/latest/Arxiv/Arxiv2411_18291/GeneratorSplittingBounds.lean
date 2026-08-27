import Arxiv.Arxiv2411_18291.GeneratorSplittingMultiplicity

/-!
# Boundary bounds for split generators

The original support retains its old multiplicities, while all new edges
have multiplicity at most two. This gives a constant loss in the boundary
degree bound without assuming any original edge multiplicity bound.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]
variable {q r : ℕ} {S : ExchangeSystem W q (r + 1)} {D : Finset (Block V q)} {θ : ℝ}

theorem GeneratorSplitting.boundary_le (F : GeneratorSplitting S D θ)
    (e : Block V (r + 1)) : boundary (r + 1) (indicator F.cliques) e ≤
      boundary (r + 1) (indicator D) e + 2 * indicator F.graph e := by
  rw [boundary_indicator, boundary_indicator]
  by_cases heD : e ∈ cliqueSupport (r + 1) D
  · have hcount := F.clique_count_original e heD
    have heG : e ∈ F.graph := mem_union_left _ heD
    rw [indicator_apply_of_mem heG]
    exact (Int.ofNat_le.mpr hcount).trans (by omega)
  · by_cases heG : e ∈ F.graph
    · rw [indicator_apply_of_mem heG]
      have hcount : ((F.cliques.filter fun P => e.val ⊆ P.val).card : ℤ) ≤ 2 :=
        Int.ofNat_le.mpr (F.clique_count_outside e heD)
      have hd : (0 : ℤ) ≤ (D.filter fun Q => e.val ⊆ Q.val).card := Nat.cast_nonneg _
      omega
    · have hz : boundary (r + 1) (indicator F.cliques) e = 0 :=
        boundary_zero_outside_support F.cliques F.graph (indicator F.cliques)
          (fun Q hQ => indicator_apply_of_notMem hQ) F.cliques_support e heG
      rw [boundary_indicator] at hz
      rw [hz, indicator_apply_of_notMem heG, mul_zero, add_zero]
      exact Nat.cast_nonneg _

theorem GeneratorSplitting.cliques_bounded (F : GeneratorSplitting S D θ)
    {η : ℝ} (hD : IsCliqueFamilyBounded r D η) :
    IsCliqueFamilyBounded r F.cliques (η + 2 * θ) := by
  intro T
  have hdeg := degree_mono_int F.boundary_le T.val
  have hsum : degree (fun e => boundary (r + 1) (indicator D) e + 2 * indicator F.graph e) T.val =
      degree (boundary (r + 1) (indicator D)) T.val + 2 * degree (indicator F.graph) T.val := by
    unfold degree
    rw [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro e _
    split_ifs <;> ring
  rw [hsum, degree_indicator] at hdeg
  have hreal : ((degree (boundary (r + 1) (indicator F.cliques)) T.val : ℤ) : ℝ) ≤
      ((degree (boundary (r + 1) (indicator D)) T.val : ℤ) : ℝ) +
        2 * ((F.graph.filter fun e => T.val ⊆ e.val).card : ℝ) := by exact_mod_cast hdeg
  have hgraph := F.bounded T
  change ((F.graph.filter fun e => T.val ⊆ e.val).card : ℝ) < θ * Fintype.card V at hgraph
  have hold := hD T
  nlinarith only [hreal, hgraph, hold]

end Arxiv2411_18291
