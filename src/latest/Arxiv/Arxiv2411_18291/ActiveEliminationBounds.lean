import Arxiv.Arxiv2411_18291.EliminationActiveFamily
import Arxiv.Arxiv2411_18291.EliminationBoundaryBounds

/-! # Boundary degrees for the active part of elimination

Only the graph of the near replacement cliques enters this estimate.
The much larger graph of the full exchange need not be charged again.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {I W V : Type*} [Fintype I] [Fintype W] [Fintype V]
variable [DecidableEq W] [DecidableEq V] {q r : ℕ}
variable {S : ExchangeSystem W q (r + 1)} {N : Block W q} {e₀ : Block W (r + 1)}
variable {B : Hypergraph V (r + 1)} {P Q : I → Block V q} {θ : ℝ}

theorem EliminationFamily.active_boundary_le (F : EliminationFamily S N B P Q θ)
    (hpair : IsEliminationPair S N e₀) (e : Block V (r + 1)) :
    boundary (r + 1) (indicator F.activeCliques) e ≤
      (familyDegree P e.val : ℤ) + (familyDegree Q e.val : ℤ) +
        2 * indicator F.activeGraph e := by
  rw [boundary_indicator]
  have hsub : ((F.activeCliques.filter fun R => e.val ⊆ R.val).card : ℤ) ≤
      (F.cliques.filter fun R => e.val ⊆ R.val).card :=
    Int.ofNat_le.mpr (card_le_card (filter_subset_filter _ F.activeCliques_subset))
  by_cases heB : e ∈ B
  · have h : ((F.cliques.filter fun R => e.val ⊆ R.val).card : ℤ) ≤
        (familyDegree P e.val : ℤ) + (familyDegree Q e.val : ℤ) := by
      exact_mod_cast F.clique_count_original_sharp hpair e heB
    rw [indicator_apply_of_mem (show e ∈ F.activeGraph from mem_union_left _ heB)]
    omega
  · by_cases heG : e ∈ F.activeGraph
    · have h : ((F.cliques.filter fun R => e.val ⊆ R.val).card : ℤ) ≤ 2 := by
        exact_mod_cast F.clique_count_outside hpair e heB
      rw [indicator_apply_of_mem heG]
      have hp : (0 : ℤ) ≤ familyDegree P e.val := Nat.cast_nonneg _
      have hq : (0 : ℤ) ≤ familyDegree Q e.val := Nat.cast_nonneg _
      omega
    · have hz : boundary (r + 1) (indicator F.activeCliques) e = 0 :=
        boundary_zero_outside_support F.activeCliques F.activeGraph (indicator F.activeCliques)
          (fun R hR => indicator_apply_of_notMem hR) (F.active_support hpair) e heG
      rw [boundary_indicator] at hz
      rw [hz, indicator_apply_of_notMem heG, mul_zero, add_zero]
      positivity

theorem EliminationFamily.active_bounded_from_degrees (F : EliminationFamily S N B P Q θ)
    (hpair : IsEliminationPair S N e₀) {A η : ℝ}
    (hG : IsGraphBounded F.activeGraph η)
    (hP : ∀ T : Block V r, (familyDegree P T.val : ℝ) ≤ A * Fintype.card V)
    (hQ : ∀ T : Block V r, (familyDegree Q T.val : ℝ) ≤ A * Fintype.card V) :
    IsCliqueFamilyBounded r F.activeCliques (2 * ((q - r : ℕ) : ℝ) * A + 2 * η) :=
  clique_boundary_bounded_of_indexed_roots F.activeCliques F.activeGraph hG
    (F.active_boundary_le hpair) hP hQ

end Arxiv2411_18291
