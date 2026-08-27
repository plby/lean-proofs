import Arxiv.Arxiv2411_18291.CliqueFamilyBoundedness

/-!
# Passing from a bounded clique boundary to its support graph

Every edge in the support has boundary multiplicity at least one. Thus
the same degree bound applies to the support graph, without a separate
upper bound on the clique multiplicities.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem indicator_cliqueSupport_le_boundary (D : Finset (Block V q)) (e : Block V r) :
    indicator (cliqueSupport r D) e ≤ boundary r (indicator D) e := by
  rw [boundary_indicator]
  by_cases he : e ∈ cliqueSupport r D
  · rw [indicator_apply_of_mem he]
    obtain ⟨Q, hQ, heQ⟩ := mem_biUnion.mp he
    have hc : 0 < (D.filter fun P => e.val ⊆ P.val).card :=
      card_pos.mpr ⟨Q, mem_filter.mpr ⟨hQ, (mem_cliqueEdges _ _).mp heQ⟩⟩
    exact_mod_cast hc
  · rw [indicator_apply_of_notMem he]
    exact Nat.cast_nonneg _

theorem IsCliqueFamilyBounded.support_graphBounded {D : Finset (Block V q)} {θ : ℝ}
    (hD : IsCliqueFamilyBounded r D θ) : IsGraphBounded (cliqueSupport (r + 1) D) θ := by
  intro S
  have hdeg := degree_mono_int (indicator_cliqueSupport_le_boundary (r := r + 1) D) S.val
  rw [degree_indicator] at hdeg
  exact (Int.cast_le.mpr hdeg).trans_lt (hD S)

theorem IsCliqueFamilyBounded.mono {D : Finset (Block V q)} {θ θ' : ℝ}
    (hD : IsCliqueFamilyBounded r D θ) (hθ : θ ≤ θ') : IsCliqueFamilyBounded r D θ' := by
  intro S
  exact (hD S).trans_le (mul_le_mul_of_nonneg_right hθ (Nat.cast_nonneg _))

theorem IsCliqueFamilyBounded.subfamily {D E : Finset (Block V q)} {θ : ℝ}
    (hD : IsCliqueFamilyBounded r D θ) (hE : E ⊆ D) : IsCliqueFamilyBounded r E θ := by
  have hboundary (e : Block V (r + 1)) :
      boundary (r + 1) (indicator E) e ≤ boundary (r + 1) (indicator D) e := by
    simp only [boundary_indicator]
    exact_mod_cast card_le_card (filter_subset_filter _ hE)
  intro T
  exact (Int.cast_le.mpr (degree_mono_int hboundary T.val)).trans_lt (hD T)

end Arxiv2411_18291
