import ErdosProblems.Erdos19.BoundedRankLists
import ErdosProblems.Erdos19.BoundedRankCoveredLists
import ErdosProblems.Erdos19.ReservedColorConflicts
import ErdosProblems.Erdos19.ProjectiveSparsity

/-! # Coloring bounded-rank medium edges around a projective reserved palette

Only the already colored edges using the reserved palette need projective
minimum size. There is no unproved arbitrary-precoloring extension input.
-/

namespace Erdos19.SetHypergraph

open Finset

attribute [local instance] Classical.propDecidable

theorem eventually_color_medium_avoiding_projective_palette
    (R s : ℕ) (hR : 0 < R) (hs : 0 < s) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ L M : SetHypergraph (Fin n), L.IsLinear → M.IsLinear →
      ∀ color : L.EdgeColoring (Fin n), ∀ palette : Finset (Fin n),
      ∀ t : ℕ, 2 ≤ t →
        (∀ e : L, color.color e ∈ palette →
          projectiveScale n - projectiveScale n / t ≤ e.1.ncard) →
        (∀ e : M, s + 1 ≤ e.1.ncard) → (∀ e : M, e.1.ncard ≤ R) →
        2 * (n / s) ≤ palette.card →
        ∃ c : M.EdgeColoring palette, ∀ e : M, ∀ f : L,
          (e.1 ∩ f.1).Nonempty → (c.color e).1 ≠ color.color f := by
  classical
  obtain ⟨delta, hdelta, N₀, hN₀⟩ := eventually_bounded_rank_sparse_lists R s hR hs
  obtain ⟨N₁, hN₁⟩ := eventually_projective_conflicts_sparse R s hs delta hdelta
  refine ⟨max N₀ (max N₁ (4 * 4 + 4 + 2)), ?_⟩
  intro n hn L M hL hM color palette t ht hcoremin hmin hmax hpalette
  have hn₀ : N₀ ≤ n := (le_max_left _ _).trans hn
  have hn₁ : N₁ ≤ n := ((le_max_left _ _).trans (le_max_right _ _)).trans hn
  have hnscale : 4 * 4 + 4 + 2 ≤ n :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hn
  have hk := projectiveScale_ge_of_large_card 4 n hnscale
  have hdiv : 2 * (projectiveScale n / t) ≤ projectiveScale n :=
    (Nat.mul_le_mul_right _ ht).trans (Nat.mul_div_le (projectiveScale n) t)
  have hr : 2 ≤ projectiveScale n - projectiveScale n / t := by omega
  let F : M → Finset palette := fun e ↦ L.forbiddenReservedColors color e.1 palette
  have hF : ∀ e, ((F e).card : ℝ) ≤ delta * ((n / s : ℕ) : ℝ) := by
    intro e
    have h := L.forbiddenReservedColors_card_le hL color e.1 palette
      (projectiveScale n - projectiveScale n / t) hr hcoremin
    simp only [Fintype.card_fin] at h
    have hmax' := Nat.mul_le_mul_right
      ((n - 1) / (projectiveScale n - projectiveScale n / t - 1)) (hmax e)
    have hcount : (F e).card ≤ R *
        ((n - 1) / (projectiveScale n - projectiveScale n / t - 1)) := h.trans hmax'
    exact (show ((F e).card : ℝ) ≤
      (R * ((n - 1) / (projectiveScale n - projectiveScale n / t - 1)) : ℕ) by
        exact_mod_cast hcount).trans (hN₁ n hn₁ t ht)
  obtain ⟨c, hc⟩ := hN₀ n hn₀ M hM hmin hmax palette F hF
    (by simpa only [Fintype.card_coe] using hpalette)
  refine ⟨c, ?_⟩
  intro e f hinter heq
  apply hc e
  exact mem_filter.mpr ⟨mem_univ _, f, heq.symm, hinter⟩

theorem eventually_color_medium_with_coverage_palette
    (R s a : ℕ) (hR : 0 < R) (hs : 0 < s) (ha : 0 < a) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ L M : SetHypergraph (Fin n), L.IsLinear → M.IsLinear →
      ∀ (P : Type) [Fintype P] [DecidableEq P],
      ∀ color : L.EdgeColoring P, ∀ palette : Finset P,
      ∀ t : ℕ, 2 ≤ t →
        (∀ e : L, color.color e ∈ palette →
          projectiveScale n - projectiveScale n / t ≤ e.1.ncard) →
        (∀ e : M, 16 * a * s + 1 ≤ e.1.ncard) → (∀ e : M, e.1.ncard ≤ R) →
        2 * (n / s) ≤ palette.card →
        ∃ c : M.EdgeColoring palette,
          (∀ e : M, ∀ f : L, (e.1 ∩ f.1).Nonempty → (c.color e).1 ≠ color.color f) ∧
          (∀ x, (M.coveredVertices {e : M | c.color e = x}).ncard ≤ n / a) := by
  classical
  obtain ⟨delta, hdelta, N₀, hN₀⟩ := eventually_bounded_rank_covered_lists R s a hR hs ha
  obtain ⟨N₁, hN₁⟩ := eventually_projective_conflicts_sparse R s hs delta hdelta
  refine ⟨max N₀ (max N₁ (4 * 4 + 4 + 2)), ?_⟩
  intro n hn L M hL hM P _ _ color palette t ht hcoremin hmin hmax hpalette
  have hn₀ : N₀ ≤ n := (le_max_left _ _).trans hn
  have hn₁ : N₁ ≤ n := ((le_max_left _ _).trans (le_max_right _ _)).trans hn
  have hnscale : 4 * 4 + 4 + 2 ≤ n :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hn
  have hk := projectiveScale_ge_of_large_card 4 n hnscale
  have hdiv : 2 * (projectiveScale n / t) ≤ projectiveScale n :=
    (Nat.mul_le_mul_right _ ht).trans (Nat.mul_div_le (projectiveScale n) t)
  have hr : 2 ≤ projectiveScale n - projectiveScale n / t := by omega
  let F : M → Finset palette := fun e ↦ L.forbiddenReservedColors color e.1 palette
  have hF : ∀ e, ((F e).card : ℝ) ≤ delta * ((n / s : ℕ) : ℝ) := by
    intro e
    have h := L.forbiddenReservedColors_card_le hL color e.1 palette
      (projectiveScale n - projectiveScale n / t) hr hcoremin
    simp only [Fintype.card_fin] at h
    have hmax' := Nat.mul_le_mul_right
      ((n - 1) / (projectiveScale n - projectiveScale n / t - 1)) (hmax e)
    have hcount : (F e).card ≤ R *
        ((n - 1) / (projectiveScale n - projectiveScale n / t - 1)) := h.trans hmax'
    exact (show ((F e).card : ℝ) ≤
      (R * ((n - 1) / (projectiveScale n - projectiveScale n / t - 1)) : ℕ) by
        exact_mod_cast hcount).trans (hN₁ n hn₁ t ht)
  obtain ⟨c, hc, hcCover⟩ := hN₀ n hn₀ M hM hmin hmax palette F hF
    (by simpa only [Fintype.card_coe] using hpalette)
  refine ⟨c, ?_, hcCover⟩
  intro e f hinter heq
  apply hc e
  exact mem_filter.mpr ⟨mem_univ _, f, heq.symm, hinter⟩


theorem eventually_color_medium_with_coverage
    (R s a : ℕ) (hR : 0 < R) (hs : 0 < s) (ha : 0 < a) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ L M : SetHypergraph (Fin n), L.IsLinear → M.IsLinear →
      ∀ color : L.EdgeColoring (Fin n), ∀ palette : Finset (Fin n),
      ∀ t : ℕ, 2 ≤ t →
        (∀ e : L, color.color e ∈ palette →
          projectiveScale n - projectiveScale n / t ≤ e.1.ncard) →
        (∀ e : M, 16 * a * s + 1 ≤ e.1.ncard) → (∀ e : M, e.1.ncard ≤ R) →
        2 * (n / s) ≤ palette.card →
        ∃ c : M.EdgeColoring palette,
          (∀ e : M, ∀ f : L, (e.1 ∩ f.1).Nonempty → (c.color e).1 ≠ color.color f) ∧
          (∀ x, (M.coveredVertices {e : M | c.color e = x}).ncard ≤ n / a) := by
  classical
  obtain ⟨delta, hdelta, N₀, hN₀⟩ := eventually_bounded_rank_covered_lists R s a hR hs ha
  obtain ⟨N₁, hN₁⟩ := eventually_projective_conflicts_sparse R s hs delta hdelta
  refine ⟨max N₀ (max N₁ (4 * 4 + 4 + 2)), ?_⟩
  intro n hn L M hL hM color palette t ht hcoremin hmin hmax hpalette
  have hn₀ : N₀ ≤ n := (le_max_left _ _).trans hn
  have hn₁ : N₁ ≤ n := ((le_max_left _ _).trans (le_max_right _ _)).trans hn
  have hnscale : 4 * 4 + 4 + 2 ≤ n :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hn
  have hk := projectiveScale_ge_of_large_card 4 n hnscale
  have hdiv : 2 * (projectiveScale n / t) ≤ projectiveScale n :=
    (Nat.mul_le_mul_right _ ht).trans (Nat.mul_div_le (projectiveScale n) t)
  have hr : 2 ≤ projectiveScale n - projectiveScale n / t := by omega
  let F : M → Finset palette := fun e ↦ L.forbiddenReservedColors color e.1 palette
  have hF : ∀ e, ((F e).card : ℝ) ≤ delta * ((n / s : ℕ) : ℝ) := by
    intro e
    have h := L.forbiddenReservedColors_card_le hL color e.1 palette
      (projectiveScale n - projectiveScale n / t) hr hcoremin
    simp only [Fintype.card_fin] at h
    have hmax' := Nat.mul_le_mul_right
      ((n - 1) / (projectiveScale n - projectiveScale n / t - 1)) (hmax e)
    have hcount : (F e).card ≤ R *
        ((n - 1) / (projectiveScale n - projectiveScale n / t - 1)) := h.trans hmax'
    exact (show ((F e).card : ℝ) ≤
      (R * ((n - 1) / (projectiveScale n - projectiveScale n / t - 1)) : ℕ) by
        exact_mod_cast hcount).trans (hN₁ n hn₁ t ht)
  obtain ⟨c, hc, hcCover⟩ := hN₀ n hn₀ M hM hmin hmax palette F hF
    (by simpa only [Fintype.card_coe] using hpalette)
  refine ⟨c, ?_, hcCover⟩
  intro e f hinter heq
  apply hc e
  exact mem_filter.mpr ⟨mem_univ _, f, heq.symm, hinter⟩

#print axioms eventually_color_medium_with_coverage_palette

#print axioms eventually_color_medium_with_coverage

#print axioms eventually_color_medium_avoiding_projective_palette

end Erdos19.SetHypergraph
