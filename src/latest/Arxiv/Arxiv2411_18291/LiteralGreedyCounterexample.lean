import Arxiv.Arxiv2411_18291.GreedyRootCompatibility
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # The forbidden-root defect in the printed process definition

Definition 5.4 literally forbids every edge of the chosen embedding from
belonging to B. This includes prescribed root edges, although its lemma
allows those edges in B. The example below has a nonempty extension and
satisfies the printed smallness assumptions at arbitrarily large n.

The implemented process exempts root edges. Its legal set is nonempty
on the same example. This counterexample concerns the literal definition,
not the still separate smallness question for the intended process.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

def literalLegalExtensions {W V : Type*} [Fintype W] [Fintype V]
    [DecidableEq W] [DecidableEq V] {F : Finset W} {r : ℕ}
    (φ : F ↪ V) (H : Hypergraph W (r + 1)) (B : Hypergraph V (r + 1)) :
    Finset (EmbeddingExtension φ) :=
  univ.filter fun a => ∀ e ∈ H, mapBlock a.val e ∉ B

theorem literalLegalExtensions_empty_of_forbidden_root {W V : Type*}
    [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V] {F : Finset W} {r : ℕ}
    (φ : F ↪ V) (H : Hypergraph W (r + 1)) (B : Hypergraph V (r + 1))
    (e : Block W (r + 1)) (he : e ∈ H) (heF : e.val ⊆ F)
    (heB : rootImage φ e heF ∈ B) : literalLegalExtensions φ H B = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro a ha
  have hnot := (mem_filter.mp ha).2 e he
  rw [EmbeddingExtension.map_rootBlock φ a e heF] at hnot
  exact hnot heB

theorem inverse_sqrt_lt_one_div_thirty_two {n : ℕ} (hn : 1025 ≤ n) :
    (n : ℝ) ^ (-(1 / 2 : ℝ)) < 1 / 32 := by
  have hN : (1025 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : (32 : ℝ) < Real.sqrt n := by
    have hsq := Real.sq_sqrt (Nat.cast_nonneg n)
    have hpos := Real.sqrt_nonneg (n : ℝ)
    nlinarith only [hN, hsq, hpos]
  rw [Real.rpow_neg (Nat.cast_nonneg n), ← Real.sqrt_eq_rpow]
  simpa only [one_div] using
    (inv_lt_inv₀ (by linarith only [hs]) (by norm_num : (0 : ℝ) < 32)).2 hs

theorem literal_greedy_counterexample {n : ℕ} (hn : 1025 ≤ n) :
    ∃ H : Hypergraph (Fin 2) 1, ∃ F : Finset (Fin 2),
      ∃ Φ : ℕ → F ↪ Fin n, ∃ B : Hypergraph (Fin n) 1,
        H.card = 2 ∧ IsAdmissible H F ∧ (newEdges F H).Nonempty ∧
        (n : ℝ) ^ (-(1 / 2 : ℝ)) < 1 / 32 ∧
        (1 / 32 : ℝ) < (8 * ((1 : ℕ).factorial : ℝ) ^ 2 * H.card)⁻¹ ∧
        IsGraphBounded B (1 / 32) ∧
        (∀ e ∈ H, ∀ he : e.val ⊆ F,
          IsEdgeFamilyBounded (fun i : Fin 1 => rootImage (Φ i) e he) (1 / 32)) ∧
        literalLegalExtensions (Φ 0) H B = ∅ ∧ (legalExtensions (Φ 0) H B).Nonempty := by
  classical
  have hnpos : 0 < n := by omega
  have hN : (1025 : ℝ) ≤ n := by exact_mod_cast hn
  let H : Hypergraph (Fin 2) 1 := complete (Fin 2) 1
  let F : Finset (Fin 2) := {0}
  let e₀ : Block (Fin 2) 1 := ⟨F, by simp only [F, card_singleton]⟩
  let e₁ : Block (Fin 2) 1 := ⟨{1}, card_singleton _⟩
  let φ : F ↪ Fin n :=
    ⟨fun _ => ⟨0, hnpos⟩, by
      intro x y _
      apply Subtype.ext
      have hx : x.val = 0 := mem_singleton.mp x.property
      have hy : y.val = 0 := mem_singleton.mp y.property
      exact hx.trans hy.symm⟩
  let B : Hypergraph (Fin n) 1 := {rootImage φ e₀ (Subset.refl _)}
  have hcard : H.card = 2 := by
    simp only [H, complete, card_univ, Block, Fintype.card_finset_len, Fintype.card_fin]
    decide
  have hbound : (1 : ℝ) < (1 / 32 : ℝ) * n := by linarith only [hN]
  have hB : IsGraphBounded B (1 / 32) := by
    intro S
    have hc : (B.filter fun e => S.val ⊆ e.val).card ≤ 1 := by
      simpa only [B, card_singleton] using card_filter_le B (fun e => S.val ⊆ e.val)
    exact (by exact_mod_cast hc :
      ((B.filter fun e => S.val ⊆ e.val).card : ℝ) ≤ 1).trans_lt
        (by simpa only [Fintype.card_fin] using hbound)
  refine ⟨H, F, fun _ => φ, B, hcard, ?_, ?_,
    inverse_sqrt_lt_one_div_thirty_two hn, ?_, hB, ?_, ?_, ?_⟩
  · intro e _ _
    exact ⟨e₀, mem_univ _, Subset.refl _, inter_subset_right⟩
  · refine ⟨e₁, (mem_newEdges H e₁).mpr ⟨mem_univ _, ?_⟩⟩
    simp only [e₁, F, singleton_subset_iff, mem_singleton]
    decide
  · rw [hcard]
    norm_num
  · intro e _ he S
    have hc : familyDegree (fun _i : Fin 1 => rootImage φ e he) S.val ≤ 1 := by
      simpa only [familyDegree, card_univ, Fintype.card_fin] using
        card_filter_le (univ : Finset (Fin 1)) (fun _i => S.val ⊆ (rootImage φ e he).val)
    exact (by exact_mod_cast hc :
      (familyDegree (fun _i : Fin 1 => rootImage φ e he) S.val : ℝ) ≤ 1).trans_lt
        (by simpa only [Fintype.card_fin] using hbound)
  · exact literalLegalExtensions_empty_of_forbidden_root φ H B e₀
      (mem_univ _) (Subset.refl _) (mem_singleton_self _)
  · have hc := legalExtensions_card_half φ H B hB (by norm_num : (0 : ℝ) ≤ 1 / 32)
      (by simp only [Fintype.card_fin]; omega)
      (by rw [hcard]; norm_num)
    have hp : (0 : ℝ) < (legalExtensions φ H B).card :=
      (by simp only [Fintype.card_fin]; positivity : (0 : ℝ) < (1 / 2 : ℝ) *
        (Fintype.card (Fin n) : ℝ) ^ (Fintype.card (Fin 2) - F.card)).trans_le hc
    exact card_pos.mp (by exact_mod_cast hp)

end Arxiv2411_18291
