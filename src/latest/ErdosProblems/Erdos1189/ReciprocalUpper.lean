/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The elementary logarithmic upper bound on the reciprocal sum.
Informal source: comparison of distinct positive integers with the harmonic sum.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.Density
import Mathlib.Data.Finset.Sort
import Mathlib.NumberTheory.Harmonic.Bounds

namespace Erdos1189

open Finset

lemma ordered_modulus_lower {D : Finset ℕ} (hD : ∀ d ∈ D, 1 < d) :
    ∀ i : Fin D.card, i.val + 2 ≤ D.orderEmbOfFin rfl i := by
  have h : ∀ j (hj : j < D.card), j + 2 ≤ D.orderEmbOfFin rfl ⟨j, hj⟩ := by
    intro j
    induction j with
    | zero =>
        intro hj
        exact hD _ (orderEmbOfFin_mem D rfl ⟨0, hj⟩)
    | succ j ih =>
        intro hj
        have hj' : j < D.card := by omega
        have hlt := (D.orderEmbOfFin rfl).strictMono
          (show (⟨j, hj'⟩ : Fin D.card) < ⟨j + 1, hj⟩ from Nat.lt_succ_self j)
        have hh := ih hj'
        omega
  exact fun i => h i i.isLt

lemma reciprocalSum_le_harmonic {D : Finset ℕ} (hD : ∀ d ∈ D, 1 < d) :
    reciprocalSum D ≤ harmonic D.card := by
  have hsum : reciprocalSum D =
      ∑ i : Fin D.card, ((D.orderEmbOfFin rfl i : ℕ) : ℚ)⁻¹ := by
    unfold reciprocalSum
    conv_lhs => rw [← image_orderEmbOfFin_univ D rfl]
    exact sum_image (fun _ _ _ _ h => (D.orderEmbOfFin rfl).injective h)
  rw [hsum, harmonic, sum_range]
  apply sum_le_sum
  intro i _
  have hle : (i : ℕ) + 1 ≤ D.orderEmbOfFin rfl i := by
    have := ordered_modulus_lower hD i
    omega
  have hdpos : (0 : ℚ) < D.orderEmbOfFin rfl i := by
    exact_mod_cast lt_trans Nat.zero_lt_one (hD _ (orderEmbOfFin_mem D rfl i))
  apply (inv_le_inv₀ hdpos (by positivity)).mpr
  exact_mod_cast hle

theorem reciprocalSum_le_one_add_log {D : Finset ℕ} (hD : ∀ d ∈ D, 1 < d) :
    (reciprocalSum D : ℝ) ≤ 1 + Real.log D.card := by
  exact (show (reciprocalSum D : ℝ) ≤ (harmonic D.card : ℝ) by
    exact_mod_cast reciprocalSum_le_harmonic hD).trans (harmonic_le_one_add_log D.card)

theorem eventually_reciprocalSum_le_two_log :
    ∀ᶠ k : ℕ in Filter.atTop, ∀ D : Finset ℕ, (∀ d ∈ D, 1 < d) → D.card = k →
      (reciprocalSum D : ℝ) ≤ 2 * Real.log k := by
  have ht : Filter.Tendsto (fun k : ℕ => Real.log k) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually (Filter.eventually_ge_atTop 1)] with k hk
  intro D hD hcard
  have h := reciprocalSum_le_one_add_log hD
  rw [hcard] at h
  linarith

end Erdos1189
