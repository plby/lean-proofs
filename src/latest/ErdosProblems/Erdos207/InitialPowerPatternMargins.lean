/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InitialPatternMargins
import ErdosProblems.Erdos207.BoundedPatternIndex

/-! # Initial relative pattern margins on every constructed power-vortex level -/

namespace Erdos207

open Finset
open scoped Classical

noncomputable section

theorem initial_inner_pattern_margin
    (M t C : ℝ) (s : ℕ) (ht : 1 ≤ t) (hC : C ≤ t) (hM : t ^ s ≤ M) :
    C ≤ M * (8 * t ^ 2 / t ^ s) := by
  have htpos : 0 < t := by linarith
  have ht2 : 1 ≤ t ^ 2 := one_le_pow₀ ht
  calc
    _ ≤ t := hC
    _ ≤ 8 * t ^ 2 := by nlinarith only [ht, ht2]
    _ = t ^ s * (8 * t ^ 2 / t ^ s) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hM (by positivity)

theorem initial_outer_pattern_loss_power
    (h t v : ℕ) (ht : 1 ≤ t) (hcoef : 2 * h + 36 * h ^ 2 ≤ t) :
    2 * h + h ^ 2 * (3 * t ^ v) ≤ t ^ (v + 1) := by
  have hpow : 1 ≤ t ^ v := Nat.one_le_pow _ _ ht
  calc
    _ ≤ (2 * h) * t ^ v + (36 * h ^ 2) * t ^ v := by
      have hfirst := Nat.mul_le_mul_left (2 * h) hpow
      nlinarith only [hfirst, Nat.zero_le (h ^ 2 * t ^ v)]
    _ = (2 * h + 36 * h ^ 2) * t ^ v := by ring
    _ ≤ t * t ^ v := Nat.mul_le_mul_right _ hcoef
    _ = _ := by rw [pow_succ]; ring

theorem InitialPowerVortexPackage.initial_pattern_margins
    {q h n ell t rootPower step : ℕ}
    (P : InitialPowerVortexPackage q h n ell t rootPower step) (s R : ℕ)
    (ht : 2 ≤ t) (hc : powerAbsorberCoefficient q ≤ t)
    (hpattern : 2 * h + 36 * h ^ 2 ≤ t) (hroot : s ≤ rootPower)
    (hscale : t ^ R ≤ n) (hgap : initialSupportPower rootPower + 1 + s ≤ R) :
    let S₀ := absorberGreedyInitialState (absorberErdosForbiddenConfigurationsOn q P.B)
      (outsideAvailableTriangles P.H P.B)
    ∀ i : Fin (ell + 1), ∀ Q : WorkingGraphPattern (graphDifference (SimpleGraph.completeGraph (Fin n)) P.H) h,
      |((properPatternExtensions S₀.available Q.1.1 (P.W.U i)).card : ℝ) - (P.W.U i).card| ≤
        (P.W.U i).card * (8 * (t : ℝ) ^ 2 / (t : ℝ) ^ s) := by
  dsimp only
  intro i Q
  have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have htpos : (0 : ℝ) < t := by linarith
  by_cases hi : i = 0
  · subst i
    rw [P.W.root, card_univ, Fintype.card_fin]
    have hs := P.support_power_bounds hc
    have herror := initial_ambient_proper_pattern_error (q := q) hs.1 hs.2.2 Q.2 Q.1.2
    have hnat := initial_outer_pattern_loss_power h t (initialSupportPower rootPower) (by omega) hpattern
    have hscaleR : (t : ℝ) ^ (initialSupportPower rootPower + 1 + s) ≤ n := by
      exact_mod_cast (Nat.pow_le_pow_right (by omega : 0 < t) hgap).trans hscale
    have hbudget := initial_outer_neighbor_margin (n : ℝ)
      (t ^ (initialSupportPower rootPower + 1) : ℕ) t (initialSupportPower rootPower + 1) s htR
      (by simp only [Nat.cast_pow]; exact le_rfl) hscaleR
    have hN : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have htSquare : (t : ℝ) ≤ (t : ℝ) ^ 2 := by
      simpa only [pow_one] using pow_le_pow_right₀ ht1 (show 1 ≤ 2 by omega)
    calc
      _ ≤ ((2 * h + h ^ 2 * (3 * t ^ initialSupportPower rootPower) : ℕ) : ℝ) := by
        simpa only [Fintype.card_fin] using herror
      _ ≤ ((t ^ (initialSupportPower rootPower + 1) : ℕ) : ℝ) := by exact_mod_cast hnat
      _ ≤ ((t ^ (initialSupportPower rootPower + 1) : ℕ) : ℝ) + 1 := by linarith
      _ ≤ 8 * (n : ℝ) * t / (t : ℝ) ^ s := hbudget
      _ ≤ 8 * (n : ℝ) * (t : ℝ) ^ 2 / (t : ℝ) ^ s := by gcongr
      _ = _ := by ring
  · have hsep : AbsorberSeparatedLevel P.H P.X P.B (P.W.U i) := by
      rw [P.vortex_eq]
      exact separatedCardinalVortex_separated _ _ _ _ _ hi
    have herror := initial_separated_proper_pattern_error hsep P.rootBounds Q.2 Q.1.2
    have hM : (t : ℝ) ^ s ≤ ((P.W.U i).card : ℝ) := by
      exact_mod_cast (Nat.pow_le_pow_right (by omega : 0 < t) hroot).trans (P.level_card_lower i)
    have hcoef : ((2 * h + h ^ 2 * 36 : ℕ) : ℝ) ≤ t := by
      exact_mod_cast (show 2 * h + h ^ 2 * 36 ≤ t by simpa only [Nat.mul_comm 36] using hpattern)
    exact herror.trans (initial_inner_pattern_margin (P.W.U i).card t _ s ht1 hcoef hM)

end

end Erdos207
