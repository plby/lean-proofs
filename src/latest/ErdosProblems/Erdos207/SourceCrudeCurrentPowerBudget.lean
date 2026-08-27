/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceCrudeUniformTail
import ErdosProblems.Erdos207.SourceCrudeCoefficientPower
import ErdosProblems.Erdos207.DyadicCrudeCutoffs

/-! # Generalized crude budgets with the current, not ambient, vertex count -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem dyadicCrudeThresholds_one_le
    (V U : Type*) [DecidableEq V] [Fintype U] (q t k : ℕ) (ht : 1 ≤ t)
    (i : CrudeStatisticIndex V q) :
    1 ≤ crudeThreshold (dyadicCrudeThresholds U t k) i := by
  have ht' : (1 : ℝ≥0) ≤ t := by exact_mod_cast ht
  have hU : (1 : ℝ≥0) ≤ Fintype.card U + 1 := by
    exact_mod_cast (show 1 ≤ Fintype.card U + 1 by omega)
  rcases i with ⟨j, roots⟩ | ⟨T, P⟩ | ⟨T, T'⟩ | ⟨j, T⟩
  · exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hU) (one_le_pow₀ ht')
  · exact one_le_pow₀ ht'
  · exact one_le_pow₀ ht'
  · exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hU) (one_le_pow₀ ht')

theorem source_current_power_cutoff (n e k : ℕ) (t U : ℝ≥0) (hcut : t * U ≤ t ^ k) :
    t * U * (n : ℝ≥0) ^ e ≤ (n + 1 : ℝ≥0) ^ e * t ^ k := by
  have hn : (n : ℝ≥0) ≤ n + 1 := le_add_of_nonneg_right zero_le
  calc
    _ ≤ t ^ k * (n : ℝ≥0) ^ e := mul_le_mul_of_nonneg_right hcut zero_le
    _ ≤ t ^ k * (n + 1 : ℝ≥0) ^ e := mul_le_mul_of_nonneg_left (pow_le_pow_left' hn e) zero_le
    _ = _ := by ring

theorem sourceCrudeTailBound_sum_current_power_budget
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] {ell q : ℕ}
    (W : Vortex V ell) (order : I → ℕ) (z : I → ℝ≥0) (s R c t k : ℕ) (w Z A epsilon : ℝ≥0)
    (horder : ∀ i, order i ≤ q) (hz : ∀ i, z i ≤ Z)
    (ht : 1 ≤ t) (hw : 1 ≤ w) (hN : Fintype.card V ≤ t ^ R) (hs : 6 * R + c ≤ s)
    (hcut : (t : ℝ≥0) * sourceCrudeUniformCoefficient ell q (Fintype.card I) w Z ≤ (t : ℝ≥0) ^ k) :
    (∑ i : CrudeStatisticIndex V q,
      sourceCrudeTailBound W order z s w A epsilon (dyadicCrudeThresholds (Fin W.terminalSize) t k) i) ≤
      (256 * (q + 1 : ℝ≥0) ^ 2) * A * (boundedIntersectionMomentCoefficient (2 * q) s : ℝ≥0) ^ s / (t : ℝ≥0) ^ c +
      (256 * (q + 1 : ℝ≥0) ^ 2) * epsilon *
        (sourceCrudeUniformWitnessFactor q (Fintype.card I) * (2 : ℝ≥0) ^ (6 * q)) ^ s *
          (t : ℝ≥0) ^ (6 * R + (6 * q * R) * s) := by
  apply sourceCrudeTailBound_sum_budget W order z s R c t w Z A epsilon
    (dyadicCrudeThresholds (Fin W.terminalSize) t k) horder hz (by exact_mod_cast ht) hw (by exact_mod_cast hN) hs
  · exact dyadicCrudeThresholds_one_le V (Fin W.terminalSize) q t k ht
  · intro j c
    simpa only [dyadicCrudeThresholds, Fintype.card_fin] using
      source_current_power_cutoff W.terminalSize (j - c - 5) k t
        (sourceCrudeUniformCoefficient ell q (Fintype.card I) w Z) hcut
  · exact hcut
  · exact hcut
  · intro j c
    simpa only [dyadicCrudeThresholds, Fintype.card_fin] using
      source_current_power_cutoff W.terminalSize (j - c - 4) k t
        (sourceCrudeUniformCoefficient ell q (Fintype.card I) w Z) hcut

theorem sourceCrudeTailBound_sum_current_power_prior_error_budget
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] {ell q : ℕ}
    (W : Vortex V ell) (order : I → ℕ) (z : I → ℝ≥0) (s R c t k L : ℕ) (w Z A epsilon B : ℝ≥0)
    (horder : ∀ i, order i ≤ q) (hz : ∀ i, z i ≤ Z)
    (ht : 1 ≤ t) (hw : 1 ≤ w) (hN : Fintype.card V ≤ t ^ R) (hs : 6 * R + c ≤ s)
    (hL : 6 * R + (6 * q * R) * s + c ≤ L)
    (hcut : (t : ℝ≥0) * sourceCrudeUniformCoefficient ell q (Fintype.card I) w Z ≤ (t : ℝ≥0) ^ k)
    (hepsilon : epsilon ≤ A * B / (t : ℝ≥0) ^ L) :
    (∑ i : CrudeStatisticIndex V q,
      sourceCrudeTailBound W order z s w A epsilon (dyadicCrudeThresholds (Fin W.terminalSize) t k) i) ≤
      (256 * (q + 1 : ℝ≥0) ^ 2) * A *
        ((boundedIntersectionMomentCoefficient (2 * q) s : ℝ≥0) ^ s +
          B * (sourceCrudeUniformWitnessFactor q (Fintype.card I) * (2 : ℝ≥0) ^ (6 * q)) ^ s) / (t : ℝ≥0) ^ c := by
  let C : ℝ≥0 := 256 * (q + 1 : ℝ≥0) ^ 2
  let Q := sourceCrudeUniformWitnessFactor q (Fintype.card I) * (2 : ℝ≥0) ^ (6 * q)
  have herr : C * epsilon * Q ^ s * (t : ℝ≥0) ^ (6 * R + (6 * q * R) * s) ≤ C * A * B * Q ^ s / (t : ℝ≥0) ^ c := by
    calc
      _ ≤ C * (A * B / (t : ℝ≥0) ^ L) * Q ^ s * (t : ℝ≥0) ^ (6 * R + (6 * q * R) * s) := by gcongr
      _ = (C * A * B * Q ^ s) * ((t : ℝ≥0) ^ (6 * R + (6 * q * R) * s) / (t : ℝ≥0) ^ L) := by ring
      _ ≤ (C * A * B * Q ^ s) * (1 / (t : ℝ≥0) ^ c) :=
        mul_le_mul_of_nonneg_left (moment_power_ratio_le t (6 * R + (6 * q * R) * s) L c (by exact_mod_cast ht) hL) zero_le
      _ = _ := by ring
  have hsum := sourceCrudeTailBound_sum_current_power_budget W order z s R c t k w Z A epsilon horder hz ht hw hN hs hcut
  exact (hsum.trans (add_le_add le_rfl herr)).trans_eq (by dsimp [C, Q]; ring)

end

end Erdos207
