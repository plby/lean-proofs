/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FiniteProbability

/-! # Corrected asymmetric degree-spread contraction in hypergraph regularization -/

namespace Erdos207

/-- The symmetric error estimate printed in the source is insufficient for
its claimed halving implication. This is only a counterexample to that
intermediate arithmetic implication. -/
theorem regularization_symmetric_error_does_not_imply_halving :
    |(5 : ℝ) - 4| ≤ 4 / 4 ∧ |(6 : ℝ) - 8| ≤ 8 / 4 ∧
      4 ≤ (4 : ℝ) ∧ (8 : ℝ) ≤ 2 * 4 ∧
      (4 : ℝ) + 4 = 4 + 4 ∧ (0 : ℝ) + 8 = 4 + 4 ∧
      (4 : ℝ) / 2 < |(4 + 5 : ℝ) - (0 + 6)| := by
  norm_num

theorem regularization_new_degree_interval
    (D F d w mu X : ℝ) (hcenter : d + w = D + F)
    (hw : w ≤ 2 * F) (hmuLow : 13 * w / 16 ≤ mu) (hmuHigh : mu ≤ w)
    (hdev : |X - mu| ≤ F / 32) :
    D + F - 13 * F / 32 ≤ d + X ∧ d + X ≤ D + F + F / 32 := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hdev
  constructor <;> linarith

theorem regularization_degree_gap_lt_half
    (D F d e w v mu nu X Y : ℝ) (hF : 0 < F)
    (hd : d + w = D + F) (he : e + v = D + F)
    (hw : w ≤ 2 * F) (hv : v ≤ 2 * F)
    (hmuLow : 13 * w / 16 ≤ mu) (hmuHigh : mu ≤ w)
    (hnuLow : 13 * v / 16 ≤ nu) (hnuHigh : nu ≤ v)
    (hX : |X - mu| ≤ F / 32) (hY : |Y - nu| ≤ F / 32) :
    |(d + X) - (e + Y)| < F / 2 := by
  obtain ⟨hxlo, hxhi⟩ := regularization_new_degree_interval D F d w mu X hd hw hmuLow hmuHigh hX
  obtain ⟨hylo, hyhi⟩ := regularization_new_degree_interval D F e v nu Y he hv hnuLow hnuHigh hY
  apply abs_lt.mpr
  constructor <;> linarith

end Erdos207
