/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos1099.Basic
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Finite gap-energy lemmas for Erdős Problem 1099

The estimates here are deliberately independent of divisors. They say that
an increasing finite partition whose gaps are at most `g` has `alpha`-energy
at most `g^(alpha-1)` times its total length, and that subdividing an interval
can only lower this energy when `alpha >= 1`.
-/

open Finset
open scoped BigOperators

namespace Erdos1099

noncomputable section

/-- Additive `alpha`-energy of the consecutive gaps of a finite sequence. -/
def gapEnergy (alpha : ℝ) {m : ℕ} (x : Fin (m + 1) → ℝ) : ℝ :=
  ∑ i : Fin m, (x ⟨i.1 + 1, by omega⟩ - x ⟨i.1, by omega⟩) ^ alpha

/-- Consecutive differences telescope. -/
lemma sum_fin_consecutive_sub {m : ℕ} (x : Fin (m + 1) → ℝ) :
    (∑ i : Fin m, (x ⟨i.1 + 1, by omega⟩ - x ⟨i.1, by omega⟩)) =
      x ⟨m, by omega⟩ - x ⟨0, by omega⟩ := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Fin.sum_univ_succ]
      have htail := ih (fun j : Fin (m + 1) ↦ x j.succ)
      have htail' :
          (∑ i : Fin m,
            (x ⟨i.1 + 2, by omega⟩ - x ⟨i.1 + 1, by omega⟩)) =
            x ⟨m + 1, by omega⟩ - x ⟨1, by omega⟩ := by
        simpa only [Fin.succ_mk, Nat.add_assoc] using htail
      change (x ⟨1, by omega⟩ - x ⟨0, by omega⟩) +
          (∑ i : Fin m,
            (x ⟨i.1 + 2, by omega⟩ - x ⟨i.1 + 1, by omega⟩)) =
        x ⟨m + 1, by omega⟩ - x ⟨0, by omega⟩
      rw [htail']
      ring

/-- The standard mesh-times-length estimate for a finite partition. -/
lemma gapEnergy_le_mesh_mul_length {alpha : ℝ} (halpha : 1 ≤ alpha)
    {m : ℕ} (x : Fin (m + 1) → ℝ) (hx : Monotone x) {g : ℝ}
    (hmesh : ∀ i : Fin m,
      x ⟨i.1 + 1, by omega⟩ - x ⟨i.1, by omega⟩ ≤ g) :
    gapEnergy alpha x ≤ g ^ (alpha - 1) *
      (x ⟨m, by omega⟩ - x ⟨0, by omega⟩) := by
  unfold gapEnergy
  calc
    (∑ i : Fin m,
        (x ⟨i.1 + 1, by omega⟩ - x ⟨i.1, by omega⟩) ^ alpha)
        ≤ ∑ i : Fin m, g ^ (alpha - 1) *
            (x ⟨i.1 + 1, by omega⟩ - x ⟨i.1, by omega⟩) := by
          apply Finset.sum_le_sum
          intro i _
          let d := x ⟨i.1 + 1, by omega⟩ - x ⟨i.1, by omega⟩
          have hd : 0 ≤ d := sub_nonneg.mpr (hx (by simp))
          have hexp : 0 ≤ alpha - 1 := sub_nonneg.mpr halpha
          have hpow : d ^ (alpha - 1) ≤ g ^ (alpha - 1) :=
            Real.rpow_le_rpow hd (hmesh i) hexp
          have hfactor : d ^ alpha = d ^ (alpha - 1) * d := by
            calc
              d ^ alpha = d ^ ((alpha - 1) + 1) := by
                congr 1
                ring
              _ = d ^ (alpha - 1) * d := by
                rw [Real.rpow_add' hd (by linarith), Real.rpow_one]
          rw [hfactor]
          exact mul_le_mul_of_nonneg_right hpow hd
    _ = g ^ (alpha - 1) *
        (x ⟨m, by omega⟩ - x ⟨0, by omega⟩) := by
          rw [← Finset.mul_sum, sum_fin_consecutive_sub]

/-- Two nonnegative subgaps have no more `alpha`-energy than their sum. -/
lemma two_gap_energy_le {alpha a b : ℝ} (halpha : 1 ≤ alpha)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ^ alpha + b ^ alpha ≤ (a + b) ^ alpha :=
  Real.add_rpow_le_rpow_add ha hb halpha

end

end Erdos1099
