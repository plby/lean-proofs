import ErdosProblems.Erdos587.CenteredCyclic

/-!
# Uniform centered prefix estimates above a fixed cutoff

The power-margin condition improves as the frequency cutoff increases.
All prefix estimates can consequently use a common logarithmic envelope.
-/

open scoped BigOperators

namespace Erdos587

lemma iterated_root_margin_exponent_nonneg {j : ℕ} (hj : 0 < j) :
    0 ≤ (1 - 2 / (4 ^ j : ℕ) : ℝ) := by
  have hfour : (4 : ℕ) ≤ 4 ^ j := by
    calc
      4 = (4 : ℕ) ^ 1 := (pow_one _).symm
      _ ≤ 4 ^ j := pow_le_pow_right₀ (by norm_num) hj
  have hfourR : (4 : ℝ) ≤ (4 ^ j : ℕ) := by exact_mod_cast hfour
  have hpos : (0 : ℝ) < (4 ^ j : ℕ) := by positivity
  have hh : (2 : ℝ) / (4 ^ j : ℕ) ≤ 1 := (div_le_iff₀ hpos).mpr (by linarith)
  linarith

lemma iterated_root_margin_mono {j X Y q : ℕ} (hj : 0 < j) (hXY : X ≤ Y)
    (hroot : 3 ≤ (X : ℝ) ^ (1 / (4 ^ j : ℕ) : ℝ))
    (hmargin : (q : ℝ) ≤ (X : ℝ) ^ (1 - 2 / (4 ^ j : ℕ) : ℝ)) :
    3 ≤ (Y : ℝ) ^ (1 / (4 ^ j : ℕ) : ℝ) ∧
      (q : ℝ) ≤ (Y : ℝ) ^ (1 - 2 / (4 ^ j : ℕ) : ℝ) := by
  have hXYR : (X : ℝ) ≤ Y := by exact_mod_cast hXY
  exact ⟨hroot.trans (Real.rpow_le_rpow (Nat.cast_nonneg X) hXYR (by positivity)),
    hmargin.trans (Real.rpow_le_rpow (Nat.cast_nonneg X) hXYR
      (iterated_root_margin_exponent_nonneg hj))⟩

theorem exists_uniform_centered_cyclic_prefix_bound (j : ℕ) (hj : 0 < j) :
    ∃ K : ℝ, 0 < K ∧ ∃ O : ℕ, 0 < O ∧
      ∀ (q A C X Z L M₀ B : ℕ) [NeZero q], A.Coprime q → 0 < L → 0 < M₀ → M₀ ≤ B →
        3 ≤ (((2 * M₀ * L : ℕ) : ℝ) ^ (1 / (4 ^ j : ℕ) : ℝ)) →
        (q : ℝ) ≤ (((2 * M₀ * L : ℕ) : ℝ) ^ (1 - 2 / (4 ^ j : ℕ) : ℝ)) →
        ∀ M : ℕ, M₀ ≤ M → M ≤ B →
          (∑ h ∈ (Finset.univ.erase (0 : ZMod q)).filter (fun h => h.valMinAbs.natAbs ≤ M),
            ‖nvCenteredQuadraticIntervalSum q A 0 C X Z L h‖) ≤
            K * M * Real.sqrt L * Real.log ((2 * B * L : ℕ) : ℝ) ^ O := by
  obtain ⟨K, hK, O, hO, hmean⟩ := exists_centered_cyclic_low_mean_bound j
  refine ⟨K, hK, O, hO, ?_⟩
  intro q A C X Z L M₀ B hq ha hL hM₀ hM₀B hroot hmargin M hM hMB
  have hsmall : 2 * M₀ * L ≤ 2 * M * L := Nat.mul_le_mul_right L (Nat.mul_le_mul_left 2 hM)
  obtain ⟨hrootM, hmarginM⟩ := iterated_root_margin_mono hj hsmall hroot hmargin
  have hMpos : 0 < M := hM₀.trans_le hM
  have hsize : 0 < 2 * M * L := by positivity
  have hbig : 2 * M * L ≤ 2 * B * L := Nat.mul_le_mul_right L (Nat.mul_le_mul_left 2 hMB)
  have hlog : Real.log ((2 * M * L : ℕ) : ℝ) ≤ Real.log ((2 * B * L : ℕ) : ℝ) :=
    Real.log_le_log (by exact_mod_cast hsize) (by exact_mod_cast hbig)
  have hlog0 : 0 ≤ Real.log ((2 * M * L : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hsize)
  apply (hmean q A C X Z L M ha hsize hrootM hmarginM).trans
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog0 hlog O) (by positivity)

end Erdos587
