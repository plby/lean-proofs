import ErdosProblems.Erdos587.CyclicPrefix
import ErdosProblems.Erdos587.ArithmeticBlocks

/-!
# Dyadic summation of the centered cyclic error

A plain interval coefficient suffices: each dyadic block costs the same
amount, and the number of blocks contributes just one logarithm.
-/

open scoped BigOperators

namespace Erdos587

noncomputable def cyclicDyadicBlock (q R : ℕ) [NeZero q] : Finset (ZMod q) := by
  classical
  exact (Finset.univ.erase 0).filter
    (fun h => R ≤ h.valMinAbs.natAbs ∧ h.valMinAbs.natAbs < 2 * R)

lemma sum_cyclicDyadicBlock_le_prefix (q R M : ℕ) [NeZero q]
    (f : ZMod q → ℝ) (hf : ∀ h, 0 ≤ f h) (hRM : 2 * R ≤ M) :
    (∑ h ∈ cyclicDyadicBlock q R, f h) ≤
      ∑ h ∈ (Finset.univ.erase (0 : ZMod q)).filter
        (fun h => h.valMinAbs.natAbs ≤ M), f h := by
  classical
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro h hh
    obtain ⟨hh, hlo, hhi⟩ := Finset.mem_filter.mp hh
    exact Finset.mem_filter.mpr ⟨hh, by omega⟩
  · intro h hh hnot
    exact hf h

lemma sum_cyclicDyadicBlock_coeff_le (q U M₀ R B : ℕ) [NeZero q]
    (f : ZMod q → ℝ) (D : ℝ) (hf : ∀ h, 0 ≤ f h) (hD : 0 ≤ D)
    (hR : 0 < R) (hRsmall : R ≤ q) (hM₀B : M₀ ≤ B) (hqB : 2 * q ≤ B)
    (hqU : q ≤ U * M₀)
    (hprefix : ∀ M : ℕ, M₀ ≤ M → M ≤ B →
      (∑ h ∈ (Finset.univ.erase (0 : ZMod q)).filter
        (fun h => h.valMinAbs.natAbs ≤ M), f h) ≤ D * M) :
    (∑ h ∈ cyclicDyadicBlock q R, ‖nvCyclicIntervalCoeff q U h‖ * f h) ≤
      D * U * M₀ := by
  classical
  by_cases hsmall : 2 * R ≤ M₀
  · calc
      _ ≤ ∑ h ∈ cyclicDyadicBlock q R, (U : ℝ) * f h :=
        Finset.sum_le_sum (fun h hh => mul_le_mul_of_nonneg_right
          (norm_nvCyclicIntervalCoeff_le_length q U h) (hf h))
      _ = U * ∑ h ∈ cyclicDyadicBlock q R, f h := (Finset.mul_sum ..).symm
      _ ≤ U * (D * M₀) := mul_le_mul_of_nonneg_left
        ((sum_cyclicDyadicBlock_le_prefix q R M₀ f hf hsmall).trans
          (hprefix M₀ le_rfl hM₀B)) (Nat.cast_nonneg U)
      _ = _ := by ring
  · have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
    have hblock : ∀ h ∈ cyclicDyadicBlock q R,
        ‖nvCyclicIntervalCoeff q U h‖ ≤ (q : ℝ) / (2 * R) := by
      intro h hh
      obtain ⟨hh, hlo, hhi⟩ := Finset.mem_filter.mp hh
      have hnz : h ≠ 0 := (Finset.mem_erase.mp hh).1
      have hloR : (R : ℝ) ≤ h.valMinAbs.natAbs := by exact_mod_cast hlo
      apply (norm_nvCyclicIntervalCoeff_le_leastResidue q U hnz).trans
      gcongr
    calc
      _ ≤ ∑ h ∈ cyclicDyadicBlock q R, ((q : ℝ) / (2 * R)) * f h :=
        Finset.sum_le_sum (fun h hh => mul_le_mul_of_nonneg_right (hblock h hh) (hf h))
      _ = (q : ℝ) / (2 * R) * ∑ h ∈ cyclicDyadicBlock q R, f h :=
        (Finset.mul_sum ..).symm
      _ ≤ (q : ℝ) / (2 * R) * (D * (2 * R : ℕ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (sum_cyclicDyadicBlock_le_prefix q R (2 * R) f hf le_rfl).trans
          (hprefix (2 * R) (by omega) ((Nat.mul_le_mul_left 2 hRsmall).trans hqB))
      _ = D * q := by push_cast; field_simp
      _ ≤ D * (U * M₀ : ℕ) := mul_le_mul_of_nonneg_left (by exact_mod_cast hqU) hD
      _ = _ := by push_cast; ring

theorem sum_cyclic_interval_coeff_mul_le (q U M₀ B : ℕ) [NeZero q]
    (f : ZMod q → ℝ) (D : ℝ) (hf : ∀ h, 0 ≤ f h) (hD : 0 ≤ D)
    (hM₀B : M₀ ≤ B) (hqB : 2 * q ≤ B) (hqU : q ≤ U * M₀)
    (hprefix : ∀ M : ℕ, M₀ ≤ M → M ≤ B →
      (∑ h ∈ (Finset.univ.erase (0 : ZMod q)).filter
        (fun h => h.valMinAbs.natAbs ≤ M), f h) ≤ D * M) :
    (∑ h ∈ Finset.univ.erase (0 : ZMod q), ‖nvCyclicIntervalCoeff q U h‖ * f h) ≤
      D * U * M₀ * (q.log2 + 1 : ℕ) := by
  classical
  have hq : 0 < q := NeZero.pos q
  calc
    _ ≤ ∑ i ∈ dyadicBlockIndices q,
        ∑ h ∈ cyclicDyadicBlock q (2 ^ i), ‖nvCyclicIntervalCoeff q U h‖ * f h := by
      apply sum_le_sum_family_of_cover _ _ _ _ (fun h => mul_nonneg (norm_nonneg _) (hf h))
      intro h hh
      have hnz : h ≠ 0 := (Finset.mem_erase.mp hh).1
      have hd : 0 < h.valMinAbs.natAbs := by
        by_contra hd
        have hz : h.valMinAbs = 0 := Int.natAbs_eq_zero.mp (by omega)
        exact hnz ((ZMod.valMinAbs_eq_zero h).mp hz)
      have hdq : h.valMinAbs.natAbs ≤ q :=
        (ZMod.natAbs_valMinAbs_le h).trans (Nat.div_le_self q 2)
      obtain ⟨i, hi, hlo, hhi, hpow⟩ := exists_dyadic_block hd hdq
      exact ⟨i, hi, Finset.mem_filter.mpr ⟨hh, hlo, hhi⟩⟩
    _ ≤ ∑ _i ∈ dyadicBlockIndices q, D * U * M₀ := by
      apply Finset.sum_le_sum
      intro i hi
      exact sum_cyclicDyadicBlock_coeff_le q U M₀ (2 ^ i) B f D hf hD
        (by positivity) (pow_le_of_mem_dyadicBlockIndices hi) hM₀B hqB hqU hprefix
    _ = _ := by simp [dyadicBlockIndices, hq.ne', mul_comm]

theorem exists_centered_cyclic_weighted_error_bound (j : ℕ) (hj : 0 < j) :
    ∃ K : ℝ, 0 < K ∧ ∃ O : ℕ, 0 < O ∧
      ∀ (q A C X Z L U M₀ : ℕ) [NeZero q], A.Coprime q → 0 < L → 0 < M₀ →
        q ≤ U * M₀ →
        3 ≤ (((2 * M₀ * L : ℕ) : ℝ) ^ (1 / (4 ^ j : ℕ) : ℝ)) →
        (q : ℝ) ≤ (((2 * M₀ * L : ℕ) : ℝ) ^ (1 - 2 / (4 ^ j : ℕ) : ℝ)) →
        ‖∑ h : ZMod q, nvCyclicIntervalCoeff q U h *
          nvCenteredQuadraticIntervalSum q A 0 C X Z L h‖ ≤
          K * U * M₀ * Real.sqrt L * Real.log ((4 * (q + M₀) * L : ℕ) : ℝ) ^ O *
            (q.log2 + 1 : ℕ) := by
  classical
  obtain ⟨K, hK, O, hO, hmean⟩ := exists_uniform_centered_cyclic_prefix_bound j hj
  refine ⟨K, hK, O, hO, ?_⟩
  intro q A C X Z L U M₀ hq ha hL hM₀ hqU hroot hmargin
  let B := 2 * (q + M₀)
  let D := K * Real.sqrt L * Real.log ((2 * B * L : ℕ) : ℝ) ^ O
  have hM₀B : M₀ ≤ B := by dsimp [B]; omega
  have hqB : 2 * q ≤ B := by dsimp [B]; omega
  have hsize : 0 < 2 * B * L := by
    have : 0 < B := hM₀.trans_le hM₀B
    positivity
  have hlog : 0 ≤ Real.log ((2 * B * L : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hsize)
  have hD : 0 ≤ D := mul_nonneg (mul_nonneg hK.le (Real.sqrt_nonneg _)) (pow_nonneg hlog O)
  have hprefix : ∀ M : ℕ, M₀ ≤ M → M ≤ B →
      (∑ h ∈ (Finset.univ.erase (0 : ZMod q)).filter
        (fun h => h.valMinAbs.natAbs ≤ M),
        ‖nvCenteredQuadraticIntervalSum q A 0 C X Z L h‖) ≤ D * M := by
    intro M hM hMB
    apply (hmean q A C X Z L M₀ B ha hL hM₀ hM₀B hroot hmargin M hM hMB).trans_eq
    dsimp [D]
    ring
  have hweighted := sum_cyclic_interval_coeff_mul_le q U M₀ B
    (fun h => ‖nvCenteredQuadraticIntervalSum q A 0 C X Z L h‖) D
    (fun h => norm_nonneg _) hD hM₀B hqB hqU hprefix
  have hzero : nvCyclicIntervalCoeff q U 0 *
      nvCenteredQuadraticIntervalSum q A 0 C X Z L 0 = 0 := by
    rw [nvCenteredQuadraticIntervalSum_zero, mul_zero]
  have hsum : (∑ h : ZMod q, nvCyclicIntervalCoeff q U h *
      nvCenteredQuadraticIntervalSum q A 0 C X Z L h) =
      ∑ h ∈ Finset.univ.erase (0 : ZMod q), nvCyclicIntervalCoeff q U h *
        nvCenteredQuadraticIntervalSum q A 0 C X Z L h := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : ZMod q)), hzero, add_zero]
  rw [hsum]
  apply (norm_sum_le _ _).trans
  simp only [norm_mul]
  apply hweighted.trans_eq
  have harg : 2 * B * L = 4 * (q + M₀) * L := by dsimp [B]; ring
  dsimp only [D]
  rw [harg]
  ring

end Erdos587
