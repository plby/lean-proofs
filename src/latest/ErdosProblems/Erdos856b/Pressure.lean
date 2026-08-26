import ErdosProblems.Erdos856b.Optimization

/-!
# Finite-block and weighted variational quantities

The finite-block domain is exactly `n ≥ 1`, `1 ≤ r ≤ n`, as in equation (1.2).
The uniform pressure additionally includes rank zero, as in equation (4.4).
-/

namespace Erdos856b

open Real

def blockScores (k : ℕ) : Set ℝ :=
  {v | ∃ n r : ℕ, 0 < n ∧ 0 < r ∧ r ≤ n ∧ v = blockValue n r (M k n r)}

/-- The candidate exponent, defined without assuming any asymptotic statement. -/
noncomputable def gamma (k : ℕ) : ℝ := sSup (blockScores k)

theorem blockScores_nonempty (k : ℕ) : (blockScores k).Nonempty :=
  ⟨blockValue 1 1 (M k 1 1), 1, 1, by omega, by omega, by omega, rfl⟩

theorem blockScores_bddAbove {k : ℕ} (hk : 3 ≤ k) : BddAbove (blockScores k) := by
  refine ⟨1, ?_⟩
  rintro v ⟨n, r, hn, hr, hrn, rfl⟩
  exact blockValue_le_one hk hn hr hrn

theorem blockValue_le_gamma {k n r : ℕ} (hk : 3 ≤ k) (hn : 0 < n)
    (hr : 0 < r) (hrn : r ≤ n) : blockValue n r (M k n r) ≤ gamma k :=
  le_csSup (blockScores_bddAbove hk) ⟨n, r, hn, hr, hrn, rfl⟩

theorem gamma_pos {k : ℕ} (hk : 3 ≤ k) : 0 < gamma k := by
  have h := blockValue_le_gamma hk (by omega : 0 < 1) (by omega : 0 < 1) (by omega)
  have hpos : 0 < blockValue 1 1 (M k 1 1) := by
    dsimp [blockValue]
    positivity
  exact hpos.trans_le h

theorem gamma_le_one {k : ℕ} (hk : 3 ≤ k) : gamma k ≤ 1 := by
  apply csSup_le (blockScores_nonempty k)
  rintro v ⟨n, r, hn, hr, hrn, rfl⟩
  exact blockValue_le_one hk hn hr hrn

theorem gamma_eq_finite_block_sup {k : ℕ} (hk : 3 ≤ k) :
    gamma k = sSup {v : ℝ | ∃ n r : ℕ, 0 < n ∧ 0 < r ∧ r ≤ n ∧
      v = (r : ℝ) / (exp 1 * n) * (M k n r : ℝ) ^ (1 / (r : ℝ))} := by
  unfold gamma
  congr 1
  ext v
  simp only [blockScores, Set.mem_ofPred_eq]
  constructor <;> rintro ⟨n, r, hn, hr, hrn, h⟩
  · refine ⟨n, r, hn, hr, hrn, ?_⟩
    exact h.trans (blockValue_eq_rpow (by exact_mod_cast M_pos hk hrn))
  · refine ⟨n, r, hn, hr, hrn, ?_⟩
    exact h.trans (blockValue_eq_rpow (by exact_mod_cast M_pos hk hrn)).symm

theorem log_M_weight_le_gamma {k n r : ℕ} (hk : 3 ≤ k) (hn : 0 < n)
    (hrn : r ≤ n) {z : ℝ} (hz : 0 < z) :
    log (M k n r) + r * log z ≤ n * (gamma k * z) := by
  by_cases hr : r = 0
  · subst r
    simp only [M_rank_zero hk, Nat.cast_one, log_one, Nat.cast_zero, zero_mul, add_zero]
    positivity [gamma_pos hk]
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
    have h := (log_weight_div_le_blockValue hn hrpos hz (M k n r)).trans
      (blockValue_le_gamma hk hn hrpos hrn)
    have h' := (div_le_iff₀ (mul_pos (by positivity : (0 : ℝ) < n) hz)).mp h
    nlinarith

def logPressureScores (k : ℕ) (z : ℝ) : Set ℝ :=
  {v | ∃ n r : ℕ, 0 < n ∧ r ≤ n ∧ v = (log (M k n r) + r * log z) / n}

/-- The logarithm of the uniform weighted pressure. -/
noncomputable def logPressure (k : ℕ) (z : ℝ) : ℝ := sSup (logPressureScores k z)

theorem zero_mem_logPressureScores {k : ℕ} (hk : 3 ≤ k) (z : ℝ) :
    0 ∈ logPressureScores k z := by
  refine ⟨1, 0, by omega, by omega, ?_⟩
  simp [M_rank_zero hk]

theorem logPressureScores_bddAbove {k : ℕ} (hk : 3 ≤ k) {z : ℝ} (hz : 0 < z) :
    BddAbove (logPressureScores k z) := by
  refine ⟨z, ?_⟩
  rintro v ⟨n, r, hn, hrn, rfl⟩
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < n)).mpr
  simpa [mul_comm] using log_M_weight_le hk hrn hz

theorem logPressure_nonneg {k : ℕ} (hk : 3 ≤ k) {z : ℝ} (hz : 0 < z) :
    0 ≤ logPressure k z :=
  le_csSup (logPressureScores_bddAbove hk hz) (zero_mem_logPressureScores hk z)

theorem logPressure_le_gamma_mul {k : ℕ} (hk : 3 ≤ k) {z : ℝ} (hz : 0 < z) :
    logPressure k z ≤ gamma k * z := by
  apply csSup_le ⟨0, zero_mem_logPressureScores hk z⟩
  rintro v ⟨n, r, hn, hrn, rfl⟩
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < n)).mpr
  simpa [mul_comm] using log_M_weight_le_gamma hk hn hrn hz

theorem log_M_weight_div_le_logPressure {k n r : ℕ} (hk : 3 ≤ k) (hn : 0 < n)
    (hrn : r ≤ n) {z : ℝ} (hz : 0 < z) :
    (log (M k n r) + r * log z) / n ≤ logPressure k z :=
  le_csSup (logPressureScores_bddAbove hk hz) ⟨n, r, hn, hrn, rfl⟩

/-- Interchanging the finite-block and positive-weight suprema is exact. This is the
optimization part of equations (4.2) and (4.4), without any arithmetic assumption. -/
theorem gamma_eq_sup_logPressure_div {k : ℕ} (hk : 3 ≤ k) :
    gamma k = sSup {v : ℝ | ∃ z : ℝ, 0 < z ∧ v = logPressure k z / z} := by
  let S : Set ℝ := {v | ∃ z : ℝ, 0 < z ∧ v = logPressure k z / z}
  have hSne : S.Nonempty := ⟨logPressure k 1 / 1, 1, by norm_num, rfl⟩
  have hSbound : ∀ v ∈ S, v ≤ gamma k := by
    rintro v ⟨z, hz, rfl⟩
    exact (div_le_iff₀ hz).mpr (logPressure_le_gamma_mul hk hz)
  have hSbdd : BddAbove S := ⟨gamma k, hSbound⟩
  apply le_antisymm
  · apply csSup_le (blockScores_nonempty k)
    rintro v ⟨n, r, hn, hr, hrn, rfl⟩
    let z := exp (1 - log (M k n r) / r)
    have hz : 0 < z := exp_pos _
    have hP := div_le_div_of_nonneg_right
      (log_M_weight_div_le_logPressure hk hn hrn hz) hz.le
    have hblock : blockValue n r (M k n r) ≤ logPressure k z / z := by
      rw [blockValue_eq_log_weight hn hr]
      simpa only [div_div, z] using hP
    exact hblock.trans (le_csSup hSbdd ⟨z, hz, rfl⟩)
  · exact csSup_le hSne hSbound

end Erdos856b
