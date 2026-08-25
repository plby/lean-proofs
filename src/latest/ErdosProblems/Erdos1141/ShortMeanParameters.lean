import ErdosProblems.Erdos1141.SiegelParameters
import ErdosProblems.Erdos1141.BurgessParameters

/-!
# Parameters for the short convolution mean
-/

open scoped Topology

namespace Erdos1141

lemma eventually_const_add_log_le_rpow (c d ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ M : ℕ in Filter.atTop, c + d * Real.log (M : ℝ) ≤ (M : ℝ) ^ ε := by
  have hconst := ((tendsto_rpow_neg_atTop hε).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul c
  have hlog := tendsto_rpow_neg_mul_log d ε hε
  have hsum := hconst.add hlog
  simp only [mul_zero, zero_add] at hsum
  filter_upwards [hsum.eventually_le_const (by norm_num : (0 : ℝ) < 1),
    Filter.eventually_ge_atTop 1] with M hM hM1
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM1
  dsimp only [Function.comp_apply] at hM
  have h : (c + d * Real.log (M : ℝ)) * (M : ℝ) ^ (-ε) ≤ 1 := by nlinarith [hM]
  have hmul := mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hMr.le ε)
  rwa [mul_assoc, ← Real.rpow_add hMr, neg_add_cancel, Real.rpow_zero, mul_one, one_mul] at hmul

lemma pv_tail_le_short_mean_scale {q M : ℕ} (hq : 1 < q) (hqM : q ≤ M)
    (hlog : 4 * Real.log (M : ℝ) ≤ (M : ℝ) ^ (511 / 1024 : ℝ)) :
    4 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) / M ≤ (M : ℝ) ^ (-1 / 1024 : ℝ) := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hMr : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq.le)
  calc
    _ = Real.sqrt (q : ℝ) * (4 * Real.log (q : ℝ)) / M := by ring
    _ ≤ Real.sqrt (M : ℝ) * (4 * Real.log (M : ℝ)) / M := by gcongr
    _ ≤ Real.sqrt (M : ℝ) * (M : ℝ) ^ (511 / 1024 : ℝ) / M := by gcongr
    _ = (M : ℝ) ^ (-1 / 1024 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hMr]
      conv_lhs => arg 2; rw [← Real.rpow_one (M : ℝ)]
      rw [← Real.rpow_sub hMr]
      norm_num

theorem exists_short_mean_parameter_cutoff :
    ∃ M0 : ℕ, ∀ M : ℕ, M0 ≤ M →
      let X := ⌊(M : ℝ) ^ (31 / 64 : ℝ)⌋₊
      let D := ⌈(M : ℝ) ^ (15 / 32 : ℝ)⌉₊
      0 < X ∧ 0 < D ∧ D ≤ X ∧ X ≤ M ∧
        ∀ q : ℕ, 1 < q → q ≤ M →
          (D : ℝ) + X * (M : ℝ) ^ (-1 / 512 : ℝ) *
            (5 + Real.log (X : ℝ) + Real.log (M : ℝ)) +
            (4 * Real.sqrt (q : ℝ) * Real.log (q : ℝ)) * X / M ≤
              3 * (X : ℝ) * (M : ℝ) ^ (-1 / 1024 : ℝ) := by
  have hevent : ∀ᶠ M : ℕ in Filter.atTop,
      2 ≤ M ∧ 2 ≤ (M : ℝ) ^ (31 / 64 : ℝ) ∧
      4 ≤ (M : ℝ) ^ (15 / 1024 : ℝ) ∧
      5 + 2 * Real.log (M : ℝ) ≤ (M : ℝ) ^ (1 / 1024 : ℝ) ∧
      4 * Real.log (M : ℝ) ≤ (M : ℝ) ^ (511 / 1024 : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop 2,
      eventually_const_le_rpow 2 (31 / 64) (by norm_num),
      eventually_const_le_rpow 4 (15 / 1024) (by norm_num),
      eventually_const_add_log_le_rpow 5 2 (1 / 1024) (by norm_num),
      eventually_const_add_log_le_rpow 0 4 (511 / 1024) (by norm_num)] with M h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, by simpa only [zero_add] using h5⟩
  obtain ⟨M0, hcut⟩ := Filter.eventually_atTop.mp hevent
  refine ⟨M0, ?_⟩
  intro M hM
  rcases hcut M hM with ⟨hM2, hX2, h4, hlogs, hpv⟩
  let X := ⌊(M : ℝ) ^ (31 / 64 : ℝ)⌋₊
  let D := ⌈(M : ℝ) ^ (15 / 32 : ℝ)⌉₊
  have hMone : (1 : ℝ) ≤ M := by exact_mod_cast (by omega : 1 ≤ M)
  have hMr : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hXlo : (M : ℝ) ^ (31 / 64 : ℝ) / 2 ≤ (X : ℝ) := half_le_nat_floor hX2
  have hXhi : (X : ℝ) ≤ (M : ℝ) ^ (31 / 64 : ℝ) := Nat.floor_le (by positivity)
  have hXpos : 0 < X := by
    have h : (0 : ℝ) < X := lt_of_lt_of_le (by positivity) hXlo
    exact_mod_cast h
  have hXM : X ≤ M := by
    have h := hXhi.trans (Real.rpow_le_rpow_of_exponent_le hMone (by norm_num : (31 / 64 : ℝ) ≤ 1))
    simpa only [Real.rpow_one, Nat.cast_le] using h
  have hbase : (1 : ℝ) ≤ (M : ℝ) ^ (15 / 32 : ℝ) := Real.one_le_rpow hMone (by norm_num)
  have hDpos : 0 < D := Nat.ceil_pos.mpr (by positivity)
  have hDhi : (D : ℝ) ≤ 2 * (M : ℝ) ^ (15 / 32 : ℝ) :=
    Nat.ceil_le_two_mul (by linarith)
  have hDerror : (D : ℝ) ≤ (X : ℝ) * (M : ℝ) ^ (-1 / 1024 : ℝ) := by
    calc
      _ ≤ 2 * (M : ℝ) ^ (15 / 32 : ℝ) := hDhi
      _ ≤ ((M : ℝ) ^ (15 / 1024 : ℝ) / 2) * (M : ℝ) ^ (15 / 32 : ℝ) := by gcongr; linarith
      _ = ((M : ℝ) ^ (31 / 64 : ℝ) / 2) * (M : ℝ) ^ (-1 / 1024 : ℝ) := by
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← Real.rpow_add hMr, ← Real.rpow_add hMr]
        norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_right hXlo (by positivity)
  have hRone : (M : ℝ) ^ (-1 / 1024 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hMone (by norm_num)
  have hDX : D ≤ X := by
    have h := hDerror.trans (mul_le_of_le_one_right (Nat.cast_nonneg X) hRone)
    exact_mod_cast h
  refine ⟨hXpos, hDpos, hDX, hXM, ?_⟩
  intro q hq hqM
  have hXr : (0 : ℝ) < X := by exact_mod_cast hXpos
  have hlogX : Real.log (X : ℝ) ≤ Real.log (M : ℝ) := Real.log_le_log hXr (by exact_mod_cast hXM)
  have hmiddle : (X : ℝ) * (M : ℝ) ^ (-1 / 512 : ℝ) *
      (5 + Real.log (X : ℝ) + Real.log (M : ℝ)) ≤
        (X : ℝ) * (M : ℝ) ^ (-1 / 1024 : ℝ) := by
    calc
      _ ≤ (X : ℝ) * (M : ℝ) ^ (-1 / 512 : ℝ) * (M : ℝ) ^ (1 / 1024 : ℝ) := by
        gcongr
        linarith
      _ = _ := by rw [mul_assoc, ← Real.rpow_add hMr]; norm_num
  have hlast : (4 * Real.sqrt (q : ℝ) * Real.log (q : ℝ)) * X / M ≤
      (X : ℝ) * (M : ℝ) ^ (-1 / 1024 : ℝ) := by
    have h := mul_le_mul_of_nonneg_left (pv_tail_le_short_mean_scale hq hqM hpv) (Nat.cast_nonneg X)
    simpa only [mul_div_assoc, mul_left_comm, mul_comm, mul_assoc] using h
  change (D : ℝ) + _ + _ ≤ _
  linarith

end Erdos1141
