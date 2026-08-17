import ErdosProblems.Erdos49.UniformTheta

/-!
# Elementary consequences of the chosen scales

These are the inequalities used repeatedly when the finite estimate is
converted to Tao's asymptotic error term.
-/

open Filter Set Topology

namespace Erdos49

noncomputable section

def taoErrorScale (N : ℕ) : ℝ :=
  (N : ℝ) * scaleT N ^ 5 / Real.log (N : ℝ) ^ 2

lemma scale_exp_t {N : ℕ} (hs : ScaleFacts N) :
    Real.exp (scaleT N) = Real.log (N : ℝ) := by
  unfold scaleT
  rw [Real.exp_log]
  have hlog : (0 : ℝ) < Real.log N := by
    have ht := hs.t_ge
    have hlog0 : (0 : ℝ) ≤ Real.log N :=
      Real.log_nonneg (by exact_mod_cast hs.N_pos)
    by_contra hn
    have heq : Real.log (N : ℝ) = 0 := le_antisymm (not_lt.mp hn) hlog0
    unfold scaleT at ht
    rw [heq, Real.log_zero] at ht
    norm_num at ht
  exact hlog

lemma scale_h_ge {N : ℕ} (hs : ScaleFacts N) :
    (100 : ℝ) ≤ Real.log (N : ℝ) := by
  have he := scale_exp_t hs
  calc
    (100 : ℝ) ≤ Real.exp 10 := by
      calc
        (100 : ℝ) ≤ 2 ^ (10 : ℕ) := by norm_num
        _ ≤ Real.exp 1 ^ (10 : ℕ) := by gcongr; exact Real.exp_one_gt_two.le
        _ = Real.exp 10 := by rw [← Real.exp_nat_mul]; norm_num
    _ ≤ Real.exp (scaleT N) := Real.exp_le_exp.mpr hs.t_ge
    _ = Real.log (N : ℝ) := he

lemma scale_logL_upper {N : ℕ} (hs : ScaleFacts N) :
    Real.log (scaleL N : ℝ) ≤ 21 * scaleT N := by
  have hLpos : (0 : ℝ) < scaleL N := by exact_mod_cast hs.L_pos
  calc
    Real.log (scaleL N : ℝ) ≤
        Real.log (2 * Real.exp (20 * scaleT N)) :=
      Real.log_le_log hLpos hs.L_bounds.2
    _ = Real.log 2 + 20 * scaleT N := by
      rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp]
    _ ≤ 21 * scaleT N := by
      have hlog2' := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at hlog2'
      linarith [hs.t_ge]

lemma scale_logD_upper {N : ℕ} (hs : ScaleFacts N) :
    Real.log (scaleD N : ℝ) ≤ 2 * scaleT N ^ 4 := by
  have hDpos : (0 : ℝ) < scaleD N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hs.D_one)
  calc
    Real.log (scaleD N : ℝ) ≤
        Real.log (2 * Real.exp (scaleT N ^ 4)) :=
      Real.log_le_log hDpos hs.D_bounds.2
    _ = Real.log 2 + scaleT N ^ 4 := by
      rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp]
    _ ≤ 2 * scaleT N ^ 4 := by
      have hlog2' := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at hlog2'
      have ht4 : (1 : ℝ) ≤ scaleT N ^ 4 := by
        have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 10) hs.t_ge 4
        norm_num at hp ⊢
        linarith
      linarith

lemma scale_logW_sub_one_lower {N : ℕ} (hs : ScaleFacts N) :
    Real.log (N : ℝ) / 3 ≤ Real.log (scaleW N - 1 : ℕ) := by
  have hW3 := hs.W_three
  have hWsubpos : (0 : ℝ) < (scaleW N - 1 : ℕ) := by exact_mod_cast (by omega : 0 < scaleW N - 1)
  have hhalf : (scaleW N : ℝ) / 2 ≤ (scaleW N - 1 : ℕ) := by
    have hnat : scaleW N ≤ 2 * (scaleW N - 1) := by omega
    have hreal : (scaleW N : ℝ) ≤ 2 * (scaleW N - 1 : ℕ) := by
      exact_mod_cast hnat
    linarith
  have hloghalf : Real.log (scaleW N : ℝ) - Real.log 2 ≤
      Real.log (scaleW N - 1 : ℕ) := by
    calc
      Real.log (scaleW N : ℝ) - Real.log 2 =
          Real.log ((scaleW N : ℝ) / 2) := by
        rw [Real.log_div (by positivity) (by norm_num)]
      _ ≤ Real.log (scaleW N - 1 : ℕ) :=
        Real.log_le_log (by positivity) hhalf
  have hlog2 : Real.log 2 ≤ 1 := by
    have h' := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h' ⊢
    exact h'
  have hh := scale_h_ge hs
  linarith [hs.logW_lower]

lemma scale_medium_power_lower {N : ℕ} (hs : ScaleFacts N) :
    Real.exp (scaleT N / 20) ≤
      Real.log (scaleW N - 1 : ℕ) ^ ((1 : ℝ) / 10) := by
  let t := scaleT N
  let h := Real.log (N : ℝ)
  have ht : 10 ≤ t := hs.t_ge
  have hexpt : Real.exp t = h := by simpa [t, h] using scale_exp_t hs
  have he5 : (3 : ℝ) ≤ Real.exp (t / 2) := by
    calc
      (3 : ℝ) ≤ Real.exp 5 := by
        calc
          (3 : ℝ) ≤ 2 ^ (5 : ℕ) := by norm_num
          _ ≤ Real.exp 1 ^ (5 : ℕ) := by gcongr; exact Real.exp_one_gt_two.le
          _ = Real.exp 5 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ Real.exp (t / 2) := Real.exp_le_exp.mpr (by linarith)
  have hsqrt : Real.exp (t / 2) ≤ h / 3 := by
    rw [← hexpt]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 3)).2
    have hmul := mul_le_mul_of_nonneg_left he5 (Real.exp_pos (t / 2)).le
    rw [← Real.exp_add] at hmul
    have heq : t / 2 + t / 2 = t := by ring
    rw [heq] at hmul
    exact hmul
  have hbase : Real.exp (t / 2) ≤ Real.log (scaleW N - 1 : ℕ) :=
    hsqrt.trans (by simpa [h] using scale_logW_sub_one_lower hs)
  have hrpow := Real.rpow_le_rpow (Real.exp_pos (t / 2)).le hbase
    (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 10)
  calc
    Real.exp (t / 20) =
        Real.exp (t / 2) ^ ((1 : ℝ) / 10) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      congr 1 <;> ring
    _ ≤ Real.log (scaleW N - 1 : ℕ) ^ ((1 : ℝ) / 10) := hrpow

lemma primary_cell_factor_bound {N : ℕ} (hs : ScaleFacts N) :
    ((((N / scaleW N + 1) * scaleD N : ℕ) : ℝ) * scaleD N) ≤
      500 * Real.exp (4 * scaleT N ^ 4 + 20 * scaleT N) := by
  have hWpos : (0 : ℝ) < scaleW N := by
    have hW3 := hs.W_three
    exact_mod_cast (show 0 < scaleW N by omega)
  have hQposNat : 0 < scaleQ N := by
    unfold scaleQ
    exact Nat.mul_pos (by positivity) hs.L_pos
  have hQpos : (0 : ℝ) < scaleQ N := by
    exact_mod_cast hQposNat
  have hNW : ((N / scaleW N : ℕ) : ℝ) ≤ 2 * scaleQ N := by
    calc
      ((N / scaleW N : ℕ) : ℝ) ≤ (N : ℝ) / scaleW N := Nat.cast_div_le
      _ ≤ 2 * scaleQ N := by
        apply (div_le_iff₀ hWpos).2
        have hm := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * scaleQ N)).mp
          hs.W_cast_lower
        simpa [mul_assoc, mul_comm, mul_left_comm] using hm
  have hQone : (1 : ℝ) ≤ scaleQ N := by
    exact_mod_cast (show 1 ≤ scaleQ N from hQposNat)
  have hDsq : (scaleD N : ℝ) ^ 2 ≤
      4 * Real.exp (2 * scaleT N ^ 4) := by
    calc
      (scaleD N : ℝ) ^ 2 ≤
          (2 * Real.exp (scaleT N ^ 4)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hs.D_bounds.2 2
      _ = 4 * Real.exp (2 * scaleT N ^ 4) := by
        rw [show (2 : ℝ) * scaleT N ^ 4 =
          scaleT N ^ 4 + scaleT N ^ 4 by ring, Real.exp_add]
        ring
  push_cast
  calc
    ((N / scaleW N : ℕ) + 1) * (scaleD N : ℝ) * scaleD N ≤
        (3 * (scaleQ N : ℝ)) * (scaleD N : ℝ) ^ 2 := by
      nlinarith [hNW, hQone]
    _ ≤ (3 * (40 * Real.exp
        (2 * scaleT N ^ 4 + 20 * scaleT N))) *
          (4 * Real.exp (2 * scaleT N ^ 4)) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hs.Q_bound (by norm_num)) hDsq
        (by positivity) (by positivity)
    _ ≤ 500 * Real.exp (4 * scaleT N ^ 4 + 20 * scaleT N) := by
      have hexp : Real.exp
          (2 * scaleT N ^ 4 + 20 * scaleT N) *
            Real.exp (2 * scaleT N ^ 4) =
          Real.exp (4 * scaleT N ^ 4 + 20 * scaleT N) := by
        rw [← Real.exp_add]
        congr 1 <;> ring
      calc
        (3 * (40 * Real.exp
            (2 * scaleT N ^ 4 + 20 * scaleT N))) *
              (4 * Real.exp (2 * scaleT N ^ 4)) =
            480 * (Real.exp (2 * scaleT N ^ 4 + 20 * scaleT N) *
              Real.exp (2 * scaleT N ^ 4)) := by ring
        _ = 480 * Real.exp (4 * scaleT N ^ 4 + 20 * scaleT N) := by rw [hexp]
        _ ≤ 500 * Real.exp (4 * scaleT N ^ 4 + 20 * scaleT N) := by
          nlinarith [Real.exp_pos (4 * scaleT N ^ 4 + 20 * scaleT N)]

lemma taoErrorScale_pos {N : ℕ} (hs : ScaleFacts N) :
    0 < taoErrorScale N := by
  unfold taoErrorScale
  have hh := scale_h_ge hs
  have hN : (0 : ℝ) < N := by exact_mod_cast hs.N_pos
  have ht : (0 : ℝ) < scaleT N := by linarith [hs.t_ge]
  positivity

end

end Erdos49
