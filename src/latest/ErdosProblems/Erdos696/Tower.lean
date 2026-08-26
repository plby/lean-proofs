/-
Adapted from Jayyhk/erdos-lean, problems/696/Erdos696.lean,
revision 806d0b587ea7a2fb5afd5154edfe416a0cd404a4.
Source: https://www.erdosproblems.com/forum/thread/696#post-6848
All upstream heartbeat overrides have been removed.
-/

import ErdosProblems.Erdos696.Defs
import ErdosProblems.Erdos696.AnalyticInputs
import ErdosProblems.Erdos696.SubsetProduct

namespace Erdos696

open scoped BigOperators Topology
open Real MeasureTheory

-- === Inlined from Erdos696/Tower.lean ===
/-
# Tower arithmetic

Real-analysis lemmas about the tower `T_m`, the auxiliary scale
`U_m = T_m^3`, and the iterated-tower descent functions
`G(t) = (log t)^2` (used for `H`) and
`f(t) = C_f (log log t)(log log log t)^2` (used for `h`).

Mirrors §2.2, the start of §3, and the start of §4 of the paper.
-/



open Real

/-- Identity (2.4): `log T_m = T_{m-1}` for `m ≥ 1`. -/
lemma log_tower_succ (m : ℕ) :
    Real.log (tower (m + 1)) = tower m := by
  -- `tower (m+1) = exp (tower m)` by definition;
  -- then `log (exp x) = x` for any real `x`.
  show Real.log (Real.exp (tower m)) = tower m
  exact Real.log_exp _

/-- The tower is strictly positive: `T_m > 0`. -/
lemma tower_pos (m : ℕ) : 0 < tower m := by
  induction m with
  | zero =>
      -- `tower 0 = exp 1 > 0`.
      show 0 < Real.exp 1
      exact Real.exp_pos 1
  | succ m _ =>
      -- `tower (m+1) = exp (tower m) > 0`.
      show 0 < Real.exp (tower m)
      exact Real.exp_pos _

/-- Auxiliary lemma: every value in the tower satisfies `T_m ≥ 1`. -/
lemma one_le_tower (m : ℕ) : 1 ≤ tower m := by
  induction m with
  | zero =>
      show (1 : ℝ) ≤ Real.exp 1
      have : Real.exp 0 ≤ Real.exp 1 :=
        Real.exp_le_exp.mpr (by norm_num)
      simpa [Real.exp_zero] using this
  | succ m ih =>
      show (1 : ℝ) ≤ Real.exp (tower m)
      have : Real.exp 0 ≤ Real.exp (tower m) :=
        Real.exp_le_exp.mpr (le_trans (by norm_num : (0 : ℝ) ≤ 1) ih)
      simpa [Real.exp_zero] using this

/-- The tower is strictly monotonic: `T_m < T_{m+1}`. -/
lemma tower_lt_succ (m : ℕ) : tower m < tower (m + 1) := by
  show tower m < Real.exp (tower m)
  have h1 : tower m + 1 ≤ Real.exp (tower m) := Real.add_one_le_exp _
  linarith

/-- The tower satisfies `T_m ≥ m + 1`. -/
lemma tower_ge (m : ℕ) : (m : ℝ) + 1 ≤ tower m := by
  induction m with
  | zero =>
      -- tower 0 = exp 1, and exp 1 ≥ 1 = 0 + 1
      have h1 : Real.exp 0 ≤ Real.exp 1 := Real.exp_le_exp.mpr (by norm_num)
      have h2 : (1 : ℝ) ≤ Real.exp 1 := by simpa [Real.exp_zero] using h1
      simp only [Nat.cast_zero, zero_add]
      exact h2
  | succ k ih =>
      -- tower (k+1) = exp (tower k) ≥ tower k + 1 ≥ (k+1) + 1 = k + 2
      have h1 : tower k + 1 ≤ Real.exp (tower k) := Real.add_one_le_exp _
      have h2 : tower (k+1) = Real.exp (tower k) := rfl
      push_cast
      linarith

/-- The tower grows without bound. -/
lemma tower_tendsto_atTop :
    Filter.Tendsto tower Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop]
  intro b
  refine Filter.eventually_atTop.mpr ⟨⌈b⌉₊, fun m hm => ?_⟩
  have h1 : (m : ℝ) + 1 ≤ tower m := tower_ge m
  have h2 : b ≤ ⌈b⌉₊ := Nat.le_ceil _
  have h3 : ((⌈b⌉₊ : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  linarith

/-- `log U_m = 3 T_{m-1}` for `m ≥ 1`. -/
lemma log_Um_succ (m : ℕ) :
    Real.log (Um (m + 1)) = 3 * tower m := by
  -- `log (T_{m+1}^3) = 3 log T_{m+1} = 3 T_m`.
  show Real.log ((tower (m+1)) ^ 3) = 3 * tower m
  rw [Real.log_pow, log_tower_succ]
  ring

/-- A concrete lower bound used in the `U`-tower estimates. -/
lemma tower_two_gt_nine : (9 : ℝ) < tower 2 := by
  change 9 < Real.exp (tower 1)
  have hthree : (3 : ℝ) < tower 1 := by
    change 3 < Real.exp (Real.exp 1)
    have h₁ : (3 : ℝ) < Real.exp 2 := by
      have hne : (2 : ℝ) ≠ 0 := by norm_num
      linarith [add_one_lt_exp hne]
    have h₂ : (2 : ℝ) < Real.exp 1 := exp_one_gt_two
    exact h₁.trans (Real.exp_lt_exp.mpr h₂)
  have hnine : (9 : ℝ) < Real.exp 3 := by
    have h₁ : (9 / 4 : ℝ) < Real.exp 1 := by
      linarith [exp_one_gt_d9]
    calc
      (9 : ℝ) < (9 / 4 : ℝ) ^ 3 := by norm_num
      _ < (Real.exp 1) ^ 3 := by gcongr
      _ = Real.exp 3 := by simp [Real.exp_one_pow]
  exact hnine.trans (Real.exp_lt_exp.mpr hthree)

/-- The square of the third logarithm is eventually dominated by `2 * T_n`. -/
lemma eventually_log_sq_le_two_mul_tower :
    ∀ᶠ n : ℕ in Filter.atTop, (Real.log (tower n + Real.log 3)) ^ 2 ≤ 2 * tower n := by
  have ht : Filter.Tendsto tower Filter.atTop Filter.atTop := tower_tendsto_atTop
  have h :
      (fun n : ℕ => (Real.log (tower n + Real.log 3)) ^ 2) =o[Filter.atTop]
        fun n => tower n + Real.log 3 := by
    simpa only [Function.comp_def, id_eq] using
      (Real.isLittleO_pow_log_id_atTop (n := 2)).comp_tendsto
        (ht.atTop_add (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => Real.log 3) _ _))
  have h' := h.bound (show (0 : ℝ) < 1 by norm_num)
  have h₁ : ∀ᶠ n : ℕ in Filter.atTop, tower n + Real.log 3 ≤ 2 * tower n := by
    filter_upwards [ht.eventually_ge_atTop (Real.log 3)] with n hn
    linarith
  filter_upwards [h', h₁] with n hn hn1
  have hlogsq : 0 ≤ (Real.log (tower n + Real.log 3)) ^ 2 := by positivity
  have hsum : 0 ≤ tower n + Real.log 3 := by
    have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    linarith [tower_pos n, hlog3]
  have hn' : (Real.log (tower n + Real.log 3)) ^ 2 ≤ tower n + Real.log 3 := by
    simpa [one_mul, Real.norm_of_nonneg hlogsq, Real.norm_of_nonneg hsum] using hn
  linarith

/-- The function `G(t) := (log t)^2`, used in the upper bound for `H`. -/
noncomputable def G (t : ℝ) : ℝ := (Real.log t) ^ 2

/-- Lemma 3.3 of the paper: `G(U_m) ≤ U_{m-1}` for `m ≥ 5`.

Proof: `G(U_m) = (3 T_{m-1})^2 = 9 T_{m-1}^2`.  We need
`9 T_{m-1}^2 ≤ T_{m-1}^3 = U_{m-1}`, i.e. `T_{m-1} ≥ 9`, which holds
already for `m ≥ 2`. -/
lemma U_tower_H (m : ℕ) (hm : 5 ≤ m) :
    G (Um m) ≤ Um (m - 1) := by
  unfold G
  rw [show m = (m - 1) + 1 by omega, log_Um_succ]
  unfold Um
  have hmono : StrictMono tower := strictMono_nat_of_lt_succ tower_lt_succ
  have hbig : (9 : ℝ) ≤ tower (m - 1) := by
    have hlt : tower 2 < tower (m - 1) := hmono (by omega)
    linarith [tower_two_gt_nine, hlt]
  calc
    (3 * tower (m - 1)) ^ 2 = 9 * tower (m - 1) ^ 2 := by ring
    _ ≤ tower (m - 1) * tower (m - 1) ^ 2 := by
      gcongr
    _ = tower (m - 1) ^ 3 := by ring

/-- The function `f(t) := C_f (log log t)(log log log t)^2` of equation
(4.5). -/
noncomputable def fH (Cf t : ℝ) : ℝ :=
  Cf * Real.log (Real.log t) * (Real.log (Real.log (Real.log t))) ^ 2

/-- The nested logs appearing in `fH (Um (n+2))` collapse to a tower expression. -/
lemma fH_Um_succ_succ (Cf : ℝ) (n : ℕ) :
    fH Cf (Um (n + 2)) =
      Cf * (tower n + Real.log 3) * (Real.log (tower n + Real.log 3)) ^ 2 := by
  unfold fH
  have hthree : (3 : ℝ) ≠ 0 := by norm_num
  have htower : tower (n + 1) ≠ 0 := (tower_pos (n + 1)).ne'
  rw [show n + 2 = (n + 1) + 1 by omega, log_Um_succ]
  rw [Real.log_mul hthree htower, log_tower_succ]
  simp [add_comm, mul_assoc]

/-- Lemma 4.4 (`U`-tower lemma for `h`).

For every absolute constant `C_f > 0`, there is some `m₀* = m₀*(C_f) ≥ 6`
such that for all `m ≥ m₀*`, `f(U_m) ≤ U_{m-2}`.

Sketch: `log U_m = 3 T_{m-1}`, `log log U_m = T_{m-2} + log 3`,
`log log log U_m = T_{m-3} + O(T_{m-3}^{-1})`; hence
`f(U_m) ≤ 2 C_f T_{m-2} T_{m-3}^2`, while
`U_{m-2} = T_{m-2}^3`.  The ratio `f(U_m) / U_{m-2}` is
`≤ 2 C_f (log T_{m-2})^2 / T_{m-2}^2 → 0`.  Choose `m₀*` so the ratio
is `≤ 1`.

Multi-step real-analysis estimate. -/
lemma U_tower_h (Cf : ℝ) (hCf : 0 < Cf) :
    ∃ m₀ : ℕ, 6 ≤ m₀ ∧
      ∀ m : ℕ, m₀ ≤ m → fH Cf (Um m) ≤ Um (m - 2) := by
  have ht : Filter.Tendsto tower Filter.atTop Filter.atTop := tower_tendsto_atTop
  have hA := eventually_log_sq_le_two_mul_tower
  have hB : ∀ᶠ n : ℕ in Filter.atTop, 4 * Cf ≤ tower n :=
    ht.eventually_ge_atTop (4 * Cf)
  have hC : ∀ᶠ n : ℕ in Filter.atTop, Real.log 3 ≤ tower n :=
    ht.eventually_ge_atTop (Real.log 3)
  have hmain :
      ∀ᶠ n : ℕ in Filter.atTop,
        Cf * (tower n + Real.log 3) * (Real.log (tower n + Real.log 3)) ^ 2 ≤ tower n ^ 3 := by
    filter_upwards [hA, hB, hC] with n hnA hnB hnC
    have hsum : tower n + Real.log 3 ≤ 2 * tower n := by
      linarith
    calc
      Cf * (tower n + Real.log 3) * (Real.log (tower n + Real.log 3)) ^ 2
          ≤ Cf * (2 * tower n) * (Real.log (tower n + Real.log 3)) ^ 2 := by
            gcongr
      _ ≤ Cf * (2 * tower n) * (2 * tower n) := by
            have hnonneg : 0 ≤ Cf * (2 * tower n) := by
              nlinarith [hCf, tower_pos n]
            gcongr
      _ = 4 * Cf * tower n ^ 2 := by ring
      _ ≤ tower n ^ 3 := by
            have hsq : 0 ≤ tower n ^ 2 := by positivity
            nlinarith
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hmain
  refine ⟨max 6 (N + 2), le_max_left _ _, ?_⟩
  intro m hm
  have hmN : N ≤ m - 2 := by
    have hm' : N + 2 ≤ m := le_trans (le_max_right _ _) hm
    omega
  have hNm := hN (m - 2) hmN
  rw [show m = (m - 2) + 2 by omega, fH_Um_succ_succ]
  simpa [Um] using hNm

end Erdos696
