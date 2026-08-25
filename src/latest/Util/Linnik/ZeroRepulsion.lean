import Util.Linnik.ReciprocalRoots

/-!
# Quantitative repulsion from an exceptional real zero

Combine four-character positivity, fixed-disk logarithmic growth, and the
positive real power-sum estimate.  The result is stated exponentially so
that its dependence on the exceptional gap can be used directly in zero
density estimates.
-/

namespace Linnik

open Complex
open scoped BigOperators Classical

theorem exists_power_index_bound (Z : ℂ →₀ ℕ) {w : ℂ}
    (hw : w ∈ Z.support) {M epsilon : ℝ} (hM : 1 ≤ M) (hepsilon : 0 ≤ epsilon)
    (hnorm : ∀ z ∈ Z.support, ‖z‖ ≤ 1) (hw₀ : (1 : ℝ) / 4 ≤ ‖w‖)
    (hmass : Z.sum (fun _ m ↦ (m : ℝ)) ≤ 8 * M)
    (hpower : ∀ k : ℕ, 1 ≤ k →
      (Z.sum (fun z m ↦ (m : ℂ) * z ^ k)).re ≤
        4 * k * epsilon + (64 * M + 2) * (1 / 9 : ℝ) ^ k) :
    ∃ N : ℕ, 1 ≤ N ∧ (N : ℝ) ≤ 4096 * M ∧ ‖w‖ ^ N < 32 * N * epsilon := by
  obtain ⟨z₀, hz₀, hmax⟩ := Finset.exists_max_image Z.support (fun z : ℂ ↦ ‖z‖) ⟨w, hw⟩
  let N : ℕ := ⌈32 * (72 * M + 3)⌉₊
  have hNlower : 32 * (72 * M + 3) ≤ (N : ℝ) := Nat.le_ceil _
  have hNupper : (N : ℝ) < 32 * (72 * M + 3) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hN₁ : 1 ≤ N := by
    have hpos : (0 : ℝ) < N := by linarith
    exact Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast hpos.ne')
  have hNbound : (N : ℝ) ≤ 4096 * M := by linarith
  have hr : (1 : ℝ) / 4 ≤ ‖z₀‖ := hw₀.trans (hmax w hw)
  have hlarge := largestRoot_pow_lt_of_weighted_powerSum_bound Z (N := N) hz₀ hr (hnorm z₀ hz₀)
    hmax rfl (show 0 ≤ 64 * M + 2 by linarith) (by norm_num : (0 : ℝ) ≤ 4)
    hepsilon (by linarith) (fun k hk ↦ hpower k (Finset.mem_Icc.mp hk).1)
  refine ⟨N, hN₁, hNbound, ?_⟩
  have hwmax := pow_le_pow_left₀ (norm_nonneg w) (hmax w hw) N
  have h := hwmax.trans_lt hlarge
  simpa only [show (8 : ℝ) * 4 = 32 by norm_num, mul_assoc] using h

theorem exp_le_target_root_pow {rho : ℂ} (hrho : rho.re < 1) (N : ℕ) :
    Real.exp (-2 * (1 - rho.re) * N) ≤
      ‖(((2 : ℂ) + rho.im * I - rho) ^ 2)⁻¹‖ ^ N := by
  have hd : 0 < 2 - rho.re := by linarith
  have hr : 0 < ((2 - rho.re) ^ 2)⁻¹ := by positivity
  rw [target_root_norm hrho]
  have hexp : Real.exp ((N : ℝ) * Real.log (((2 - rho.re) ^ 2)⁻¹)) =
      (((2 - rho.re) ^ 2)⁻¹) ^ N := by rw [Real.exp_nat_mul, Real.exp_log hr]
  rw [← hexp, Real.exp_le_exp, Real.log_inv, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  have hlog := Real.log_le_sub_one_of_pos hd
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith

/-- An exponential form of the Deuring--Heilbronn phenomenon, uniform in
the modulus, the character, and the height of the other zero. -/
theorem exists_exceptional_zero_repulsion :
    ∃ A : ℕ, 37 ≤ A ∧
      ∀ (q : ℕ) [NeZero q], 1 < q →
        ∀ (chi1 chi : DirichletCharacter ℂ q), chi1 ≠ 1 → chi1 ^ 2 = 1 →
          ∀ beta : ℝ, 0 < beta → beta < 1 →
            DirichletCharacter.LFunction chi1 (beta : ℂ) = 0 →
            ∀ rho : ℂ, 0 < rho.re → rho.re < 1 →
              DirichletCharacter.LFunction chi rho = 0 →
              (chi ≠ chi1 ∨ rho ≠ (beta : ℂ)) →
              Real.exp (-8192 * ((A : ℝ) * Real.log ((q : ℝ) * (|rho.im| + 2))) *
                (1 - rho.re)) <
                131072 * ((A : ℝ) * Real.log ((q : ℝ) * (|rho.im| + 2))) * (1 - beta) := by
  obtain ⟨A₁, hA₁, hmass⟩ := exists_fourRemainingRoots_mass_bound
  obtain ⟨A₂, hA₂, hpower⟩ := exists_fourRemainingRoots_powerSum_bound
  let A := max A₁ A₂
  refine ⟨A, hA₁.trans (le_max_left _ _), ?_⟩
  intro q _ hq chi1 chi hchi1 hsquare beta hbeta₀ hbeta₁ hzero rho hrho₀ hrho₁ hrhoZero hne
  let B : ℝ := (q : ℝ) * (|rho.im| + 2)
  let M : ℝ := (A : ℝ) * Real.log B
  let Z := fourRemainingRoots chi1 chi beta rho.im
  let w : ℂ := (((2 : ℂ) + rho.im * I - rho) ^ 2)⁻¹
  have hq₂ : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hB₄ : 4 ≤ B := by dsimp [B]; nlinarith [abs_nonneg rho.im]
  have hlog : Real.log 2 ≤ Real.log B := Real.log_le_log (by norm_num) (by linarith)
  have hlog₀ : 0 ≤ Real.log B := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le.trans hlog
  have hA : (37 : ℝ) ≤ A := by exact_mod_cast hA₁.trans (le_max_left A₁ A₂)
  have hM : 1 ≤ M := by dsimp [M]; nlinarith [Real.log_two_gt_d9]
  have hA₁le : (A₁ : ℝ) ≤ A := by exact_mod_cast le_max_left A₁ A₂
  have hA₂le : (A₂ : ℝ) ≤ A := by exact_mod_cast le_max_right A₁ A₂
  have hmass' : Z.sum (fun _ m ↦ (m : ℝ)) ≤ 8 * M := by
    apply (hmass q hq chi1 chi beta rho.im).trans
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hA₁le hlog₀) (by norm_num)
  have hpower' (k : ℕ) (hk : 1 ≤ k) :
      (Z.sum (fun z m ↦ (m : ℂ) * z ^ k)).re ≤
        4 * k * (1 - beta) + (64 * M + 2) * (1 / 9 : ℝ) ^ k := by
    apply (hpower q hq chi1 chi hchi1 hsquare beta hbeta₀ hbeta₁ hzero rho.im k hk).trans
    gcongr
    exact mul_le_mul_of_nonneg_right hA₂le hlog₀
  have hw := target_mem_fourRemainingRoots chi1 chi beta hrho₀ hrho₁ hrhoZero hne
  obtain ⟨N, hN₁, hNbound, hNpower⟩ := exists_power_index_bound Z hw hM
    (sub_nonneg.mpr hbeta₁.le) (fun z hz ↦ fourRemainingRoots_norm_le_one chi1 chi beta rho.im hz)
    (target_root_norm_ge_quarter hrho₀ hrho₁) hmass' hpower'
  have hdelta : 0 ≤ 1 - rho.re := sub_nonneg.mpr hrho₁.le
  have heps : 0 ≤ 1 - beta := sub_nonneg.mpr hbeta₁.le
  calc
    Real.exp (-8192 * M * (1 - rho.re)) ≤ Real.exp (-2 * (1 - rho.re) * N) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    _ ≤ ‖w‖ ^ N := exp_le_target_root_pow hrho₁ N
    _ < 32 * N * (1 - beta) := hNpower
    _ ≤ 131072 * M * (1 - beta) := by nlinarith

end Linnik
