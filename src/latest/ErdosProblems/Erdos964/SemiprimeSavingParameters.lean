import ErdosProblems.Erdos964.SemiprimeSavingBounds

/-!
# Choosing the conductor and saving parameters

Logarithmic powers are dominated by every fixed positive power of the
scale. This provides one threshold, independent of the dyadic block, for
all the inequalities used by the scalar saving bound.
-/

namespace Erdos964

open BoundedGaps.Maynard

theorem exists_log_pow_le_mul_rpow_nat (k : ℕ) (r c : ℝ) (hr : 0 < r) (hc : 0 < c) :
    ∃ N : ℕ, 4 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      (Real.log (n : ℝ)) ^ k ≤ c * Real.rpow (n : ℝ) r := by
  have hdom := ((isLittleO_log_rpow_rpow_atTop (k : ℝ) hr).comp_tendsto
    tendsto_natCast_atTop_atTop).def hc
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hdom
  refine ⟨max 4 N, le_max_left _ _, ?_⟩
  intro n hn
  have hbound := hN n ((le_max_right 4 N).trans hn)
  simp only [Function.comp_apply, Real.norm_eq_abs] at hbound
  rw [abs_of_nonneg (Real.rpow_nonneg (Real.log_natCast_nonneg n) _),
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)] at hbound
  have hbound' : (Real.log (n : ℝ)) ^ k ≤ c * (n : ℝ) ^ r := by
    simpa only [Real.rpow_natCast] using hbound
  exact hbound'

theorem two_le_log_natCast_of_sixteen_le {L : ℕ} (hL : 16 ≤ L) :
    2 ≤ Real.log (L : ℝ) := by
  have hlogFour : 1 ≤ Real.log (4 : ℝ) := one_le_log_natCast (by norm_num : 4 ≤ 4)
  have hlogSixteen : 2 ≤ Real.log (16 : ℝ) := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.log_pow]
    norm_num
    linarith
  exact hlogSixteen.trans (Real.log_le_log (by norm_num) (by exact_mod_cast hL))

/-- The threshold is uniform in the smaller-prime block. The modulus
cutoff has exponent `θ < 1` relative to `L`, hence exponent below `1/2`
relative to the product cap `L²`. -/
theorem exists_semiprime_saving_parameters (b : ℕ) (η θ : ℝ)
    (hη : 0 < η) (hθ : 0 < θ) (hθ1 : θ < 1) :
    ∃ L₀ : ℕ, 16 ≤ L₀ ∧ ∀ L : ℕ, L₀ ≤ L →
      let s := (Real.log (L : ℝ)) ^ b
      let D := ⌊(Real.log (L : ℝ)) ^ (b + 1)⌋₊
      let T := modulusCutoff θ L
      1 ≤ s ∧ 0 < D ∧ D ≤ T ∧ T < L ∧
      (T : ℝ) * s ≤ L ∧ s ≤ D ∧
      (D : ℝ) ≤ (Real.log (L : ℝ)) ^ (b + 1) ∧
      s ≤ (Real.log (L : ℝ)) ^ (b + 1) ∧
      ∀ M : ℕ, Real.rpow (L : ℝ) η / 2 ≤ M → s ^ 2 ≤ M := by
  obtain ⟨N₁, _, hg₁⟩ := exists_log_pow_le_mul_rpow_nat (2 * b) η (1 / 2) hη (by norm_num)
  obtain ⟨N₂, _, hg₂⟩ := exists_log_pow_le_mul_rpow_nat (b + 1) θ 1 hθ (by norm_num)
  obtain ⟨N₃, _, hg₃⟩ := exists_log_pow_le_mul_rpow_nat b (1 - θ) 1 (by linarith) (by norm_num)
  refine ⟨max 16 (max N₁ (max N₂ N₃)), le_max_left _ _, ?_⟩
  intro L hL
  have hL16 : 16 ≤ L := (le_max_left _ _).trans hL
  have hN₁ : N₁ ≤ L := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hL
  have hN₂ : N₂ ≤ L := by omega
  have hN₃ : N₃ ≤ L := by omega
  have hlogTwo := two_le_log_natCast_of_sixteen_le hL16
  have hlogOne : 1 ≤ Real.log (L : ℝ) := by linarith
  have hlogpos : 0 < Real.log (L : ℝ) := by linarith
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hLone : (1 : ℝ) < L := by exact_mod_cast (show 1 < L by omega)
  let s := (Real.log (L : ℝ)) ^ b
  let D := ⌊(Real.log (L : ℝ)) ^ (b + 1)⌋₊
  let T := modulusCutoff θ L
  have hs : 1 ≤ s := one_le_pow₀ hlogOne
  have hs0 : 0 ≤ s := by linarith
  have hpow : (Real.log (L : ℝ)) ^ (b + 1) = s * Real.log (L : ℝ) := pow_succ _ _
  have hsD : s ≤ D := by
    have hfloor := Nat.lt_floor_add_one ((Real.log (L : ℝ)) ^ (b + 1))
    change (Real.log (L : ℝ)) ^ (b + 1) < (D : ℝ) + 1 at hfloor
    rw [hpow] at hfloor
    nlinarith
  have hD : 0 < D := by
    have hDreal : (1 : ℝ) ≤ D := hs.trans hsD
    exact_mod_cast hDreal
  have hDupper : (D : ℝ) ≤ (Real.log (L : ℝ)) ^ (b + 1) :=
    Nat.floor_le (pow_nonneg hlogpos.le _)
  have hDT : D ≤ T := by
    apply Nat.floor_mono
    simpa only [one_mul] using hg₂ L hN₂
  have hTupper : (T : ℝ) ≤ Real.rpow (L : ℝ) θ :=
    Nat.floor_le (Real.rpow_nonneg hLpos.le _)
  have hTL : T < L := by
    have hlt : (T : ℝ) < L := by
      calc
        _ ≤ Real.rpow (L : ℝ) θ := hTupper
        _ < Real.rpow (L : ℝ) 1 := Real.rpow_lt_rpow_of_exponent_lt hLone hθ1
        _ = L := Real.rpow_one _
    exact_mod_cast hlt
  have hsupper : s ≤ Real.rpow (L : ℝ) (1 - θ) := by
    simpa only [one_mul] using hg₃ L hN₃
  have hTs : (T : ℝ) * s ≤ L := by
    calc
      _ ≤ Real.rpow (L : ℝ) θ * Real.rpow (L : ℝ) (1 - θ) :=
        mul_le_mul hTupper hsupper hs0 (Real.rpow_nonneg hLpos.le _)
      _ = Real.rpow (L : ℝ) (θ + (1 - θ)) := (Real.rpow_add hLpos θ (1 - θ)).symm
      _ = L := by rw [show θ + (1 - θ) = 1 by ring]; exact Real.rpow_one _
  refine ⟨hs, hD, hDT, hTL, hTs, hsD, hDupper, hsD.trans hDupper, ?_⟩
  intro M hM
  have h := hg₁ L hN₁
  have hsquare : s ^ 2 = (Real.log (L : ℝ)) ^ (2 * b) := by
    dsimp only [s]
    rw [← pow_mul, Nat.mul_comm b 2]
  rw [hsquare]
  linarith

theorem le_double_mul_div (N M : ℕ) (hM : 0 < M) (hMN : M ≤ N) :
    N ≤ (M + M) * (N / M) := by
  have hq : 1 ≤ N / M := (Nat.le_div_iff_mul_le hM).mpr (by simpa using hMN)
  have hMq := Nat.mul_le_mul_left M hq
  have hrem := Nat.mod_lt N hM
  have hdiv := Nat.mod_add_div N M
  nlinarith

end Erdos964
