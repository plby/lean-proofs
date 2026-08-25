import ErdosProblems.Erdos381.ShortPrimes
import ErdosProblems.Erdos381.GallagherZeta
import BoundedGaps.PrimeNumberTheorem.Analytic.StrongChebyshev
import ErdosProblems.Erdos48.EndpointPowerScale

namespace Erdos381

open Complex Set Filter Asymptotics
open scoped BigOperators ComplexConjugate Topology
open BoundedGaps.Maynard

noncomputable section

theorem consecutive_pow_gap_lower {n L : ℕ} (hL : 1 ≤ L) :
    n ^ (L - 1) ≤ (n + 1) ^ L - n ^ L := by
  let k := L - 1
  have hLk : L = k + 1 := (Nat.sub_add_cancel hL).symm
  rw [hLk, Nat.add_sub_cancel]
  apply Nat.le_sub_of_add_le
  rw [pow_succ, pow_succ]
  calc
    n ^ k + n ^ k * n = n ^ k * (n + 1) := by ring
    _ ≤ (n + 1) ^ k * (n + 1) := by
      exact Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) k) (by omega)

theorem consecutive_pow_upper {n L : ℕ} (hn : 1 ≤ n) :
    (n + 1) ^ L ≤ 2 ^ L * n ^ L := by
  calc
    (n + 1) ^ L ≤ (2 * n) ^ L := by gcongr; omega
    _ = 2 ^ L * n ^ L := by rw [mul_pow]

theorem log_two_mul_natSq_add_two_le_four_log {n : ℕ} (hn : 2 ≤ n) :
    Real.log (2 * ((n ^ 2 : ℕ) + 2 : ℕ) : ℕ) ≤
      4 * Real.log (n : ℝ) := by
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  have hnat : 2 * (n ^ 2 + 2) ≤ n ^ 4 := by
    nlinarith [sq_nonneg (n ^ 2 - 4),
      Nat.pow_le_pow_left hn 2]
  have hpos : (0 : ℝ) < 2 * ((n ^ 2 : ℕ) + 2 : ℕ) := by positivity
  calc
    Real.log (2 * (((n ^ 2 : ℕ) + 2 : ℕ) : ℝ)) ≤
        Real.log ((n : ℝ) ^ 4) := by
      apply Real.log_le_log hpos
      exact_mod_cast hnat
    _ = 4 * Real.log (n : ℝ) := by rw [Real.log_pow]; norm_num

theorem log_natSq_add_two_le_three_log {n : ℕ} (hn : 2 ≤ n) :
    Real.log (((n ^ 2 : ℕ) + 2 : ℕ) : ℝ) ≤
      3 * Real.log (n : ℝ) := by
  have hnat : n ^ 2 + 2 ≤ n ^ 3 := by
    nlinarith [sq_nonneg (n - 2)]
  have hpos : (0 : ℝ) < ((n ^ 2 : ℕ) + 2 : ℕ) := by positivity
  calc
    Real.log (((n ^ 2 : ℕ) + 2 : ℕ) : ℝ) ≤
        Real.log ((n : ℝ) ^ 3) := by
      apply Real.log_le_log hpos
      exact_mod_cast hnat
    _ = 3 * Real.log (n : ℝ) := by rw [Real.log_pow]; norm_num

theorem natPow_rpow_neg_le_inv_four
    {n L : ℕ} {delta : ℝ} (hn : 1 ≤ n) (hdelta : 0 ≤ delta)
    (hLdelta : 4 ≤ (L : ℝ) * delta) :
    (((n ^ L : ℕ) : ℝ) ^ (-delta)) ≤ 1 / (n : ℝ) ^ 4 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := zero_lt_one.trans_le hnR
  calc
    (((n ^ L : ℕ) : ℝ) ^ (-delta)) =
        ((n : ℝ) ^ (L : ℝ)) ^ (-delta) := by
      rw [Nat.cast_pow, Real.rpow_natCast]
    _ = (n : ℝ) ^ ((L : ℝ) * (-delta)) := by
      exact (Real.rpow_mul (by positivity : (0 : ℝ) ≤ n) _ _).symm
    _ ≤ (n : ℝ) ^ (-4 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le hnR
      linarith
    _ = 1 / (n : ℝ) ^ 4 := by
      rw [← Real.rpow_natCast]
      rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ n)]
      rw [one_div]
      congr 1

theorem sqrt_cast_even_pow (n k : ℕ) :
    Real.sqrt (((n ^ (2 * k) : ℕ) : ℝ)) = ((n ^ k : ℕ) : ℝ) := by
  rw [Nat.cast_pow, show (n : ℝ) ^ (2 * k) = ((n : ℝ) ^ k) ^ 2 by
    rw [← pow_mul]; congr 1; omega, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (by positivity), Nat.cast_pow]

theorem explicitFormula_powerEndpoints_le_gap_mul
    {n L K : ℕ} (hn : 2 ≤ n) (hL : 1 ≤ L) :
    (K : ℝ) * dirichletExplicitFormulaErrorScale
        ((n ^ L : ℕ) : ℝ) 1 ((n ^ 2 : ℕ) : ℝ) +
      (K : ℝ) * dirichletExplicitFormulaErrorScale
        (((n + 1) ^ L : ℕ) : ℝ) 1 ((n ^ 2 : ℕ) : ℝ) ≤
      (((n + 1) ^ L - n ^ L : ℕ) : ℝ) *
        ((K : ℝ) * (L : ℝ) ^ 2 * (1 + 4 * (2 : ℝ) ^ L) *
          (Real.log (n : ℝ) ^ 2 / (n : ℝ))) := by
  let g : ℝ := (n : ℝ) ^ (L - 1)
  let D : ℝ := (K : ℝ) * (L : ℝ) ^ 2
  have hnpos : (0 : ℝ) < n := by positivity
  have hlogn : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hgap : g ≤ (((n + 1) ^ L - n ^ L : ℕ) : ℝ) := by
    dsimp [g]
    exact_mod_cast consecutive_pow_gap_lower hL
  have hpowEq : (n : ℝ) ^ (L - 1) * (n : ℝ) = (n : ℝ) ^ L := by
    simpa using (pow_sub_mul_pow (m := 1) (n := L) (n : ℝ) hL)
  have hxEq :
      (K : ℝ) * dirichletExplicitFormulaErrorScale
          ((n ^ L : ℕ) : ℝ) 1 ((n ^ 2 : ℕ) : ℝ) =
        g * (D * (Real.log (n : ℝ) ^ 2 / (n : ℝ))) := by
    dsimp [g, D]
    unfold dirichletExplicitFormulaErrorScale
    simp only [Nat.cast_one, mul_one, Nat.cast_pow]
    rw [Real.log_pow]
    norm_num only [Nat.cast_pow]
    rw [← hpowEq]
    field_simp
  have hyPow : (((n + 1) ^ L : ℕ) : ℝ) ≤
      (2 : ℝ) ^ L * (n : ℝ) ^ L := by
    exact_mod_cast consecutive_pow_upper (show 1 ≤ n by omega) (L := L)
  have hlogy : Real.log (((n + 1) ^ L : ℕ) : ℝ) ≤
      2 * (L : ℝ) * Real.log (n : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
    have hbase : (n + 1 : ℝ) ≤ (n : ℝ) ^ 2 := by
      exact_mod_cast (show n + 1 ≤ n ^ 2 by nlinarith)
    have hlogbase : Real.log (n + 1 : ℝ) ≤
        2 * Real.log (n : ℝ) := by
      calc
        Real.log (n + 1 : ℝ) ≤ Real.log ((n : ℝ) ^ 2) :=
          Real.log_le_log (by positivity) hbase
        _ = 2 * Real.log (n : ℝ) := by rw [Real.log_pow]; norm_num
    calc
      (L : ℝ) * Real.log ((n + 1 : ℕ) : ℝ) =
          (L : ℝ) * Real.log ((n : ℝ) + 1) := by norm_num
      _ ≤
          (L : ℝ) * (2 * Real.log (n : ℝ)) := by gcongr
      _ = 2 * (L : ℝ) * Real.log (n : ℝ) := by ring
  have hlogy0 : 0 ≤ Real.log (((n + 1) ^ L : ℕ) : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast Nat.one_le_pow L (n + 1) (by omega)
  have hlogySq : Real.log (((n + 1) ^ L : ℕ) : ℝ) ^ 2 ≤
      4 * (L : ℝ) ^ 2 * Real.log (n : ℝ) ^ 2 := by
    nlinarith [sq_nonneg
      (2 * (L : ℝ) * Real.log (n : ℝ) -
        Real.log (((n + 1) ^ L : ℕ) : ℝ))]
  have hyPowStep : (((n + 1 : ℕ) : ℝ) ^ L) ≤
      (2 : ℝ) ^ L * ((n : ℝ) ^ (L - 1) * (n : ℝ)) := by
    rw [hpowEq]
    simpa only [Nat.cast_pow] using hyPow
  have hlogySq' : Real.log ((((n + 1 : ℕ) : ℝ) ^ L)) ^ 2 ≤
      4 * (L : ℝ) ^ 2 * Real.log (n : ℝ) ^ 2 := by
    simpa only [Nat.cast_pow] using hlogySq
  have hyBound :
      (K : ℝ) * dirichletExplicitFormulaErrorScale
          (((n + 1) ^ L : ℕ) : ℝ) 1 ((n ^ 2 : ℕ) : ℝ) ≤
        g * ((4 * (2 : ℝ) ^ L) * D *
          (Real.log (n : ℝ) ^ 2 / (n : ℝ))) := by
    unfold dirichletExplicitFormulaErrorScale
    simp only [Nat.cast_one, mul_one, Nat.cast_pow]
    dsimp [g, D]
    calc
      (K : ℝ) *
          ((((n + 1 : ℕ) : ℝ) ^ L) *
            Real.log (((n + 1 : ℕ) : ℝ) ^ L) ^ 2 /
              (n : ℝ) ^ 2) ≤
        (K : ℝ) *
          (((2 : ℝ) ^ L * ((n : ℝ) ^ (L - 1) * (n : ℝ))) *
            (4 * (L : ℝ) ^ 2 * Real.log (n : ℝ) ^ 2) /
              (n : ℝ) ^ 2) := by gcongr
      _ = ((n : ℝ) ^ (L - 1)) *
          ((4 * (2 : ℝ) ^ L) * ((K : ℝ) * (L : ℝ) ^ 2) *
            (Real.log (n : ℝ) ^ 2 / (n : ℝ))) := by
        field_simp
  rw [hxEq]
  calc
    g * (D * (Real.log (n : ℝ) ^ 2 / (n : ℝ))) +
        (K : ℝ) * dirichletExplicitFormulaErrorScale
          (((n + 1) ^ L : ℕ) : ℝ) 1 ((n ^ 2 : ℕ) : ℝ) ≤
      g * (D * (Real.log (n : ℝ) ^ 2 / (n : ℝ))) +
        g * ((4 * (2 : ℝ) ^ L) * D *
          (Real.log (n : ℝ) ^ 2 / (n : ℝ))) := by gcongr
    _ = g * (D * (1 + 4 * (2 : ℝ) ^ L) *
          (Real.log (n : ℝ) ^ 2 / (n : ℝ))) := by ring
    _ ≤ (((n + 1) ^ L - n ^ L : ℕ) : ℝ) *
        (D * (1 + 4 * (2 : ℝ) ^ L) *
          (Real.log (n : ℝ) ^ 2 / (n : ℝ))) := by gcongr
    _ = _ := by dsimp [D]

theorem exists_hoheisel_even_exponent
    {lambda delta C c : ℝ}
    (hlambda : 0 < lambda) (hdelta : 0 < delta) (hC : 0 < C) :
    ∃ k : ℕ,
      8 ≤ 2 * k ∧
      16 * c ≤ (2 * k : ℕ) ∧
      8 * Real.log 2 / lambda ≤ (2 * k : ℕ) ∧
      4 / delta ≤ (2 * k : ℕ) ∧
      2 * C * Real.exp
        (c * lambda - lambda * ((2 * k : ℕ) : ℝ) / 16) < 1 / 8 := by
  let a : ℝ := Real.exp (-lambda / 16)
  have ha0 : 0 ≤ a := (Real.exp_pos _).le
  have ha1 : a < 1 := by
    dsimp [a]
    rw [Real.exp_lt_one_iff]
    linarith
  have hlim : Tendsto (fun L : ℕ ↦
      2 * C * Real.exp (c * lambda - lambda * (L : ℝ) / 16))
      atTop (nhds 0) := by
    have hpow := (tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1).const_mul
      (2 * C * Real.exp (c * lambda))
    have heq : (fun L : ℕ ↦
        2 * C * Real.exp (c * lambda) * a ^ L) =ᶠ[atTop]
        (fun L : ℕ ↦
          2 * C * Real.exp (c * lambda - lambda * (L : ℝ) / 16)) := by
      filter_upwards [] with L
      dsimp [a]
      rw [show c * lambda - lambda * (L : ℝ) / 16 =
          c * lambda + (L : ℝ) * (-lambda / 16) by ring,
        Real.exp_add, Real.exp_nat_mul]
      ring
    simpa using hpow.congr' heq
  have hsmall : ∀ᶠ L : ℕ in atTop,
      2 * C * Real.exp
        (c * lambda - lambda * (L : ℝ) / 16) < 1 / 8 :=
    hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8))
  have hc : ∀ᶠ L : ℕ in atTop, 16 * c ≤ (L : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop _
  have hcontract : ∀ᶠ L : ℕ in atTop,
      8 * Real.log 2 / lambda ≤ (L : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop _
  have hfar : ∀ᶠ L : ℕ in atTop, 4 / delta ≤ (L : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop _
  have hall := (eventually_ge_atTop 8).and
    (hc.and (hcontract.and (hfar.and hsmall)))
  have htwo : Tendsto (fun k : ℕ ↦ 2 * k) atTop atTop := by
    apply Filter.tendsto_atTop_mono (f := fun k : ℕ ↦ k)
    · intro k
      omega
    · exact tendsto_id
  obtain ⟨k, hk8, hkc, hkcontract, hkfar, hksmall⟩ :=
    (htwo.eventually hall).exists
  exact ⟨k, hk8, hkc, hkcontract, hkfar, hksmall⟩

theorem primePower_powerEndpoint_le_gap_mul
    {n k : ℕ} (hn : 2 ≤ n) (hk : 2 ≤ k) :
    Chebyshev.psi ((((n + 1) ^ (2 * k) : ℕ) : ℝ)) -
        Chebyshev.theta ((((n + 1) ^ (2 * k) : ℕ) : ℝ)) ≤
      ((((n + 1) ^ (2 * k) - n ^ (2 * k) : ℕ) : ℝ)) *
        ((8 : ℝ) * (2 : ℝ) ^ k * (k : ℝ) *
          (Real.log (n : ℝ) / (n : ℝ))) := by
  let g : ℝ := (n : ℝ) ^ (2 * k - 1)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnpos : (0 : ℝ) < n := zero_lt_one.trans_le hnR
  have hlogn : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hgap : g ≤
      ((((n + 1) ^ (2 * k) - n ^ (2 * k) : ℕ) : ℝ)) := by
    dsimp [g]
    exact_mod_cast consecutive_pow_gap_lower (show 1 ≤ 2 * k by omega)
  have hsqrt :
      Real.sqrt ((((n + 1) ^ (2 * k) : ℕ) : ℝ)) =
        (((n + 1) ^ k : ℕ) : ℝ) := sqrt_cast_even_pow (n + 1) k
  have hlogy :
      Real.log ((((n + 1) ^ (2 * k) : ℕ) : ℝ)) ≤
        4 * (k : ℝ) * Real.log (n : ℝ) := by
    rw [Erdos48.log_natCast_pow]
    have hbase : (n + 1 : ℝ) ≤ (n : ℝ) ^ 2 := by
      exact_mod_cast (show n + 1 ≤ n ^ 2 by nlinarith)
    have hlogbase : Real.log (n + 1 : ℝ) ≤
        2 * Real.log (n : ℝ) := by
      calc
        Real.log (n + 1 : ℝ) ≤ Real.log ((n : ℝ) ^ 2) :=
          Real.log_le_log (by positivity) hbase
        _ = 2 * Real.log (n : ℝ) := by rw [Real.log_pow]; norm_num
    have hk0 : (0 : ℝ) ≤ k := by positivity
    calc
      ((2 * k : ℕ) : ℝ) * Real.log ((n + 1 : ℕ) : ℝ) =
          ((2 * k : ℕ) : ℝ) * Real.log ((n : ℝ) + 1) := by norm_num
      _ ≤
          ((2 * k : ℕ) : ℝ) * (2 * Real.log (n : ℝ)) := by gcongr
      _ = 4 * (k : ℝ) * Real.log (n : ℝ) := by push_cast; ring
  have hnk : (n : ℝ) ^ k ≤ (n : ℝ) ^ (2 * k - 2) := by
    apply pow_le_pow_right₀ hnR
    omega
  have hpow : (((n + 1) ^ k : ℕ) : ℝ) ≤
      (2 : ℝ) ^ k * (n : ℝ) ^ (2 * k - 2) := by
    calc
      (((n + 1) ^ k : ℕ) : ℝ) ≤
          (2 : ℝ) ^ k * (n : ℝ) ^ k := by
        exact_mod_cast consecutive_pow_upper (show 1 ≤ n by omega) (L := k)
      _ ≤ (2 : ℝ) ^ k * (n : ℝ) ^ (2 * k - 2) := by gcongr
  have hraw := Chebyshev.psi_sub_theta_le
    (x := (((n + 1) ^ (2 * k) : ℕ) : ℝ))
    (by exact_mod_cast Nat.one_le_pow (2 * k) (n + 1) (by omega))
  rw [hsqrt] at hraw
  have hlocal :
      Chebyshev.psi ((((n + 1) ^ (2 * k) : ℕ) : ℝ)) -
          Chebyshev.theta ((((n + 1) ^ (2 * k) : ℕ) : ℝ)) ≤
        (n : ℝ) ^ (2 * k - 1) *
          ((8 : ℝ) * (2 : ℝ) ^ k * (k : ℝ) *
            (Real.log (n : ℝ) / (n : ℝ))) := by
    calc
      _ ≤ 2 * (((n + 1) ^ k : ℕ) : ℝ) *
          Real.log ((((n + 1) ^ (2 * k) : ℕ) : ℝ)) := hraw
      _ ≤ 2 * ((2 : ℝ) ^ k * (n : ℝ) ^ (2 * k - 2)) *
          (4 * (k : ℝ) * Real.log (n : ℝ)) := by gcongr
      _ = (n : ℝ) ^ (2 * k - 1) *
          ((8 : ℝ) * (2 : ℝ) ^ k * (k : ℝ) *
            (Real.log (n : ℝ) / (n : ℝ))) := by
        rw [show 2 * k - 1 = (2 * k - 2) + 1 by omega, pow_succ]
        field_simp
        ring
  exact hlocal.trans (mul_le_mul_of_nonneg_right hgap (by positivity))

/-- The log-free zero-density estimate summed over the Hoheisel bands. -/
theorem sum_logFreeDensityBands_le_geometric
    {B x C c eta h T : ℝ} {J : ℕ}
    (hB : 0 < B) (hx : 1 ≤ x) (hC : 0 ≤ C)
    (heta : 0 ≤ eta) (hh : 0 ≤ h)
    (hdensity : ∀ j ∈ Finset.range J,
      (zetaHighZeroRectangleMass
        (((j + 2 : ℕ) : ℝ) * eta) T : ℝ) ≤
          C * B ^ (c * (((j + 2 : ℕ) : ℝ) * eta)))
    (hscale : c * Real.log B ≤ Real.log x / 4)
    (hcontract : 2 * Real.log 2 ≤ eta * Real.log x) :
    (∑ j ∈ Finset.range J,
      2 * ((zetaHighZeroRectangleMass
          (((j + 2 : ℕ) : ℝ) * eta) T : ℝ) *
        (x ^ (-(((j + 1 : ℕ) : ℝ) * eta)) * h))) ≤
      2 * C * Real.exp
        (c * eta * Real.log B - eta * Real.log x / 4) * h := by
  calc
    (∑ j ∈ Finset.range J,
      2 * ((zetaHighZeroRectangleMass
          (((j + 2 : ℕ) : ℝ) * eta) T : ℝ) *
        (x ^ (-(((j + 1 : ℕ) : ℝ) * eta)) * h))) ≤
      ∑ j ∈ Finset.range J,
        2 * ((C * B ^ (c * (((j + 2 : ℕ) : ℝ) * eta))) *
          (x ^ (-(((j + 1 : ℕ) : ℝ) * eta)) * h)) := by
            apply Finset.sum_le_sum
            intro j hj
            gcongr
            exact hdensity j hj
    _ ≤ ∑ j ∈ Finset.range J,
        (2 * C * Real.exp
          (c * eta * Real.log B - eta * Real.log x / 4) * h) *
            (1 / 2 : ℝ) ^ (j + 1) := by
      apply Finset.sum_le_sum
      intro j hj
      simpa only [mul_assoc] using shortDensityKernelBand_le_geometric
        hB hx hC heta hh hscale hcontract (j := j)
    _ ≤ (2 * C * Real.exp
          (c * eta * Real.log B - eta * Real.log x / 4) * h) * 1 := by
      let A : ℝ := 2 * C * Real.exp
        (c * eta * Real.log B - eta * Real.log x / 4) * h
      change (∑ j ∈ Finset.range J, A * (1 / 2 : ℝ) ^ (j + 1)) ≤ A * 1
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (by dsimp [A]; positivity)
      rw [show (∑ j ∈ Finset.range J, (1 / 2 : ℝ) ^ (j + 1)) =
          (1 / 2 : ℝ) * ∑ j ∈ Finset.range J, (1 / 2 : ℝ) ^ j by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [pow_succ']]
      nlinarith [sum_geometric_two_le J]
    _ = _ := by ring

/-- Subtracting the two modulus-one explicit formulas bounds the Chebyshev
increment error by the two endpoint errors and the termwise zero-kernel
increment. -/
theorem abs_chebyshevPsi_interval_sub_length_le
    {x y : ℕ} {T : ℝ} {Eₓ Eᵧ : ℝ}
    (hxy : x ≤ y)
    (hxFormula :
      ‖twistedChebyshevSum x 1 (1 : DirichletCharacter ℂ 1) -
          dirichletExplicitFormulaMainZeroTerms
            (1 : DirichletCharacter ℂ 1) (x : ℝ) T‖ ≤ Eₓ)
    (hyFormula :
      ‖twistedChebyshevSum y 1 (1 : DirichletCharacter ℂ 1) -
          dirichletExplicitFormulaMainZeroTerms
            (1 : DirichletCharacter ℂ 1) (y : ℝ) T‖ ≤ Eᵧ) :
    |(Chebyshev.psi (y : ℝ) - Chebyshev.psi (x : ℝ)) - (y - x : ℕ)| ≤
      Eᵧ + Eₓ +
        ∑ rho ∈ dirichletNontrivialLFunctionZerosFinset
            (1 : DirichletCharacter ℂ 1) T,
          ‖(analyticOrderNatAt
              (DirichletCharacter.LFunction
                (1 : DirichletCharacter ℂ 1)) rho : ℂ) *
            (dirichletExplicitFormulaKernel (y : ℝ) rho -
              dirichletExplicitFormulaKernel (x : ℝ) rho)‖ := by
  let Ey : ℂ :=
    twistedChebyshevSum y 1 (1 : DirichletCharacter ℂ 1) -
      dirichletExplicitFormulaMainZeroTerms
        (1 : DirichletCharacter ℂ 1) (y : ℝ) T
  let Ex : ℂ :=
    twistedChebyshevSum x 1 (1 : DirichletCharacter ℂ 1) -
      dirichletExplicitFormulaMainZeroTerms
        (1 : DirichletCharacter ℂ 1) (x : ℝ) T
  let Z : ℂ :=
    ∑ rho ∈ dirichletNontrivialLFunctionZerosFinset
        (1 : DirichletCharacter ℂ 1) T,
      (analyticOrderNatAt
          (DirichletCharacter.LFunction
            (1 : DirichletCharacter ℂ 1)) rho : ℂ) *
        (dirichletExplicitFormulaKernel (y : ℝ) rho -
          dirichletExplicitFormulaKernel (x : ℝ) rho)
  have hidentity :
      (((Chebyshev.psi (y : ℝ) - Chebyshev.psi (x : ℝ)) -
        (y - x : ℕ) : ℝ) : ℂ) = Ey - Ex - Z := by
    push_cast
    rw [← BoundedGaps.PrimeNumberTheorem.twistedChebyshevSum_one_eq_psi,
      ← BoundedGaps.PrimeNumberTheorem.twistedChebyshevSum_one_eq_psi]
    simp only [Ey, Ex, Z, dirichletExplicitFormulaMainZeroTerms,
      if_pos, dirichletNontrivialZeroKernelSum, Nat.cast_sub hxy,
      Complex.ofReal_sub, Complex.ofReal_natCast]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    ring
  rw [← Real.norm_eq_abs, ← Complex.norm_real, hidentity]
  calc
    ‖Ey - Ex - Z‖ ≤ ‖Ey‖ + ‖Ex‖ + ‖Z‖ := by
      calc
        ‖Ey - Ex - Z‖ ≤ ‖Ey - Ex‖ + ‖Z‖ := norm_sub_le _ _
        _ ≤ ‖Ey‖ + ‖Ex‖ + ‖Z‖ := by gcongr; exact norm_sub_le _ _
    _ ≤ Eᵧ + Eₓ + ‖Z‖ := by
      exact add_le_add
        (add_le_add (by simpa [Ey] using hyFormula)
          (by simpa [Ex] using hxFormula)) le_rfl
    _ ≤ Eᵧ + Eₓ +
        ∑ rho ∈ dirichletNontrivialLFunctionZerosFinset
            (1 : DirichletCharacter ℂ 1) T,
          ‖(analyticOrderNatAt
              (DirichletCharacter.LFunction
                (1 : DirichletCharacter ℂ 1)) rho : ℂ) *
            (dirichletExplicitFormulaKernel (y : ℝ) rho -
              dirichletExplicitFormulaKernel (x : ℝ) rho)‖ := by
      gcongr
      exact norm_sum_le _ _

theorem chebyshevTheta_lt_of_psi_interval_error
    {x y : ℕ} {E P : ℝ} (hxy : x ≤ y)
    (hpsi :
      |(Chebyshev.psi (y : ℝ) - Chebyshev.psi (x : ℝ)) - (y - x : ℕ)| ≤ E)
    (hpower : Chebyshev.psi (y : ℝ) - Chebyshev.theta (y : ℝ) ≤ P)
    (hbudget : E + P < (y - x : ℕ)) :
    Chebyshev.theta (x : ℝ) < Chebyshev.theta (y : ℝ) := by
  have hpsiLower :
      (y - x : ℕ) - E ≤
        Chebyshev.psi (y : ℝ) - Chebyshev.psi (x : ℝ) := by
    have := neg_le_of_abs_le hpsi
    linarith
  have hthetaPsi := Chebyshev.theta_le_psi (x : ℝ)
  linarith

theorem exists_prime_between_of_chebyshevTheta_lt
    {x y : ℕ} (hxy : x ≤ y)
    (htheta : Chebyshev.theta (x : ℝ) < Chebyshev.theta (y : ℝ)) :
    ∃ p : ℕ, p.Prime ∧ x < p ∧ p ≤ y := by
  by_contra hnot
  push_neg at hnot
  have hsets : Nat.primesLE x = Nat.primesLE y := by
    apply Finset.Subset.antisymm
    · intro p hp
      rw [Nat.mem_primesLE] at hp ⊢
      exact ⟨hp.1.trans hxy, hp.2⟩
    · intro p hp
      rw [Nat.mem_primesLE] at hp ⊢
      refine ⟨?_, hp.2⟩
      by_contra hpx
      exact (not_lt_of_ge hp.1) (hnot p hp.2 (lt_of_not_ge hpx))
  rw [Chebyshev.theta_eq_sum_primesLE_log,
    Chebyshev.theta_eq_sum_primesLE_log, hsets] at htheta
  exact (lt_irrefl _ htheta)

private lemma cast_add_two_mul_pos (j : ℕ) {eta : ℝ} (heta : 0 < eta) :
    0 < ((j + 2 : ℕ) : ℝ) * eta :=
  mul_pos (Nat.cast_pos.mpr (Nat.zero_lt_succ (j + 1))) heta

private lemma lambda_le_cast_add_two_mul_log_of_mul_log_eq
    (j : ℕ) {lambda eta logB : ℝ} (hlambda : 0 ≤ lambda)
    (hetaLogB : eta * logB = lambda) :
    lambda ≤ (((j + 2 : ℕ) : ℝ) * eta) * logB := by
  rw [mul_assoc, hetaLogB]
  have hj : 1 ≤ j + 2 := by omega
  have hjR0 : ((1 : ℕ) : ℝ) ≤ ((j + 2 : ℕ) : ℝ) := Nat.cast_le.mpr hj
  have hjR : (1 : ℝ) ≤ ((j + 2 : ℕ) : ℝ) := by
    simpa only [Nat.cast_one] using hjR0
  exact le_mul_of_one_le_left hlambda hjR

private theorem power_density_scale_bounds
    {n L : ℕ} {B eta lambda c x : ℝ}
    (heta : 0 ≤ eta) (hlambda : 0 ≤ lambda) (hc : 0 ≤ c)
    (hlogn : 0 ≤ Real.log (n : ℝ))
    (hetaLogB : eta * Real.log B = lambda)
    (hlogBupper : Real.log B ≤ 4 * Real.log (n : ℝ))
    (hlogx : Real.log x = (L : ℝ) * Real.log (n : ℝ))
    (hLscale : 16 * c ≤ (L : ℝ))
    (hLcontract : 8 * Real.log 2 ≤ (L : ℝ) * lambda) :
    lambda * (L : ℝ) / 4 ≤ eta * Real.log x ∧
      c * Real.log B ≤ Real.log x / 4 ∧
      2 * Real.log 2 ≤ eta * Real.log x := by
  have hlambdaUpper : lambda ≤ eta * (4 * Real.log (n : ℝ)) := by
    rw [← hetaLogB]
    exact mul_le_mul_of_nonneg_left hlogBupper heta
  have hLnonneg : 0 ≤ (L : ℝ) / 4 := by positivity
  have hetaLogxLower : lambda * (L : ℝ) / 4 ≤
      eta * Real.log x := by
    rw [hlogx]
    calc
      lambda * (L : ℝ) / 4 = lambda * ((L : ℝ) / 4) := by ring
      _ ≤ (eta * (4 * Real.log (n : ℝ))) * ((L : ℝ) / 4) :=
        mul_le_mul_of_nonneg_right hlambdaUpper hLnonneg
      _ = eta * ((L : ℝ) * Real.log (n : ℝ)) := by ring
  have hcL : 4 * c ≤ (L : ℝ) / 4 := by linarith
  have hscale : c * Real.log B ≤ Real.log x / 4 := by
    rw [hlogx]
    calc
      c * Real.log B ≤ c * (4 * Real.log (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hlogBupper hc
      _ = (4 * c) * Real.log (n : ℝ) := by ring
      _ ≤ ((L : ℝ) / 4) * Real.log (n : ℝ) :=
        mul_le_mul_of_nonneg_right hcL hlogn
      _ = (L : ℝ) * Real.log (n : ℝ) / 4 := by ring
  have hquarter :
      (8 * Real.log 2) / 4 ≤ ((L : ℝ) * lambda) / 4 :=
    (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 4)).2 hLcontract
  have hcontract : 2 * Real.log 2 ≤ eta * Real.log x := by
    apply le_trans _ hetaLogxLower
    calc
      2 * Real.log 2 = (8 * Real.log 2) / 4 := by ring
      _ ≤ ((L : ℝ) * lambda) / 4 := hquarter
      _ = lambda * (L : ℝ) / 4 := by ring
  exact ⟨hetaLogxLower, hscale, hcontract⟩

private lemma cast_consecutive_power_gap_pos {n L : ℕ} (hL : 1 ≤ L) :
    (0 : ℝ) < ((n + 1) ^ L - n ^ L : ℕ) :=
  Nat.cast_pos.mpr
    (Nat.sub_pos_of_lt (Nat.pow_lt_pow_left (Nat.lt_succ_self n) (by omega)))

private theorem density_majorant_lt_eighth
    {S C c eta B x lambda L h : ℝ}
    (hband : S ≤ 2 * C * Real.exp
      (c * eta * Real.log B - eta * Real.log x / 4) * h)
    (hetaLogB : eta * Real.log B = lambda)
    (hetaLogxLower : lambda * L / 4 ≤ eta * Real.log x)
    (hC : 0 < C) (hh : 0 < h)
    (hmiddleSmall : 2 * C * Real.exp (c * lambda - lambda * L / 16) < 1 / 8) :
    S < (1 / 8 : ℝ) * h := by
  have hsave0 : (lambda * L / 4) / 4 ≤
      (eta * Real.log x) / 4 :=
    (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 4)).2
      hetaLogxLower
  have hsave : lambda * L / 16 ≤ eta * Real.log x / 4 := by
    convert hsave0 using 1 <;> ring
  have hexp : c * eta * Real.log B - eta * Real.log x / 4 ≤
      c * lambda - lambda * L / 16 := by
    rw [show c * eta * Real.log B = c * (eta * Real.log B) by ring,
      hetaLogB]
    exact sub_le_sub_left hsave _
  have hcoef : 2 * C * Real.exp
      (c * eta * Real.log B - eta * Real.log x / 4) < 1 / 8 :=
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp)
      (mul_nonneg (by norm_num) hC.le)).trans_lt hmiddleSmall
  exact hband.trans_lt (mul_lt_mul_of_pos_right hcoef hh)

private lemma sq_le_nine_sq_of_nonneg_le_three_mul
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ 3 * b) :
    a ^ 2 ≤ 9 * b ^ 2 := by
  nlinarith [sq_nonneg (3 * b - a)]

private theorem dirichletNontrivialZeroReciprocalMultiplicitySum_nonneg
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (T : ℝ) :
    0 ≤ dirichletNontrivialZeroReciprocalMultiplicitySum chi T := by
  apply Finset.sum_nonneg
  intro rho hrho
  exact div_nonneg (Nat.cast_nonneg _)
    (by positivity : (0 : ℝ) ≤ 1 + |rho.im|)

private lemma le_add_lt_eighths_implies_lt_quarter
    {Z S F G h : ℝ} (hZ : Z ≤ S + F)
    (hS : S < (1 / 8 : ℝ) * h) (hF : F ≤ G)
    (hG : G < (1 / 8 : ℝ) * h) :
    Z < (1 / 4 : ℝ) * h := by
  linarith

private lemma three_eighth_add_one_eighth_lt
    {h : ℝ} (hh : 0 < h) :
    (3 / 8 : ℝ) * h + (1 / 8 : ℝ) * h < h := by
  linarith

/-- Hoheisel's theorem in the form needed below: one fixed even exponent has
a prime between every pair of consecutive `L`-th powers, once the base is
large enough. -/
theorem eventually_exists_prime_between_consecutive_fixed_powers :
    ∃ L : ℕ, 8 ≤ L ∧ ∀ᶠ n : ℕ in atTop,
      ∃ p : ℕ, p.Prime ∧ n ^ L < p ∧ p ≤ (n + 1) ^ L := by
  obtain ⟨M, hM, hzeroFree⟩ := exists_nat_riemannZeta_zero_re_lt
  let lambda : ℝ := 1 / (M : ℝ) ^ 2
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hlambda : 0 < lambda := by dsimp [lambda]; positivity
  obtain ⟨C, c, T₀, hC, hc, hdensity⟩ :=
    exists_zeta_logFreeDensity_power_bound hlambda
  obtain ⟨K, hK, hformula⟩ :=
    exists_nat_norm_twistedChebyshevSum_sub_dirichletExplicitFormulaMainZeroTerms_le
  obtain ⟨A, hA, hreciprocal⟩ :=
    exists_nat_dirichletNontrivialZeroReciprocalMultiplicitySum_le
  let delta : ℝ := min (1 / 16) (1 / ((M : ℝ) ^ 2 * Real.log 3))
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  obtain ⟨k, hL8, hLscale, hLcontract, hLfar, hmiddleSmall⟩ :=
    exists_hoheisel_even_exponent (lambda := lambda) (delta := delta)
      (C := C) (c := c) hlambda hdelta hC
  let L : ℕ := 2 * k
  have hLeq : L = 2 * k := rfl
  have hL1 : 1 ≤ L := by omega
  have hk2 : 2 ≤ k := by omega
  have hLdelta : 4 ≤ (L : ℝ) * delta := by
    have := (div_le_iff₀ hdelta).mp hLfar
    simpa only [L, Nat.cast_mul, Nat.cast_ofNat] using this
  let Derr : ℝ :=
    (K : ℝ) * (L : ℝ) ^ 2 * (1 + 4 * (2 : ℝ) ^ L)
  have herrLim : Tendsto (fun n : ℕ ↦
      Derr * (Real.log (n : ℝ) ^ 2 / (n : ℝ))) atTop (nhds 0) := by
    simpa [Derr] using Erdos48.tendsto_log_sq_div_nat.const_mul Derr
  have herrSmall : ∀ᶠ n : ℕ in atTop,
      Derr * (Real.log (n : ℝ) ^ 2 / (n : ℝ)) < 1 / 8 :=
    herrLim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8))
  have hfarLim : Tendsto (fun n : ℕ ↦
      (288 * (A : ℝ)) *
        (Real.log (n : ℝ) ^ 2 / (n : ℝ) ^ 2)) atTop (nhds 0) := by
    simpa using Erdos48.tendsto_log_sq_div_nat_sq.const_mul (288 * (A : ℝ))
  have hfarSmall : ∀ᶠ n : ℕ in atTop,
      (288 * (A : ℝ)) *
        (Real.log (n : ℝ) ^ 2 / (n : ℝ) ^ 2) < 1 / 8 :=
    hfarLim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8))
  have hlogDiv : Tendsto (fun n : ℕ ↦
      Real.log (n : ℝ) / (n : ℝ)) atTop (nhds 0) := by
    simpa [Function.comp_def, Real.rpow_one] using
      (isLittleO_log_rpow_atTop (r := (1 : ℝ)) (by norm_num)).tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  let Dpp : ℝ := 8 * (2 : ℝ) ^ k * (k : ℝ)
  have hppLim : Tendsto (fun n : ℕ ↦
      Dpp * (Real.log (n : ℝ) / (n : ℝ))) atTop (nhds 0) := by
    simpa [Dpp] using hlogDiv.const_mul Dpp
  have hppSmall : ∀ᶠ n : ℕ in atTop,
      Dpp * (Real.log (n : ℝ) / (n : ℝ)) < 1 / 8 :=
    hppLim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8))
  let Bn : ℕ → ℕ := fun n ↦ 2 * (n ^ 2 + 2)
  have hBnTop : Tendsto Bn atTop atTop := by
    apply Filter.tendsto_atTop_mono (f := fun n : ℕ ↦ n)
    · intro n
      dsimp [Bn]
      have hnn : n ≤ n ^ 2 :=
        Nat.le_pow (a := n) (b := 2) (by omega)
      exact hnn.trans (by omega)
    · exact tendsto_id
  have hlogBnTop : Tendsto (fun n : ℕ ↦ Real.log (Bn n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).comp hBnTop)
  have hetaSmallEventually : ∀ᶠ n : ℕ in atTop,
      16 * lambda ≤ Real.log (Bn n : ℝ) :=
    hlogBnTop.eventually_ge_atTop _
  refine ⟨L, hL8, ?_⟩
  filter_upwards [herrSmall, hfarSmall, hppSmall, hetaSmallEventually,
      eventually_ge_atTop (max 4 T₀)] with n herrN hfarN hppN hetaN hn
  simp only [Derr] at herrN
  simp only [Dpp] at hppN
  clear herrLim herrSmall hfarLim hfarSmall hlogDiv hppLim hppSmall
    hBnTop hlogBnTop hetaSmallEventually Derr Dpp hK hA hLeq hLfar
  let x : ℕ := n ^ L
  let y : ℕ := (n + 1) ^ L
  let T : ℕ := n ^ 2
  let B : ℝ := 2 * ((T : ℝ) + 2)
  let eta : ℝ := lambda / Real.log B
  let J : ℕ := Erdos48.endpointBandCount eta
  let h : ℝ := (y - x : ℕ)
  have hhpos : 0 < h := by
    dsimp [h, x, y]
    exact cast_consecutive_power_gap_pos hL1
  have hn4 : 4 ≤ n := (le_max_left 4 T₀).trans hn
  have hn2 : 2 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hlogn : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hxyNat : x ≤ y := by
    dsimp [x, y]
    exact Nat.pow_le_pow_left (by omega) L
  have hx4 : 4 ≤ x := by
    dsimp [x]
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ n ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ ≤ n ^ L := Nat.pow_le_pow_right (by omega) (by omega)
  have hy4 : 4 ≤ y := hx4.trans hxyNat
  have hT2 : 2 ≤ T := by dsimp [T]; nlinarith
  have hTx : (T : ℝ) ≤ x := by
    exact_mod_cast (show n ^ 2 ≤ n ^ L by
      exact Nat.pow_le_pow_right (by omega) (by omega))
  have hTy : (T : ℝ) ≤ y := hTx.trans (by exact_mod_cast hxyNat)
  have hT₀ : T₀ ≤ T := by
    dsimp [T]
    exact (le_max_right 4 T₀).trans hn |>.trans
      (Nat.le_pow (a := n) (b := 2) (by omega))
  have hBdef : B = (Bn n : ℝ) := by
    dsimp [B, Bn, T]
    norm_num
  have hBpos : 0 < B := by dsimp [B, T]; positivity
  have hBone : 1 < B := by
    dsimp [B]
    have hT0 : (0 : ℝ) ≤ T := by positivity
    linarith
  have hlogB : 0 < Real.log B := Real.log_pos hBone
  have hlogT : 0 < Real.log ((T : ℝ) + 2) := by
    apply Real.log_pos
    have hT0 : (0 : ℝ) ≤ T := by positivity
    linarith
  have heta : 0 < eta := by dsimp [eta]; positivity
  have hetaSmall : eta ≤ 1 / 16 := by
    rw [div_le_iff₀ hlogB]
    rw [hBdef]
    nlinarith
  have hetaZF : eta ≤
      1 / ((M : ℝ) ^ 2 * Real.log ((T : ℝ) + 2)) := by
    have hlogMono : Real.log ((T : ℝ) + 2) ≤ Real.log B := by
      apply Real.log_le_log (by positivity)
      dsimp [B]
      nlinarith
    have hdenT : 0 < (M : ℝ) ^ 2 * Real.log ((T : ℝ) + 2) := by
      positivity
    have hdenLe : (M : ℝ) ^ 2 * Real.log ((T : ℝ) + 2) ≤
        (M : ℝ) ^ 2 * Real.log B := by gcongr
    calc
      eta = 1 / ((M : ℝ) ^ 2 * Real.log B) := by
        dsimp [eta, lambda]
        field_simp
      _ ≤ 1 / ((M : ℝ) ^ 2 * Real.log ((T : ℝ) + 2)) :=
        one_div_le_one_div_of_le hdenT hdenLe
  have hdelta0 : 0 ≤ delta := hdelta.le
  have hdeltaLow : delta ≤
      1 / ((M : ℝ) ^ 2 * Real.log 3) := by
    exact min_le_right _ _
  have hdeltaHigh : delta ≤ ((J + 1 : ℕ) : ℝ) * eta := by
    exact (min_le_left _ _).trans
      (Erdos48.endpointBandCount_far_saving heta)
  have hwidthEight : ∀ j ∈ Finset.range J,
      (((j + 2 : ℕ) : ℝ) * eta) ≤ 1 / 8 := by
    simpa [J] using Erdos48.endpointBandCount_width heta hetaSmall
  have hwidth : ∀ j ∈ Finset.range J,
      (((j + 2 : ℕ) : ℝ) * eta) ≤ 1 := by
    intro j hj
    exact (hwidthEight j hj).trans (by norm_num)
  have hetaLogB : eta * Real.log B = lambda := by
    dsimp [eta]
    field_simp
  have hlogBupper : Real.log B ≤ 4 * Real.log (n : ℝ) := by
    rw [hBdef]
    simpa [Bn] using log_two_mul_natSq_add_two_le_four_log hn2
  have hlogx : Real.log (x : ℝ) = (L : ℝ) * Real.log (n : ℝ) := by
    dsimp [x]
    exact Erdos48.log_natCast_pow n L
  have hLscaleR : 16 * c ≤ (L : ℝ) := by
    dsimp [L]
    exact hLscale
  have hLcontractR : 8 * Real.log 2 ≤ (L : ℝ) * lambda := by
    have hbase := (div_le_iff₀ hlambda).mp hLcontract
    change 8 * Real.log 2 ≤ ((2 * k : ℕ) : ℝ) * lambda
    exact hbase
  obtain ⟨hetaLogxLower, hscale, hcontract⟩ :=
    power_density_scale_bounds heta.le hlambda.le hc.le hlogn.le
      hetaLogB hlogBupper hlogx hLscaleR hLcontractR
  have hdensityBands : ∀ j ∈ Finset.range J,
      (zetaHighZeroRectangleMass
        (((j + 2 : ℕ) : ℝ) * eta) (T : ℝ) : ℝ) ≤
          C * B ^ (c * (((j + 2 : ℕ) : ℝ) * eta)) := by
    intro j hj
    have hetaJ : 0 < (((j + 2 : ℕ) : ℝ) * eta) :=
      cast_add_two_mul_pos (eta := eta) j heta
    have hlambdaJ := lambda_le_cast_add_two_mul_log_of_mul_log_eq
        (lambda := lambda) (eta := eta) (logB := Real.log B)
        j hlambda.le hetaLogB
    have hlambdaJDensity : lambda ≤
        (((j + 2 : ℕ) : ℝ) * eta) *
          Real.log (2 * ((T : ℝ) + 2)) := by
      rw [show 2 * ((T : ℝ) + 2) = B from rfl]
      exact hlambdaJ
    have hd := hdensity T hT₀
      (((j + 2 : ℕ) : ℝ) * eta) hetaJ (hwidthEight j hj)
        hlambdaJDensity
    simpa [B] using hd
  have hband := sum_logFreeDensityBands_le_geometric
    hBpos (show 1 ≤ (x : ℝ) by exact_mod_cast (show 1 ≤ x by omega))
    hC.le heta.le (show 0 ≤ h by positivity) hdensityBands hscale hcontract
  have hbandSmall :
      (∑ j ∈ Finset.range J,
        2 * ((zetaHighZeroRectangleMass
            (((j + 2 : ℕ) : ℝ) * eta) (T : ℝ) : ℝ) *
          ((x : ℝ) ^ (-(((j + 1 : ℕ) : ℝ) * eta)) * h))) <
        (1 / 8 : ℝ) * h := by
    apply density_majorant_lt_eighth hband hetaLogB hetaLogxLower hC
    · exact hhpos
    · exact hmiddleSmall
  have hzero := sum_norm_all_zetaKernelDiff_le_densityBands_add_far
    hM (x := (x : ℝ)) (y := (y : ℝ)) (eta := eta) (delta := delta)
    (T := (T : ℝ)) (J := J)
    (by exact_mod_cast (show 1 ≤ x by omega))
    (by exact_mod_cast hxyNat) (by exact_mod_cast hT2) heta.le hetaZF
    hdelta0 hdeltaLow hdeltaHigh hwidth hzeroFree
  have hrecip := hreciprocal 1 (1 : DirichletCharacter ℂ 1) (T : ℝ)
    (by exact_mod_cast hT2)
  have hpowSave : (x : ℝ) ^ (-delta) ≤ 1 / (n : ℝ) ^ 4 := by
    dsimp [x]
    exact natPow_rpow_neg_le_inv_four hn1 hdelta.le hLdelta
  have hlogTupper : Real.log ((T : ℝ) + 2) ≤
      3 * Real.log (n : ℝ) := by
    dsimp [T]
    simpa using log_natSq_add_two_le_three_log hn2
  have hlogTnonneg : 0 ≤ Real.log ((T : ℝ) + 2) := hlogT.le
  have hfarBound :
      2 * (((x : ℝ) ^ (-delta) * h) * (1 + (T : ℝ)) *
        dirichletNontrivialZeroReciprocalMultiplicitySum
          (1 : DirichletCharacter ℂ 1) (T : ℝ)) ≤
        h * ((288 * (A : ℝ)) *
          (Real.log (n : ℝ) ^ 2 / (n : ℝ) ^ 2)) := by
    have hTone : 1 + (T : ℝ) ≤ 2 * (n : ℝ) ^ 2 := by
      dsimp [T]
      norm_num only [Nat.cast_pow]
      have hnSq : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ hnR
      linarith
    have hlogSq : Real.log ((T : ℝ) + 2) ^ 2 ≤
        9 * Real.log (n : ℝ) ^ 2 := by
      exact sq_le_nine_sq_of_nonneg_le_three_mul
        hlogTnonneg hlogn.le hlogTupper
    calc
      _ ≤ 2 * (((1 / (n : ℝ) ^ 4) * h) *
          (2 * (n : ℝ) ^ 2) *
          (8 * (A : ℝ) * Real.log ((T : ℝ) + 2) ^ 2)) := by
            have hrecip' :
                dirichletNontrivialZeroReciprocalMultiplicitySum
                    (1 : DirichletCharacter ℂ 1) (T : ℝ) ≤
                  8 * (A : ℝ) * Real.log ((T : ℝ) + 2) ^ 2 := by
              simpa only [Nat.cast_one, one_mul] using hrecip
            gcongr
            exact dirichletNontrivialZeroReciprocalMultiplicitySum_nonneg _ _
      _ ≤ 2 * (((1 / (n : ℝ) ^ 4) * h) *
          (2 * (n : ℝ) ^ 2) *
          (8 * (A : ℝ) * (9 * Real.log (n : ℝ) ^ 2))) := by gcongr
      _ = h * ((288 * (A : ℝ)) *
          (Real.log (n : ℝ) ^ 2 / (n : ℝ) ^ 2)) := by
        field_simp
        ring
  have hzeroSmall :
      (∑ rho ∈ dirichletNontrivialLFunctionZerosFinset
          (1 : DirichletCharacter ℂ 1) (T : ℝ),
        ‖(analyticOrderNatAt
          (DirichletCharacter.LFunction
            (1 : DirichletCharacter ℂ 1)) rho : ℂ) *
          (dirichletExplicitFormulaKernel (y : ℝ) rho -
            dirichletExplicitFormulaKernel (x : ℝ) rho)‖) <
        (1 / 4 : ℝ) * h := by
    have hfarSmall' : h * ((288 * (A : ℝ)) *
        (Real.log (n : ℝ) ^ 2 / (n : ℝ) ^ 2)) < (1 / 8 : ℝ) * h := by
      simpa only [mul_comm] using mul_lt_mul_of_pos_left hfarN hhpos
    have hcastGap : (y : ℝ) - (x : ℝ) = h := by
      dsimp [h]
      rw [Nat.cast_sub hxyNat]
    rw [hcastGap] at hzero
    have hfarActualSmall := hfarBound.trans_lt hfarSmall'
    have hadd := add_lt_add hbandSmall hfarActualSmall
    apply hzero.trans_lt
    exact hadd.trans_eq (by ring)
  have hxFormula := hformula 1 (1 : DirichletCharacter ℂ 1)
    (T : ℝ) (by exact_mod_cast hT2) x hx4 hTx
  have hyFormula := hformula 1 (1 : DirichletCharacter ℂ 1)
    (T : ℝ) (by exact_mod_cast hT2) y hy4 hTy
  have hpsi := abs_chebyshevPsi_interval_sub_length_le hxyNat
    hxFormula hyFormula
  have herrBound := explicitFormula_powerEndpoints_le_gap_mul
    (K := K) hn2 hL1
  have hformulaSmall :
      (K : ℝ) * dirichletExplicitFormulaErrorScale (x : ℝ) 1 (T : ℝ) +
        (K : ℝ) * dirichletExplicitFormulaErrorScale (y : ℝ) 1 (T : ℝ) <
          (1 / 8 : ℝ) * h := by
    apply herrBound.trans_lt
    simpa only [mul_comm] using mul_lt_mul_of_pos_left herrN hhpos
  have hpsiSmall :
      |(Chebyshev.psi (y : ℝ) - Chebyshev.psi (x : ℝ)) - (y - x : ℕ)| <
        (3 / 8 : ℝ) * h := by
    have hformulaSmallYX :
        (K : ℝ) * dirichletExplicitFormulaErrorScale (y : ℝ) 1 (T : ℝ) +
          (K : ℝ) * dirichletExplicitFormulaErrorScale (x : ℝ) 1 (T : ℝ) <
            (1 / 8 : ℝ) * h := by
      simpa only [add_comm] using hformulaSmall
    calc
      _ ≤ (K : ℝ) * dirichletExplicitFormulaErrorScale (y : ℝ) 1 (T : ℝ) +
          (K : ℝ) * dirichletExplicitFormulaErrorScale (x : ℝ) 1 (T : ℝ) +
          (∑ rho ∈ dirichletNontrivialLFunctionZerosFinset
              (1 : DirichletCharacter ℂ 1) (T : ℝ),
            ‖(analyticOrderNatAt
                (DirichletCharacter.LFunction
                  (1 : DirichletCharacter ℂ 1)) rho : ℂ) *
              (dirichletExplicitFormulaKernel (y : ℝ) rho -
                dirichletExplicitFormulaKernel (x : ℝ) rho)‖) := hpsi
      _ < (1 / 8 : ℝ) * h + (1 / 4 : ℝ) * h :=
        add_lt_add hformulaSmallYX hzeroSmall
      _ = (3 / 8 : ℝ) * h := by ring
  have hpp := primePower_powerEndpoint_le_gap_mul hn2 hk2
  have hpowGapEq :
      ((((n + 1) ^ (2 * k) - n ^ (2 * k) : ℕ) : ℝ)) = h := by
    dsimp [h, x, y, L]
  rw [hpowGapEq] at hpp
  have hpp' : Chebyshev.psi (y : ℝ) - Chebyshev.theta (y : ℝ) <
      (1 / 8 : ℝ) * h := by
    apply hpp.trans_lt
    simpa only [mul_comm, mul_left_comm, mul_assoc] using
      mul_lt_mul_of_pos_left hppN hhpos
  have htheta : Chebyshev.theta (x : ℝ) < Chebyshev.theta (y : ℝ) :=
    chebyshevTheta_lt_of_psi_interval_error hxyNat hpsiSmall.le hpp'.le
      (by
        dsimp [h]
        exact three_eighth_add_one_eighth_lt hhpos)
  obtain ⟨p, hp, hxp, hpy⟩ :=
    exists_prime_between_of_chebyshevTheta_lt hxyNat htheta
  exact ⟨p, hp, hxp, hpy⟩

end

end Erdos381
