import ErdosProblems.Erdos538.GoodParameterCount

/- Ported from Lean 4.31.0 to 4.33.0; imports, namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos538.IsotropicKernel

open scoped BigOperators

/-- If `q` is at least twice the exponent, the birthday-free factor
`(1-1/q)^d` is at least one half, in integer-cleared form. -/
theorem pow_le_two_mul_pred_pow (q d : ℕ) (hq0 : 0 < q) (hqd : 2 * d ≤ q) :
    q ^ d ≤ 2 * (q - 1) ^ d := by
  let a : ℝ := (q - 1 : ℕ) / (q : ℝ)
  have hqR : 0 < (q : ℝ) := by positivity
  have hbern := one_add_mul_sub_le_pow (a := a) (by
    dsimp [a]
    have : (0 : ℝ) ≤ (q - 1 : ℕ) / q := by positivity
    linarith) d
  have hcast : (2 : ℝ) * d ≤ q := by exact_mod_cast hqd
  have hdq : (d : ℝ) / q ≤ 1 / 2 := by
    apply (div_le_iff₀ hqR).2
    nlinarith
  have ha_sub : a - 1 = -(1 / (q : ℝ)) := by
    dsimp [a]
    rw [Nat.cast_sub (by omega : 1 ≤ q)]
    field_simp
    ring
  rw [ha_sub] at hbern
  have hleft : 1 + (d : ℝ) * -(1 / (q : ℝ)) = 1 - (d : ℝ) / q := by
    ring
  rw [hleft] at hbern
  have hhalf : (1 / 2 : ℝ) ≤ a ^ d := by linarith
  have ha_pow : a ^ d = ((q - 1 : ℕ) : ℝ) ^ d / (q : ℝ) ^ d := by
    dsimp [a]
    rw [div_pow]
  rw [ha_pow] at hhalf
  have hqpow : 0 < (q : ℝ) ^ d := by positivity
  have hmul := (le_div_iff₀ hqpow).mp hhalf
  exact_mod_cast (by nlinarith : (q : ℝ) ^ d ≤ 2 * ((q - 1 : ℕ) : ℝ) ^ d)

/-- Every factor in the independent-basis count is bounded below by the last
codimension-one factor. -/
theorem basis_factor_lower (q d : ℕ) (hq0 : 0 < q) {i : ℕ} (hi : i < d) :
    (q - 1) * q ^ (d - 1) ≤ q ^ d - q ^ i := by
  have hpow : q ^ i ≤ q ^ (d - 1) :=
    Nat.pow_le_pow_right hq0 (by omega)
  have hd : d = (d - 1) + 1 := by omega
  have hsplit : q ^ d = q ^ (d - 1) * q := by
    calc
      q ^ d = q ^ ((d - 1) + 1) := congrArg (q ^ ·) hd
      _ = q ^ (d - 1) * q := pow_succ _ _
  have hA : q ^ (d - 1) ≤ q * q ^ (d - 1) := by
    simpa [Nat.mul_comm] using Nat.le_mul_of_pos_left (q ^ (d - 1)) hq0
  have hbase : (q - 1) * q ^ (d - 1) + q ^ (d - 1) =
      q * q ^ (d - 1) := by
    rw [Nat.sub_mul, one_mul, Nat.sub_add_cancel hA]
  apply Nat.le_sub_of_add_le
  calc
    (q - 1) * q ^ (d - 1) + q ^ i ≤
        (q - 1) * q ^ (d - 1) + q ^ (d - 1) :=
      Nat.add_le_add_left hpow _
    _ = q * q ^ (d - 1) := hbase
    _ = q ^ d := by rw [hsplit, Nat.mul_comm]

/-- The exact favorable fixed-child parameter count is at least one eighth of
all child samples divided by `q`, under `q ≥ 2(d+1)`. -/
theorem eight_q_mul_goodParam_ge_childSample
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (d : ℕ) (hd : 0 < d)
    (hq : 2 * (d + 1) ≤ Fintype.card K) :
    Nat.card (ChildSample K d) ≤
      8 * Fintype.card K * Nat.card (GoodParam K d) := by
  let q := Fintype.card K
  have hq0 : 0 < q := Fintype.card_pos
  have hqd : 2 * d ≤ q := by omega
  have htail : q ^ d ≤ 2 * (q - 1) ^ d :=
    pow_le_two_mul_pred_pow q d hq0 hqd
  have hcoeff : q ^ d ≤ 2 * (q ^ d - 1) := by
    have hq2 : 2 ≤ q := by omega
    have htwo : 2 ≤ q ^ d := by
      calc 2 ≤ q := hq2
           _ ≤ q ^ d := Nat.le_pow hd
    omega
  have hfac : ∀ i : Fin d,
      (q - 1) * q ^ (d - 1) ≤ q ^ d - q ^ i.val := by
    intro i
    exact basis_factor_lower q d hq0 i.isLt
  have hprod : ((q - 1) * q ^ (d - 1)) ^ d ≤
      ∏ i : Fin d, (q ^ d - q ^ i.val) := by
    calc
      ((q - 1) * q ^ (d - 1)) ^ d =
          ∏ _i : Fin d, ((q - 1) * q ^ (d - 1)) := by simp
      _ ≤ ∏ i : Fin d, (q ^ d - q ^ i.val) :=
        Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun i _ => hfac i)
  have hdd : d ≤ d * d := by
    simpa using Nat.le_mul_of_pos_right d hd
  have hexp : d * d = d + d * (d - 1) := by
    rw [Nat.mul_sub_left_distrib]
    omega
  have hGLclear : q ^ (d * d) ≤
      2 * (((q - 1) * q ^ (d - 1)) ^ d) := by
    calc
      q ^ (d * d) = q ^ d * q ^ (d * (d - 1)) := by
        rw [hexp, pow_add]
      _ ≤ (2 * (q - 1) ^ d) * q ^ (d * (d - 1)) :=
        Nat.mul_le_mul_right _ htail
      _ = 2 * ((q - 1) ^ d * q ^ (d * (d - 1))) := by ring
      _ = 2 * ((q - 1) ^ d * q ^ ((d - 1) * d)) := by
        congr 3
        ring
      _ = 2 * (((q - 1) * q ^ (d - 1)) ^ d) := by
        rw [mul_pow, pow_mul]
  have hqcard : Nat.card K = q := Nat.card_eq_fintype_card
  rw [natCard_childSample, natCard_goodParam, hqcard]
  change q ^ ((d + 1) * (d + 1)) ≤
    8 * q * ((q - 1) ^ d * (∏ i : Fin d, (q ^ d - q ^ i.val)) *
      (q ^ d - 1))
  calc
    q ^ ((d + 1) * (d + 1)) = q * q ^ d * q ^ (d * d) * q ^ d := by
      calc
        q ^ ((d + 1) * (d + 1)) = q ^ (1 + d + d * d + d) := by
          congr 1
          ring
        _ = q ^ 1 * q ^ d * q ^ (d * d) * q ^ d := by
          rw [pow_add, pow_add, pow_add]
        _ = q * q ^ d * q ^ (d * d) * q ^ d := by simp
    _ ≤ q * (2 * (q - 1) ^ d) *
          (2 * (((q - 1) * q ^ (d - 1)) ^ d)) *
          (2 * (q ^ d - 1)) := by
      gcongr
    _ = 8 * q * ((q - 1) ^ d *
          (((q - 1) * q ^ (d - 1)) ^ d) * (q ^ d - 1)) := by ring
    _ ≤ 8 * q * ((q - 1) ^ d *
          (∏ i : Fin d, (q ^ d - q ^ i.val)) * (q ^ d - 1)) := by
      gcongr

end Erdos538.IsotropicKernel
