import ErdosProblems.Erdos788.SuffixSlackDesign

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Exact integer parameters for the Trevisan construction

The ceilings needed for the seed length and entropy slack are represented by
`Nat.clog`.  Keeping them integral makes the later finite construction exact;
the elementary bounds below remove the ceilings before asymptotic estimates.
-/

namespace Erdos788

/-- Prediction/list-decoding advantage used in reconstruction. -/
noncomputable def trevisanEta (p r : ℕ) : ℝ :=
  1 / (40 * (p : ℝ) * r)

/-- Least exponent that can encode all binary design seeds over `𝔽_p`. -/
def trevisanSeedExponent (p D : ℕ) : ℕ :=
  Nat.clog p (2 ^ D)

/-- The integral factor whose absorption into `p^s` is exactly what the
reconstruction counting argument needs. -/
def trevisanSlackThreshold (p r D : ℕ) : ℕ :=
  40 * r * 2 ^ D * (3200 * p ^ 2 * r ^ 2 + 1)

/-- Least entropy-slack exponent that absorbs every reconstruction
description and every candidate in its agreement list. -/
def trevisanSlackExponent (p r D : ℕ) : ℕ :=
  Nat.clog p (trevisanSlackThreshold p r D)

theorem trevisanEta_pos {p r : ℕ} (hp : 0 < p) (hr : 0 < r) :
    0 < trevisanEta p r := by
  rw [trevisanEta]
  positivity

theorem trevisanEta_lt_half {p r : ℕ} (hp : 2 < p) (hr : 0 < r) :
    trevisanEta p r < 1 / 2 := by
  rw [trevisanEta]
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hden : (2 : ℝ) < 40 * p * r := by nlinarith
  exact one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 2) hden

theorem seedThreshold_le_pow_seedExponent {p D : ℕ} (hp : 1 < p) :
    2 ^ D ≤ p ^ trevisanSeedExponent p D := by
  exact Nat.le_pow_clog hp _

theorem slackThreshold_pos {p r D : ℕ} (hr : 0 < r) :
    0 < trevisanSlackThreshold p r D := by
  rw [trevisanSlackThreshold]
  positivity

theorem slackThreshold_le_pow_slackExponent {p r D : ℕ}
    (hp : 1 < p) :
    trevisanSlackThreshold p r D ≤
      p ^ trevisanSlackExponent p r D := by
  exact Nat.le_pow_clog hp _

/-- Removing a ceiling logarithm costs at most one factor of its base. -/
theorem pow_clog_le_base_mul {p x : ℕ} (hp : 1 < p) (hx : 0 < x) :
    p ^ Nat.clog p x ≤ p * x := by
  by_cases hx1 : x = 1
  · subst x
    rw [Nat.clog_one_right, pow_zero, mul_one]
    omega
  · have hxgt : 1 < x := by omega
    have hcpos : 0 < Nat.clog p x := Nat.clog_pos hp hxgt
    have hpred : p ^ (Nat.clog p x).pred < x :=
      Nat.pow_pred_clog_lt_self hp hxgt
    have hc : Nat.clog p x = (Nat.clog p x).pred + 1 := by
      simpa [Nat.succ_eq_add_one] using!
        (Nat.succ_pred_eq_of_pos hcpos).symm
    rw [hc,
      pow_succ, Nat.mul_comm]
    exact Nat.mul_le_mul_left p hpred.le

theorem pow_seedExponent_le {p D : ℕ} (hp : 1 < p) :
    p ^ trevisanSeedExponent p D ≤ p * 2 ^ D := by
  exact pow_clog_le_base_mul hp (by positivity)

theorem pow_slackExponent_le {p r D : ℕ}
    (hp : 1 < p) (hr : 0 < r) :
    p ^ trevisanSlackExponent p r D ≤
      p * trevisanSlackThreshold p r D := by
  exact pow_clog_le_base_mul hp (slackThreshold_pos hr)

theorem slackExponent_le_iff {p r D R : ℕ} (hp : 1 < p) :
    trevisanSlackExponent p r D ≤ R ↔
      trevisanSlackThreshold p r D ≤ p ^ R := by
  exact Nat.clog_le_iff_le_pow hp

/-- Real upper bound for an integral ceiling logarithm. -/
theorem cast_clog_lt_logb_add_one {b n : ℕ}
    (hb : 1 < b) (hn : 1 ≤ n) :
    ((Nat.clog b n : ℕ) : ℝ) < Real.logb b n + 1 := by
  have hbR : (1 : ℝ) < b := by exact_mod_cast hb
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [← Real.natCeil_logb_natCast]
  exact Nat.ceil_lt_add_one (Real.logb_nonneg hbR hnR)

theorem cast_seedExponent_lt {p D : ℕ} (hp : 1 < p) :
    ((trevisanSeedExponent p D : ℕ) : ℝ) <
      (D : ℝ) * Real.logb p 2 + 1 := by
  have hpowpos : 0 < 2 ^ D := pow_pos (by omega) D
  have h := cast_clog_lt_logb_add_one hp (by omega : 1 ≤ 2 ^ D)
  simpa [trevisanSeedExponent, Real.logb_pow] using! h

/-- The ceiling choice of `trevisanSlackExponent` implies exactly the real
counting inequality consumed by the reconstruction theorem. -/
theorem trevisan_reconstruction_count {p r D : ℕ}
    (hp : 2 < p) (hr : 0 < r) :
    ((((2 ^ D * p ^ (r - 1) : ℕ) : ℝ) *
          (2 / trevisanEta p r ^ 2 + 1))) ≤
      trevisanEta p r *
        (p ^ (r + trevisanSlackExponent p r D) : ℕ) := by
  let s := trevisanSlackExponent p r D
  have hp0 : 0 < p := by omega
  have hp1 : 1 < p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hden : (0 : ℝ) < 40 * p * r := by positivity
  have hlist : 2 / trevisanEta p r ^ 2 + 1 =
      3200 * (p : ℝ) ^ 2 * (r : ℝ) ^ 2 + 1 := by
    rw [trevisanEta]
    field_simp
    ring
  have hKnat : trevisanSlackThreshold p r D ≤ p ^ s := by
    exact slackThreshold_le_pow_slackExponent hp1
  have hK : ((trevisanSlackThreshold p r D : ℕ) : ℝ) ≤
      ((p ^ s : ℕ) : ℝ) := by
    exact_mod_cast hKnat
  have hmul : ((p ^ r : ℕ) : ℝ) *
        (trevisanSlackThreshold p r D : ℕ) ≤
      ((p ^ r : ℕ) : ℝ) * (p ^ s : ℕ) :=
    mul_le_mul_of_nonneg_left hK (by positivity)
  have hpowNat : p ^ (r - 1) * p = p ^ r := by
    rw [← pow_succ]
    congr 1
    omega
  have hpowR : ((p ^ (r - 1) : ℕ) : ℝ) * p =
      ((p ^ r : ℕ) : ℝ) := by
    exact_mod_cast hpowNat
  push_cast at hpowR
  rw [hlist, trevisanEta, one_div, inv_mul_eq_div]
  apply (le_div_iff₀ hden).2
  have hleft :
      (((2 ^ D * p ^ (r - 1) : ℕ) : ℝ) *
          (3200 * (p : ℝ) ^ 2 * (r : ℝ) ^ 2 + 1)) *
          (40 * (p : ℝ) * r) =
        ((p ^ r : ℕ) : ℝ) *
          (trevisanSlackThreshold p r D : ℕ) := by
    rw [trevisanSlackThreshold]
    push_cast
    calc
      2 ^ D * (p : ℝ) ^ (r - 1) *
            (3200 * (p : ℝ) ^ 2 * (r : ℝ) ^ 2 + 1) *
            (40 * p * r) =
          ((p : ℝ) ^ (r - 1) * p) *
            (40 * r * 2 ^ D *
              (3200 * (p : ℝ) ^ 2 * (r : ℝ) ^ 2 + 1)) := by ring
      _ = (p : ℝ) ^ r *
            (40 * r * 2 ^ D *
              (3200 * (p : ℝ) ^ 2 * (r : ℝ) ^ 2 + 1)) := by
            rw [hpowR]
  have hright :
      ((p ^ (r + s) : ℕ) : ℝ) =
        ((p ^ r : ℕ) : ℝ) * (p ^ s : ℕ) := by
    rw [Nat.pow_add]
    push_cast
    ring
  rw [hleft, hright]
  exact hmul

end Erdos788
