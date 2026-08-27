import ErdosProblems.Erdos587.HooleyReciprocalMajorant
import ErdosProblems.Erdos587.HooleyDirichlet
import ErdosProblems.Erdos587.HooleyDenominatorBlocks

/-! # Reciprocal approximants: nonzero encodings and uniform shell sizes -/

namespace Erdos587

theorem exists_delta_reciprocal_approximant_family (c : ℕ) (A : ℕ → ℤ)
    {K : ℝ} (hK : 1 ≤ K) :
    ∃ x : ℕ → DeltaApproximant, ∀ m : ℕ, (x m).index = m ∧
      0 < (x m).denominator ∧ ((x m).denominator : ℝ) ≤ K ∧
      IsUnit ((x m).numerator : ZMod (x m).denominator) ∧
      |deltaReciprocalFrequencyError c A (x m)| ≤ 2 / (((x m).denominator : ℝ) * K) := by
  classical
  have hex (m : ℕ) := exists_delta_dirichlet_approximant ((A m : ℝ) / (c * m : ℕ)) hK
  choose b h hb hbK hu he using hex
  refine ⟨fun m => ⟨m, b m, h m⟩, ?_⟩
  intro m
  refine ⟨rfl, hb m, hbK m, hu m, (he m).trans ?_⟩
  apply div_le_div_of_nonneg_right (by norm_num)
  positivity

lemma delta_reciprocal_encoded_ne_zero {a b v q : ℕ} {K : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hK : 1 ≤ K) (hbK : (b : ℝ) ≤ K)
    (hcop : q.Coprime v) (hq : (a : ℝ) * K < q) (t : ℤ) :
    (b : ℤ) * a * v - q * t ≠ 0 := by
  have hqfloor : a * ⌊K⌋₊ < q := by
    have h := (mul_le_mul_of_nonneg_left (Nat.floor_le (by linarith : 0 ≤ K))
      (Nat.cast_nonneg a)).trans_lt hq
    exact_mod_cast h
  have h := reciprocal_delta_encoding_ne_zero ha hb (Nat.le_floor hbK) hcop hqfloor t
  simpa only [mul_comm (a : ℤ) (b : ℤ)] using h

lemma delta_reciprocal_gcd_cancel {a b v q : ℕ} (hcop : q.Coprime v) :
    Int.gcd ((b : ℤ) * a * v) q = q.gcd (a * b) := by
  simp only [Int.gcd_eq_natAbs_gcd_natAbs, Int.natAbs_mul, Int.natAbs_natCast]
  rw [hcop.symm.gcd_mul_right_cancel (b * a), Nat.mul_comm b a, Nat.gcd_comm]

lemma delta_reciprocal_dyadic_scale {K : ℝ} (hK : 0 < K) {D j c : ℕ}
    (hKD : K ≤ 2 ^ D) (hjD : j ≤ D) (A : ℕ → ℤ)
    {x : DeltaApproximant} (hb : 0 < x.denominator)
    (hblock : Nat.clog 2 x.denominator = j)
    (herror : |deltaReciprocalFrequencyError c A x| ≤ 2 / ((x.denominator : ℝ) * K)) :
    K ^ 2 * |deltaReciprocalFrequencyError c A x| ≤ 2 ^ (D - j + 2) := by
  have hbR : (0 : ℝ) < x.denominator := by exact_mod_cast hb
  have hlo := (delta_dyadic_denominator_bounds hb).1
  rw [hblock] at hlo
  have hmul := (le_div_iff₀ (mul_pos hbR hK)).mp herror
  apply delta_dyadic_error_scale (by positivity) hKD hjD (by linarith :
    (2 : ℝ) ^ j ≤ 2 * x.denominator)
  nlinarith [mul_le_mul_of_nonneg_right hmul hK.le]

lemma delta_reciprocal_shell_tolerance_le {c b D : ℕ} {K R : ℝ}
    (hK : 1 ≤ K) (hR : 0 ≤ R) (hDK : (2 : ℝ) ^ D ≤ 2 * K)
    (hbD : Nat.clog 2 b ≤ D) :
    (2 * (c : ℝ) * R * b / K ^ 2) * 2 ^ (D - Nat.clog 2 b + 2) ≤ 16 * c * R := by
  have hKpos : 0 < K := by linarith
  have hb : (b : ℝ) ≤ 2 ^ Nat.clog 2 b := by
    exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) b
  have hpow : (2 : ℝ) ^ Nat.clog 2 b * 2 ^ (D - Nat.clog 2 b + 2) = 4 * 2 ^ D := by
    rw [← pow_add, show Nat.clog 2 b + (D - Nat.clog 2 b + 2) = D + 2 by omega, pow_add]
    norm_num
    ring
  have hbpow : (b : ℝ) * 2 ^ (D - Nat.clog 2 b + 2) ≤ 8 * K := by
    have h := mul_le_mul_of_nonneg_right hb (by positivity : (0 : ℝ) ≤ 2 ^ (D - Nat.clog 2 b + 2))
    rw [hpow] at h
    linarith
  calc
    _ = (2 * (c : ℝ) * R) * (b * 2 ^ (D - Nat.clog 2 b + 2)) / K ^ 2 := by ring
    _ ≤ (2 * (c : ℝ) * R) * (8 * K) / K ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg K)
      exact mul_le_mul_of_nonneg_left hbpow (by positivity)
    _ = (16 * (c : ℝ) * R) / K := by field_simp; ring
    _ ≤ _ := div_le_self (by positivity) hK

lemma delta_reciprocal_value_size {a b c v q X : ℕ} {K R : ℝ}
    (hbK : (b : ℝ) ≤ K)
    (hX : (a : ℝ) * v * K + 16 * c * q * R ≤ X)
    (t : ℤ) (ht : |(t : ℝ)| ≤ 16 * c * R) :
    ((b : ℤ) * a * v - q * t).natAbs ≤ X := by
  have hbound : (((b : ℤ) * a * v - q * t).natAbs : ℝ) ≤ X := by
    rw [Nat.cast_natAbs, Int.cast_abs]
    push_cast
    calc
      _ ≤ |(b : ℝ) * a * v| + |(q : ℝ) * t| := abs_sub _ _
      _ = (b : ℝ) * a * v + (q : ℝ) * |(t : ℝ)| := by
        rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (b : ℝ) * a * v), abs_mul,
          abs_of_nonneg (Nat.cast_nonneg q)]
      _ ≤ K * a * v + (q : ℝ) * (16 * c * R) :=
        add_le_add (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hbK (Nat.cast_nonneg a)) (Nat.cast_nonneg v))
          (mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg q))
      _ ≤ X := by nlinarith
  exact_mod_cast hbound

end Erdos587
