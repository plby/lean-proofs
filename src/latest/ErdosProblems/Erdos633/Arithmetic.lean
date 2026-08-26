import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Tactic

/-!
# Arithmetic for Erdős problem 633

Unconditional arithmetic lemmas used by the congruent-triangle classification.
No geometric classification theorem is assumed in this file.
-/

namespace Erdos633

/-- Multiplication by a nonzero rational square preserves the square class. -/
theorem isSquare_sq_mul_iff (r q : ℚ) (hr : r ≠ 0) :
    IsSquare (r ^ 2 * q) ↔ IsSquare q := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x / r, ?_⟩
    apply (mul_left_cancel₀ (pow_ne_zero 2 hr))
    calc
      r ^ 2 * q = x * x := hx
      _ = r ^ 2 * (x / r * (x / r)) := by field_simp
  · rintro ⟨x, rfl⟩
    exact ⟨r * x, by ring⟩

/-- The arithmetic content of the area-square test, with no assumed tiling. -/
theorem count_isSquare_iff (N : ℕ) (r q : ℚ) (hr : r ≠ 0)
    (harea : (N : ℚ) = r ^ 2 * q) : IsSquare N ↔ IsSquare q := by
  rw [← Rat.isSquare_natCast_iff, harea, isSquare_sq_mul_iff r q hr]

/-- The modulo-three obstruction to a primitive sum of two squares. -/
theorem not_sq_add_sq_eq_three_sq {u v : ℕ} (huv : u.Coprime v) (w : ℕ) :
    w ^ 2 + u ^ 2 ≠ 3 * v ^ 2 := by
  intro h
  have hz : (w : ZMod 3) ^ 2 + (u : ZMod 3) ^ 2 = 0 := by
    have h' := congrArg (fun n : ℕ => (n : ZMod 3)) h
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
      show (3 : ZMod 3) = 0 by decide, zero_mul] using h'
  have hmod : ∀ x y : ZMod 3, x ^ 2 + y ^ 2 = 0 → x = 0 ∧ y = 0 := by
    decide
  obtain ⟨hw0, hu0⟩ := hmod _ _ hz
  have hw : 3 ∣ w := (ZMod.natCast_eq_zero_iff w 3).mp hw0
  have hu : 3 ∣ u := (ZMod.natCast_eq_zero_iff u 3).mp hu0
  obtain ⟨w', hw'⟩ := hw
  obtain ⟨u', hu'⟩ := hu
  have hv2 : 3 ∣ v ^ 2 := by
    refine ⟨w' ^ 2 + u' ^ 2, ?_⟩
    nlinarith [h]
  have hv : 3 ∣ v := Nat.prime_three.dvd_of_dvd_pow hv2
  have hbad : 3 ∣ 1 := by
    rw [← huv.gcd_eq_one]
    exact Nat.dvd_gcd ⟨u', hu'⟩ hv
  norm_num at hbad

theorem groupOne_factors_coprime {u v : ℕ} (huv : u.Coprime v) (hu : u < v) :
    (2 * v ^ 2 - u ^ 2).Coprime (3 * v ^ 2 - u ^ 2) := by
  have hs : u ^ 2 ≤ v ^ 2 := Nat.pow_le_pow_left (Nat.le_of_lt hu) 2
  have ha : 2 * v ^ 2 - u ^ 2 + u ^ 2 = 2 * v ^ 2 := Nat.sub_add_cancel (by omega)
  have hb : 3 * v ^ 2 - u ^ 2 = (2 * v ^ 2 - u ^ 2) + v ^ 2 := by omega
  let d := Nat.gcd (2 * v ^ 2 - u ^ 2) (3 * v ^ 2 - u ^ 2)
  have hdA : d ∣ 2 * v ^ 2 - u ^ 2 := Nat.gcd_dvd_left _ _
  have hdB : d ∣ 3 * v ^ 2 - u ^ 2 := Nat.gcd_dvd_right _ _
  have hdv : d ∣ v ^ 2 := by
    rw [hb] at hdB
    exact (Nat.dvd_add_iff_right hdA).mpr hdB
  have hdu : d ∣ u ^ 2 := by
    have hd : d ∣ (2 * v ^ 2 - u ^ 2) + u ^ 2 := by
      rw [ha]
      exact dvd_mul_of_dvd_right hdv 2
    exact (Nat.dvd_add_iff_right hdA).mpr hd
  have hd1 : d ∣ 1 := by
    rw [← (huv.pow 2 2).gcd_eq_one]
    exact Nat.dvd_gcd hdu hdv
  exact Nat.dvd_one.mp hd1

/-- The numerator of the group-one `U` area ratio is never a square. -/
theorem groupOne_U_numerator_not_isSquare {u v : ℕ} (huv : u.Coprime v)
    (hu : u < v) : ¬ IsSquare ((2 * v ^ 2 - u ^ 2) * (3 * v ^ 2 - u ^ 2)) := by
  rintro ⟨w, hw⟩
  have hc := groupOne_factors_coprime huv hu
  have hunit : IsUnit (gcd (3 * v ^ 2 - u ^ 2) (2 * v ^ 2 - u ^ 2)) := by
    rw [gcd_eq_nat_gcd, hc.symm.gcd_eq_one]
    exact isUnit_one
  obtain ⟨z, hz⟩ := exists_eq_pow_of_mul_eq_pow hunit
    (show (3 * v ^ 2 - u ^ 2) * (2 * v ^ 2 - u ^ 2) = w ^ 2 by
      simpa [mul_comm, pow_two] using hw)
  apply not_sq_add_sq_eq_three_sq huv z
  have hs : u ^ 2 ≤ v ^ 2 := Nat.pow_le_pow_left (Nat.le_of_lt hu) 2
  have hsub := Nat.sub_add_cancel (show u ^ 2 ≤ 3 * v ^ 2 by omega)
  omega

/-- Clearing the denominator gives the exact square test for the `V` family. -/
theorem groupOne_V_isSquare_iff {u v : ℕ} (hu : u < v) :
    IsSquare (2 - ((u : ℚ) / v) ^ 2) ↔ IsSquare (2 * v ^ 2 - u ^ 2) := by
  have hv : (v : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hu)
  have hs : u ^ 2 ≤ v ^ 2 := Nat.pow_le_pow_left hu.le 2
  have hsub : u ^ 2 ≤ 2 * v ^ 2 := by omega
  have heq : (v : ℚ) ^ 2 * (2 - ((u : ℚ) / v) ^ 2) =
      ((2 * v ^ 2 - u ^ 2 : ℕ) : ℚ) := by
    rw [Nat.cast_sub hsub]
    push_cast
    field_simp
  rw [← isSquare_sq_mul_iff (v : ℚ) _ hv, heq, Rat.isSquare_natCast_iff]

/-- The elementary nonsquare obstruction after rational normalization. -/
theorem groupOne_U_ratio_not_isSquare {u v : ℕ} (huv : u.Coprime v) (hu : u < v) :
    ¬ IsSquare ((2 - ((u : ℚ) / v) ^ 2) * (3 - ((u : ℚ) / v) ^ 2)) := by
  intro h
  have hv : (v : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hu)
  have hs : u ^ 2 ≤ v ^ 2 := Nat.pow_le_pow_left hu.le 2
  have hsub2 : u ^ 2 ≤ 2 * v ^ 2 := by omega
  have hsub3 : u ^ 2 ≤ 3 * v ^ 2 := by omega
  have heq : ((v : ℚ) ^ 2) ^ 2 *
      ((2 - ((u : ℚ) / v) ^ 2) * (3 - ((u : ℚ) / v) ^ 2)) =
      (((2 * v ^ 2 - u ^ 2) * (3 * v ^ 2 - u ^ 2) : ℕ) : ℚ) := by
    rw [Nat.cast_mul, Nat.cast_sub hsub2, Nat.cast_sub hsub3]
    push_cast
    field_simp
  have h' := (isSquare_sq_mul_iff ((v : ℚ) ^ 2) _ (pow_ne_zero 2 hv)).mpr h
  rw [heq, Rat.isSquare_natCast_iff] at h'
  exact groupOne_U_numerator_not_isSquare huv hu h'

/-- The exceptional parameter `s = 1/5` really has square `V` area ratio. -/
theorem groupOne_V_one_fifth_isSquare : IsSquare (2 - (1 / 5 : ℚ) ^ 2) := by
  exact ⟨7 / 5, by norm_num⟩

/-- A nonnegative rational parameter below one has reduced natural coordinates
with strictly smaller numerator than denominator. -/
theorem rational_parameter_coordinates {s : ℚ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    ∃ u v : ℕ, u.Coprime v ∧ u < v ∧ s = (u : ℚ) / v := by
  have hn : 0 ≤ s.num := Rat.num_nonneg.mpr hs0
  have hnabs : (s.num.natAbs : ℤ) = s.num := Int.natAbs_of_nonneg hn
  have heq : s = (s.num.natAbs : ℚ) / s.den := by
    calc
      s = (s.num : ℚ) / s.den := (Rat.num_div_den s).symm
      _ = (s.num.natAbs : ℚ) / s.den := by
        congr 1
        simpa only [Int.cast_natCast] using
          congrArg (fun n : ℤ => (n : ℚ)) hnabs.symm
  refine ⟨s.num.natAbs, s.den, s.reduced, ?_, heq⟩
  have hd : (0 : ℚ) < s.den := by exact_mod_cast s.den_pos
  rw [heq, div_lt_one hd] at hs1
  exact_mod_cast hs1

/-- No rational parameter in the geometric interval has square `U` area ratio.
This proves the entire required arithmetic assertion, not just a finite check. -/
theorem groupOne_U_not_isSquare (s : ℚ) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    ¬ IsSquare ((2 - s ^ 2) * (3 - s ^ 2)) := by
  obtain ⟨u, v, huv, hu, rfl⟩ := rational_parameter_coordinates hs0 hs1
  exact groupOne_U_ratio_not_isSquare huv hu

/-- A rational area equation for the `U` family forces a nonsquare tile count. -/
theorem groupOne_U_count_not_isSquare (N : ℕ) (r s : ℚ) (hr : r ≠ 0)
    (hs0 : 0 ≤ s) (hs1 : s < 1)
    (harea : (N : ℚ) = r ^ 2 * ((2 - s ^ 2) * (3 - s ^ 2))) :
    ¬ IsSquare N := by
  intro hN
  exact groupOne_U_not_isSquare s hs0 hs1 ((count_isSquare_iff N r _ hr harea).mp hN)

/-- The `V` area equation gives exactly the integer test, including the square
exceptional parameters. -/
theorem groupOne_V_count_isSquare_iff (N : ℕ) (r : ℚ) (hr : r ≠ 0)
    {u v : ℕ} (hu : u < v)
    (harea : (N : ℚ) = r ^ 2 * (2 - ((u : ℚ) / v) ^ 2)) :
    IsSquare N ↔ IsSquare (2 * v ^ 2 - u ^ 2) := by
  exact (count_isSquare_iff N r _ hr harea).trans (groupOne_V_isSquare_iff hu)

/-- A finite family of positive rational scales has one positive natural
denominator and positive natural numerators. -/
theorem positive_rationals_common_denominator {ι : Type*} [Finite ι]
    (r : ι → ℚ) (hr : ∀ i, 0 < r i) :
    ∃ d : ℕ, 0 < d ∧ ∃ k : ι → ℕ, (∀ i, 0 < k i) ∧
      ∀ i, r i = (k i : ℚ) / d := by
  let : Fintype ι := Fintype.ofFinite ι
  let d : ℕ := ∏ i, (r i).den
  have hd : 0 < d := Finset.prod_pos fun i _ => (r i).den_pos
  have hdiv (i : ι) : (r i).den ∣ d := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  let k : ι → ℕ := fun i => (r i).num.natAbs * (d / (r i).den)
  have heq (i : ι) : r i = (k i : ℚ) / d := by
    have hnabs : ((r i).num.natAbs : ℤ) = (r i).num :=
      Int.natAbs_of_nonneg (Rat.num_pos.mpr (hr i)).le
    have hnQ : ((r i).num.natAbs : ℚ) = ((r i).num : ℚ) := by
      simpa only [Int.cast_natCast] using congrArg (fun n : ℤ => (n : ℚ)) hnabs
    have hmul : ((r i).den : ℚ) * (d / (r i).den : ℕ) = d := by
      exact_mod_cast Nat.mul_div_cancel' (hdiv i)
    have hden : ((r i).den : ℚ) ≠ 0 := by exact_mod_cast (r i).den_ne_zero
    have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hd
    rw [← Rat.num_div_den (r i)]
    dsimp [k]
    push_cast
    rw [hnQ]
    apply (div_eq_div_iff hden hdQ).mpr
    rw [← hmul]
    ring
  refine ⟨d, hd, k, ?_, heq⟩
  intro i
  have hkQ : (0 : ℚ) < k i := by
    have hi := hr i
    rw [heq i] at hi
    exact (div_pos_iff_of_pos_right (by exact_mod_cast hd)).mp hi
  exact_mod_cast hkQ

end Erdos633
