import ErdosProblems.Erdos633b.Arithmetic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.Positivity

/-! Elementary integer and rational lemmas for the Euler descent. -/

namespace Erdos633b.EulerDescent

def Q (u v : ℤ) : ℤ := u ^ 2 - 3 * u * v + 3 * v ^ 2

theorem Q_pos (u v : ℤ) (hv : 0 < v) : 0 < Q u v := by
  dsimp [Q]
  nlinarith [sq_nonneg (2 * u - 3 * v), sq_pos_of_pos hv]

theorem square_factor {a b : ℤ} (ha : 0 < a) (hc : IsCoprime a b)
    (hs : IsSquare (a * b)) : IsSquare a := by
  obtain ⟨c, hc'⟩ := hs
  obtain ⟨d, hd | hd⟩ := Int.sq_of_gcd_eq_one
    (Int.isCoprime_iff_gcd_eq_one.mp hc) (by simpa [sq] using hc')
  · exact ⟨d, by simpa [sq] using hd⟩
  · nlinarith [sq_nonneg d]

theorem coprime_Q_right (u v : ℤ) (hc : IsCoprime u v) : IsCoprime v (Q u v) := by
  have h := hc.symm.pow_right (n := 2)
  rw [show Q u v = u ^ 2 + (3 * v - 3 * u) * v by dsimp [Q]; ring]
  exact h.add_mul_right_right (3 * v - 3 * u)

theorem coprime_Q_left (u v : ℤ) (hc : IsCoprime u v) (h3 : IsCoprime u 3) :
    IsCoprime u (Q u v) := by
  have h := h3.mul_right (hc.pow_right (n := 2))
  rw [show Q u v = 3 * v ^ 2 + (u - 3 * v) * u by dsimp [Q]; ring]
  exact h.add_mul_right_right (u - 3 * v)

theorem triple_square_factors (u v : ℤ) (hu : 0 < u) (hv : 0 < v)
    (hc : IsCoprime u v) (h3 : IsCoprime u 3)
    (hs : IsSquare (u * v * Q u v)) :
    IsSquare u ∧ IsSquare v ∧ IsSquare (Q u v) := by
  have huQ := coprime_Q_left u v hc h3
  have hvQ := coprime_Q_right u v hc
  refine ⟨square_factor hu (hc.mul_right huQ) ?_,
    square_factor hv (hc.symm.mul_right hvQ) ?_,
    square_factor (Q_pos u v hv) (huQ.symm.mul_right hvQ.symm) ?_⟩
  · simpa [mul_assoc] using hs
  · convert hs using 1; ring
  · simpa [mul_comm] using hs

theorem coprime_three_iff (m : ℤ) : IsCoprime m 3 ↔ ¬ (3 : ℤ) ∣ m := by
  rw [isCoprime_comm, Int.prime_three.coprime_iff_not_dvd]

theorem sign_mod_three (u w : ℤ) (hu : ¬ (3 : ℤ) ∣ u)
    (hw : (w : ZMod 3) ^ 2 = (u : ZMod 3) ^ 2) :
    ∃ z : ℤ, z ^ 2 = w ^ 2 ∧ (3 : ℤ) ∣ z + u ∧ ¬ (3 : ℤ) ∣ z - u := by
  have hu0 : (u : ZMod 3) ≠ 0 := by
    exact fun h => hu ((ZMod.intCast_zmod_eq_zero_iff_dvd u 3).mp h)
  have hf : ∀ a b : ZMod 3, a ≠ 0 → b ^ 2 = a ^ 2 →
      (b + a = 0 ∧ b - a ≠ 0) ∨ (-b + a = 0 ∧ -b - a ≠ 0) := by decide
  rcases hf u w hu0 hw with h | h
  · refine ⟨w, rfl, ?_, ?_⟩
    · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp
      simpa using h.1
    · intro hd
      apply h.2
      simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr hd
  · refine ⟨-w, by ring, ?_, ?_⟩
    · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp
      simpa using h.1
    · intro hd
      apply h.2
      simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr hd

theorem reduced_ratio (a b : ℤ) (hb : b ≠ 0) :
    ∃ m n : ℤ, 0 < n ∧ IsCoprime m n ∧ m ∣ a ∧ n ∣ b ∧ a * n = m * b := by
  let r : ℚ := Rat.divInt a b
  refine ⟨r.num, r.den, by exact_mod_cast r.pos, r.isCoprime_num_den, ?_, ?_, ?_⟩
  · exact Rat.num_dvd a hb
  · exact Rat.den_dvd a b
  · have he : (r.num : ℚ) / r.den = (a : ℚ) / b := by
      simpa [r, Rat.divInt_eq_div] using r.num_div_den
    have he' := (div_eq_div_iff (by exact_mod_cast r.den_nz) (by exact_mod_cast hb)).mp he
    exact_mod_cast he'.symm

theorem reduced_cross_sign (u v A B : ℤ) (huv : IsCoprime u v)
    (hAB : IsCoprime A B) (he : u * B = A * v) :
    (u = A ∧ v = B) ∨ (u = -A ∧ v = -B) := by
  obtain ⟨r, s, hrs⟩ := hAB
  let k := r * u + s * v
  have hu : u = k * A := by dsimp [k]; linear_combination -u * hrs + s * he
  have hv : v = k * B := by dsimp [k]; linear_combination -v * hrs - r * he
  have hk : IsUnit k := huv.isUnit_of_dvd' ⟨A, hu⟩ ⟨B, hv⟩
  rcases Int.isUnit_iff.mp hk with hk | hk
  · left; simpa [hk] using And.intro hu hv
  · right; simpa [hk] using And.intro hu hv

theorem conic_fraction_coprime (m n : ℤ) (hc : IsCoprime m n)
    (h3 : IsCoprime m 3) : IsCoprime (3 * n ^ 2 - m ^ 2) (n * (2 * m + 3 * n)) := by
  let A := 3 * n ^ 2 - m ^ 2
  let L := 2 * m + 3 * n
  have hAn : IsCoprime A n := by
    rw [show A = -(m ^ 2) + (3 * n) * n by dsimp [A]; ring]
    exact (hc.pow_left (m := 2)).neg_left.add_mul_right_left (3 * n)
  have hAL : IsCoprime A L := by
    apply Int.isCoprime_iff_gcd_eq_one.mpr
    let g : ℤ := Int.gcd A L
    have hgA : g ∣ A := Int.gcd_dvd_left A L
    have hgL : g ∣ L := Int.gcd_dvd_right A L
    have hgN : g ∣ 3 * n ^ 2 := by
      rw [show 3 * n ^ 2 = 4 * A + L * (2 * m - 3 * n) by dsimp [A, L]; ring]
      exact dvd_add (dvd_mul_of_dvd_right hgA 4)
        (dvd_mul_of_dvd_left hgL (2 * m - 3 * n))
    have hgm : g ∣ m ^ 2 := by
      rw [show m ^ 2 = 3 * n ^ 2 - A by dsimp [A]; ring]
      exact dvd_sub hgN hgA
    have hgunit : IsUnit g :=
      ((h3.pow_left (m := 2)).mul_right hc.pow).isUnit_of_dvd' hgm hgN
    simpa [g] using Int.isUnit_iff_natAbs_eq.mp hgunit
  exact hAn.mul_right hAL

end Erdos633b.EulerDescent
