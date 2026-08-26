/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/
import ErdosProblems.Erdos730.FullDensityCore

/-!
# Erdős 730: exact obstruction-map algebra

This file formalizes equations (13)--(17) of the positive-density proof.
Everything here is elementary algebra over `ℤ`; in particular, this module
contains no asymptotic or distributional assertion.

The integer-valued left descriptions are used as the definitions of the
four obstruction maps.  For the `R` and `S` branches, the division by two is
certified from parity before it is used.  The subsequent progression
identities expose the common quadratic coefficient and the four residual
linear coefficients exactly.
-/

namespace Erdos730
namespace ObstructionMaps

open FullDensityCore

/-! ## Integer copies of the four branches -/

def Tz : ℤ := (FullDensityCore.T : ℤ)

def Pz (x : ℤ) : ℤ := 42 * Tz * x + 11
def Qz (x : ℤ) : ℤ := 72 * Tz * x + 13
def Rz (x : ℤ) : ℤ := 28 * Tz * x + 5
def Sz (x : ℤ) : ℤ := 72 * Tz * x + 19

theorem Tz_eq : Tz = 5289 := by
  norm_num [Tz, FullDensityCore.T]

theorem branch_casts (x : ℕ) :
    Pz x = (FullDensityCore.P x : ℤ) ∧
    Qz x = (FullDensityCore.Q x : ℤ) ∧
    Rz x = (FullDensityCore.R x : ℤ) ∧
    Sz x = (FullDensityCore.S x : ℤ) := by
  norm_num [Pz, Qz, Rz, Sz, Tz, FullDensityCore.P,
    FullDensityCore.Q, FullDensityCore.R, FullDensityCore.S,
    FullDensityCore.T]

theorem identity_PQz (x : ℤ) : 12 * Pz x = 7 * Qz x + 41 := by
  simp only [Pz, Qz]
  ring

theorem identity_RSz (x : ℤ) : 18 * Rz x + 43 = 7 * Sz x := by
  simp only [Rz, Sz]
  ring

theorem Rz_odd (x : ℤ) : Odd (Rz x) := by
  refine ⟨14 * Tz * x + 2, ?_⟩
  simp only [Rz]
  ring

theorem Sz_odd (x : ℤ) : Odd (Sz x) := by
  refine ⟨36 * Tz * x + 9, ?_⟩
  simp only [Sz]
  ring

/-! ## Integer-valued left descriptions and cleared formulas -/

/-- `Phi_P(c) = c Q`, the integral left description in (13). -/
def PhiP (x c : ℤ) : ℤ := c * Qz x

/-- `Phi_Q(c) = c P`, the integral left description in (13). -/
def PhiQ (x c : ℤ) : ℤ := c * Pz x

/-- `Phi_R(c) = (3 c S - 1) / 2`, the integral left description in (14). -/
def PhiR (x c : ℤ) : ℤ := (3 * c * Sz x - 1) / 2

/-- `Phi_S(c) = (3 c R - 1) / 2`, the integral left description in (15). -/
def PhiS (x c : ℤ) : ℤ := (3 * c * Rz x - 1) / 2

lemma two_dvd_PhiR_numerator {x c : ℤ} (hc : Odd c) :
    (2 : ℤ) ∣ 3 * c * Sz x - 1 := by
  rcases hc with ⟨d, hd⟩
  rcases Sz_odd x with ⟨e, he⟩
  refine ⟨6 * d * e + 3 * d + 3 * e + 1, ?_⟩
  rw [hd, he]
  ring

lemma two_dvd_PhiS_numerator {x c : ℤ} (hc : Odd c) :
    (2 : ℤ) ∣ 3 * c * Rz x - 1 := by
  rcases hc with ⟨d, hd⟩
  rcases Rz_odd x with ⟨e, he⟩
  refine ⟨6 * d * e + 3 * d + 3 * e + 1, ?_⟩
  rw [hd, he]
  ring

/-- The left description in (14) really is integral. -/
theorem two_mul_PhiR {x c : ℤ} (hc : Odd c) :
    2 * PhiR x c = 3 * c * Sz x - 1 := by
  have h := Int.ediv_mul_cancel (two_dvd_PhiR_numerator (x := x) hc)
  simpa only [PhiR, mul_comm] using h

/-- The left description in (15) really is integral. -/
theorem two_mul_PhiS {x c : ℤ} (hc : Odd c) :
    2 * PhiS x c = 3 * c * Rz x - 1 := by
  have h := Int.ediv_mul_cancel (two_dvd_PhiS_numerator (x := x) hc)
  simpa only [PhiS, mul_comm] using h

lemma R_cofactor_odd {q x c : ℤ} (hbranch : q * c = Rz x) : Odd c := by
  have hprod : Odd (q * c) := by
    rw [hbranch]
    exact Rz_odd x
  exact (Int.odd_mul.mp hprod).2

lemma S_cofactor_odd {q x c : ℤ} (hbranch : q * c = Sz x) : Odd c := by
  have hprod : Odd (q * c) := by
    rw [hbranch]
    exact Sz_odd x
  exact (Int.odd_mul.mp hprod).2

/-- Cleared first formula in (13), under `q c = P(x)`. -/
theorem PhiP_cleared {q x c : ℤ} (hbranch : q * c = Pz x) :
    7 * PhiP x c = 12 * q * c ^ 2 - 41 * c := by
  simp only [PhiP]
  have hid := identity_PQz x
  linear_combination -c * hid - 12 * c * hbranch

/-- Cleared second formula in (13), under `q c = Q(x)`. -/
theorem PhiQ_cleared {q x c : ℤ} (hbranch : q * c = Qz x) :
    12 * PhiQ x c = 7 * q * c ^ 2 + 41 * c := by
  simp only [PhiQ]
  have hid := identity_PQz x
  linear_combination c * hid - 7 * c * hbranch

/-- Cleared formula (14), under `q c = R(x)`.  Oddness of `c`, and hence
integrality of the left description, follows from the branch equation. -/
theorem PhiR_cleared {q x c : ℤ} (hbranch : q * c = Rz x) :
    14 * PhiR x c = 54 * q * c ^ 2 + 129 * c - 7 := by
  have hc := R_cofactor_odd hbranch
  have hhalf := two_mul_PhiR (x := x) hc
  have hid := identity_RSz x
  linear_combination 7 * hhalf - 3 * c * hid - 54 * c * hbranch

/-- Cleared formula (15), under `q c = S(x)`.  Oddness of `c`, and hence
integrality of the left description, follows from the branch equation. -/
theorem PhiS_cleared {q x c : ℤ} (hbranch : q * c = Sz x) :
    12 * PhiS x c = 7 * q * c ^ 2 - 43 * c - 6 := by
  have hc := S_cofactor_odd hbranch
  have hhalf := two_mul_PhiS (x := x) hc
  have hid := identity_RSz x
  linear_combination 6 * hhalf + c * hid - 7 * c * hbranch

/-! ## Root-progression substitution: equations (16)--(17) -/

/-- The four numerator coefficients all reduce to the same quadratic
coefficient after division by their respective clearing denominator. -/
theorem common_quadratic_coefficient :
    12 * (42 * Tz) ^ 2 = 7 * (3024 * Tz ^ 2) ∧
    7 * (72 * Tz) ^ 2 = 12 * (3024 * Tz ^ 2) ∧
    54 * (28 * Tz) ^ 2 = 14 * (3024 * Tz ^ 2) ∧
    7 * (72 * Tz) ^ 2 = 12 * (3024 * Tz ^ 2) := by
  constructor
  · ring
  · constructor
    · ring
    · constructor <;> ring

lemma P_shift_branch {q x0 c0 k : ℤ} (hbranch : q * c0 = Pz x0) :
    q * (c0 + 42 * Tz * k) = Pz (x0 + q * k) := by
  simp only [Pz] at hbranch ⊢
  linear_combination hbranch

lemma Q_shift_branch {q x0 c0 k : ℤ} (hbranch : q * c0 = Qz x0) :
    q * (c0 + 72 * Tz * k) = Qz (x0 + q * k) := by
  simp only [Qz] at hbranch ⊢
  linear_combination hbranch

lemma R_shift_branch {q x0 c0 k : ℤ} (hbranch : q * c0 = Rz x0) :
    q * (c0 + 28 * Tz * k) = Rz (x0 + q * k) := by
  simp only [Rz] at hbranch ⊢
  linear_combination hbranch

lemma S_shift_branch {q x0 c0 k : ℤ} (hbranch : q * c0 = Sz x0) :
    q * (c0 + 72 * Tz * k) = Sz (x0 + q * k) := by
  simp only [Sz] at hbranch ⊢
  linear_combination hbranch

lemma R_progression_odd {c0 k : ℤ} (hc0 : Odd c0) :
    Odd (c0 + 28 * Tz * k) := by
  rcases hc0 with ⟨d, hd⟩
  refine ⟨d + 14 * Tz * k, ?_⟩
  rw [hd]
  ring

lemma S_progression_odd {c0 k : ℤ} (hc0 : Odd c0) :
    Odd (c0 + 72 * Tz * k) := by
  rcases hc0 with ⟨d, hd⟩
  refine ⟨d + 36 * Tz * k, ?_⟩
  rw [hd]
  ring

/-- `P` instance of (16), with `u_P = 144 T c₀` and `b_P = -246 T`. -/
theorem PhiP_root_progression {q x0 c0 : ℤ}
    (hbranch : q * c0 = Pz x0) (k : ℤ) :
    PhiP (x0 + q * k) (c0 + 42 * Tz * k) =
      3024 * Tz ^ 2 * q * k ^ 2 +
        (q * (144 * Tz * c0) - 246 * Tz) * k + PhiP x0 c0 := by
  have hbase := PhiP_cleared hbranch
  have hshift := PhiP_cleared (P_shift_branch (k := k) hbranch)
  have hscaled :
      7 * PhiP (x0 + q * k) (c0 + 42 * Tz * k) =
        7 * (3024 * Tz ^ 2 * q * k ^ 2 +
          (q * (144 * Tz * c0) - 246 * Tz) * k + PhiP x0 c0) := by
    linear_combination hshift - hbase
  omega

/-- `Q` instance of (16), with `u_Q = 84 T c₀` and `b_Q = 246 T`. -/
theorem PhiQ_root_progression {q x0 c0 : ℤ}
    (hbranch : q * c0 = Qz x0) (k : ℤ) :
    PhiQ (x0 + q * k) (c0 + 72 * Tz * k) =
      3024 * Tz ^ 2 * q * k ^ 2 +
        (q * (84 * Tz * c0) + 246 * Tz) * k + PhiQ x0 c0 := by
  have hbase := PhiQ_cleared hbranch
  have hshift := PhiQ_cleared (Q_shift_branch (k := k) hbranch)
  have hscaled :
      12 * PhiQ (x0 + q * k) (c0 + 72 * Tz * k) =
        12 * (3024 * Tz ^ 2 * q * k ^ 2 +
          (q * (84 * Tz * c0) + 246 * Tz) * k + PhiQ x0 c0) := by
    linear_combination hshift - hbase
  omega

/-- `R` instance of (16), with `u_R = 216 T c₀` and `b_R = 258 T`. -/
theorem PhiR_root_progression {q x0 c0 : ℤ}
    (hbranch : q * c0 = Rz x0) (k : ℤ) :
    PhiR (x0 + q * k) (c0 + 28 * Tz * k) =
      3024 * Tz ^ 2 * q * k ^ 2 +
        (q * (216 * Tz * c0) + 258 * Tz) * k + PhiR x0 c0 := by
  have hbase := PhiR_cleared hbranch
  have hshift := PhiR_cleared (R_shift_branch (k := k) hbranch)
  have hscaled :
      14 * PhiR (x0 + q * k) (c0 + 28 * Tz * k) =
        14 * (3024 * Tz ^ 2 * q * k ^ 2 +
          (q * (216 * Tz * c0) + 258 * Tz) * k + PhiR x0 c0) := by
    linear_combination hshift - hbase
  omega

/-- `S` instance of (16), with `u_S = 84 T c₀` and `b_S = -258 T`. -/
theorem PhiS_root_progression {q x0 c0 : ℤ}
    (hbranch : q * c0 = Sz x0) (k : ℤ) :
    PhiS (x0 + q * k) (c0 + 72 * Tz * k) =
      3024 * Tz ^ 2 * q * k ^ 2 +
        (q * (84 * Tz * c0) - 258 * Tz) * k + PhiS x0 c0 := by
  have hbase := PhiS_cleared hbranch
  have hshift := PhiS_cleared (S_shift_branch (k := k) hbranch)
  have hscaled :
      12 * PhiS (x0 + q * k) (c0 + 72 * Tz * k) =
        12 * (3024 * Tz ^ 2 * q * k ^ 2 +
          (q * (84 * Tz * c0) - 258 * Tz) * k + PhiS x0 c0) := by
    linear_combination hshift - hbase
  omega

/-- Exact residual tuple from (17). -/
theorem residual_linear_coefficients :
    ((-246 : ℤ) * Tz, 246 * Tz, 258 * Tz, (-258 : ℤ) * Tz) =
      (-1301094, 1301094, 1364562, -1364562) := by
  norm_num [Tz, FullDensityCore.T]

/-! ## Exceptional-prime support -/

theorem exceptional_coefficient_factorizations :
    246 * FullDensityCore.T = 2 * 3 ^ 2 * 41 ^ 2 * 43 ∧
    258 * FullDensityCore.T = 2 * 3 ^ 2 * 41 * 43 ^ 2 := by
  norm_num [FullDensityCore.T]

private lemma prime_eq_of_dvd_prime {p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (h : p ∣ q) : p = q := by
  rcases (Nat.dvd_prime hq).mp h with hp1 | hpq
  · exact (hp.ne_one hp1).elim
  · exact hpq

private lemma prime_dvd_four_factors {p a b c d : ℕ} (hp : Nat.Prime p)
    (h : p ∣ a * b * c * d) : p ∣ a ∨ p ∣ b ∨ p ∣ c ∨ p ∣ d := by
  rcases hp.dvd_mul.mp h with habc | hd
  · rcases hp.dvd_mul.mp habc with hab | hc
    · rcases hp.dvd_mul.mp hab with ha | hb
      · exact Or.inl ha
      · exact Or.inr (Or.inl hb)
    · exact Or.inr (Or.inr (Or.inl hc))
  · exact Or.inr (Or.inr (Or.inr hd))

/-- Every prime divisor of either residual coefficient lies in the exact
exceptional set `{2,3,41,43}`. -/
theorem prime_dvd_residual_support {p : ℕ} (hp : Nat.Prime p)
    (h : p ∣ 246 * FullDensityCore.T ∨
      p ∣ 258 * FullDensityCore.T) :
    p = 2 ∨ p = 3 ∨ p = 41 ∨ p = 43 := by
  rcases h with h246 | h258
  · rw [exceptional_coefficient_factorizations.1] at h246
    have h' : p ∣ 2 * 3 ^ 2 * 41 ^ 2 * 43 := h246
    rcases prime_dvd_four_factors hp h' with h2 | h3sq | h41sq | h43
    · exact Or.inl (prime_eq_of_dvd_prime hp Nat.prime_two h2)
    · have h3 : p ∣ 3 := hp.dvd_of_dvd_pow h3sq
      exact Or.inr (Or.inl (prime_eq_of_dvd_prime hp Nat.prime_three h3))
    · have h41 : p ∣ 41 := hp.dvd_of_dvd_pow h41sq
      exact Or.inr (Or.inr (Or.inl
        (prime_eq_of_dvd_prime hp (by norm_num) h41)))
    · exact Or.inr (Or.inr (Or.inr
        (prime_eq_of_dvd_prime hp (by norm_num) h43)))
  · rw [exceptional_coefficient_factorizations.2] at h258
    have h' : p ∣ 2 * 3 ^ 2 * 41 * 43 ^ 2 := h258
    rcases prime_dvd_four_factors hp h' with h2 | h3sq | h41 | h43sq
    · exact Or.inl (prime_eq_of_dvd_prime hp Nat.prime_two h2)
    · have h3 : p ∣ 3 := hp.dvd_of_dvd_pow h3sq
      exact Or.inr (Or.inl (prime_eq_of_dvd_prime hp Nat.prime_three h3))
    · exact Or.inr (Or.inr (Or.inl
        (prime_eq_of_dvd_prime hp (by norm_num) h41)))
    · have h43 : p ∣ 43 := hp.dvd_of_dvd_pow h43sq
      exact Or.inr (Or.inr (Or.inr
        (prime_eq_of_dvd_prime hp (by norm_num) h43)))

end ObstructionMaps
end Erdos730
