import ErdosProblems.Erdos941.LocalNorms
import ErdosProblems.Erdos941.Forms

/-!
# The integral quadratic form in Ankeny's construction
-/

namespace Erdos941

def ankenyU (a b x y : ℤ) : ℤ := a * x + b * y

def ankenyR (a b t m x y z : ℤ) : ℤ := t * ankenyU a b x y + m * z

def ankenyQ (a b c t m x y z : ℤ) : ℤ :=
  ankenyR a b t m x y z ^ 2 + a * x ^ 2 + 2 * b * x * y + c * y ^ 2

theorem ankenyQ_identity {a b c m : ℤ} (hc : a * c = b ^ 2 + m)
    (t x y z : ℤ) :
    a * ankenyQ a b c t m x y z = a * ankenyR a b t m x y z ^ 2 +
      ankenyU a b x y ^ 2 + m * y ^ 2 := by
  unfold ankenyQ ankenyU
  linear_combination y ^ 2 * hc

theorem ankenyQ_mod_identity {a b c m : ℤ} (hc : a * c = b ^ 2 + m)
    (t x y z : ℤ) :
    a * ankenyQ a b c t m x y z =
      (a * t ^ 2 + 1) * ankenyU a b x y ^ 2 +
        m * (2 * a * t * ankenyU a b x y * z + a * m * z ^ 2 + y ^ 2) := by
  rw [ankenyQ_identity hc]
  unfold ankenyR
  ring

theorem ankenyQ_dvd {a b c m t : ℤ} (hc : a * c = b ^ 2 + m)
    (ht : m ∣ a * t ^ 2 + 1) (ham : IsCoprime m a) (x y z : ℤ) :
    m ∣ ankenyQ a b c t m x y z := by
  apply ham.dvd_of_dvd_mul_left
  rw [ankenyQ_mod_identity hc]
  exact dvd_add (dvd_mul_of_dvd_left ht _) (dvd_mul_right _ _)

theorem ankenyQ_pos {a b c m : ℤ} (ha : 0 < a) (hm : 0 < m)
    (hc : a * c = b ^ 2 + m) (t x y z : ℤ) (hne : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) :
    0 < ankenyQ a b c t m x y z := by
  have hi := ankenyQ_identity hc t x y z
  have hR0 : 0 ≤ a * ankenyR a b t m x y z ^ 2 := mul_nonneg ha.le (sq_nonneg _)
  have hU0 := sq_nonneg (ankenyU a b x y)
  have hy0 : 0 ≤ m * y ^ 2 := mul_nonneg hm.le (sq_nonneg _)
  by_contra h
  have hq : ankenyQ a b c t m x y z ≤ 0 := by omega
  have hproduct : a * ankenyQ a b c t m x y z ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha.le hq
  have hR : ankenyR a b t m x y z = 0 := by
    have hh : a * ankenyR a b t m x y z ^ 2 = 0 := by omega
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hh).resolve_left ha.ne')
  have hU : ankenyU a b x y = 0 := sq_eq_zero_iff.mp (by omega)
  have hy : y = 0 := by
    have hh : m * y ^ 2 = 0 := by omega
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hh).resolve_left hm.ne')
  have hx : x = 0 := by
    simp only [ankenyU, hy, mul_zero, add_zero] at hU
    exact (mul_eq_zero.mp hU).resolve_left ha.ne'
  have hz : z = 0 := by
    simp only [ankenyR, ankenyU, hx, hy, mul_zero, zero_add, add_zero] at hR
    exact (mul_eq_zero.mp hR).resolve_left hm.ne'
  exact hne.elim (fun h => h hx) (fun h => h.elim (fun h => h hy) (fun h => h hz))

theorem ankenyQ_eq_of_short {a b c m t x y z : ℤ} (ha : 0 < a) (hm : 0 < m)
    (hc : a * c = b ^ 2 + m) (ht : m ∣ a * t ^ 2 + 1) (ham : IsCoprime m a)
    (hne : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) (hshort : ankenyQ a b c t m x y z < 2 * m) :
    ankenyQ a b c t m x y z = m := by
  have hpos := ankenyQ_pos ha hm hc t x y z hne
  obtain ⟨r, hr⟩ := ankenyQ_dvd hc ht ham x y z
  have hrpos : 0 < r := (mul_pos_iff_of_pos_left hm).mp (hr ▸ hpos)
  have hrlt : r < 2 := by nlinarith only [hshort, hr, hm]
  have : r = 1 := by omega
  simpa [this] using hr

theorem ankeny_three_squares_of_Q {a m : ℕ} {b c t x y z : ℤ}
    (ha : 0 < a) (hm : 0 < m) (hsq : Squarefree m)
    (hc : (a : ℤ) * c = b ^ 2 + m)
    (hprime : ∀ p : ℕ, p.Prime → p % 4 = 3 →
      ¬ p ∣ a ∧ (p ∣ m → IsSquare (-(a : ZMod p))))
    (hQ : ankenyQ a b c t m x y z = m) :
    ∃ X Y Z : ℤ, norm3 X Y Z = m := by
  let R := ankenyR a b t m x y z
  let U := ankenyU a b x y
  have hi : (a : ℤ) * ((m : ℤ) - R ^ 2) = U ^ 2 + (m : ℤ) * y ^ 2 := by
    have hh := ankenyQ_identity hc t x y z
    rw [hQ] at hh
    dsimp [R, U]
    linear_combination hh
  have ha' : 0 < (a : ℤ) := by exact_mod_cast ha
  have hm' : 0 < (m : ℤ) := by exact_mod_cast hm
  have hk : 0 ≤ (m : ℤ) - R ^ 2 := by
    apply nonneg_of_mul_nonneg_left _ ha'
    rw [mul_comm, hi]
    positivity
  lift ((m : ℤ) - R ^ 2) to ℕ using hk with k hkdef
  have hR : (m : ℤ) = R ^ 2 + k := by omega
  have hU : (a : ℤ) * k = U ^ 2 + (m : ℤ) * y ^ 2 := by
    exact hi
  obtain ⟨X, Z, hXZ⟩ := ankeny_two_squares ha hsq hprime hR hU
  refine ⟨R, X, Z, ?_⟩
  dsimp [norm3]
  have hh : (k : ℤ) = (X : ℤ) ^ 2 + (Z : ℤ) ^ 2 := by exact_mod_cast hXZ
  omega

end Erdos941
