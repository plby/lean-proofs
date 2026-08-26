import ErdosProblems.Erdos633b.ReptilingAlgebra

/-! Elimination in the first two rows of a zero-diagonal right-triangle
boundary matrix. All coefficient comparisons take place over the integers. -/

namespace Erdos633b

theorem right_rows_irrational_coefficient {L a b c : ℝ} {n : ℕ}
    (d e f g : ℤ) (hc : c ≠ 0) (hL : L ^ 2 = n) (hirr : Irrational L)
    (hP : a ^ 2 + b ^ 2 = c ^ 2)
    (h0 : L * a = (d : ℝ) * b + (e : ℝ) * c)
    (h1 : L * b = (g : ℝ) * a + (f : ℝ) * c) :
    2 * e * f * (d + g) = 0 := by
  let s : ℝ := n - (d : ℝ) * g
  have ha : s * a = ((d : ℝ) * f + (e : ℝ) * L) * c := by
    dsimp [s]
    linear_combination L * h0 + (d : ℝ) * h1 - a * hL
  have hb : s * b = ((e : ℝ) * g + (f : ℝ) * L) * c := by
    dsimp [s]
    linear_combination (g : ℝ) * h0 + L * h1 - b * hL
  have hvec : ((d : ℝ) * f + (e : ℝ) * L) ^ 2 +
      ((e : ℝ) * g + (f : ℝ) * L) ^ 2 = s ^ 2 := by
    apply mul_right_cancel₀ (pow_ne_zero 2 hc)
    have ha2 := congrArg (fun x : ℝ => x ^ 2) ha
    have hb2 := congrArg (fun x : ℝ => x ^ 2) hb
    linear_combination -ha2 - hb2 + s ^ 2 * hP
  have hcoeff : ((2 * e * f * (d + g) : ℤ) : ℝ) * L =
      (((n : ℤ) - d * g) ^ 2 - d ^ 2 * f ^ 2 - e ^ 2 * g ^ 2 -
        (e ^ 2 + f ^ 2) * n : ℤ) := by
    push_cast
    dsimp [s] at hvec
    linear_combination hvec - ((e : ℝ) ^ 2 + (f : ℝ) ^ 2) * hL
  exact (int_coefficients_of_irrational hirr _ _ hcoeff).1

theorem right_rows_alternatives {L a b c : ℝ} {n : ℕ}
    (d e f g : ℤ) (hd : 0 ≤ d) (hf : 0 < f) (hg : 0 ≤ g)
    (hc : c ≠ 0) (hL : L ^ 2 = n) (hirr : Irrational L)
    (hP : a ^ 2 + b ^ 2 = c ^ 2)
    (h0 : L * a = (d : ℝ) * b + (e : ℝ) * c)
    (h1 : L * b = (g : ℝ) * a + (f : ℝ) * c) :
    e = 0 ∨ d = 0 ∧ g = 0 := by
  have hc := right_rows_irrational_coefficient d e f g hc hL hirr hP h0 h1
  rcases mul_eq_zero.mp hc with hc | hc
  · rcases mul_eq_zero.mp hc with hc | hc
    · have he : e = 0 := (mul_eq_zero.mp hc).resolve_left (by decide)
      exact Or.inl he
    · exact False.elim (hf.ne' hc)
  · exact Or.inr ⟨by omega, by omega⟩

theorem biquadratic_rows_count {L a b c : ℝ} {n : ℕ} (e f : ℤ)
    (hc : c ≠ 0) (hL : L ^ 2 = n) (hP : a ^ 2 + b ^ 2 = c ^ 2)
    (h0 : L * a = (e : ℝ) * c) (h1 : L * b = (f : ℝ) * c) :
    (n : ℤ) = e ^ 2 + f ^ 2 := by
  have heq : (n : ℝ) = (e : ℝ) ^ 2 + (f : ℝ) ^ 2 := by
    apply mul_right_cancel₀ (pow_ne_zero 2 hc)
    have ha2 := congrArg (fun x : ℝ => x ^ 2) h0
    have hb2 := congrArg (fun x : ℝ => x ^ 2) h1
    linear_combination ha2 + hb2 - L ^ 2 * hP - c ^ 2 * hL
  exact_mod_cast heq

theorem biquadratic_rows_ratio {L a b c : ℝ} (e f : ℤ)
    (hb : b ≠ 0) (hc : c ≠ 0) (hf : f ≠ 0)
    (h0 : L * a = (e : ℝ) * c) (h1 : L * b = (f : ℝ) * c) :
    a / b = (e : ℝ) / f := by
  apply (div_eq_div_iff hb (by exact_mod_cast hf)).mpr
  apply mul_right_cancel₀ hc
  linear_combination b * h0 - a * h1

end Erdos633b
