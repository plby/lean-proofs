import ErdosProblems.Erdos633.Rationality

/-!
# The four 120-degree rationality arguments from two boundary invariants

Normalize the longest tile side to one, so `a²+ab+b²=1`. The two integer
equations in each theorem are the consequences of the direction characters.
Theorems here prove their algebraic consequences, not the still separate
assertion that every geometric tiling supplies those equations and counts.
-/

namespace Erdos633

/-- W: the two signed boundary sums make `a` and `ℓ/b` rational. -/
theorem oneTwenty_W_invariant_rational (a b ℓ : ℝ) (hb : 0 < b) (hℓ : 0 < ℓ)
    (m n : ℤ) (hm : (m : ℝ) = ℓ * (1 - a) / b)
    (hn : (n : ℝ) = ℓ * (1 + a) / b) :
    a ∈ rationalReals ∧ ℓ / b ∈ rationalReals := by
  have hsum : ((m : ℝ) + n) / 2 = ℓ / b := by rw [hm, hn]; ring
  have hratio : ℓ / b ∈ rationalReals := by
    rw [← hsum]
    exact rationalReals.div_mem
      (rationalReals.add_mem (rationalReals_int m) (rationalReals_int n))
      (rationalReals_nat 2)
  have hdiff : ((n : ℝ) - m) / 2 = (ℓ / b) * a := by rw [hm, hn]; ring
  have hmul : (ℓ / b) * a ∈ rationalReals := by
    rw [← hdiff]
    exact rationalReals.div_mem
      (rationalReals.sub_mem (rationalReals_int n) (rationalReals_int m))
      (rationalReals_nat 2)
  exact ⟨rational_of_mul hratio (ne_of_gt (div_pos hℓ hb)) hmul, hratio⟩

/-- W: a boundary edge of length one supplies the positive rational term. -/
theorem oneTwenty_W_rational (a b ℓ : ℝ) (ha : 0 < a) (hb : 0 < b) (hℓ : 0 < ℓ)
    (m n : ℤ) (hm : (m : ℝ) = ℓ * (1 - a) / b)
    (hn : (n : ℝ) = ℓ * (1 + a) / b)
    (p q r : ℕ) (hr : 0 < r) (hedge : ℓ * a = p * a + q * b + r) :
    a ∈ rationalReals ∧ b ∈ rationalReals := by
  obtain ⟨har, hlr⟩ := oneTwenty_W_invariant_rational a b ℓ hb hℓ m n hm hn
  refine ⟨har, rational_of_positive_boundary
    (rationalReals.sub_mem (rationalReals.mul_mem hlr har) (rationalReals_nat q))
    (rationalReals.add_mem (rationalReals.mul_mem (rationalReals_nat p) har)
      (rationalReals_nat r)) ?_ ?_⟩
  · have hrR : (0 : ℝ) < r := by exact_mod_cast hr
    positivity
  · have hb0 := ne_of_gt hb
    field_simp
    nlinarith only [hedge]

/-- Y: the two integer invariants determine the scale and the first side. -/
theorem oneTwenty_Y_invariant_rational (a ℓ : ℝ) (hℓ : 0 < ℓ)
    (m n : ℤ) (hm : (m : ℝ) = -ℓ * (1 - a))
    (hn : (n : ℝ) = ℓ * (1 + a)) :
    ℓ ∈ rationalReals ∧ a ∈ rationalReals := by
  have hdiff : ((n : ℝ) - m) / 2 = ℓ := by rw [hm, hn]; ring
  have hlr : ℓ ∈ rationalReals := by
    rw [← hdiff]
    exact rationalReals.div_mem
      (rationalReals.sub_mem (rationalReals_int n) (rationalReals_int m))
      (rationalReals_nat 2)
  have hsum : ((m : ℝ) + n) / 2 = ℓ * a := by rw [hm, hn]; ring
  have hmul : ℓ * a ∈ rationalReals := by
    rw [← hsum]
    exact rationalReals.div_mem
      (rationalReals.add_mem (rationalReals_int m) (rationalReals_int n))
      (rationalReals_nat 2)
  exact ⟨hlr, rational_of_mul hlr (ne_of_gt hℓ) hmul⟩

/-- Y: area forces the remaining side to be rational. -/
theorem oneTwenty_Y_rational (a b ℓ : ℝ) (ha : 0 < a) (hℓ : 0 < ℓ)
    (hconic : a ^ 2 + a * b + b ^ 2 = 1)
    (m n : ℤ) (hm : (m : ℝ) = -ℓ * (1 - a))
    (hn : (n : ℝ) = ℓ * (1 + a)) (N : ℕ)
    (harea : (N : ℝ) = ℓ ^ 2 * (a + b) * (2 * a + b)) :
    a ∈ rationalReals ∧ b ∈ rationalReals := by
  obtain ⟨hlr, har⟩ := oneTwenty_Y_invariant_rational a ℓ hℓ m n hm hn
  have hscale : ℓ ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hℓ)
  have hquot : (N : ℝ) / ℓ ^ 2 = 1 + a ^ 2 + 2 * a * b := by
    apply (div_eq_iff hscale).mpr
    rw [harea]
    linear_combination ℓ ^ 2 * hconic
  have hrat : 2 * a * b ∈ rationalReals := by
    have h := rationalReals.sub_mem
      (rationalReals.div_mem (rationalReals_nat N) (rationalReals.pow_mem hlr 2))
      (rationalReals.add_mem rationalReals.one_mem (rationalReals.pow_mem har 2))
    rw [hquot] at h
    convert h using 1
    ring
  exact ⟨har, rational_of_mul
    (rationalReals.mul_mem (rationalReals_nat 2) har) (by positivity) hrat⟩

/-- U₂: its two integers determine the scale and `2a+b`. -/
theorem oneTwenty_U_two_invariant_rational (a b ℓ : ℝ) (hℓ : 0 < ℓ)
    (m n : ℤ) (hm : (m : ℝ) = -ℓ * (2 * a + b - 1))
    (hn : (n : ℝ) = ℓ * (2 * a + b + 1)) :
    ℓ ∈ rationalReals ∧ 2 * a + b ∈ rationalReals := by
  have hsum : ((m : ℝ) + n) / 2 = ℓ := by rw [hm, hn]; ring
  have hlr : ℓ ∈ rationalReals := by
    rw [← hsum]
    exact rationalReals.div_mem
      (rationalReals.add_mem (rationalReals_int m) (rationalReals_int n))
      (rationalReals_nat 2)
  have hdiff : ((n : ℝ) - m) / 2 = ℓ * (2 * a + b) := by rw [hm, hn]; ring
  have hmul : ℓ * (2 * a + b) ∈ rationalReals := by
    rw [← hdiff]
    exact rationalReals.div_mem
      (rationalReals.sub_mem (rationalReals_int n) (rationalReals_int m))
      (rationalReals_nat 2)
  exact ⟨hlr, rational_of_mul hlr (ne_of_gt hℓ) hmul⟩

/-- U₂: its area equation completes rationality. -/
theorem oneTwenty_U_two_rational (a b ℓ : ℝ) (ha : 0 < a) (hb : 0 < b) (hℓ : 0 < ℓ)
    (hconic : a ^ 2 + a * b + b ^ 2 = 1)
    (m n : ℤ) (hm : (m : ℝ) = -ℓ * (2 * a + b - 1))
    (hn : (n : ℝ) = ℓ * (2 * a + b + 1)) (N : ℕ)
    (harea : (N : ℝ) = 3 * ℓ ^ 2 * (a + b) * (a + 2 * b)) :
    a ∈ rationalReals ∧ b ∈ rationalReals := by
  obtain ⟨hlr, hhr⟩ := oneTwenty_U_two_invariant_rational a b ℓ hℓ m n hm hn
  have hscale : 3 * ℓ ^ 2 ≠ 0 := by positivity
  have hquot : (N : ℝ) / (3 * ℓ ^ 2) = 1 + (2 * a + b) * b := by
    apply (div_eq_iff hscale).mpr
    rw [harea]
    linear_combination 3 * ℓ ^ 2 * hconic
  have hprod : (2 * a + b) * b ∈ rationalReals := by
    have h := rationalReals.sub_mem
      (rationalReals.div_mem (rationalReals_nat N)
        (rationalReals.mul_mem (rationalReals_nat 3) (rationalReals.pow_mem hlr 2)))
      rationalReals.one_mem
    norm_num only [Nat.cast_ofNat] at h
    rw [hquot] at h
    simpa using h
  have hbr := rational_of_mul hhr (by positivity : 2 * a + b ≠ 0) hprod
  refine ⟨?_, hbr⟩
  have h := rationalReals.div_mem (rationalReals.sub_mem hhr hbr) (rationalReals_nat 2)
  convert h using 1
  ring

/-- Z: the scale and the side difference are rational. -/
theorem oneTwenty_Z_invariant_rational (a b ℓ : ℝ) (hℓ : 0 < ℓ)
    (m n : ℤ) (hm : (m : ℝ) = -ℓ * (1 - a + b))
    (hn : (n : ℝ) = -ℓ * (1 + a - b)) :
    ℓ ∈ rationalReals ∧ a - b ∈ rationalReals := by
  apply oneTwenty_Y_invariant_rational (a - b) ℓ hℓ m (-n)
  · linear_combination hm
  · push_cast
    linear_combination -hn

/-- Z: two boundary sides have opposite coefficients of a hypothetical
irrational side. Nonnegative edge counts exclude this possibility. -/
theorem oneTwenty_Z_rational (a b ℓ : ℝ) (hℓ : 0 < ℓ) (hab : a ≠ b)
    (hconic : a ^ 2 + a * b + b ^ 2 = 1)
    (m n : ℤ) (hm : (m : ℝ) = -ℓ * (1 - a + b))
    (hn : (n : ℝ) = -ℓ * (1 + a - b))
    (p q r u v w : ℕ)
    (hX : ℓ * a * (a + 2 * b) = p * a + q * b + r)
    (hY : ℓ * b * (2 * a + b) = u * a + v * b + w) :
    a ∈ rationalReals ∧ b ∈ rationalReals := by
  obtain ⟨hlr, hdr⟩ := oneTwenty_Z_invariant_rational a b ℓ hℓ m n hm hn
  have hprod : a * b ∈ rationalReals := by
    have h := rationalReals.div_mem
      (rationalReals.sub_mem rationalReals.one_mem (rationalReals.pow_mem hdr 2))
      (rationalReals_nat 3)
    convert h using 1
    nlinarith only [hconic]
  have htr := rationalReals.mul_mem hlr hdr
  have hLr := rationalReals.mul_mem
    (rationalReals.mul_mem (rationalReals_nat 3) hlr) hprod
  have har : a ∈ rationalReals := by
    by_contra hai
    have hz : ℓ * (a - b) = 0 := opposite_boundary_coefficients hai htr
      (rationalReals.sub_mem
        (rationalReals.sub_mem (rationalReals_nat r)
          (rationalReals.mul_mem (rationalReals_nat q) hdr)) hLr)
      (rationalReals.sub_mem
        (rationalReals.sub_mem
          (rationalReals.sub_mem (rationalReals_nat w)
            (rationalReals.mul_mem (rationalReals_nat v) hdr)) hLr)
        (rationalReals.mul_mem htr hdr))
      (p + q) (u + v) (by push_cast; linear_combination hX)
      (by push_cast; linear_combination hY)
    exact (mul_ne_zero (ne_of_gt hℓ) (sub_ne_zero.mpr hab)) hz
  refine ⟨har, ?_⟩
  have h := rationalReals.sub_mem har hdr
  simpa using h

end Erdos633
