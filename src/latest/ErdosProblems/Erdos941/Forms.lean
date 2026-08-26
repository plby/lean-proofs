import ErdosProblems.Erdos941.Basic

/-!
# Integral maps from spheres to the four powerful ternary forms

These lemmas check the arithmetic maps only. Existence of sphere points meeting
their congruence conditions is a separate counting problem.
-/

namespace Erdos941

/-- The norm of an integral vector with three coordinates. -/
def norm3 (A B C : ℤ) : ℤ := A ^ 2 + B ^ 2 + C ^ 2

theorem norm3_nonneg (A B C : ℤ) : 0 ≤ norm3 A B C := by
  unfold norm3
  positivity

theorem binary_norm_identity (a b A B : ℤ) :
    (a * A + b * B) ^ 2 + (-b * A + a * B) ^ 2 =
      (a ^ 2 + b ^ 2) * (A ^ 2 + B ^ 2) := by ring

theorem sphere_to_cube_form {q n a b A B C : ℤ} (hq : q ≠ 0)
    (hab : a ^ 2 + b ^ 2 = q) (hv : norm3 A B C = q * n)
    (hx : q ∣ a * A + b * B) (hy : q ∣ -b * A + a * B)
    (hz : q ^ 2 ∣ C) : ∃ x y z : ℤ, x ^ 2 + y ^ 2 + q ^ 3 * z ^ 2 = n := by
  obtain ⟨x, hx⟩ := hx
  obtain ⟨y, hy⟩ := hy
  obtain ⟨z, hz⟩ := hz
  refine ⟨x, y, z, ?_⟩
  have hbin := binary_norm_identity a b A B
  rw [hab, hx, hy] at hbin
  have hcancel : q ^ 2 * (x ^ 2 + y ^ 2 + q ^ 3 * z ^ 2 - n) = 0 := by
    dsimp [norm3] at hv
    linear_combination hbin + q * hv - q * (C + q ^ 2 * z) * hz
  have : x ^ 2 + y ^ 2 + q ^ 3 * z ^ 2 - n = 0 :=
    (mul_eq_zero.mp hcancel).resolve_left (pow_ne_zero _ hq)
  linarith

private theorem five_sign {A B : ℤ} (h : (5 : ℤ) ∣ A ^ 2 + B ^ 2) :
    (5 : ℤ) ∣ A + 2 * B ∨ (5 : ℤ) ∣ A - 2 * B := by
  have hp : Prime (5 : ℤ) := by norm_num
  have hd : (5 : ℤ) ∣ (A + 2 * B) * (A - 2 * B) := by
    rw [show (A + 2 * B) * (A - 2 * B) = (A ^ 2 + B ^ 2) - 5 * B ^ 2 by ring]
    exact dvd_sub h (dvd_mul_right _ _)
  exact hp.dvd_mul.mp hd

private theorem thirteen_sign {A B : ℤ} (h : (13 : ℤ) ∣ A ^ 2 + B ^ 2) :
    (13 : ℤ) ∣ 2 * A + 3 * B ∨ (13 : ℤ) ∣ 2 * A - 3 * B := by
  have hp : Prime (13 : ℤ) := by norm_num
  have hd : (13 : ℤ) ∣ (2 * A + 3 * B) * (2 * A - 3 * B) := by
    rw [show (2 * A + 3 * B) * (2 * A - 3 * B) =
      4 * (A ^ 2 + B ^ 2) - 13 * B ^ 2 by ring]
    exact dvd_sub (dvd_mul_of_dvd_right h 4) (dvd_mul_right _ _)
  exact hp.dvd_mul.mp hd

private theorem sphere_binary_divisibility {q n A B C : ℤ}
    (hv : norm3 A B C = q * n) (hz : q ^ 2 ∣ C) : q ∣ A ^ 2 + B ^ 2 := by
  have hqC : q ∣ C := (dvd_pow_self q (by omega : 2 ≠ 0)).trans hz
  have hqC2 : q ∣ C ^ 2 := dvd_pow hqC (by omega : 2 ≠ 0)
  have hqv : q ∣ norm3 A B C := by rw [hv]; exact dvd_mul_right _ _
  simpa only [norm3, add_sub_cancel_right] using dvd_sub hqv hqC2

theorem sphere_five_to_form {n A B C : ℤ}
    (hv : norm3 A B C = 5 * n) (hz : (25 : ℤ) ∣ C) :
    ∃ x y z : ℤ, x ^ 2 + y ^ 2 + 125 * z ^ 2 = n := by
  have hz' : (5 : ℤ) ^ 2 ∣ C := by norm_num; exact hz
  have hbin := sphere_binary_divisibility hv hz'
  have base : ∀ B' : ℤ, norm3 A B' C = 5 * n → (5 : ℤ) ∣ A + 2 * B' →
      ∃ x y z : ℤ, x ^ 2 + y ^ 2 + 125 * z ^ 2 = n := by
    intro B' hv' hx
    have hy : (5 : ℤ) ∣ -2 * A + B' := by
      rw [show -2 * A + B' = (A + 2 * B') * (-2) + 5 * B' by ring]
      exact dvd_add (dvd_mul_of_dvd_left hx (-2)) (dvd_mul_right _ _)
    simpa using sphere_to_cube_form (by norm_num : (5 : ℤ) ≠ 0)
      (by norm_num : (1 : ℤ) ^ 2 + 2 ^ 2 = 5) hv' (by simpa using hx)
      (by simpa using hy) hz'
  rcases five_sign hbin with hx | hx
  · exact base B hv hx
  · apply base (-B)
    · simpa [norm3] using hv
    · simpa [sub_eq_add_neg] using hx

theorem sphere_thirteen_to_form {n A B C : ℤ}
    (hv : norm3 A B C = 13 * n) (hz : (169 : ℤ) ∣ C) :
    ∃ x y z : ℤ, x ^ 2 + y ^ 2 + 2197 * z ^ 2 = n := by
  have hz' : (13 : ℤ) ^ 2 ∣ C := by norm_num; exact hz
  have hbin := sphere_binary_divisibility hv hz'
  have base : ∀ B' : ℤ, norm3 A B' C = 13 * n → (13 : ℤ) ∣ 2 * A + 3 * B' →
      ∃ x y z : ℤ, x ^ 2 + y ^ 2 + 2197 * z ^ 2 = n := by
    intro B' hv' hx
    have hy : (13 : ℤ) ∣ -3 * A + 2 * B' := by
      rw [show -3 * A + 2 * B' =
        (2 * A + 3 * B') * (-21) + 13 * (3 * A + 5 * B') by ring]
      exact dvd_add (dvd_mul_of_dvd_left hx (-21)) (dvd_mul_right _ _)
    simpa using sphere_to_cube_form (by norm_num : (13 : ℤ) ≠ 0)
      (by norm_num : (2 : ℤ) ^ 2 + 3 ^ 2 = 13) hv' hx hy hz'
  rcases thirteen_sign hbin with hx | hx
  · exact base B hv hx
  · apply base (-B)
    · simpa [norm3] using hv
    · simpa [sub_eq_add_neg] using hx

/-- Orthogonal coordinates with squared lengths 42, 14, and 3. -/
def alpha (A B C : ℤ) : ℤ := -5 * A - 4 * B + C
def beta (A B C : ℤ) : ℤ := -A + 2 * B + 3 * C
def lambda (A B C : ℤ) : ℤ := -A + B - C

theorem orthogonal_norm_identity (A B C : ℤ) :
    alpha A B C ^ 2 + 3 * beta A B C ^ 2 + 14 * lambda A B C ^ 2 =
      42 * norm3 A B C := by
  unfold alpha beta lambda norm3
  ring

theorem sphere_seven_to_form {m A B C : ℤ} (hv : norm3 A B C = 7 * m)
    (ha : (28 : ℤ) ∣ alpha A B C) (hb : (84 : ℤ) ∣ beta A B C)
    (hc : (49 : ℤ) ∣ lambda A B C) :
    ∃ x y z : ℤ, 8 * x ^ 2 + 216 * y ^ 2 + 343 * z ^ 2 = 3 * m := by
  obtain ⟨x, hx⟩ := ha
  obtain ⟨y, hy⟩ := hb
  obtain ⟨z, hz⟩ := hc
  refine ⟨x, y, z, ?_⟩
  have h := orthogonal_norm_identity A B C
  rw [hx, hy, hz, hv] at h
  nlinarith only [h]

theorem sphere_fourteen_to_form {m A B C : ℤ} (hv : norm3 A B C = 14 * m)
    (ha : (14 : ℤ) ∣ alpha A B C) (hb : (42 : ℤ) ∣ beta A B C)
    (hc : (196 : ℤ) ∣ lambda A B C) :
    ∃ x y z : ℤ, x ^ 2 + 27 * y ^ 2 + 2744 * z ^ 2 = 3 * m := by
  obtain ⟨x, hx⟩ := ha
  obtain ⟨y, hy⟩ := hb
  obtain ⟨z, hz⟩ := hc
  refine ⟨x, y, z, ?_⟩
  have h := orthogonal_norm_identity A B C
  rw [hx, hy, hz, hv] at h
  nlinarith only [h]

/-- The target conditions at 7 together with the required parity and turn. -/
def SevenTarget (A B C : ℤ) : Prop :=
  (7 : ℤ) ∣ A - 3 * B ∧ (7 : ℤ) ∣ C - 5 * B ∧
    (49 : ℤ) ∣ lambda A B C ∧ (3 : ℤ) ∣ A + B ∧ (3 : ℤ) ∣ C ∧
      (4 : ℤ) ∣ C - A ∧ (2 : ℤ) ∣ A - B

private theorem alpha_div_seven {A B C : ℤ}
    (hA : (7 : ℤ) ∣ A - 3 * B) (hC : (7 : ℤ) ∣ C - 5 * B) :
    (7 : ℤ) ∣ alpha A B C := by
  dsimp [alpha]
  omega

private theorem beta_div_seven {A B C : ℤ}
    (hA : (7 : ℤ) ∣ A - 3 * B) (hC : (7 : ℤ) ∣ C - 5 * B) :
    (7 : ℤ) ∣ beta A B C := by
  dsimp [beta]
  omega

private theorem beta_div_three {A B C : ℤ}
    (hAB : (3 : ℤ) ∣ A + B) (hC : (3 : ℤ) ∣ C) :
    (3 : ℤ) ∣ beta A B C := by
  dsimp [beta]
  omega

private theorem alpha_div_four {A B C : ℤ} (h : (4 : ℤ) ∣ C - A) :
    (4 : ℤ) ∣ alpha A B C := by
  dsimp [alpha]
  omega

private theorem beta_div_four {A B C : ℤ} (h : (4 : ℤ) ∣ C - A)
    (hpar : (2 : ℤ) ∣ A - B) : (4 : ℤ) ∣ beta A B C := by
  dsimp [beta]
  omega

private theorem beta_div_two {A B C : ℤ} (h : (4 : ℤ) ∣ C - A) :
    (2 : ℤ) ∣ beta A B C := by
  dsimp [beta]
  omega

private theorem lambda_div_four {A B C : ℤ} (hA : A % 2 = 1)
    (hB : B % 4 = 2) (hCA : (4 : ℤ) ∣ C - A) :
    (4 : ℤ) ∣ lambda A B C := by
  dsimp [lambda]
  omega

private theorem div_twenty_eight {n : ℤ} (h7 : 7 ∣ n) (h4 : 4 ∣ n) : 28 ∣ n := by
  omega

private theorem div_eighty_four {n : ℤ} (h7 : 7 ∣ n) (h4 : 4 ∣ n) (h3 : 3 ∣ n) :
    84 ∣ n := by omega

private theorem div_fourteen {n : ℤ} (h7 : 7 ∣ n) (h2 : 2 ∣ n) : 14 ∣ n := by omega

private theorem div_forty_two {n : ℤ} (h7 : 7 ∣ n) (h2 : 2 ∣ n) (h3 : 3 ∣ n) :
    42 ∣ n := by omega

private theorem div_one_ninety_six {n : ℤ} (h49 : 49 ∣ n) (h4 : 4 ∣ n) :
    196 ∣ n := by omega

theorem seven_target_divisibility {A B C : ℤ} (h : SevenTarget A B C) :
    (28 : ℤ) ∣ alpha A B C ∧ (84 : ℤ) ∣ beta A B C ∧
      (49 : ℤ) ∣ lambda A B C := by
  obtain ⟨hA, hC, hL, hAB, hC3, hCA, hpar⟩ := h
  exact ⟨div_twenty_eight (alpha_div_seven hA hC) (alpha_div_four hCA),
    div_eighty_four (beta_div_seven hA hC) (beta_div_four hCA hpar)
      (beta_div_three hAB hC3), hL⟩

/-- For the sphere of norm `14m`, the middle coordinate is even and the others
are odd and equal modulo four. -/
def FourteenTarget (A B C : ℤ) : Prop :=
  (7 : ℤ) ∣ A - 3 * B ∧ (7 : ℤ) ∣ C - 5 * B ∧
    (49 : ℤ) ∣ lambda A B C ∧ (3 : ℤ) ∣ A + B ∧ (3 : ℤ) ∣ C ∧
      A % 2 = 1 ∧ B % 4 = 2 ∧ (4 : ℤ) ∣ C - A

theorem fourteen_target_divisibility {A B C : ℤ} (h : FourteenTarget A B C) :
    (14 : ℤ) ∣ alpha A B C ∧ (42 : ℤ) ∣ beta A B C ∧
      (196 : ℤ) ∣ lambda A B C := by
  obtain ⟨hA, hC, hL, hAB, hC3, hAo, hB, hCA⟩ := h
  exact ⟨div_fourteen (alpha_div_seven hA hC)
    ((by norm_num : (2 : ℤ) ∣ 4).trans (alpha_div_four hCA)),
    div_forty_two (beta_div_seven hA hC) (beta_div_two hCA) (beta_div_three hAB hC3),
    div_one_ninety_six hL (lambda_div_four hAo hB hCA)⟩

theorem seven_target_to_form {m A B C : ℤ} (hv : norm3 A B C = 7 * m)
    (h : SevenTarget A B C) :
    ∃ x y z : ℤ, 8 * x ^ 2 + 216 * y ^ 2 + 343 * z ^ 2 = 3 * m := by
  obtain ⟨ha, hb, hc⟩ := seven_target_divisibility h
  exact sphere_seven_to_form hv ha hb hc

theorem fourteen_target_to_form {m A B C : ℤ} (hv : norm3 A B C = 14 * m)
    (h : FourteenTarget A B C) :
    ∃ x y z : ℤ, x ^ 2 + 27 * y ^ 2 + 2744 * z ^ 2 = 3 * m := by
  obtain ⟨ha, hb, hc⟩ := fourteen_target_divisibility h
  exact sphere_fourteen_to_form hv ha hb hc

theorem representable_of_five_form {n : ℕ} (hn : 0 < n) {x y z : ℤ}
    (h : x ^ 2 + y ^ 2 + 125 * z ^ 2 = n) : Representable n := by
  apply representable_of_int_cube_form hn 1 1 5 x y z
  norm_num
  exact h

theorem representable_of_thirteen_form {n : ℕ} (hn : 0 < n) {x y z : ℤ}
    (h : x ^ 2 + y ^ 2 + 2197 * z ^ 2 = n) : Representable n := by
  apply representable_of_int_cube_form hn 1 1 13 x y z
  norm_num
  exact h

theorem representable_of_seven_form {n : ℕ} (hn : 0 < n) {x y z : ℤ}
    (h : 8 * x ^ 2 + 216 * y ^ 2 + 343 * z ^ 2 = n) : Representable n := by
  apply representable_of_int_cube_form hn 2 6 7 x y z
  norm_num
  exact h

theorem representable_of_fourteen_form {n : ℕ} (hn : 0 < n) {x y z : ℤ}
    (h : x ^ 2 + 27 * y ^ 2 + 2744 * z ^ 2 = n) : Representable n := by
  apply representable_of_int_cube_form hn 1 3 14 x y z
  norm_num
  exact h

end Erdos941
