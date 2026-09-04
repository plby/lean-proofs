import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Arithmetic optimization in the Deléglise interval-cover argument

For `h = r+s+q`, the overlap count produces

`D = (r+1)(s+q) + s*q`.

The two-distance parameters `s,q` are positive and coprime.  This file proves
that `D` is at most the reciprocal of Deléglise's optimal interval length.
-/

namespace Erdos336.Problem336

/-- The quadratic expression which occurs in Deléglise's overlap count. -/
def delegliseD (r s q : ℕ) : ℕ := (r + 1) * (s + q) + s * q

private lemma sq_nonneg_int (x : ℤ) : 0 ≤ x ^ 2 := sq_nonneg x

private lemma one_le_sq_of_ne_zero {x : ℤ} (hx : x ≠ 0) : 1 ≤ x ^ 2 := by
  have hx_cases : x ≤ -1 ∨ 1 ≤ x := by omega
  rcases hx_cases with hxneg | hxpos <;> nlinarith

/-- The elementary three-residue-class optimization behind `L(h)`.

For `h ≡ 2 (mod 3)` the exceptional real maximizer would have `s=q`; the
coprimality hypothesis excludes it (apart from `h=2`, which is outside the
stated range), yielding the correction by two in the numerator. -/
theorem delegliseD_bound
    (h r s q : ℕ)
    (h_eq : h = r + s + q)
    (h_ge : 3 ≤ h)
    (s_pos : 0 < s)
    (q_pos : 0 < q)
    (cop : s.Coprime q) :
    3 * delegliseD r s q ≤
      h * (h + 2) - (if h % 3 = 2 then 2 else 0) := by
  have hs1 : 1 ≤ s := s_pos
  have hq1 : 1 ≤ q := q_pos
  let A : ℤ := 3 * ((s + q : ℕ) : ℤ) - 2 * ((h + 1 : ℕ) : ℤ)
  let B : ℤ := (s : ℤ) - (q : ℤ)
  have ident :
      (4 : ℤ) * ((h : ℤ) * ((h : ℤ) + 2)) -
          12 * (delegliseD r s q : ℤ) = A ^ 2 + 3 * B ^ 2 - 4 := by
    dsimp [A, B, delegliseD]
    push_cast
    nlinarith
  have hB0 : B = 0 → s = q := by
    intro hb
    dsimp [B] at hb
    exact_mod_cast (sub_eq_zero.mp hb)
  have cop_self_one : s = q → s = 1 := by
    intro heq
    subst q
    exact (Nat.coprime_self s).mp cop
  by_cases hmod : h % 3 = 2
  · simp only [if_pos hmod]
    have h_ge5 : 5 ≤ h := by omega
    have target_sep : 12 ≤ A ^ 2 + 3 * B ^ 2 := by
      by_cases hA : A = 0
      · have hbne : B ≠ 0 := by
          intro hb
          have heq := hB0 hb
          have hs : s = 1 := cop_self_one heq
          have hq : q = 1 := heq ▸ hs
          dsimp [A] at hA
          omega
        have b_even : ∃ z : ℤ, B = 2 * z := by
          obtain ⟨k, hk⟩ : ∃ k, h = 3 * k + 2 := by
            use h / 3
            omega
          use (s : ℤ) - ((k + 1 : ℕ) : ℤ)
          dsimp [A] at hA
          dsimp [B]
          push_cast at hA ⊢
          omega
        obtain ⟨z, hz⟩ := b_even
        have hz0 : z ≠ 0 := by
          intro hz0
          apply hbne
          rw [hz, hz0]
          norm_num
        have hzsq : 1 ≤ z ^ 2 := one_le_sq_of_ne_zero hz0
        rw [hA, hz]
        nlinarith [sq_nonneg_int z]
      · have hA3 : ∃ z : ℤ, A = 3 * z := by
          obtain ⟨k, hk⟩ : ∃ k, h = 3 * k + 2 := by
            use h / 3
            omega
          use ((s + q : ℕ) : ℤ) - 2 * ((k + 1 : ℕ) : ℤ)
          dsimp [A]
          push_cast
          omega
        obtain ⟨z, hz⟩ := hA3
        have hz0 : z ≠ 0 := by
          intro hz0
          apply hA
          rw [hz, hz0]
          norm_num
        have hzsq : 1 ≤ z ^ 2 := one_le_sq_of_ne_zero hz0
        by_cases hB : B = 0
        · have heq := hB0 hB
          have hs : s = 1 := cop_self_one heq
          have hq : q = 1 := heq ▸ hs
          dsimp [A, B] at *
          push_cast at *
          nlinarith
        · have hbsq : 1 ≤ B ^ 2 := one_le_sq_of_ne_zero hB
          rw [hz]
          nlinarith [sq_nonneg_int z, sq_nonneg_int B]
    have cast_goal :
        (3 : ℤ) * (delegliseD r s q : ℤ) ≤
          (h : ℤ) * ((h : ℤ) + 2) - 2 := by
      nlinarith
    have cast_goal_add :
        (3 : ℤ) * (delegliseD r s q : ℤ) + 2 ≤
          (h : ℤ) * ((h : ℤ) + 2) := by
      omega
    have nat_goal_add : 3 * delegliseD r s q + 2 ≤ h * (h + 2) := by
      exact_mod_cast cast_goal_add
    omega
  · have hres : h % 3 = 0 ∨ h % 3 = 1 := by omega
    simp only [if_neg hmod]
    have target_sep : 4 ≤ A ^ 2 + 3 * B ^ 2 := by
      by_cases hB : B = 0
      · have heq := hB0 hB
        have hs : s = 1 := cop_self_one heq
        have hq : q = 1 := heq ▸ hs
        dsimp [A, B]
        push_cast
        nlinarith
      · have hbsq : 1 ≤ B ^ 2 := one_le_sq_of_ne_zero hB
        have hAne : A ≠ 0 := by
          intro hAz
          dsimp [A] at hAz
          rcases hres with h0 | h1
          · obtain ⟨k, hk⟩ : ∃ k, h = 3 * k := by
              use h / 3
              omega
            push_cast at hAz
            omega
          · obtain ⟨k, hk⟩ : ∃ k, h = 3 * k + 1 := by
              use h / 3
              omega
            push_cast at hAz
            omega
        have hAsq : 1 ≤ A ^ 2 := one_le_sq_of_ne_zero hAne
        nlinarith
    have cast_goal :
        (3 : ℤ) * (delegliseD r s q : ℤ) ≤
          (h : ℤ) * ((h : ℤ) + 2) := by
      nlinarith
    exact_mod_cast cast_goal

end Erdos336.Problem336
