/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 482.
https://www.erdosproblems.com/forum/thread/482

Informal authors:
- R. L. Graham
- H. O. Pollak
- G. Rabinowitz
- E. Gilbert
- Thomas Stoll

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos482.md
-/
import Mathlib

/-!
# Erdős Problem 482: the Graham--Pollak recurrence

Graham and Pollak proved that the recurrence

`a 1 = 1`, `a (n + 1) = ⌊√2 * (a n + 1/2)⌋`

encodes the binary digits of `√2`: `a (2*n+1) - 2*a (2*n-1)` is the
`n`th digit, counting the leading digit as the first one.

We prove the stronger arbitrary-real binary theorem of Rabinowitz--Gilbert
and Stoll.  For every normalized `t ∈ [1,2)`, an explicit alternating
recurrence extracts the canonical Mathlib digits of `t`.  At `t = √2` its
two coefficients both simplify to `√2`, yielding the original recurrence.

References:

* R. L. Graham and H. O. Pollak, *Note on a nonlinear recurrence related
  to √2*, Math. Mag. 43 (1970), 143--145.
* T. Stoll, *On families of nonlinear recurrences related to digits*,
  J. Integer Sequences 8 (2005), Article 05.3.2.
* T. Stoll, *On a problem of Erdős and Graham concerning digits*,
  Acta Arith. 125 (2006), 89--100.
-/

namespace Erdos482

/-! ## The arbitrary-real binary recurrence -/

/-- The odd-step coefficient in the Rabinowitz--Gilbert/Stoll recurrence. -/
noncomputable def alpha (t : ℝ) : ℝ := 2 * (t + 1) / (t + 2)

/-- The even-step coefficient in the Rabinowitz--Gilbert/Stoll recurrence. -/
noncomputable def beta (t : ℝ) : ℝ := (t + 2) / (t + 1)

/-- Zero-based form of Stoll's binary recurrence: `stollBinary t k` is
the paper's `u_{k+1}`. -/
noncomputable def stollBinary (t : ℝ) : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
      ⌊(if Even n then alpha t else beta t) *
          ((stollBinary t n : ℝ) + 1 / 2)⌋₊

@[simp] lemma stollBinary_zero (t : ℝ) : stollBinary t 0 = 1 := rfl

lemma stollBinary_even_step (t : ℝ) (k : ℕ) :
    stollBinary t (2 * k + 1) =
      ⌊alpha t * ((stollBinary t (2 * k) : ℝ) + 1 / 2)⌋₊ := by
  rw [stollBinary]
  simp

lemma stollBinary_odd_step (t : ℝ) (k : ℕ) :
    stollBinary t (2 * k + 2) =
      ⌊beta t * ((stollBinary t (2 * k + 1) : ℝ) + 1 / 2)⌋₊ := by
  rw [show 2 * k + 2 = (2 * k + 1) + 1 by omega, stollBinary]
  simp

/-! ## Floor arithmetic -/

/-- Doubling a nonnegative real can add only one new binary digit to its
natural floor. -/
lemma floor_two_mul (y : ℝ) (hy : 0 ≤ y) :
    ⌊2 * y⌋₊ = 2 * ⌊y⌋₊ ∨ ⌊2 * y⌋₊ = 2 * ⌊y⌋₊ + 1 := by
  have hlo : 2 * ⌊y⌋₊ ≤ ⌊2 * y⌋₊ := by
    apply Nat.le_floor
    have hfloor : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy
    push_cast
    linarith
  have hhi : ⌊2 * y⌋₊ < 2 * ⌊y⌋₊ + 2 := by
    rw [Nat.floor_lt (by positivity)]
    have hylt : y < (⌊y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one y
    push_cast
    linarith
  omega

/-- The `alpha` branch advances
`P + ⌊tP/2⌋` to `P + ⌊tP⌋`. -/
lemma alpha_floor_step (t : ℝ) (ht1 : 1 ≤ t)
    (P : ℕ) (hP : 0 < P) :
    ⌊alpha t * ((P : ℝ) + (⌊t * P / 2⌋₊ : ℝ) + 1 / 2)⌋₊ =
      P + ⌊t * P⌋₊ := by
  have ht0 : 0 ≤ t := le_trans (by norm_num) ht1
  have hPR : (0 : ℝ) < P := by exact_mod_cast hP
  have hden : 0 < t + 2 := by linarith
  let y : ℝ := t * P / 2
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hty : t * P = 2 * y := by dsimp [y]; ring
  have hqle : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy
  have hylt : y < (⌊y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one y
  have hQle : (⌊2 * y⌋₊ : ℝ) ≤ 2 * y := Nat.floor_le (by positivity)
  have h2ylt : 2 * y < (⌊2 * y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one (2 * y)
  have harg :
      0 ≤ alpha t * ((P : ℝ) + (⌊y⌋₊ : ℝ) + 1 / 2) := by
    have ha : 0 ≤ alpha t := by
      dsimp [alpha]
      positivity
    have hsum : 0 ≤ (P : ℝ) + (⌊y⌋₊ : ℝ) + 1 / 2 := by positivity
    positivity
  have hdouble := floor_two_mul y hy
  rw [hty]
  norm_num
  change
    ⌊alpha t * ((P : ℝ) + (⌊y⌋₊ : ℝ) + 1 / 2)⌋₊ =
      P + ⌊2 * y⌋₊
  apply (Nat.floor_eq_iff harg).2
  rcases hdouble with hdouble | hdouble
  · constructor
    · push_cast
      rw [alpha, div_mul_eq_mul_div, le_div_iff₀ hden]
      rw [hdouble] at hQle h2ylt ⊢
      push_cast at hQle h2ylt ⊢
      nlinarith
    · push_cast
      rw [alpha, div_mul_eq_mul_div, div_lt_iff₀ hden]
      rw [hdouble] at hQle h2ylt ⊢
      push_cast at hQle h2ylt ⊢
      nlinarith
  · constructor
    · push_cast
      rw [alpha, div_mul_eq_mul_div, le_div_iff₀ hden]
      rw [hdouble] at hQle h2ylt ⊢
      push_cast at hQle h2ylt ⊢
      nlinarith
    · push_cast
      rw [alpha, div_mul_eq_mul_div, div_lt_iff₀ hden]
      rw [hdouble] at hQle h2ylt ⊢
      push_cast at hQle h2ylt ⊢
      nlinarith

/-- The `beta` branch advances `P + ⌊tP⌋` to
`2P + ⌊tP⌋`. -/
lemma beta_floor_step (t : ℝ) (ht1 : 1 ≤ t) (P : ℕ) (hP : 0 < P) :
    ⌊beta t * ((P : ℝ) + (⌊t * P⌋₊ : ℝ) + 1 / 2)⌋₊ =
      2 * P + ⌊t * P⌋₊ := by
  have ht0 : 0 ≤ t := le_trans (by norm_num) ht1
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht1
  have hPR : (0 : ℝ) < P := by exact_mod_cast hP
  have hden : 0 < t + 1 := by linarith
  have htp : 0 ≤ t * (P : ℝ) := mul_nonneg ht0 (le_of_lt hPR)
  have hqle : (⌊t * P⌋₊ : ℝ) ≤ t * P := Nat.floor_le htp
  have htplt : t * P < (⌊t * P⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one (t * P)
  have harg :
      0 ≤ beta t * ((P : ℝ) + (⌊t * P⌋₊ : ℝ) + 1 / 2) := by
    have hb : 0 ≤ beta t := by
      dsimp [beta]
      positivity
    positivity
  apply (Nat.floor_eq_iff harg).2
  constructor
  · push_cast
    rw [beta, div_mul_eq_mul_div, le_div_iff₀ hden]
    nlinarith
  · push_cast
    rw [beta, div_mul_eq_mul_div, div_lt_iff₀ hden]
    nlinarith

/-! ## Closed forms -/

/-- The two interlaced closed forms for Stoll's recurrence. -/
theorem stollBinary_closed_forms (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2)
    (k : ℕ) :
    stollBinary t (2 * k) =
        2 ^ k + ⌊t * (2 ^ k : ℕ) / 2⌋₊ ∧
      stollBinary t (2 * k + 1) =
        2 ^ k + ⌊t * (2 ^ k : ℕ)⌋₊ := by
  induction k with
  | zero =>
      have hhalf : ⌊t / 2⌋₊ = 0 := by
        apply (Nat.floor_eq_iff (by positivity)).2
        constructor
        · nlinarith
        · norm_num
          linarith
      constructor
      · simp [hhalf]
      · rw [stollBinary_even_step]
        simpa [hhalf] using alpha_floor_step t ht1 1 (by norm_num)
  | succ k ih =>
      rcases ih with ⟨heven, hodd⟩
      have heven' :
          stollBinary t (2 * (k + 1)) =
            2 ^ (k + 1) + ⌊t * (2 ^ (k + 1) : ℕ) / 2⌋₊ := by
        rw [show 2 * (k + 1) = 2 * k + 2 by omega,
          stollBinary_odd_step, hodd]
        push_cast
        have hbeta := beta_floor_step t ht1 (2 ^ k) (pow_pos (by norm_num) k)
        push_cast at hbeta
        rw [hbeta]
        congr 1
        · simp [pow_succ, Nat.mul_comm]
        · congr 1
          ring
      constructor
      · exact heven'
      · rw [stollBinary_even_step, heven']
        simpa using
          alpha_floor_step t ht1 (2 ^ (k + 1))
            (pow_pos (by norm_num) (k + 1))

/-! ## Binary digits -/

/-- The binary digits of a normalized real `t ∈ [1,2)`, indexed from one
and including the leading digit.  The value at index zero is a harmless
padding digit. -/
noncomputable def binaryDigit (t : ℝ) : ℕ → Fin 2
  | 0 => 0
  | 1 => 1
  | k + 2 => Real.digits (t - 1) 2 k

/-- A canonical base-two digit is the increment in consecutive doubled
natural floors. -/
lemma realDigits_two_val (x : ℝ) (hx : 0 ≤ x) (k : ℕ) :
    (Real.digits x 2 k).val =
      ⌊x * (2 : ℝ) ^ (k + 1)⌋₊ - 2 * ⌊x * (2 : ℝ) ^ k⌋₊ := by
  have hy : 0 ≤ x * (2 : ℝ) ^ k := by positivity
  have hpow : x * (2 : ℝ) ^ (k + 1) = 2 * (x * (2 : ℝ) ^ k) := by
    rw [pow_succ]
    ring
  have hdouble := floor_two_mul (x * (2 : ℝ) ^ k) hy
  rw [Real.digits, Fin.val_ofNat]
  change ⌊x * (2 : ℝ) ^ (k + 1)⌋₊ % 2 = _
  rw [hpow]
  rcases hdouble with hdouble | hdouble
  · rw [hdouble]
    simp
  · rw [hdouble]
    simp

/-- Removing the leading binary digit commutes with taking floors at powers
of two. -/
lemma floor_mul_pow_two_shift (t : ℝ) (ht1 : 1 ≤ t) (k : ℕ) :
    ⌊t * (2 : ℝ) ^ k⌋₊ =
      2 ^ k + ⌊(t - 1) * (2 : ℝ) ^ k⌋₊ := by
  have hx : 0 ≤ (t - 1) * (2 : ℝ) ^ k := by positivity
  calc
    ⌊t * (2 : ℝ) ^ k⌋₊ =
        ⌊(t - 1) * (2 : ℝ) ^ k + (2 ^ k : ℕ)⌋₊ := by
          congr 1
          push_cast
          ring
    _ = ⌊(t - 1) * (2 : ℝ) ^ k⌋₊ + 2 ^ k :=
      Nat.floor_add_natCast hx (2 ^ k)
    _ = 2 ^ k + ⌊(t - 1) * (2 : ℝ) ^ k⌋₊ := by omega

/-- The floor difference for `t` is the corresponding digit of its
fractional part `t - 1`. -/
lemma floor_gap_eq_binary_tail (t : ℝ) (ht1 : 1 ≤ t) (k : ℕ) :
    ⌊t * (2 : ℝ) ^ (k + 1)⌋₊ - 2 * ⌊t * (2 : ℝ) ^ k⌋₊ =
      (Real.digits (t - 1) 2 k).val := by
  have hdigit := realDigits_two_val (t - 1) (by linarith) k
  have hnext := floor_mul_pow_two_shift t ht1 (k + 1)
  have hprev := floor_mul_pow_two_shift t ht1 k
  have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by
    simp [pow_succ, Nat.mul_comm]
  omega

/-- The gaps in the even subsequence of Stoll's recurrence are precisely the
one-indexed binary digits of `t`, including its leading digit. -/
theorem stollBinary_digit_gap (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2)
    (n : ℕ) (hn : 1 ≤ n) :
    stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) =
      (binaryDigit t n).val := by
  rcases n with _ | n
  · omega
  rcases n with _ | k
  · have htwo := (stollBinary_closed_forms t ht1 ht2 1).1
    have hfloor : ⌊t⌋₊ = 1 := by
      apply (Nat.floor_eq_iff (le_trans (by norm_num) ht1)).2
      norm_num
      exact ⟨ht1, ht2⟩
    norm_num at htwo
    rw [htwo, stollBinary_zero, hfloor]
    simp [binaryDigit]
  · have hbig := (stollBinary_closed_forms t ht1 ht2 (k + 2)).1
    have hsmall := (stollBinary_closed_forms t ht1 ht2 (k + 1)).1
    push_cast at hbig hsmall
    have hdivbig :
        t * (2 : ℝ) ^ (k + 2) / 2 = t * (2 : ℝ) ^ (k + 1) := by
      rw [pow_succ]
      ring
    have hdivsmall :
        t * (2 : ℝ) ^ (k + 1) / 2 = t * (2 : ℝ) ^ k := by
      rw [pow_succ]
      ring
    rw [hdivbig] at hbig
    rw [hdivsmall] at hsmall
    rw [show 2 * (k + 2) - 2 = 2 * (k + 1) by omega, hbig, hsmall]
    simp only [binaryDigit]
    have htail := floor_gap_eq_binary_tail t ht1 k
    have hpow : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by
      simp [pow_succ, Nat.mul_comm]
    omega

/-- The tail digits obtained from the recurrence reconstruct the fractional
part of the normalized real. -/
theorem binaryDigit_expansion (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2) :
    Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1 := by
  have hx : t - 1 ∈ Set.Ico (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  simpa [binaryDigit] using
    (Real.ofDigits_digits (x := t - 1) (b := 2) (by norm_num) hx)

/-- The arbitrary-real binary resolution: the recurrence extracts every
digit and those digits reconstruct the original normalized real. -/
theorem stollBinary_resolution (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2) :
    (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) =
          (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1 := by
  exact ⟨stollBinary_digit_gap t ht1 ht2, binaryDigit_expansion t ht1 ht2⟩

/-! ## The Graham--Pollak specialization at `√2` -/

lemma sqrt_two_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2

lemma sqrt_two_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)

lemma one_le_sqrt_two : 1 ≤ Real.sqrt 2 := by
  nlinarith [sqrt_two_nonneg, sqrt_two_sq]

lemma sqrt_two_lt_two : Real.sqrt 2 < 2 := by
  nlinarith [sqrt_two_nonneg, sqrt_two_sq]

lemma alpha_sqrt_two : alpha (Real.sqrt 2) = Real.sqrt 2 := by
  rw [alpha]
  apply (div_eq_iff (by nlinarith [sqrt_two_nonneg])).2
  nlinarith [sqrt_two_sq]

lemma beta_sqrt_two : beta (Real.sqrt 2) = Real.sqrt 2 := by
  rw [beta]
  apply (div_eq_iff (by nlinarith [sqrt_two_nonneg])).2
  nlinarith [sqrt_two_sq]

/-- The Graham--Pollak sequence, extended by a padding value at index zero.
Its positive-index restriction is exactly the recurrence in Problem 482. -/
noncomputable def grahamPollak : ℕ → ℕ
  | 0 => 0
  | n + 1 => stollBinary (Real.sqrt 2) n

@[simp] theorem grahamPollak_one : grahamPollak 1 = 1 := rfl

/-- The defining Graham--Pollak recurrence. -/
theorem grahamPollak_succ (n : ℕ) (hn : 1 ≤ n) :
    grahamPollak (n + 1) =
      ⌊Real.sqrt 2 * ((grahamPollak n : ℝ) + 1 / 2)⌋₊ := by
  rcases n with _ | n
  · omega
  change stollBinary (Real.sqrt 2) (n + 1) =
    ⌊Real.sqrt 2 * ((stollBinary (Real.sqrt 2) n : ℝ) + 1 / 2)⌋₊
  rw [stollBinary]
  simp [alpha_sqrt_two, beta_sqrt_two]

/-- Graham and Pollak's digit identity, with the leading binary digit counted
as digit number one. -/
theorem grahamPollak_digit (n : ℕ) (hn : 1 ≤ n) :
    grahamPollak (2 * n + 1) - 2 * grahamPollak (2 * n - 1) =
      (binaryDigit (Real.sqrt 2) n).val := by
  rw [show 2 * n + 1 = (2 * n) + 1 by omega,
    show 2 * n - 1 = (2 * n - 2) + 1 by omega]
  exact stollBinary_digit_gap (Real.sqrt 2) one_le_sqrt_two sqrt_two_lt_two n hn

/-- The tail produced by the Graham--Pollak gaps is the canonical binary
expansion of the fractional part of `√2`. -/
theorem grahamPollak_expansion :
    Real.ofDigits (fun k ↦ binaryDigit (Real.sqrt 2) (k + 2)) =
      Real.sqrt 2 - 1 :=
  binaryDigit_expansion (Real.sqrt 2) one_le_sqrt_two sqrt_two_lt_two

/-- Erdős Problem 482, together with the arbitrary-normalized-real binary
generalization established by the same recurrence method. -/
theorem erdos_482 :
    grahamPollak 1 = 1 ∧
      (∀ n, 1 ≤ n →
        grahamPollak (n + 1) =
          ⌊Real.sqrt 2 * ((grahamPollak n : ℝ) + 1 / 2)⌋₊) ∧
      (∀ n, 1 ≤ n →
        grahamPollak (2 * n + 1) - 2 * grahamPollak (2 * n - 1) =
          (binaryDigit (Real.sqrt 2) n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit (Real.sqrt 2) (k + 2)) =
        Real.sqrt 2 - 1 ∧
      (∀ t : ℝ, 1 ≤ t → t < 2 →
        (∀ n, 1 ≤ n →
          stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) =
            (binaryDigit t n).val) ∧
        Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) := by
  refine ⟨grahamPollak_one, grahamPollak_succ, grahamPollak_digit,
    grahamPollak_expansion, ?_⟩
  intro t ht1 ht2
  exact stollBinary_resolution t ht1 ht2

#print axioms erdos_482

end Erdos482
