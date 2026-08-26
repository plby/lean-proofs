import ErdosProblems.Erdos69.SixTermCancellation

/-!
# Iterated cancellation patterns

A pattern with `m` blocks has `36^m` signed terms, distinct slopes below
`49^m`, and cancels every direction from one through `6*m`.
-/

open scoped BigOperators

namespace Erdos69.Elementary

def PatternLabel : ℕ → Type
  | 0 => PUnit
  | m + 1 => BlockLabel × PatternLabel m

instance patternFintype : (m : ℕ) → Fintype (PatternLabel m)
  | 0 => inferInstanceAs (Fintype PUnit)
  | m + 1 =>
    letI := patternFintype m
    inferInstanceAs (Fintype (BlockLabel × PatternLabel m))

def patternDigit : (m : ℕ) → PatternLabel m → ℕ
  | 0, _ => 0
  | m + 1, i => blockDigit i.1 + 49 * patternDigit m i.2

def patternIntercept : (m : ℕ) → PatternLabel m → ℕ
  | 0, _ => 0
  | m + 1, i => blockIntercept i.1 +
      49 * (patternIntercept m i.2 + 6 * patternDigit m i.2)

def patternSign : (m : ℕ) → PatternLabel m → ℤ
  | 0, _ => 1
  | m + 1, i => blockSign i.1 * patternSign m i.2

def patternZero : (m : ℕ) → PatternLabel m
  | 0 => PUnit.unit
  | m + 1 => ((0, 0), patternZero m)

theorem card_patternLabel (m : ℕ) : Fintype.card (PatternLabel m) = 36 ^ m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change Fintype.card (BlockLabel × PatternLabel m) = _
    simp [Fintype.card_prod, BlockLabel, ih, pow_succ, Nat.mul_comm]

theorem patternDigit_lt (m : ℕ) (i : PatternLabel m) : patternDigit m i < 49 ^ m := by
  induction m with
  | zero => simp [patternDigit]
  | succ m ih =>
    have h₁ := blockDigit_lt i.1
    have h₂ := ih i.2
    simp only [patternDigit, pow_succ]
    omega

theorem patternDigit_injective (m : ℕ) : Function.Injective (patternDigit m) := by
  induction m with
  | zero =>
    intro i j _
    change PUnit at i j
    cases i
    cases j
    rfl
  | succ m ih =>
    rintro ⟨a, i⟩ ⟨b, j⟩ hij
    have ha := blockDigit_lt a
    have hb := blockDigit_lt b
    have h₁ : blockDigit a = blockDigit b := by
      simp only [patternDigit] at hij
      omega
    have h₂ : patternDigit m i = patternDigit m j := by
      simp only [patternDigit] at hij
      omega
    exact Prod.ext (blockDigit_injective h₁) (ih h₂)

theorem patternIntercept_le (m : ℕ) (i : PatternLabel m) :
    patternIntercept m i ≤ 6 * m * patternDigit m i := by
  induction m with
  | zero => simp [patternIntercept]
  | succ m ih =>
    have h₁ := blockIntercept_le i.1
    have h₂ := ih i.2
    simp only [patternIntercept, patternDigit]
    nlinarith [Nat.zero_le (m * blockDigit i.1)]

theorem patternSign_abs (m : ℕ) (i : PatternLabel m) : |patternSign m i| = 1 := by
  induction m with
  | zero => simp [patternSign]
  | succ m ih => simp [patternSign, abs_mul, blockSign_abs, ih]

theorem patternSign_abs_real (m : ℕ) (i : PatternLabel m) :
    |(patternSign m i : ℝ)| = 1 := by
  exact_mod_cast patternSign_abs m i

@[simp] theorem patternDigit_zero (m : ℕ) : patternDigit m (patternZero m) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [patternDigit, patternZero, blockDigit, hexDigit, ih]

@[simp] theorem patternIntercept_zero (m : ℕ) : patternIntercept m (patternZero m) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [patternIntercept, patternZero, blockIntercept,
      hexInterceptA, hexInterceptB, ih]

@[simp] theorem patternSign_zero (m : ℕ) : patternSign m (patternZero m) = 1 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [patternSign, patternZero, blockSign, hexSign, ih]

theorem patternDigit_eq_zero_iff (m : ℕ) (i : PatternLabel m) :
    patternDigit m i = 0 ↔ i = patternZero m := by
  constructor
  · intro h
    apply patternDigit_injective m
    simpa using h
  · rintro rfl
    exact patternDigit_zero m

theorem sum_patternSign {m : ℕ} (hm : 0 < m) :
    ∑ i : PatternLabel m, patternSign m i = 0 := by
  cases m with
  | zero => omega
  | succ m =>
    change (∑ i : BlockLabel × PatternLabel m, blockSign i.1 * patternSign m i.2) = 0
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul, sum_blockSign, zero_mul]

theorem sum_abs_patternSign (m : ℕ) :
    ∑ i : PatternLabel m, |(patternSign m i : ℝ)| = (36 : ℝ) ^ m := by
  simp [patternSign_abs_real, card_patternLabel]

def patternPhase (m : ℕ) (i : PatternLabel m) (h : ℤ) : ℤ :=
  (patternDigit m i : ℤ) * h - patternIntercept m i

theorem patternPhase_succ (m : ℕ) (a : BlockLabel) (i : PatternLabel m) (h : ℤ) :
    patternPhase (m + 1) (a, i) h =
      (blockDigit a : ℤ) * h - blockIntercept a + 49 * patternPhase m i (h - 6) := by
  simp only [patternPhase, patternDigit, patternIntercept, Nat.cast_add,
    Nat.cast_mul, Nat.cast_ofNat]
  ring

noncomputable def patternSignedSum (m : ℕ) (h : ℤ) (f : ℤ → ℝ) : ℝ :=
  ∑ i : PatternLabel m, (patternSign m i : ℝ) * f (patternPhase m i h)

theorem patternSignedSum_first (m : ℕ) (h : ℤ) (f : ℤ → ℝ) :
    patternSignedSum (m + 1) h f =
      ∑ i : PatternLabel m, (patternSign m i : ℝ) *
        blockSignedSum h (fun t ↦ f (t + 49 * patternPhase m i (h - 6))) := by
  unfold patternSignedSum
  change (∑ i : BlockLabel × PatternLabel m, _) = _
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [blockSignedSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [patternPhase_succ]
  simp only [patternSign, Int.cast_mul]
  ring

theorem patternSignedSum_tail (m : ℕ) (h : ℤ) (f : ℤ → ℝ) :
    patternSignedSum (m + 1) h f =
      ∑ a : BlockLabel, (blockSign a : ℝ) *
        patternSignedSum m (h - 6)
          (fun t ↦ f ((blockDigit a : ℤ) * h - blockIntercept a + 49 * t)) := by
  unfold patternSignedSum
  change (∑ i : BlockLabel × PatternLabel m, _) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [patternPhase_succ]
  simp only [patternSign, Int.cast_mul]
  ring

/-- All of the first `6*m` directions cancel, for an arbitrary test function. -/
theorem patternSignedSum_vanish (m : ℕ) {h : ℕ} (hpos : 1 ≤ h) (hle : h ≤ 6 * m)
    (f : ℤ → ℝ) : patternSignedSum m h f = 0 := by
  induction m generalizing h f with
  | zero => omega
  | succ m ih =>
    by_cases hsmall : h ≤ 6
    · rw [patternSignedSum_first]
      simp [blockSignedSum_vanish hpos hsmall]
    · have hsubpos : 1 ≤ h - 6 := by omega
      have hsuble : h - 6 ≤ 6 * m := by omega
      have hcast : (h : ℤ) - 6 = ((h - 6 : ℕ) : ℤ) := by omega
      rw [patternSignedSum_tail, hcast]
      simp [ih hsubpos hsuble]

theorem pattern_mass_ratio (m : ℕ) :
    (36 : ℝ) ^ m / 2 ^ (6 * m) = (9 / 16 : ℝ) ^ m := by
  rw [pow_mul, ← div_pow]
  congr 1
  norm_num

end Erdos69.Elementary
