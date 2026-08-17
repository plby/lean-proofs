/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/-!
# Elementary finite Fourier analysis for Erdős problem 438

The character in this file is the literal exponential
`exp (2 * π * I * t * x / T)`.  Residues are used only internally to prove
orthogonality; in particular, no ring homomorphism `ZMod T → ℂ` is introduced.
-/

namespace Erdos438

open scoped BigOperators ComplexConjugate

namespace Fourier

/-- The explicit additive character `e_T(tx)`. Frequencies and arguments are
integers so that negative frequencies require no modular subtraction. -/
noncomputable def phase (T : ℕ) (t x : ℤ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (t : ℂ) * (x : ℂ) / (T : ℂ))

@[simp] theorem phase_zero_left (T : ℕ) (x : ℤ) : phase T 0 x = 1 := by
  simp [phase]

@[simp] theorem phase_zero_right (T : ℕ) (t : ℤ) : phase T t 0 = 1 := by
  simp [phase]

theorem phase_add_right (T : ℕ) (t x y : ℤ) :
    phase T t (x + y) = phase T t x * phase T t y := by
  rw [phase, phase, phase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem phase_neg_right (T : ℕ) (t x : ℤ) :
    phase T t (-x) = (phase T t x)⁻¹ := by
  rw [phase, phase, ← Complex.exp_neg]
  congr 1
  push_cast
  ring

theorem phase_neg_left (T : ℕ) (t x : ℤ) :
    phase T (-t) x = (phase T t x)⁻¹ := by
  rw [phase, phase, ← Complex.exp_neg]
  congr 1
  push_cast
  ring

theorem norm_phase (T : ℕ) (t x : ℤ) : ‖phase T t x‖ = 1 := by
  rw [phase, Complex.norm_exp]
  norm_num

theorem conj_phase (T : ℕ) (t x : ℤ) :
    conj (phase T t x) = phase T t (-x) := by
  rw [phase, phase, ← Complex.exp_conj]
  congr 1
  norm_num [map_div, map_mul, map_ofNat]

private theorem phase_eq_stdAddChar (T : ℕ) [NeZero T] (t x : ℤ) :
    phase T t x = ZMod.stdAddChar ((t * x : ℤ) : ZMod T) := by
  rw [ZMod.stdAddChar_coe]
  unfold phase
  congr 1
  push_cast
  ring

/-- Complete character orthogonality, indexed by the concrete interval
`0 ≤ t < T`. -/
theorem phase_orthogonality (T : ℕ) [NeZero T] (x : ℤ) :
    (∑ t ∈ Finset.range T, phase T (t : ℤ) x) =
      if (x : ZMod T) = 0 then (T : ℂ) else 0 := by
  classical
  rw [← Fin.sum_univ_eq_sum_range]
  change (∑ t : Fin T, phase T (t : ℤ) x) = _
  have horth := AddChar.sum_mulShift (x : ZMod T) (ZMod.isPrimitive_stdAddChar T)
  calc
    (∑ t : Fin T, phase T (t : ℤ) x) =
        ∑ u : ZMod T, ZMod.stdAddChar (u * (x : ZMod T)) := by
      apply Fintype.sum_equiv (ZMod.finEquiv T)
      intro t
      rw [phase_eq_stdAddChar]
      congr 2
      simp only [Int.cast_mul, Int.cast_natCast]
      congr 1
      apply ZMod.val_injective
      rw [ZMod.val_natCast_of_lt t.isLt]
      cases T with
      | zero => exact (NeZero.ne 0 rfl).elim
      | succ T => rfl
    _ = if (x : ZMod T) = 0 then (T : ℂ) else 0 := by
      convert horth using 1
      simp

/-- An unnormalized Fourier coefficient of a finite set of naturals. -/
noncomputable def coefficient (T : ℕ) (s : Finset ℕ) (t : ℤ) : ℂ :=
  ∑ x ∈ s, phase T t (x : ℤ)

@[simp] theorem coefficient_zero (T : ℕ) (s : Finset ℕ) :
    coefficient T s 0 = (s.card : ℂ) := by
  simp [coefficient]

/-- A weighted unnormalized transform on the concrete interval `[0,T)`. -/
noncomputable def transform (T : ℕ) (f : ℕ → ℂ) (t : ℤ) : ℂ :=
  ∑ x ∈ Finset.range T, f x * phase T t (x : ℤ)

/-- Complex-algebra Parseval.  This form avoids taking real parts and is the
one from which the norm-squared statement is derived. -/
theorem parseval_transform (T : ℕ) [NeZero T] (f : ℕ → ℂ) :
    (∑ t ∈ Finset.range T,
        conj (transform T f (t : ℤ)) * transform T f (t : ℤ)) =
      (T : ℂ) * ∑ x ∈ Finset.range T, conj (f x) * f x := by
  classical
  calc
    (∑ t ∈ Finset.range T,
        conj (transform T f (t : ℤ)) * transform T f (t : ℤ)) =
      ∑ t ∈ Finset.range T, ∑ x ∈ Finset.range T, ∑ y ∈ Finset.range T,
        (conj (f x) * conj (phase T (t : ℤ) (x : ℤ))) *
          (f y * phase T (t : ℤ) (y : ℤ)) := by
      apply Finset.sum_congr rfl
      intro t ht
      simp only [transform, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = ∑ x ∈ Finset.range T, ∑ y ∈ Finset.range T, ∑ t ∈ Finset.range T,
        (conj (f x) * conj (phase T (t : ℤ) (x : ℤ))) *
          (f y * phase T (t : ℤ) (y : ℤ)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_comm]
    _ = ∑ x ∈ Finset.range T, ∑ y ∈ Finset.range T,
        (conj (f x) * f y) *
          ∑ t ∈ Finset.range T, phase T (t : ℤ) ((y : ℤ) - x) := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      rw [conj_phase]
      calc
        (conj (f x) * phase T (t : ℤ) (-(x : ℤ))) *
              (f y * phase T (t : ℤ) (y : ℤ)) =
            (conj (f x) * f y) *
              (phase T (t : ℤ) (-(x : ℤ)) *
                phase T (t : ℤ) (y : ℤ)) := by ring
        _ = (conj (f x) * f y) *
              phase T (t : ℤ) ((y : ℤ) - x) := by
          rw [← phase_add_right]
          congr 2
          ring
    _ = ∑ x ∈ Finset.range T, ∑ y ∈ Finset.range T,
        (conj (f x) * f y) *
          (if x = y then (T : ℂ) else 0) := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      rw [phase_orthogonality]
      congr 2
      simp only [Int.cast_sub, Int.cast_natCast, sub_eq_zero]
      rw [ZMod.natCast_eq_natCast_iff]
      apply propext
      constructor
      · intro hmod
        exact (hmod.eq_of_lt_of_lt (Finset.mem_range.mp hy)
          (Finset.mem_range.mp hx)).symm
      · rintro rfl
        rfl
    _ = (T : ℂ) * ∑ x ∈ Finset.range T, conj (f x) * f x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      simp [hx]
      ring

/-- Parseval for a finite set contained in `[0,T)`. -/
theorem parseval_coefficient (T : ℕ) [NeZero T] (s : Finset ℕ)
    (hs : s ⊆ Finset.range T) :
    ∑ t ∈ Finset.range T, ‖coefficient T s (t : ℤ)‖ ^ 2 = T * s.card := by
  classical
  let f : ℕ → ℂ := fun x => if x ∈ s then 1 else 0
  have hf (t : ℤ) : transform T f t = coefficient T s t := by
    unfold transform coefficient
    calc
      (∑ x ∈ Finset.range T, f x * phase T t (x : ℤ)) =
          ∑ x ∈ s, f x * phase T t (x : ℤ) := by
        symm
        apply Finset.sum_subset hs
        intro x hx hxs
        simp [f, hxs]
      _ = ∑ x ∈ s, phase T t (x : ℤ) := by
        apply Finset.sum_congr rfl
        intro x hx
        simp [f, hx]
  have hnorm (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = conj z * z := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  have hnorm' (z : ℂ) : (‖z‖ : ℂ) ^ 2 = conj z * z := by
    rw [← Complex.ofReal_pow]
    exact hnorm z
  have hp :
      (∑ t ∈ Finset.range T, ‖coefficient T s (t : ℤ)‖ ^ 2) =
        T * ∑ x ∈ Finset.range T, ‖f x‖ ^ 2 := by
    apply Complex.ofReal_injective
    push_cast
    simp_rw [hnorm', ← hf]
    exact parseval_transform T f
  have hfsum : (∑ x ∈ Finset.range T, ‖f x‖ ^ 2) = s.card := by
    calc
      (∑ x ∈ Finset.range T, ‖f x‖ ^ 2) =
          ∑ x ∈ s, ‖f x‖ ^ 2 := by
        symm
        apply Finset.sum_subset hs
        intro x hx hxs
        simp [f, hxs]
      _ = ∑ _x ∈ s, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro x hx
        simp [f, hx]
      _ = s.card := by simp
  simpa [hfsum] using hp

/-- The exact number (cast to `ℂ`) of ordered pairs whose sum belongs to
`S`. -/
noncomputable def pairSumCount (X Y S : Finset ℕ) : ℂ :=
  ∑ x ∈ X, ∑ y ∈ Y, if x + y ∈ S then 1 else 0

/-- Exact finite Fourier pair/square count.  The hypotheses are the explicit
"no wrap" conditions: every source sum and every target is below `T`. -/
theorem pairSumCount_eq_fourier (T : ℕ) [NeZero T]
    (X Y S : Finset ℕ)
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, x + y < T)
    (hS : S ⊆ Finset.range T) :
    (T : ℂ) * pairSumCount X Y S =
      ∑ t ∈ Finset.range T,
        coefficient T X (t : ℤ) * coefficient T Y (t : ℤ) *
          coefficient T S (-(t : ℤ)) := by
  classical
  symm
  calc
    (∑ t ∈ Finset.range T,
        coefficient T X (t : ℤ) * coefficient T Y (t : ℤ) *
          coefficient T S (-(t : ℤ))) =
      ∑ t ∈ Finset.range T, ∑ x ∈ X, ∑ y ∈ Y, ∑ z ∈ S,
        (phase T (t : ℤ) (x : ℤ) * phase T (t : ℤ) (y : ℤ)) *
          phase T (-(t : ℤ)) (z : ℤ) := by
      apply Finset.sum_congr rfl
      intro t ht
      simp only [coefficient, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm (s := S) (t := Y)]
      simp_rw [Finset.sum_comm (s := S) (t := X)]
      rw [Finset.sum_comm (s := Y) (t := X)]
    _ = ∑ x ∈ X, ∑ y ∈ Y, ∑ z ∈ S, ∑ t ∈ Finset.range T,
        (phase T (t : ℤ) (x : ℤ) * phase T (t : ℤ) (y : ℤ)) *
          phase T (-(t : ℤ)) (z : ℤ) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y hy
      rw [Finset.sum_comm]
    _ = ∑ x ∈ X, ∑ y ∈ Y, ∑ z ∈ S,
        ∑ t ∈ Finset.range T,
          phase T (t : ℤ) (((x : ℤ) + y) - z) := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      apply Finset.sum_congr rfl
      intro z hz
      apply Finset.sum_congr rfl
      intro t ht
      rw [phase_neg_left, ← phase_neg_right]
      rw [← phase_add_right, ← phase_add_right]
      congr 1
    _ = ∑ x ∈ X, ∑ y ∈ Y, ∑ z ∈ S,
        (if x + y = z then (T : ℂ) else 0) := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      apply Finset.sum_congr rfl
      intro z hz
      rw [phase_orthogonality]
      have hcond :
          (((((x : ℤ) + y) - z : ℤ) : ZMod T) = 0) ↔ x + y = z := by
        push_cast
        rw [sub_eq_zero, ← Nat.cast_add, ZMod.natCast_eq_natCast_iff]
        constructor
        · intro hmod
          have hzT : z < T := Finset.mem_range.mp (hS hz)
          have hsumT : x + y < T := hXY x hx y hy
          exact hmod.eq_of_lt_of_lt hsumT hzT
        · rintro rfl
          rfl
      simp only [hcond]
    _ = ∑ x ∈ X, ∑ y ∈ Y,
        (if x + y ∈ S then (T : ℂ) else 0) := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      by_cases hmem : x + y ∈ S
      · rw [Finset.sum_eq_single (x + y)]
        · simp [hmem]
        · intro z hz hne
          simp [hne.symm]
        · intro hnot
          exact (hnot hmem).elim
      · simp [hmem]
    _ = (T : ℂ) * pairSumCount X Y S := by
      rw [pairSumCount, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y hy
      by_cases hmem : x + y ∈ S <;> simp [hmem]

/-- The square numbers in the half-open interval `[0,T)`. -/
def squaresBelow (T : ℕ) : Finset ℕ :=
  (Finset.range T).filter IsSquare

theorem squaresBelow_subset_range (T : ℕ) :
    squaresBelow T ⊆ Finset.range T :=
  Finset.filter_subset _ _

/-- Number of ordered pairs whose sum is a square below `T`. -/
noncomputable def squarePairCount (T : ℕ) (X Y : Finset ℕ) : ℂ :=
  pairSumCount X Y (squaresBelow T)

/-- The square-specialized exact Fourier identity.  The strict sum bound is
what turns cyclic congruence into literal equality, so the theorem has no
wrap-around terms. -/
theorem squarePairCount_eq_fourier (T : ℕ) [NeZero T]
    (X Y : Finset ℕ)
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, x + y < T) :
    (T : ℂ) * squarePairCount T X Y =
      ∑ t ∈ Finset.range T,
        coefficient T X (t : ℤ) * coefficient T Y (t : ℤ) *
          coefficient T (squaresBelow T) (-(t : ℤ)) := by
  exact pairSumCount_eq_fourier T X Y (squaresBelow T) hXY
    (squaresBelow_subset_range T)

/-- Cauchy--Schwarz on any chosen set of frequencies.  This is the exact
minor-arc estimate used after bounding the square coefficient pointwise. -/
theorem minorArc_cauchy_bound (U : Finset ℕ) (F G H : ℕ → ℂ) (B : ℝ)
    (hB : 0 ≤ B) (hH : ∀ t ∈ U, ‖H t‖ ≤ B) :
    ‖∑ t ∈ U, F t * G t * H t‖ ≤
      B * Real.sqrt (∑ t ∈ U, ‖F t‖ ^ 2) *
          Real.sqrt (∑ t ∈ U, ‖G t‖ ^ 2) := by
  have hcs :
      (∑ t ∈ U, ‖F t‖ * ‖G t‖) ≤
        Real.sqrt (∑ t ∈ U, ‖F t‖ ^ 2) *
          Real.sqrt (∑ t ∈ U, ‖G t‖ ^ 2) :=
    Real.sum_mul_le_sqrt_mul_sqrt U (fun t => ‖F t‖) (fun t => ‖G t‖)
  calc
    ‖∑ t ∈ U, F t * G t * H t‖ ≤
        ∑ t ∈ U, ‖F t * G t * H t‖ := by
      exact norm_sum_le _ _
    _ = ∑ t ∈ U, (‖F t‖ * ‖G t‖) * ‖H t‖ := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [norm_mul, norm_mul]
    _ ≤ ∑ t ∈ U, (‖F t‖ * ‖G t‖) * B := by
      apply Finset.sum_le_sum
      intro t ht
      exact mul_le_mul_of_nonneg_left (hH t ht)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = B * ∑ t ∈ U, ‖F t‖ * ‖G t‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      ring
    _ ≤ B * (Real.sqrt (∑ t ∈ U, ‖F t‖ ^ 2) *
          Real.sqrt (∑ t ∈ U, ‖G t‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left hcs hB
    _ = B * Real.sqrt (∑ t ∈ U, ‖F t‖ ^ 2) *
          Real.sqrt (∑ t ∈ U, ‖G t‖ ^ 2) := by ring

end Fourier

end Erdos438
