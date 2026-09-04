import ErdosProblems.Erdos1002.Statement
import Mathlib.Data.Nat.Totient

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Elementary Ramanujan sums

This file supplies the finite arithmetic object used by the Fourier
reconstruction in the proof of Erdős Problem 1002.  The modulus-zero
convention is explicit: there are no reduced residues modulo zero, hence the
corresponding sum is zero.  For a positive modulus this agrees with the usual
sum over a complete reduced residue system.
-/

open scoped BigOperators ComplexConjugate FourierTransform

namespace Erdos1002

noncomputable section

/-- The reduced representatives `0 ≤ a < q`.  In particular this set is
empty when `q = 0`. -/
def reducedResidues (q : ℕ) : Finset ℕ :=
  (Finset.range q).filter fun a ↦ Nat.Coprime a q

/-- The standard additive phase `exp(2π i a n / q)`.  Division by zero has
Lean's field convention, but this value is never sampled in
`ramanujanSum 0`, because `reducedResidues 0` is empty. -/
def ramanujanPhase (q a : ℕ) (n : ℤ) : ℂ :=
  (Real.fourierChar (((a : ℤ) * n : ℤ) / (q : ℝ)) : ℂ)

/-- The complex-valued Ramanujan sum
`c_q(n) = ∑_{0 ≤ a < q, (a,q)=1} exp(2π i a n/q)`.

The integer argument is useful for Fourier coefficients of both signs. -/
def ramanujanSum (q : ℕ) (n : ℤ) : ℂ :=
  ∑ a ∈ reducedResidues q, ramanujanPhase q a n

@[simp]
theorem reducedResidues_zero : reducedResidues 0 = ∅ := by
  simp [reducedResidues]

@[simp]
theorem reducedResidues_one : reducedResidues 1 = {0} := by
  ext a
  simp [reducedResidues]

/-- The reduced-residue set has Euler-totient cardinality. -/
@[simp]
theorem card_reducedResidues (q : ℕ) :
    (reducedResidues q).card = Nat.totient q := by
  simpa [reducedResidues, Nat.coprime_comm] using!
    (Nat.totient_eq_card_coprime q).symm

@[simp]
theorem ramanujanSum_zero (n : ℤ) : ramanujanSum 0 n = 0 := by
  simp [ramanujanSum]

@[simp]
theorem ramanujanPhase_zero_index (q a : ℕ) : ramanujanPhase q a 0 = 1 := by
  simp [ramanujanPhase]

@[simp]
theorem ramanujanSum_one (n : ℤ) : ramanujanSum 1 n = 1 := by
  simp [ramanujanSum, ramanujanPhase]

/-- At frequency zero the Ramanujan sum counts the reduced residues. -/
theorem ramanujanSum_zero_index (q : ℕ) :
    ramanujanSum q 0 = (Nat.totient q : ℂ) := by
  simp only [ramanujanSum, ramanujanPhase_zero_index, Finset.sum_const,
    nsmul_eq_mul, mul_one]
  congr 2
  simp [reducedResidues, Nat.coprime_comm]

/-- The analyst's Fourier character is one at every integer. -/
@[simp]
theorem fourierChar_int (z : ℤ) :
    (Real.fourierChar (z : ℝ) : ℂ) = 1 := by
  rw [Real.fourierChar_apply]
  convert! Complex.exp_int_mul_two_pi_mul_I z using 2
  push_cast
  ring

/-- Circle-valued form of `fourierChar_int`. -/
@[simp]
theorem fourierChar_int_circle (z : ℤ) :
    Real.fourierChar (z : ℝ) = 1 := by
  apply Subtype.ext
  exact fourierChar_int z

/-- Adding the modulus to the integer frequency does not change one phase. -/
theorem ramanujanPhase_add_modulus {q a : ℕ} (n : ℤ) (hq : q ≠ 0) :
    ramanujanPhase q a (n + q) = ramanujanPhase q a n := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  have harg :
      ((((a : ℤ) * (n + q) : ℤ) : ℝ) / (q : ℝ)) =
        (((((a : ℤ) * n : ℤ) : ℝ) / (q : ℝ)) + (a : ℝ)) := by
    push_cast
    field_simp
  have haChar : (Real.fourierChar (a : ℝ) : ℂ) = 1 := by
    exact fourierChar_int (a : ℤ)
  rw [ramanujanPhase, harg, AddChar.map_add_eq_mul]
  rw [Circle.coe_mul, ramanujanPhase, haChar, mul_one]

/-- Complementing a residue modulo `q` reverses its phase. -/
theorem ramanujanPhase_complement {q a : ℕ} (ha : a ≤ q) (n : ℤ) :
    ramanujanPhase q (q - a) n = ramanujanPhase q a (-n) := by
  by_cases hq : q = 0
  · subst q
    have : a = 0 := by omega
    subst a
    simp [ramanujanPhase]
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  have harg :
      (((((q - a : ℕ) : ℤ) * n : ℤ) : ℝ) / (q : ℝ)) =
        (n : ℝ) + ((((a : ℤ) * (-n) : ℤ) : ℝ) / (q : ℝ)) := by
    push_cast [Nat.cast_sub ha]
    field_simp
    ring
  rw [ramanujanPhase, harg, AddChar.map_add_eq_mul]
  simp [ramanujanPhase]

private theorem complement_mem_reducedResidues {q a : ℕ} (hq : 2 ≤ q)
    (ha : a ∈ reducedResidues q) : q - a ∈ reducedResidues q := by
  rw [reducedResidues, Finset.mem_filter] at ha ⊢
  rcases ha with ⟨haRange, haCoprime⟩
  rw [Finset.mem_range] at haRange ⊢
  have haPos : 0 < a := by
    by_contra h
    have haZero : a = 0 := Nat.eq_zero_of_not_pos h
    subst a
    have hqOne : q = 1 := by simpa using! haCoprime
    omega
  refine ⟨by omega, ?_⟩
  exact (Nat.coprime_self_sub_left haRange.le).2 haCoprime

/-- Consequently `c_q(n)` is periodic in its integer argument, with period
`q`, for every nonzero modulus. -/
theorem ramanujanSum_add_modulus {q : ℕ} (n : ℤ) (hq : q ≠ 0) :
    ramanujanSum q (n + q) = ramanujanSum q n := by
  simp_rw [ramanujanSum, ramanujanPhase_add_modulus n hq]

/-- The full periodicity statement, including the identically-zero modulus
`q = 0` case. -/
theorem ramanujanSum_periodic (q : ℕ) :
    Function.Periodic (ramanujanSum q) (q : ℤ) := by
  by_cases hq : q = 0
  · subst q
    intro n
    simp
  · exact fun n ↦ ramanujanSum_add_modulus n hq

/-- Subtracting one modulus also leaves the sum unchanged. -/
theorem ramanujanSum_sub_modulus (q : ℕ) (n : ℤ) :
    ramanujanSum q (n - q) = ramanujanSum q n :=
  (ramanujanSum_periodic q).sub_eq n

/-- Reversing the frequency conjugates an individual phase. -/
theorem ramanujanPhase_neg (q a : ℕ) (n : ℤ) :
    ramanujanPhase q a (-n) = conj (ramanujanPhase q a n) := by
  have harg :
      ((((a : ℤ) * (-n) : ℤ) : ℝ) / (q : ℝ)) =
        -((((a : ℤ) * n : ℤ) : ℝ) / (q : ℝ)) := by
    push_cast
    ring
  rw [ramanujanPhase, harg, Real.fourierChar.map_neg_eq_inv]
  exact Circle.coe_inv_eq_conj _

/-- The negative-frequency Ramanujan sum is the complex conjugate of the
positive-frequency sum.  This is the sign/conjugation identity required by
Plancherel expansions. -/
theorem ramanujanSum_neg (q : ℕ) (n : ℤ) :
    ramanujanSum q (-n) = conj (ramanujanSum q n) := by
  simp_rw [ramanujanSum, ramanujanPhase_neg, map_sum]

/-- Ramanujan sums are even in their integer argument.  The proof explicitly
reindexes the reduced residues by the involution `a ↦ q - a`; the cases
`q = 0, 1` are handled by the conventions above. -/
theorem ramanujanSum_even (q : ℕ) (n : ℤ) :
    ramanujanSum q (-n) = ramanujanSum q n := by
  by_cases hq : q ≤ 1
  · interval_cases q <;> simp
  have hqTwo : 2 ≤ q := by omega
  unfold ramanujanSum
  refine Finset.sum_bij'
    (fun a _ ↦ q - a) (fun a _ ↦ q - a)
    (fun a ha ↦ complement_mem_reducedResidues hqTwo ha)
    (fun a ha ↦ complement_mem_reducedResidues hqTwo ha) ?_ ?_ ?_
  · intro a ha
    have haLt : a < q := (Finset.mem_filter.mp ha).1 |> Finset.mem_range.mp
    change q - (q - a) = a
    exact Nat.sub_sub_self haLt.le
  · intro a ha
    have haLt : a < q := (Finset.mem_filter.mp ha).1 |> Finset.mem_range.mp
    change q - (q - a) = a
    exact Nat.sub_sub_self haLt.le
  · intro a ha
    exact (ramanujanPhase_complement (Finset.mem_range.mp (Finset.mem_filter.mp ha).1).le n).symm

/-- Hence every Ramanujan sum is fixed by complex conjugation. -/
theorem conj_ramanujanSum (q : ℕ) (n : ℤ) :
    conj (ramanujanSum q n) = ramanujanSum q n := by
  rw [← ramanujanSum_neg, ramanujanSum_even]

/-- A Ramanujan sum is the complex embedding of its real part. -/
theorem ofReal_re_ramanujanSum (q : ℕ) (n : ℤ) :
    ((ramanujanSum q n).re : ℂ) = ramanujanSum q n :=
  Complex.conj_eq_iff_re.mp (conj_ramanujanSum q n)

/-- The imaginary part of a Ramanujan sum vanishes. -/
@[simp]
theorem ramanujanSum_im (q : ℕ) (n : ℤ) : (ramanujanSum q n).im = 0 := by
  rw [← Complex.conj_eq_iff_im]
  exact conj_ramanujanSum q n

/-- Every phase in a nonzero-modulus Ramanujan sum has norm one. -/
@[simp]
theorem norm_ramanujanPhase (q a : ℕ) (n : ℤ) :
    ‖ramanujanPhase q a n‖ = 1 := by
  simp [ramanujanPhase]

/-- The elementary triangle-inequality bound `|c_q(n)| ≤ φ(q)`. -/
theorem norm_ramanujanSum_le_totient (q : ℕ) (n : ℤ) :
    ‖ramanujanSum q n‖ ≤ (Nat.totient q : ℝ) := by
  calc
    ‖ramanujanSum q n‖ = ‖∑ a ∈ reducedResidues q, ramanujanPhase q a n‖ := rfl
    _ ≤ ∑ a ∈ reducedResidues q, ‖ramanujanPhase q a n‖ := norm_sum_le _ _
    _ = ((reducedResidues q).card : ℝ) := by simp
    _ = (Nat.totient q : ℝ) := by
      congr 1
      exact card_reducedResidues q

end

end Erdos1002
