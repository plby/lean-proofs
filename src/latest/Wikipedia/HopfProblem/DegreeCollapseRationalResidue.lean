import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic

/-!
# The literal rational-mod-integer target of meridian characters

Use the quotient of the rational numbers by the integer span of one.
Vanishing of an integral ratio in this quotient is exactly divisibility
of its numerator by its nonzero denominator.
-/

noncomputable section

namespace Wikipedia.HopfProblem.DegreeCollapse.RationalResidue

def integers : Submodule ℤ ℚ := Submodule.span ℤ {(1 : ℚ)}

abbrev Value := ℚ ⧸ integers

def residue : ℚ →ₗ[ℤ] Value := integers.mkQ

theorem residue_eq_zero_iff (x : ℚ) : residue x = 0 ↔ ∃ k : ℤ, (k : ℚ) = x := by
  change (Submodule.Quotient.mk x : ℚ ⧸ integers) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero, integers, Submodule.mem_span_singleton]
  simp only [zsmul_eq_mul, mul_one]

@[simp] theorem residue_intCast (k : ℤ) : residue (k : ℚ) = 0 :=
  (residue_eq_zero_iff _).mpr ⟨k, rfl⟩

theorem residue_div_eq_zero_iff (p l : ℤ) (hl : l ≠ 0) :
    residue ((p : ℚ) / (l : ℚ)) = 0 ↔ l ∣ p := by
  have hlQ : (l : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hl
  rw [residue_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩
    have he : (k : ℚ) * (l : ℚ) = (p : ℚ) := (eq_div_iff hlQ).mp hk
    have heZ : k * l = p := by exact_mod_cast he
    exact ⟨k, heZ.symm.trans (mul_comm k l)⟩
  · rintro ⟨k, hk⟩
    refine ⟨k, (eq_div_iff hlQ).mpr ?_⟩
    rw [hk, Int.cast_mul]
    ring

theorem residue_neg_div_eq_zero_iff (p l : ℤ) (hl : l ≠ 0) :
    residue (-(p : ℚ) / (l : ℚ)) = 0 ↔ l ∣ p := by
  simpa only [Int.cast_neg, dvd_neg] using residue_div_eq_zero_iff (-p) l hl

end Wikipedia.HopfProblem.DegreeCollapse.RationalResidue
