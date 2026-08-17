/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos215.Selector

/-!
Split a nonzero denominator into its full `p`-primary factor and the
complementary factor.  The equality is deliberately oriented as
`d = u * p ^ a`, so that a caller can eliminate `d` with `subst` before
constructing or transporting dependent data such as `LiftData d`.
-/

namespace Erdos215.Selector.PrimeSplit

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-- The exponent of `p` in `d`. -/
def exponent (p d : ℕ) : ℕ := d.factorization p

/-- The factor of `d` complementary to its full `p`-primary part. -/
def complement (p d : ℕ) : ℕ := ordCompl[p] d

/-- The canonical prime split, packaged for dependent downstream uses. -/
structure Data (p d : ℕ) where
  a : ℕ
  u : ℕ
  eq_complement_mul_pow : d = u * p ^ a
  complement_ne_zero : u ≠ 0
  coprime : Nat.Coprime p u

/-- The canonical complement really gives the requested factorization,
in the literal orientation useful for rewriting a `LiftData d`. -/
theorem eq_complement_mul_pow (p d : ℕ) :
    d = complement p d * p ^ exponent p d := by
  simpa only [complement, exponent, mul_comm] using
    (Nat.ordProj_mul_ordCompl_eq_self d p).symm

/-- A nonzero denominator has nonzero prime complement. -/
theorem complement_ne_zero (p d : ℕ) (hd : d ≠ 0) :
    complement p d ≠ 0 := by
  exact (Nat.ordCompl_pos p hd).ne'

/-- The prime is coprime to its complementary factor. -/
theorem coprime_complement {p d : ℕ} (hp : p.Prime) (hd : d ≠ 0) :
    Nat.Coprime p (complement p d) := by
  exact Nat.coprime_ordCompl hp hd

/-- The canonical packaged prime split. -/
def canonical (p d : ℕ) (hp : p.Prime) (hd : d ≠ 0) : Data p d where
  a := exponent p d
  u := complement p d
  eq_complement_mul_pow := eq_complement_mul_pow p d
  complement_ne_zero := complement_ne_zero p d hd
  coprime := coprime_complement hp hd

/-- Existential form intended for `obtain ⟨u, a, rfl, hu, hpu⟩ := ...`.
The prime exponent chosen here is exactly `d.factorization p`, and `u` is
exactly `ordCompl[p] d`. -/
theorem exists_eq_complement_mul_pow {p d : ℕ} (hp : p.Prime) (hd : d ≠ 0) :
    ∃ u a, d = u * p ^ a ∧ u ≠ 0 ∧ Nat.Coprime p u := by
  exact ⟨complement p d, exponent p d, eq_complement_mul_pow p d,
    complement_ne_zero p d hd, coprime_complement hp hd⟩

end

end Erdos215.Selector.PrimeSplit
