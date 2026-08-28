import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Data.Fin.VecNotation

/-!
# The canonical two-coordinate divisibility quotient

Reduction of the second integer coordinate modulo `d` presents the
quotient by the lattice where that coordinate is divisible by `d`.
The construction includes `d = 0`, where the quotient is infinite cyclic
and its additive index, expressed as a natural cardinal, is zero.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology.CoverAlgebra

abbrev Coordinates := Fin 2 → ℤ

/-- The second-coordinate residue, with the canonical integer module structure. -/
def secondResidue (d : ℕ) : Coordinates →ₗ[ℤ] ZMod d :=
  (Int.castAddHom (ZMod d)).toIntLinearMap.comp (LinearMap.proj 1)

@[simp] theorem secondResidue_apply (d : ℕ) (v : Coordinates) :
    secondResidue d v = (v 1 : ZMod d) := rfl

/-- The sublattice with second coordinate divisible by `d`. -/
def divisibleSecond (d : ℕ) : Submodule ℤ Coordinates :=
  LinearMap.ker (secondResidue d)

theorem mem_divisibleSecond_iff (d : ℕ) (v : Coordinates) :
    v ∈ divisibleSecond d ↔ (d : ℤ) ∣ v 1 := by
  rw [divisibleSecond, LinearMap.mem_ker, secondResidue_apply,
    ZMod.intCast_zmod_eq_zero_iff_dvd]

theorem secondResidue_surjective (d : ℕ) : Function.Surjective (secondResidue d) := by
  intro z
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective z
  exact ⟨![0, k], rfl⟩

/-- The actual quotient lattice is canonically the second-coordinate residue module. -/
def divisibleSecondQuotientEquivZMod (d : ℕ) :
    (Coordinates ⧸ divisibleSecond d) ≃ₗ[ℤ] ZMod d :=
  (secondResidue d).quotKerEquivOfSurjective (secondResidue_surjective d)

@[simp] theorem divisibleSecondQuotientEquivZMod_apply_mk (d : ℕ) (v : Coordinates) :
    divisibleSecondQuotientEquivZMod d (Submodule.Quotient.mk v) = (v 1 : ZMod d) := rfl

@[simp] theorem divisibleSecondQuotientEquivZMod_symm_apply_intCast (d : ℕ) (k : ℤ) :
    (divisibleSecondQuotientEquivZMod d).symm (k : ZMod d) =
      Submodule.Quotient.mk ![0, k] := by
  apply (divisibleSecondQuotientEquivZMod d).injective
  rw [LinearEquiv.apply_symm_apply, divisibleSecondQuotientEquivZMod_apply_mk]
  rfl

/-- The exact additive index, including the infinite-index convention at zero. -/
theorem divisibleSecond_index (d : ℕ) :
    (divisibleSecond d).toAddSubgroup.index = d := by
  change Nat.card (Coordinates ⧸ divisibleSecond d) = d
  calc
    _ = Nat.card (ZMod d) := Nat.card_congr (divisibleSecondQuotientEquivZMod d).toEquiv
    _ = d := Nat.card_zmod d

@[simp] theorem divisibleSecond_one : divisibleSecond 1 = ⊤ := by
  ext v
  simp [mem_divisibleSecond_iff]

theorem divisibleSecondQuotient_subsingleton_one :
    Subsingleton (Coordinates ⧸ divisibleSecond 1) :=
  Submodule.Quotient.subsingleton_iff.mpr divisibleSecond_one

end Wikipedia.HopfProblem.Elliptic.HigherHomology.CoverAlgebra
