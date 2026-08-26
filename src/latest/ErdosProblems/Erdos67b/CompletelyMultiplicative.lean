import Mathlib.Analysis.Complex.Circle
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.Tactic.FunProp

/-!
# Circle-valued completely multiplicative functions

This file supplies the elementary algebraic and topological infrastructure used in the
compactness part of Tao's proof of the Erdős discrepancy theorem.

There is a small but important modeling point. A monoid homomorphism `ℕ →* Circle` is always
trivial: the absorbing element `0` forces every value to be `1`. Completely multiplicative
unit-circle-valued functions therefore live naturally on the positive naturals `ℕ+`. Equivalently,
one may define a function on all naturals and only demand multiplicativity on nonzero inputs.

The compact parameter space used here is the product of one copy of `Circle` for every natural
prime. A point in this product extends by the usual finite prime-exponent product. Each individual
value of the extension depends on finitely many prime coordinates and is therefore continuous.
-/

open scoped BigOperators

namespace Erdos67b

/-- Natural primes, used as coordinates for the compact parameter space. -/
abbrev PrimeNat := {p : ℕ // p.Prime}

/-- A choice of a unit-circle value at every prime. -/
abbrev PrimeAssignment := PrimeNat → Circle

/-- Completely multiplicative circle-valued functions on the positive natural numbers. -/
abbrev CircleCharacter := ℕ+ →* Circle

/-- A monoid homomorphism on all of `ℕ` into a group is forced to be trivial because `0`
is absorbing. This is why `CircleCharacter` must use `ℕ+`, not `ℕ`. -/
theorem natMonoidHom_circle_eq_one (f : ℕ →* Circle) : f = 1 := by
  apply MonoidHom.ext
  intro n
  apply mul_left_cancel (a := f 0)
  simpa using (f.map_mul 0 n).symm

/-- Read a prime coordinate, and use `1` away from the primes. -/
noncomputable def primeValue (z : PrimeAssignment) (p : ℕ) : Circle :=
  if hp : p.Prime then z ⟨p, hp⟩ else 1

/-- Extend a prime assignment to all natural numbers by the prime-exponent product.

At `0`, where `Nat.factorization` is defined to be `0`, this has the harmless value `1`.
All multiplicative assertions below are restricted to nonzero inputs. -/
noncomputable def primeExtension (z : PrimeAssignment) (n : ℕ) : Circle :=
  n.factorization.prod fun p e ↦ primeValue z p ^ e

/-- The positive-input complete-multiplicativity property for a function defined on `ℕ`. -/
def CompletelyMultiplicativeOnPositive (f : ℕ → Circle) : Prop :=
  f 1 = 1 ∧ ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → f (m * n) = f m * f n

theorem primeExtension_one (z : PrimeAssignment) : primeExtension z 1 = 1 := by
  simp [primeExtension]

@[simp]
theorem primeExtension_prime (z : PrimeAssignment) (p : PrimeNat) :
    primeExtension z p = z p := by
  simp [primeExtension, primeValue, p.2]

theorem primeExtension_mul (z : PrimeAssignment) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    primeExtension z (m * n) = primeExtension z m * primeExtension z n := by
  rw [primeExtension, Nat.factorization_mul hm hn]
  exact Finsupp.prod_add_index' (fun _ ↦ by simp) (fun _ _ _ ↦ by simp [pow_add])

theorem primeExtension_completelyMultiplicative (z : PrimeAssignment) :
    CompletelyMultiplicativeOnPositive (primeExtension z) := by
  exact ⟨primeExtension_one z, fun hm hn ↦ primeExtension_mul z hm hn⟩

/-- Restriction of the prime-exponent extension to positive naturals, packaged as a monoid hom. -/
noncomputable def primeExtensionHom (z : PrimeAssignment) : CircleCharacter where
  toFun n := primeExtension z n
  map_one' := primeExtension_one z
  map_mul' m n := primeExtension_mul z m.2.ne' n.2.ne'

@[simp]
theorem primeExtensionHom_apply (z : PrimeAssignment) (n : ℕ+) :
    primeExtensionHom z n = primeExtension z n := rfl

/-- Prime-exponent evaluation uses only finitely many continuous coordinates. -/
theorem continuous_primeExtension (n : ℕ) :
    Continuous fun z : PrimeAssignment ↦ primeExtension z n := by
  change Continuous fun z : PrimeAssignment ↦
    ∏ p ∈ n.factorization.support, primeValue z p ^ n.factorization p
  apply continuous_finsetProd
  intro p hp
  unfold primeValue
  split_ifs
  · fun_prop
  · simp only [one_pow]
    exact continuous_const

/-- Evaluation of the extension on a positive natural is continuous. -/
theorem continuous_primeExtensionHom_apply (n : ℕ+) :
    Continuous fun z : PrimeAssignment ↦ primeExtensionHom z n := by
  simpa only [primeExtensionHom_apply] using continuous_primeExtension (n : ℕ)

/-- View the extension family in the product topology on all positive-natural values. -/
noncomputable def positiveExtensionFamily (z : PrimeAssignment) : ℕ+ → Circle :=
  fun n ↦ primeExtension z n

theorem continuous_positiveExtensionFamily : Continuous positiveExtensionFamily := by
  exact continuous_pi fun n ↦ continuous_primeExtension (n : ℕ)

/-- The family of all prime-coordinate extensions is compact in the product topology. -/
theorem isCompact_range_positiveExtensionFamily :
    IsCompact (Set.range positiveExtensionFamily) := by
  simpa only [Set.image_univ] using isCompact_univ.image continuous_positiveExtensionFamily

/-- The full prime-coordinate parameter space is compact by Tychonoff. -/
theorem compactSpace_primeAssignment : CompactSpace PrimeAssignment := inferInstance

/-- Restrict a prime assignment to a finite set of prime coordinates. -/
def finitePrimeCoordinates (s : Finset PrimeNat) (z : PrimeAssignment) : s → Circle :=
  fun p ↦ z p

theorem continuous_finitePrimeCoordinates (s : Finset PrimeNat) :
    Continuous (finitePrimeCoordinates s) := by
  unfold finitePrimeCoordinates
  fun_prop

end Erdos67b
