import Wikipedia.HopfProblem.SheafCupProductCofaceIdentities
import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalComplex
import Mathlib.Algebra.Group.PUnit

/-!
# Cofaces and two commuting derivations for the actual Dolbeault total algebra

The input consists only of the original ring cofaces and additive
derivations, with their Leibniz and commuting identities. Neither a
total differential identity nor a cup-product identity is assumed.
-/

universe u

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Algebra

def pairMap {A B : Type u} [AddCommGroup A] [AddCommGroup B]
    (f : A →+ B) : A × A →+ B × B :=
  (f.comp (AddMonoidHom.fst A A)).prod (f.comp (AddMonoidHom.snd A A))

@[simp] theorem pairMap_apply {A B : Type u} [AddCommGroup A] [AddCommGroup B]
    (f : A →+ B) (x : A × A) : pairMap f x = (f x.1, f x.2) := rfl

def gradient {A : Type u} [AddCommGroup A] (f g : A →+ A) : A →+ A × A := f.prod g

@[simp] theorem gradient_apply {A : Type u} [AddCommGroup A]
    (f g : A →+ A) (x : A) : gradient f g x = (f x, g x) := rfl

def curl {A : Type u} [AddCommGroup A] (f g : A →+ A) : A × A →+ A :=
  f.comp (AddMonoidHom.snd A A) - g.comp (AddMonoidHom.fst A A)

@[simp] theorem curl_apply {A : Type u} [AddCommGroup A]
    (f g : A →+ A) (x : A × A) : curl f g x = f x.2 - g x.1 := rfl

/-- Actual low-degree ring cofaces and compatible pairs of additive derivations. -/
structure Data (R0 R1 R2 R3 : Type u)
    [CommRing R0] [CommRing R1] [CommRing R2] [CommRing R3] where
  cofaces : SheafCupProduct.Coface.Data R0 R1 R2 R3
  deriv0 : Fin 2 → R0 →+ R0
  deriv1 : Fin 2 → R1 →+ R1
  deriv2 : Fin 2 → R2 →+ R2
  leibniz0 : ∀ j x y, deriv0 j (x * y) = deriv0 j x * y + x * deriv0 j y
  leibniz1 : ∀ j x y, deriv1 j (x * y) = deriv1 j x * y + x * deriv1 j y
  leibniz2 : ∀ j x y, deriv2 j (x * y) = deriv2 j x * y + x * deriv2 j y
  commute0 : ∀ x, deriv0 0 (deriv0 1 x) = deriv0 1 (deriv0 0 x)
  commute1 : ∀ x, deriv1 0 (deriv1 1 x) = deriv1 1 (deriv1 0 x)
  coface0 : ∀ j i x, deriv1 j (cofaces.δ0 i x) = cofaces.δ0 i (deriv0 j x)
  coface1 : ∀ j i x, deriv2 j (cofaces.δ1 i x) = cofaces.δ1 i (deriv1 j x)

namespace Data

variable {R0 R1 R2 R3 : Type u}
  [CommRing R0] [CommRing R1] [CommRing R2] [CommRing R3]
  (D : Data R0 R1 R2 R3)

abbrev gradient0 : R0 →+ R0 × R0 := gradient (D.deriv0 0) (D.deriv0 1)
abbrev gradient1 : R1 →+ R1 × R1 := gradient (D.deriv1 0) (D.deriv1 1)
abbrev gradient2 : R2 →+ R2 × R2 := gradient (D.deriv2 0) (D.deriv2 1)
abbrev curl0 : R0 × R0 →+ R0 := curl (D.deriv0 0) (D.deriv0 1)
abbrev curl1 : R1 × R1 →+ R1 := curl (D.deriv1 0) (D.deriv1 1)

/-- Each actual derivation commutes with the first alternating coface differential. -/
theorem deriv1_d0 (j : Fin 2) (x : R0) :
    D.deriv1 j (D.cofaces.d0 x) = D.cofaces.d0 (D.deriv0 j x) := by
  simp only [SheafCupProduct.Coface.Data.d0_apply, map_sub, D.coface0]

/-- Each actual derivation commutes with the next alternating coface differential. -/
theorem deriv2_d1 (j : Fin 2) (x : R1) :
    D.deriv2 j (D.cofaces.d1 x) = D.cofaces.d1 (D.deriv1 j x) := by
  simp only [SheafCupProduct.Coface.Data.d1_apply, map_add, map_sub, D.coface1]

@[simp] theorem curl0_gradient0 (x : R0) : D.curl0 (D.gradient0 x) = 0 := by
  simp only [curl_apply, gradient_apply, D.commute0, sub_self]

@[simp] theorem curl1_gradient1 (x : R1) : D.curl1 (D.gradient1 x) = 0 := by
  simp only [curl_apply, gradient_apply, D.commute1, sub_self]

end Data

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Algebra
