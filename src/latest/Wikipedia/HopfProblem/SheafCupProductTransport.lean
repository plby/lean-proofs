import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Group.Hom.Instances

/-!
# Transporting an actual bilinear pairing through additive comparisons

This elementary helper retains the representative formula and coefficient
naturality of a given pairing.  Its later application uses the proved
native sheaf-cohomology/Godement comparisons; it does not supply those
comparisons as cohomological assumptions.
-/

namespace Wikipedia.HopfProblem.SheafCupProduct

variable {A B H K : Type*} [AddCommGroup A] [AddCommGroup B]
  [AddCommGroup H] [AddCommGroup K]

/-- The pairing transported through two actual additive equivalences. -/
def transportPairing (e : H ≃+ A) (f : K ≃+ B) (p : A →+ A →+ B) : H →+ H →+ K where
  toFun a := f.symm.toAddMonoidHom.comp ((p (e a)).comp e.toAddMonoidHom)
  map_zero' := by
    ext b
    simp
  map_add' a b := by
    ext c
    simp

@[simp] theorem transportPairing_apply (e : H ≃+ A) (f : K ≃+ B)
    (p : A →+ A →+ B) (a b : H) :
    transportPairing e f p a b = f.symm (p (e a) (e b)) := rfl

/-- The chosen comparison preserves the literal product formula. -/
@[simp] theorem transportPairing_comparison (e : H ≃+ A) (f : K ≃+ B)
    (p : A →+ A →+ B) (a b : H) :
    f (transportPairing e f p a b) = p (e a) (e b) :=
  f.apply_symm_apply _

theorem transportPairing_skew (e : H ≃+ A) (f : K ≃+ B)
    (p : A →+ A →+ B) (hp : ∀ a b, p a b = -p b a) (a b : H) :
    transportPairing e f p a b = -transportPairing e f p b a := by
  apply f.injective
  rw [map_neg, transportPairing_comparison, transportPairing_comparison]
  exact hp _ _

variable {A' B' H' K' : Type*} [AddCommGroup A'] [AddCommGroup B']
  [AddCommGroup H'] [AddCommGroup K']

/-- A commuting coefficient diagram retains the original pairing naturality. -/
theorem transportPairing_naturality
    (e : H ≃+ A) (f : K ≃+ B) (e' : H' ≃+ A') (f' : K' ≃+ B')
    (p : A →+ A →+ B) (p' : A' →+ A' →+ B')
    (m₁ : A →+ A') (m₂ : B →+ B') (h₁ : H →+ H') (h₂ : K →+ K')
    (he : ∀ a, e' (h₁ a) = m₁ (e a)) (hf : ∀ a, f' (h₂ a) = m₂ (f a))
    (hp : ∀ a b, m₂ (p a b) = p' (m₁ a) (m₁ b)) (a b : H) :
    h₂ (transportPairing e f p a b) = transportPairing e' f' p' (h₁ a) (h₁ b) := by
  apply f'.injective
  rw [hf, transportPairing_comparison, transportPairing_comparison, he, he]
  exact hp _ _

end Wikipedia.HopfProblem.SheafCupProduct
