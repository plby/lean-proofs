import Wikipedia.HopfProblem.SheafCupProductTransport
import Mathlib.LinearAlgebra.BilinearMap

/-!
# Retaining actual scalar maps through additive comparisons

The scalar maps here are given endomorphisms, not structures assigned
through an equivalence.  Commuting comparison squares transfer the two
literal scalar identities, after which an already additive pairing can
be bundled as a bilinear map for the original module structures.
-/

namespace Wikipedia.HopfProblem.SheafCupProduct

section Comparison

variable {A B H K : Type*} [AddCommGroup A] [AddCommGroup B]
  [AddCommGroup H] [AddCommGroup K]

theorem transportPairing_scalar_left
    (e : H ≃+ A) (f : K ≃+ B) (p : A →+ A →+ B)
    (sA : A →+ A) (sB : B →+ B) (sH : H →+ H) (sK : K →+ K)
    (he : ∀ a, e (sH a) = sA (e a)) (hf : ∀ a, f (sK a) = sB (f a))
    (hp : ∀ a b, p (sA a) b = sB (p a b)) (a b : H) :
    transportPairing e f p (sH a) b = sK (transportPairing e f p a b) := by
  apply f.injective
  rw [transportPairing_comparison, he, hp, hf, transportPairing_comparison]

theorem transportPairing_scalar_right
    (e : H ≃+ A) (f : K ≃+ B) (p : A →+ A →+ B)
    (sA : A →+ A) (sB : B →+ B) (sH : H →+ H) (sK : K →+ K)
    (he : ∀ a, e (sH a) = sA (e a)) (hf : ∀ a, f (sK a) = sB (f a))
    (hp : ∀ a b, p a (sA b) = sB (p a b)) (a b : H) :
    transportPairing e f p a (sH b) = sK (transportPairing e f p a b) := by
  apply f.injective
  rw [transportPairing_comparison, he, hp, hf, transportPairing_comparison]

end Comparison

section Linear

variable {R H K : Type*} [CommSemiring R] [AddCommGroup H] [AddCommGroup K]
  [Module R H] [Module R K]

/-- Bundle an additive pairing only after proving both scalar identities
for the already given module structures. -/
def pairingLinear (p : H →+ H →+ K)
    (hl : ∀ (z : R) a b, p (z • a) b = z • p a b)
    (hr : ∀ (z : R) a b, p a (z • b) = z • p a b) : H →ₗ[R] H →ₗ[R] K :=
  LinearMap.mk₂ R (fun a b => p a b)
    (fun a b d => congrArg (fun q : H →+ K => q d) (p.map_add a b))
    hl (fun a b d => (p a).map_add b d) (fun z a b => hr z a b)

@[simp] theorem pairingLinear_apply (p : H →+ H →+ K)
    (hl : ∀ (z : R) a b, p (z • a) b = z • p a b)
    (hr : ∀ (z : R) a b, p a (z • b) = z • p a b) (a b : H) :
    pairingLinear p hl hr a b = p a b := rfl

end Linear

end Wikipedia.HopfProblem.SheafCupProduct
