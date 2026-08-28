import Wikipedia.NoExoticSixSphere.TwoResiduePresentation
import Wikipedia.NoExoticSixSphere.JamesSphereAttachingHopfCoefficient
import Wikipedia.NoExoticSixSphere.StableThirdAttachingPresentation
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.SetTheory.Cardinal.Finite

/-!
# The original third-stem stable stages have exactly twenty-four elements

The actual attaching relation has integer coordinate of absolute value
two. Its proved kernel description therefore gives a bijection from
Fin 2 times ZMod 12 onto the original pi8(S5). Transport through the
actual suspension equivalences gives the same finite cardinality and
exponent bound at every later third-stem stage. Cyclicity is not inferred.
-/

noncomputable section

open scoped Topology

namespace NoExoticSixSphere.SphereFiveEighth

def normalEquiv : (Fin 2 × ZMod 12) ≃ π_ 8 (Sphere 5) (spherePole 5) :=
  TwoResiduePresentation.normalEquiv projection relation.1.toAdd relation.2.toAdd
    projection_eq_one_iff_coordinates
    JamesSphere.AttachingSquare.originalAttachingClass_hopf_natAbs_two projection_surjective

theorem normalEquiv_apply (x : Fin 2 × ZMod 12) :
    normalEquiv x = projection (Multiplicative.ofAdd (x.1.val : ℤ), Multiplicative.ofAdd x.2) := rfl

instance finitePiEight : Finite (π_ 8 (Sphere 5) (spherePole 5)) :=
  Finite.of_equiv (Fin 2 × ZMod 12) normalEquiv

theorem cardinality : Nat.card (π_ 8 (Sphere 5) (spherePole 5)) = 24 := by
  rw [← Nat.card_congr normalEquiv]
  simp [Nat.card_eq_fintype_card]

theorem pow_twentyFour (x : π_ 8 (Sphere 5) (spherePole 5)) : x ^ 24 = 1 := by
  rw [← cardinality]
  exact pow_card_eq_one'

end NoExoticSixSphere.SphereFiveEighth

namespace NoExoticSixSphere.StableThirdAttaching

def normalEquiv (k : ℕ) : (Fin 2 × ZMod 12) ≃ Stage k :=
  SphereFiveEighth.normalEquiv.trans (fromFirst k).toEquiv

theorem normalEquiv_apply (k : ℕ) (x : Fin 2 × ZMod 12) :
    normalEquiv k x = projection k
      (Multiplicative.ofAdd (x.1.val : ℤ), Multiplicative.ofAdd x.2) := rfl

instance finiteStage (k : ℕ) : Finite (Stage k) :=
  Finite.of_equiv (Fin 2 × ZMod 12) (normalEquiv k)

theorem cardinality (k : ℕ) : Nat.card (Stage k) = 24 := by
  rw [← Nat.card_congr (fromFirst k).toEquiv]
  exact SphereFiveEighth.cardinality

theorem pow_twentyFour (k : ℕ) (x : Stage k) : x ^ 24 = 1 := by
  rw [← cardinality k]
  exact pow_card_eq_one'

end NoExoticSixSphere.StableThirdAttaching
