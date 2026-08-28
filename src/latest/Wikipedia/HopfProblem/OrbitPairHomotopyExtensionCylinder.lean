import Wikipedia.HopfProblem.OrbitPairHomotopyExtensionPushout

/-!
# The universal cylinder retraction supplied by homotopy extension

Apply the extension property to the union of the cylinder's bottom and
its side over the included subspace. The resulting map retains both
pieces exactly. This formulation can subsequently be multiplied by a
parameter space without assuming that arbitrary products preserve
quotient maps.
-/

noncomputable section

universe u

open CategoryTheory unitInterval

namespace Wikipedia.HopfProblem.OrbitPair.HomotopyExtension

variable {A B : TopCat.{u}} (i : A ⟶ B)

def cylinderBase : Set (I × B) := {p | p.1 = 0 ∨ p.2 ∈ Set.range i}

def cylinderBottom : C(B, ↥(cylinderBase i)) where
  toFun b := ⟨(0, b), Or.inl rfl⟩
  continuous_toFun := (continuous_const.prodMk continuous_id).subtype_mk _

def cylinderSide : C(I × A, ↥(cylinderBase i)) where
  toFun p := ⟨(p.1, i p.2), Or.inr ⟨p.2, rfl⟩⟩
  continuous_toFun := (continuous_fst.prodMk (i.hom.continuous.comp continuous_snd)).subtype_mk _

theorem exists_cylinder_retraction (hi : HasHomotopyExtension i) :
    ∃ R : C(I × B, ↥(cylinderBase i)),
      (∀ b, R (0, b) = cylinderBottom i b) ∧
        ∀ t a, R (t, i a) = cylinderSide i (t, a) :=
  hi (TopCat.of ↥(cylinderBase i)) (cylinderBottom i) (cylinderSide i) (fun _ ↦ rfl)

end Wikipedia.HopfProblem.OrbitPair.HomotopyExtension
