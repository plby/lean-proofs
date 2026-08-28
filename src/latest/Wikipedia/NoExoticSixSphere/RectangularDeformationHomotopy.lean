import Wikipedia.NoExoticSixSphere.RectangularDeformationMatrix

/-!
# A genuine deformation of injective operators onto orthonormal frames

The checked rectangular interpolation is continuous in both operator and
time. It gives a homotopy in the actual space of injective operators from
the identity to inclusion after Gram--Schmidt normalization, fixing frames.
-/

noncomputable section

open Function unitInterval

namespace NoExoticSixSphere.Stiefel

open GLOrthonormalization

namespace RectangularDeformation

variable {X : Type*} [TopologicalSpace X] {N n : ℕ}

theorem continuous_interpolation (A : X → Vector n →L[ℝ] Vector N)
    (hi : ∀ x, Injective (A x)) (hA : Continuous A) : Continuous (interpolation A) := by
  have ht : Continuous (fun p : I × X ↦ (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hnorm : Continuous (Orthonormalization.operator A) :=
    continuous_subtype_val.comp (Orthonormalization.continuous_frame A hi hA)
  exact ((continuous_const.sub ht).smul (hA.comp continuous_snd)).add
    (ht.smul (hnorm.comp continuous_snd))

end RectangularDeformation

namespace Monomorphism

abbrev Space (N n : ℕ) := {A : Vector n →L[ℝ] Vector N // Injective A}

def normalize (N n : ℕ) : C(Space N n, Stiefel.Space N n) :=
  Orthonormalization.map Subtype.val (fun A ↦ A.property) continuous_subtype_val

def inclusion (N n : ℕ) : C(Stiefel.Space N n, Space N n) where
  toFun A := ⟨A.val, Stiefel.injective A⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

def normalizationHomotopy (N n : ℕ) :
    (ContinuousMap.id (Space N n)).Homotopy ((inclusion N n).comp (normalize N n)) where
  toFun p := ⟨RectangularDeformation.interpolation Subtype.val p,
    RectangularDeformation.injective_interpolation Subtype.val (fun A ↦ A.property) p⟩
  continuous_toFun := (RectangularDeformation.continuous_interpolation Subtype.val
    (fun A : Space N n ↦ A.property) continuous_subtype_val).subtype_mk _
  map_zero_left A := Subtype.ext (RectangularDeformation.interpolation_zero Subtype.val A)
  map_one_left A := Subtype.ext (RectangularDeformation.interpolation_one Subtype.val A)

theorem normalize_inclusion {N n : ℕ} (A : Stiefel.Space N n) :
    normalize N n (inclusion N n A) = A := by
  apply Subtype.ext
  exact Orthonormalization.operator_eq_self Subtype.val (inclusion N n A) A.property

theorem normalizationHomotopy_fixed {N n : ℕ} (A : Stiefel.Space N n) (t : I) :
    normalizationHomotopy N n (t, inclusion N n A) = inclusion N n A := by
  apply Subtype.ext
  change (1 - (t : ℝ)) • A.val + (t : ℝ) •
    Orthonormalization.operator Subtype.val (inclusion N n A) = A.val
  rw [Orthonormalization.operator_eq_self Subtype.val (inclusion N n A) A.property]
  change (1 - (t : ℝ)) • A.val + (t : ℝ) • A.val = A.val
  rw [← add_smul]
  simp only [sub_add_cancel, one_smul]

end Monomorphism

end NoExoticSixSphere.Stiefel
