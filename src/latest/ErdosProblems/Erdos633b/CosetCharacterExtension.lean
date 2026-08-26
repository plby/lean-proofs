import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic.Abel

/-! Extend a subgroup character to a function on the ambient group by
choosing coset representatives. The extension is equivariant, not claimed
to be continuous or a homomorphism on the whole ambient group. -/

namespace Erdos633b

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

noncomputable def cosetRepresentative (G : AddSubgroup A) (x : A) : A :=
  Quotient.out (QuotientAddGroup.mk x : A ⧸ G)

theorem sub_cosetRepresentative_mem (G : AddSubgroup A) (x : A) :
    x - cosetRepresentative G x ∈ G := by
  apply QuotientAddGroup.eq_iff_sub_mem.mp
  exact (Quotient.out_eq' (QuotientAddGroup.mk x : A ⧸ G)).symm

theorem cosetRepresentative_add (G : AddSubgroup A) (x : A) (g : G) :
    cosetRepresentative G (x + g) = cosetRepresentative G x := by
  unfold cosetRepresentative
  apply congrArg Quotient.out
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  simpa only [add_sub_cancel_left] using g.property

noncomputable def cosetCharacterExtension (G : AddSubgroup A) (φ : G →+ B) (x : A) : B :=
  φ ⟨x - cosetRepresentative G x, sub_cosetRepresentative_mem G x⟩

theorem cosetCharacterExtension_add (G : AddSubgroup A) (φ : G →+ B) (x : A) (g : G) :
    cosetCharacterExtension G φ (x + g) = cosetCharacterExtension G φ x + φ g := by
  unfold cosetCharacterExtension
  rw [← map_add]
  congr 1
  apply Subtype.ext
  change x + (g : A) - cosetRepresentative G (x + g) =
    (x - cosetRepresentative G x) + g
  rw [cosetRepresentative_add]
  abel

end Erdos633b
