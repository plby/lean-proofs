import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyFineExtension

/-!
# Additivity and restriction of actual supported extensions

The uniquely glued extension by zero is additive, commutes with actual
restriction, and returns the original supported endomorphism when its
input is a restriction of a section already defined on the larger open.
These are proved from the two defining restrictions, not assumed as
properties of an unspecified extension operator.
-/

noncomputable section

open Set TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology

open HolomorphicFunctionSheaf.SphereH1

variable {X : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat.{0} X)
  (K : Set X) (hK : IsClosed K) (V : Opens X) (hKV : K ⊆ V)
  (φ : F ⟶ F) (hφ : IsZeroOn φ (outsideSupport K hK))

theorem supportedExtension_zero (U : Opens X) :
    supportedExtension F K hK V hKV φ hφ U 0 = 0 := by
  apply supportedExtension_ext F K hK V hKV U
  · simp only [supportedExtension_on, map_zero]
  · simp only [supportedExtension_off, map_zero]

theorem supportedExtension_add (U : Opens X) (s t : Section F (U ⊓ V)) :
    supportedExtension F K hK V hKV φ hφ U (s + t) =
      supportedExtension F K hK V hKV φ hφ U s +
        supportedExtension F K hK V hKV φ hφ U t := by
  apply supportedExtension_ext F K hK V hKV U
  · simp only [supportedExtension_on, map_add]
  · simp only [supportedExtension_off, map_add, add_zero]

/-- The actual extension-by-zero additive homomorphism. -/
def supportedExtensionHom (U : Opens X) : Section F (U ⊓ V) →+ Section F U where
  toFun := supportedExtension F K hK V hKV φ hφ U
  map_zero' := supportedExtension_zero F K hK V hKV φ hφ U
  map_add' := supportedExtension_add F K hK V hKV φ hφ U

theorem supportedExtension_sub (U : Opens X) (s t : Section F (U ⊓ V)) :
    supportedExtension F K hK V hKV φ hφ U (s - t) =
      supportedExtension F K hK V hKV φ hφ U s -
        supportedExtension F K hK V hKV φ hφ U t :=
  (supportedExtensionHom F K hK V hKV φ hφ U).map_sub s t

/-- Restricting the actual extension gives the actual extension of the
restricted input on the smaller open set. -/
theorem supportedExtension_restrict (U W : Opens X) (hWU : W ≤ U)
    (s : Section F (U ⊓ V)) :
    res F hWU (supportedExtension F K hK V hKV φ hφ U s) =
      supportedExtension F K hK V hKV φ hφ W
        (res F (inf_le_inf hWU le_rfl) s) := by
  apply supportedExtension_ext F K hK V hKV W
  · have h := congrArg (res F (U := U ⊓ V) (V := W ⊓ V) (inf_le_inf hWU le_rfl))
      (supportedExtension_on F K hK V hKV φ hφ U s)
    rw [res_trans, res_map] at h
    rw [res_trans, supportedExtension_on]
    exact h
  · have h := congrArg
      (res F (U := U ⊓ outsideSupport K hK) (V := W ⊓ outsideSupport K hK)
        (inf_le_inf hWU le_rfl))
      (supportedExtension_off F K hK V hKV φ hφ U s)
    rw [res_trans, map_zero] at h
    rw [res_trans, supportedExtension_off]
    exact h

/-- If the input is already the restriction of a section on the larger
open, extension after the supported action is that actual action. -/
theorem supportedExtension_restriction_eq_action (U : Opens X) (s : Section F U) :
    supportedExtension F K hK V hKV φ hφ U (res F inf_le_left s) =
      φ.hom.app (op U) s := by
  apply supportedExtension_ext F K hK V hKV U
  · rw [supportedExtension_on, res_map]
  · rw [supportedExtension_off, res_map,
      hφ (U ⊓ outsideSupport K hK) inf_le_right]
    rfl

end Wikipedia.HopfProblem.HolomorphicSheafCohomology
