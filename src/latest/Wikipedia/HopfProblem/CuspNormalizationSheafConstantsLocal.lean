import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsBasic
import Mathlib.Topology.Sheaves.LocallySurjective

/-!
# Local constant representatives of actual constant-sheaf sections

Sheafification is locally surjective.  Applying that theorem to the
actual constant presheaf proves that every section of the actual
constant sheaf is a constant representative on a neighbourhood of each
point.  No connectedness of the original open set is required.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.CuspNormalization.SheafConstants

/-- Every section of the actual constant sheaf is locally the image of
one complex number under the actual sheafification map. -/
theorem exists_constant_restriction {X : TopCat.{0}} (U : Opens X)
    (s : (complexSheaf X).obj.obj (op U)) (x : X) (hx : x ∈ U) :
    ∃ (V : Opens X) (hVU : V ≤ U) (c : ℂ), x ∈ V ∧
      (unit X).app (op V) c = (complexSheaf X).obj.map (homOfLE hVU).op s := by
  have hloc : TopCat.Presheaf.IsLocallySurjective (unit X) := by
    change CategoryTheory.Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology X)
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (constantPresheaf X))
    infer_instance
  obtain ⟨V, hVU, ⟨c, hc⟩, hxV⟩ :=
    (TopCat.Presheaf.isLocallySurjective_iff (unit X)).mp hloc U s x hx
  exact ⟨V, hVU, c, hxV, hc⟩

/-- Any sheaf map constructed from constants is locally its literal
constant representative, on the same neighbourhood as its source. -/
theorem lift_locally_constant {X : TopCat.{0}} (F : RingSheaf X)
    (φ : constantPresheaf X ⟶ F.obj) (U : Opens X)
    (s : (complexSheaf X).obj.obj (op U)) (x : X) (hx : x ∈ U) :
    ∃ (V : Opens X) (hVU : V ≤ U) (c : ℂ), x ∈ V ∧
      F.obj.map (homOfLE hVU).op ((lift F φ).hom.app (op U) s) = φ.app (op V) c := by
  obtain ⟨V, hVU, c, hxV, hc⟩ := exists_constant_restriction U s x hx
  refine ⟨V, hVU, c, hxV, ?_⟩
  have hn := ConcreteCategory.congr_hom
    ((lift F φ).hom.naturality (homOfLE hVU).op) s
  calc
    F.obj.map (homOfLE hVU).op ((lift F φ).hom.app (op U) s) =
        (lift F φ).hom.app (op V) ((complexSheaf X).obj.map (homOfLE hVU).op s) :=
      hn.symm
    _ = (lift F φ).hom.app (op V) ((unit X).app (op V) c) := congrArg _ hc.symm
    _ = φ.app (op V) c := lift_app_unit F φ V c

end Wikipedia.HopfProblem.CuspNormalization.SheafConstants
