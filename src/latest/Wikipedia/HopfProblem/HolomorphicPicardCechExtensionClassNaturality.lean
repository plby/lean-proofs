import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionClass
import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionMap

/-!
# Naturality of the actual Čech extension class

The actual coordinate map of the constructed extensions has endpoints
the original sheaf morphism and the identity on the native integer sheaf.
The genuine derived-category extension-class naturality theorem therefore
identifies its induced map with mathlib's actual sheaf-cohomology map.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.HolomorphicPicard.CechExtension

open HolomorphicFunctionSheaf.SphereH1

variable {X : TopCat.{0}} {F G : TopCat.Sheaf AddCommGrpCat.{0} X}
  {ι : Type} {U : ι → Opens X}

/-- The constructed Čech class is natural for actual sheaf morphisms,
with the map on the target being the genuine `Sheaf.H.map`. -/
theorem classOf_naturality (f : F ⟶ G) (c : CechOneCocycle F U)
    (hU : ∀ x : X, ∃ i : ι, x ∈ U i) :
    CategoryTheory.Sheaf.H.map f 1 (classOf c hU) =
      classOf (Cech.mapCocycle f c) hU := by
  have h := (complex_shortExact c hU).extClass_naturality
    (complex_shortExact (Cech.mapCocycle f c) hU) (complexMap f c)
  change (classOf c hU).comp (Ext.mk₀ f) (add_zero 1) =
    (Ext.mk₀ (𝟙 (degreeSheaf X))).comp
      (classOf (Cech.mapCocycle f c) hU) (zero_add 1) at h
  exact h.trans (Ext.mk₀_id_comp (classOf (Cech.mapCocycle f c) hU))

end Wikipedia.HopfProblem.HolomorphicPicard.CechExtension
