import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionKernel
import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionLocalLift
import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionSheafBasic

/-!
# The actual short exact sheaf extension of every Čech cocycle

Kernel gluing and the explicit local degree lifts prove short exactness
after genuine sheafification. The canonical sheafification isomorphism
at the first endpoint identifies this sequence with the one whose first
object is the original sheaf itself. No kernel or lifting premise remains.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.HolomorphicPicard.CechExtension

open HolomorphicFunctionSheaf.SphereH1

variable {X : TopCat.{0}} {F : TopCat.Sheaf AddCommGrpCat.{0} X}
  {ι : Type} {U : ι → Opens X} (c : CechOneCocycle F U)

/-- The original-endpoint complex is canonically the actual sheafified
presheaf complex; the middle and quotient comparisons are identities. -/
def complexSheafificationIso :
    complex c ≅ sheafifiedComplex (presheafComplex c) := by
  refine ShortComplex.isoMk (CategoryTheory.sheafificationIso F)
    (Iso.refl _) (Iso.refl _) ?_ ?_
  · apply CategoryTheory.Sheaf.hom_ext
    change CategoryTheory.toSheafify (Opens.grothendieckTopology X) F.obj ≫
        CategoryTheory.sheafifyMap (Opens.grothendieckTopology X) (inclusionPre c) =
      (inclusionPre c ≫ unit c) ≫ 𝟙 (extensionSheaf c).obj
    rw [Category.comp_id]
    exact (CategoryTheory.toSheafify_naturality
      (Opens.grothendieckTopology X) (inclusionPre c)).symm
  · exact (Category.id_comp (projection c)).trans (Category.comp_id (projection c)).symm

/-- Every actual Čech one-cocycle on an actual open cover determines
a genuine short exact sequence with its original sheaf as first object. -/
theorem complex_shortExact (hU : ∀ x : X, ∃ i : ι, x ∈ U i) :
    (complex c).ShortExact := by
  apply (ShortComplex.shortExact_iff_of_iso (complexSheafificationIso c)).mpr
  exact sheafifiedComplex_shortExact (presheafComplex c)
    (presheafComplex_exact c hU) (inclusionPre_mono c hU)
    (projectionPre_locallySurjective c hU)

theorem inclusion_mono (hU : ∀ x : X, ∃ i : ι, x ∈ U i) :
    Mono (inclusion c) :=
  (complex_shortExact c hU).mono_f

theorem projection_epi (hU : ∀ x : X, ∃ i : ι, x ∈ U i) :
    Epi (projection c) :=
  (complex_shortExact c hU).epi_g

end Wikipedia.HopfProblem.HolomorphicPicard.CechExtension
