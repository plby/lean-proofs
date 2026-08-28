import Wikipedia.HopfProblem.ThreefoldFundamentalGroupGluingSurjectivity
import Wikipedia.HopfProblem.SpecialPeriodsEllipticAttachingSurjectivity
import Wikipedia.HopfProblem.SpecialPeriodsCuspAttaching

/-!
# The actual regular family generates the threefold fundamental group

The two genuine elliptic overlaps and the genuine cusp overlap each
surject onto their filling fundamental group.  Applying the proved
van Kampen theorem to the actual finite attachment stages therefore
shows that the inclusion of the original regular family surjects onto
the fundamental group of the constructed compact threefold.
No attaching-map surjectivity is left as a hypothesis.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold

/-- All three actual filling groups come from their full regular overlaps. -/
theorem overlapFillingHom_surjective (i : Puncture) :
    Function.Surjective (overlapFillingHom i) := by
  cases i with
  | none => exact cusp_overlapFillingHom_surjective
  | some j => exact overlapFillingHom_elliptic_surjective j

/-- The regular lifted patch generates the fundamental group of the
actual threefold at every one of its basepoints. -/
theorem regularLiftedInclusion_fundamentalGroup_surjective (x : liftedPatch none) :
    Function.Surjective (FundamentalGroup.map regularLiftedInclusion x) :=
  regularLiftedInclusion_fundamentalGroup_map_surjective overlapFillingHom_surjective x

/-- The bundled literal inclusion of the original regular quotient family. -/
def regularFamilyInclusionMap : C(SpecialRegularFamily, Space) :=
  ⟨inclusion none, (inclusion_openEmbedding none).continuous⟩

@[simp] theorem regularFamilyInclusionMap_apply (x : SpecialRegularFamily) :
    regularFamilyInclusionMap x = inclusion none x := rfl

/-- This map is the actual geometric inclusion, not a homomorphism merely
chosen to have the expected generator images. -/
theorem regularFamilyInclusionMap_fundamentalGroup_surjective (x : SpecialRegularFamily) :
    Function.Surjective (FundamentalGroup.map regularFamilyInclusionMap x) := by
  let e := gluingData.patchHomeomorph none
  have hpatch := regularLiftedInclusion_fundamentalGroup_surjective (e x)
  have hlocal := (homeomorphFundamentalGroupEquiv e x).surjective
  have hmap :
      (FundamentalGroup.map regularLiftedInclusion (e x)).comp
          (homeomorphFundamentalGroupEquiv e x).toMonoidHom =
        FundamentalGroup.map regularFamilyInclusionMap x := by
    ext γ
    obtain ⟨p⟩ := γ
    apply congrArg Path.Homotopic.Quotient.mk
    ext t
    rfl
  rw [← hmap]
  exact hpatch.comp hlocal

end Wikipedia.HopfProblem.SpecialPeriods.Threefold
