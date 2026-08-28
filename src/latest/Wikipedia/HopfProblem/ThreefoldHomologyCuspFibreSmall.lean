import Wikipedia.HopfProblem.ThreefoldHomologyFinitenessCuspHomology
import Wikipedia.HopfProblem.CuspCentralHomologySpecialization
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationHomotopy

/-!
# Small literal cusp fibres generate the homology of the full cap

Choose a common radius for the proved controlled deformation and the
proved actual specialization theorem.  The controlled deformation gives
a homotopy, inside the original full cap, between its literal nonzero
fibre inclusion and the central inclusion after the prescribed collapse.
The latter two maps are surjective on actual integral homology.

The full cap keeps its original fixed radius throughout; no comparison
between that radius and an unproved deformation radius is required.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.ThreefoldHomologyCuspFibre

open SpecialPeriods.CuspFamily CuspRetraction CuspControlledRetraction
open CuspCentralHomology CuspPositiveRetraction ThreefoldHomologyFinitenessCusp
open SingularMayerVietoris PeriodTorusHigherHomology

/-- The literal inclusion of a nonzero-parameter fibre in the original full quotient. -/
def actualFibreInclusion (D : Data) (t : ℂ) :
    C(ActualQuotientFibre D.correction D.radius t, FullSpace D) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The literal closed sub-tube inclusion, with the original quotient radius unchanged. -/
def closedTubeInclusion (D : Data) (η : ℝ) :
    C(ClosedQuotient D.correction D.radius η, FullSpace D) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- A controlled deformation gives a genuine full-cap homotopy on each contained fibre. -/
def fibreCentralHomotopy (D : Data) (η : ℝ) (hη : 0 ≤ η)
    (R : C(ClosedQuotient D.correction D.radius η,
      QuotientCentralFibre D.correction D.radius))
    (H : (ContinuousMap.id (ClosedQuotient D.correction D.radius η)).Homotopy
      ((quotientCentralIntoClosed D.correction D.radius η hη).comp R))
    (t : ℂ) (htη : ‖t‖ ≤ η) :
    (actualFibreInclusion D t).Homotopy
      ((fullCentralInclusion D).comp
        (R.comp (actualFibreIntoClosed D.correction D.radius η t htη))) where
  toFun p := (H (p.1, actualFibreIntoClosed D.correction D.radius η t htη p.2)).val
  continuous_toFun := continuous_subtype_val.comp
    (H.continuous.comp (continuous_fst.prodMk
      ((actualFibreIntoClosed D.correction D.radius η t htη).continuous.comp continuous_snd)))
  map_zero_left q := congrArg Subtype.val
    (H.map_zero_left (actualFibreIntoClosed D.correction D.radius η t htη q))
  map_one_left q := congrArg Subtype.val
    (H.map_one_left (actualFibreIntoClosed D.correction D.radius η t htη q))

/-- A derived common radius works in all integral homology degrees, for
the literal fibre inclusion into the entire original fixed-radius cap. -/
theorem exists_smallFibreInclusion_homology_surjective (D : Data) :
    ∃ δ : ℝ, 0 < δ ∧ δ < D.radius ∧
      ∀ (t : ℂ), t ≠ 0 → ‖t‖ ≤ δ → ∀ n : ℕ,
        Function.Surjective (singularHomologyMap (actualFibreInclusion D t) n) := by
  obtain ⟨δs, hδs, hδsr, _hδs1, hspec⟩ :=
    exists_actual_specialization_homology D.correction D.radius D.radius_pos D.holomorphic
  obtain ⟨δr, hδr, _hδrr, _hδr1, hret⟩ :=
    exists_controlled_retraction_all_levels D.correction D.radius_pos D.holomorphic
  let δ := min δs δr
  have hδ : 0 < δ := lt_min hδs hδr
  have hδradius : δ < D.radius := (min_le_left δs δr).trans_lt hδsr
  refine ⟨δ, hδ, hδradius, ?_⟩
  intro t ht htδ n
  obtain ⟨E, hE⟩ := hspec t ht (htδ.trans (min_le_left δs δr))
  obtain ⟨hc, _hmarked, hsurj, _h2, _h3⟩ :=
    hE δ (min_le_left δs δr) htδ hδradius
  let c : C(ActualQuotientFibre D.correction D.radius t,
      QuotientCentralFibre D.correction D.radius) :=
    ⟨prescribedActualFibreCollapse D.correction D.radius D.radius_pos hδradius t ht htδ, hc⟩
  obtain ⟨R, _hR, H, _hmono, hc', hend, _hall⟩ :=
    hret δ hδ (min_le_right δs δr) hδradius t ht htδ
  have hend' : R.comp (actualFibreIntoClosed D.correction D.radius δ t htδ) = c := hend
  have hm : singularHomologyMap (actualFibreInclusion D t) n =
      (singularHomologyMap (fullCentralInclusion D) n).comp (singularHomologyMap c n) := by
    rw [homotopy_homologyMap
      (fibreCentralHomotopy D δ hδ.le R H.toHomotopy t htδ) n,
      hend', singularHomologyMap_comp]
  rw [hm, ← fullCentralHomologyEquiv_toLinearMap]
  exact (fullCentralHomologyEquiv D n).surjective.comp (hsurj n).1

end Wikipedia.HopfProblem.ThreefoldHomologyCuspFibre
