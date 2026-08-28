import Wikipedia.HopfProblem.SpecialPeriodsCuspAttachingBasic
import Wikipedia.HopfProblem.ThreefoldFundamentalGroupGluingMaps
import Wikipedia.HopfProblem.ThreefoldFundamentalGroupGluingTopology
import Wikipedia.HopfProblem.CuspFibreFundamentalGroup
import Wikipedia.HopfProblem.FundamentalGroupBasepointNaturality

/-!
# Surjectivity of the actual cusp attaching homomorphism

A genuine nonzero fibre of the small toric cusp quotient lies in the full
regular/cusp overlap.  Its inclusion into the cusp filling is already
surjective on fundamental groups.  Factoring that inclusion through the
literal global overlap, and then changing basepoint within the overlap,
proves surjectivity for the precise attaching homomorphism of the
constructed threefold.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold

attribute [local instance] localPieceChartedSpace chartedSpace

namespace CuspAttaching

open CuspUniformization

/-- The actual small cusp quotient identifies with its full global patch. -/
def fillingHomeomorph : SpecialCuspPiece ≃ₜ liftedPatch (some none) :=
  (patchBiholomorph (some none)).toHomeomorph

/-- The literal nonzero fibre in the actual small cusp quotient. -/
abbrev NonzeroFibre (s : ℂ) :=
  CuspQuotient.projection data.correction radius ⁻¹' {exponential s}

theorem nonzeroFibre_mem_regular (s : ℂ) (x : NonzeroFibre s) :
    (fillingHomeomorph x.val).val ∈ liftedPatch none := by
  change projection (fillingHomeomorph x.val) ∈ regularPatch
  have hp : projection (fillingHomeomorph x.val) =
      CuspPiece.projectionToBase specialCuspData specialBaseCover x.val :=
    gluingData.projection_inclusion (some none) x.val
  rw [hp]
  apply (CuspPiece.projectionToBase_mem_regular_iff
    specialCuspData specialBaseCover x.val).mpr
  have hx : CuspQuotient.projection data.correction radius x.val = exponential s :=
    x.property
  exact hx.trans_ne (exponential_ne_zero s)

/-- Inclusion of the actual fibre into the literal global overlap. -/
def fibreToOverlap (s : ℂ) : C(NonzeroFibre s, RegularOverlap none) where
  toFun x := ⟨fillingHomeomorph x.val,
    nonzeroFibre_mem_regular s x, (fillingHomeomorph x.val).property⟩
  continuous_toFun :=
    (continuous_subtype_val.comp
      (fillingHomeomorph.continuous.comp continuous_subtype_val)).subtype_mk _

/-- The factorization is an equality of the original continuous maps. -/
theorem fibreToOverlap_factors (s : ℂ) :
    (overlapFillingInclusion none).comp (fibreToOverlap s) =
      (⟨fillingHomeomorph, fillingHomeomorph.continuous⟩ :
        C(SpecialCuspPiece, liftedPatch (some none))).comp
          ⟨Subtype.val, continuous_subtype_val⟩ := rfl

/-- The same factorization holds for the actual induced loop maps. -/
theorem fibreToOverlap_fundamentalGroup_factors (s : ℂ) (x : NonzeroFibre s)
    (γ : FundamentalGroup (NonzeroFibre s) x) :
    FundamentalGroup.map (overlapFillingInclusion none) (fibreToOverlap s x)
        (FundamentalGroup.map (fibreToOverlap s) x γ) =
      homeomorphFundamentalGroupEquiv fillingHomeomorph x.val
        (FundamentalGroup.map ⟨Subtype.val, continuous_subtype_val⟩ x γ) := by
  obtain ⟨p⟩ := γ
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  rfl

/-- A nonzero fibre supplies a basepoint at which the true overlap inclusion
is surjective.  All cusp estimates come from the constructed small data. -/
theorem exists_surjective_overlap_basepoint (s : ℂ) (hs : ‖exponential s‖ < radius) :
    ∃ x : RegularOverlap none,
      Function.Surjective (FundamentalGroup.map (overlapFillingInclusion none) x) := by
  have hpos : 0 < ‖exponential s‖ := norm_pos_iff.mpr (exponential_ne_zero s)
  have hlog := Real.log_neg hpos (hs.trans data.radius_lt_one)
  have hRp := data.smallDrift _ hpos hs
  let x : NonzeroFibre s := fibreBasePoint data.correction radius s hs hlog hRp
  have hf : Function.Surjective
      (FundamentalGroup.map ⟨Subtype.val, continuous_subtype_val⟩ x) :=
    fibreInclusionFundamentalGroupMap_surjective data.correction radius s hs hlog hRp
      data.radius_pos data.radius_lt_one data.holomorphic data.smallDrift
  refine ⟨fibreToOverlap s x, ?_⟩
  intro γ
  obtain ⟨δ, rfl⟩ :=
    (homeomorphFundamentalGroupEquiv fillingHomeomorph x.val).surjective γ
  obtain ⟨ε, rfl⟩ := hf δ
  exact ⟨FundamentalGroup.map (fibreToOverlap s) x ε,
    fibreToOverlap_fundamentalGroup_factors s x ε⟩

/-- The chosen positive cusp radius contains an actual nonzero exponential
parameter, so no nonempty-fibre hypothesis is needed. -/
theorem exists_small_exponential : ∃ s : ℂ, ‖exponential s‖ < radius := by
  have hr : 0 < radius / 2 := half_pos data.radius_pos
  have ht : ((radius / 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hr
  refine ⟨logarithm ((radius / 2 : ℝ) : ℂ), ?_⟩
  rw [exponential_logarithm ht, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  exact half_lt_self data.radius_pos

end CuspAttaching

/-- The exact cusp attaching map used in the threefold's van Kampen
diagram is surjective, with no mathematical premises. -/
theorem cusp_overlapFillingHom_surjective :
    Function.Surjective (overlapFillingHom (none : Puncture)) := by
  obtain ⟨s, hs⟩ := CuspAttaching.exists_small_exponential
  obtain ⟨x, hx⟩ := CuspAttaching.exists_surjective_overlap_basepoint s hs
  let := liftedPatch_regular_inter_pathConnectedSpace (none : Puncture)
  exact fundamentalGroup_map_surjective_at_of_pathConnected
    (overlapFillingInclusion none) x (regularOverlapPoint none) hx

end Wikipedia.HopfProblem.SpecialPeriods.Threefold
