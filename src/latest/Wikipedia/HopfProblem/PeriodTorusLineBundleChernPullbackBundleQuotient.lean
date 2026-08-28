import Wikipedia.HopfProblem.PeriodTorusLineBundleChernPullbackFactor
import Wikipedia.HopfProblem.PeriodTorusAppellHumbertCoreIdentification

/-!
# The actual map of factor quotients under lattice-compatible linear pullback

The map on representatives is `(z,c) ↦ (L z,c)`.  Its well-definedness
comes from the actual pulled-back factor and the genuine diagonal orbit
relations.  Holomorphicity descends through the existing quotient-cover
atlases; no injectivity or surjectivity of the base map is required.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleChernPullback

open PeriodTorusAppellHumbert

variable {p q : PeriodDomain} (L : LatticeLinearMap p q) (F : FactorOfAutomorphy q)

local notation "IP" => modelWithCornersSelf ℂ (ComplexPlane₂ × ℂ)

/-- The genuine descended map between the two actual diagonal orbit quotients. -/
def pullbackAssociatedMap : AssociatedSpace (pullbackFactor L F) → AssociatedSpace F :=
  Quotient.lift (fun u : ComplexPlane₂ × ℂ => associatedMap F (L.linear u.1, u.2)) (by
    intro u v huv
    obtain ⟨l, hz, hc⟩ :=
      (associatedMap_eq_iff (pullbackFactor L F) u v).mp (Quotient.sound huv)
    apply (associatedMap_eq_iff F _ _).mpr
    refine ⟨L.latticeMap l, ?_, ?_⟩
    · change L.linear v.1 + (L.latticeMap l : ComplexPlane₂) = L.linear u.1
      rw [← L.linear_add_lattice, hz]
    · exact hc)

@[simp] theorem pullbackAssociatedMap_associatedMap (z : ComplexPlane₂) (c : ℂ) :
    pullbackAssociatedMap L F (associatedMap (pullbackFactor L F) (z, c)) =
      associatedMap F (L.linear z, c) := rfl

/-- The actual quotient map covers precisely the descended torus map. -/
@[simp] theorem pullbackAssociatedMap_projection (u : AssociatedSpace (pullbackFactor L F)) :
    projection F (pullbackAssociatedMap L F u) =
      L.torusMap (projection (pullbackFactor L F) u) := by
  obtain ⟨⟨z, c⟩, rfl⟩ := associatedMap_surjective (pullbackFactor L F) u
  simp only [pullbackAssociatedMap_associatedMap, projection_associatedMap, L.torusMap_mkQ]

/-- Analyticity is proved in the original quotient atlases. -/
theorem pullbackAssociatedMap_holomorphic :
    letI := associatedChartedSpace (pullbackFactor L F)
    letI := associatedChartedSpace F
    ContMDiff IP IP ω (pullbackAssociatedMap L F) := by
  let := associatedChartedSpace (pullbackFactor L F)
  let := associatedChartedSpace F
  let := diagonalAction (pullbackFactor L F)
  apply CoveringQuotient.contMDiff_of_comp
    (associatedMap_isQuotientCoveringMap (pullbackFactor L F)) IP ω
  have hlin : ContDiff ℂ ω (fun u : ComplexPlane₂ × ℂ => (L.linear u.1, u.2)) :=
    (L.linear.contDiff.comp contDiff_fst).prodMk contDiff_snd
  exact (associatedMap_holomorphic F).comp hlin.contMDiff

theorem pullbackAssociatedMap_continuous : Continuous (pullbackAssociatedMap L F) := by
  let := associatedChartedSpace (pullbackFactor L F)
  let := associatedChartedSpace F
  exact (pullbackAssociatedMap_holomorphic L F).continuous

end Wikipedia.HopfProblem.PeriodTorusLineBundleChernPullback
