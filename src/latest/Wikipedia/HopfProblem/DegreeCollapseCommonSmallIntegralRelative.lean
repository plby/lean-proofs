import Wikipedia.HopfProblem.DegreeCollapseCommonSmallIntegralCap
import Wikipedia.NoExoticSixSphere.CommonSmallRelativeChains

/-!
# Actual integral relative classes have simultaneous small representatives

The original integral common-small inclusion is a quasi-isomorphism
by subdivision. The actual pair sequences, with identity on the given
subspace, transfer this to their relative quotients. Surjectivity then
gives a common-small representative for every original integral class.
-/

noncomputable section

open CategoryTheory Limits

namespace Wikipedia.HopfProblem.DegreeCollapse.CommonSmallIntegralRelative

open SingularMayerVietoris NoExoticSixSphere CommonSmallRelative SingularSubcomplex
open IntegralCap (Coefficient)

variable {X : Type} [TopologicalSpace X] (U A V B W : Set X)
  (hWA : W ⊆ A) (hWB : W ⊆ B)

/-- The actual relative common-small comparison is an integral quasi-isomorphism. -/
theorem comparison_quasiIso
    (hU : IsOpen U) (hA : IsOpen A) (hUA : U ∪ A = Set.univ)
    (hV : IsOpen V) (hB : IsOpen B) (hVB : V ∪ B = Set.univ) :
    QuasiIso (comparison U A V B W hWA hWB Coefficient) :=
  HomologicalComplex.HomologySequence.quasiIso_τ₃
    (sequenceMap U A V B W hWA hWB Coefficient)
    (sequence_shortExact U A V B W hWA hWB Coefficient)
    (RelativeCoefficients.sequence_shortExact Coefficient W)
    (inferInstanceAs (QuasiIso (𝟙 ((singular W).chainComplex Coefficient))))
    (commonSmallInclusion_integral_quasiIso U A V B hU hA hUA hV hB hVB)

include hWA hWB in
/-- Subdivision supplies an actual integral representative small for both original covers. -/
theorem exists_representative
    (hU : IsOpen U) (hA : IsOpen A) (hUA : U ∪ A = Set.univ)
    (hV : IsOpen V) (hB : IsOpen B) (hVB : V ∪ B = Set.univ)
    (n : ℕ) (a : (RelativeCoefficients.complex Coefficient W).homology n) :
    ∃ c : ((commonSmall U A V B : SSet).chainComplex Coefficient).X n,
      ∃ hc : ((RelativeCoefficients.complex Coefficient W).d n (n - 1)).hom
        (RelativeCoefficients.quotientMap Coefficient W n
          (((commonSmallChainInclusion U A V B Coefficient).f n).hom c)) = 0,
      ModuleHomology.cycleClass (RelativeCoefficients.complex Coefficient W) n
        (ModuleHomology.mkCycle (RelativeCoefficients.complex Coefficient W) n
          (RelativeCoefficients.quotientMap Coefficient W n
            (((commonSmallChainInclusion U A V B Coefficient).f n).hom c)) hc) = a := by
  let Q := complex U A V B W hWA hWB Coefficient
  let f := comparison U A V B W hWA hWB Coefficient
  let π := projection U A V B W hWA hWB Coefficient
  let : QuasiIso f := comparison_quasiIso U A V B W hWA hWB hU hA hUA hV hB hVB
  obtain ⟨a', ha'⟩ := (ModuleCat.epi_iff_surjective (HomologicalComplex.homologyMap f n)).mp
    inferInstance a
  obtain ⟨z, hz⟩ := ModuleHomology.cycleClass_surjective Q n a'
  obtain ⟨c, hc⟩ := (ModuleCat.epi_iff_surjective (π.f n)).mp inferInstance z.val
  have he := congrArg (fun m => (m.f n).hom c)
    (projection_comparison U A V B W hWA hWB Coefficient)
  have hv : (ModuleHomology.mapCycles f n z).val =
      RelativeCoefficients.quotientMap Coefficient W n
        (((commonSmallChainInclusion U A V B Coefficient).f n).hom c) :=
    (ModuleHomology.mapCycles_val f n z).trans ((congrArg (f.f n).hom hc).symm.trans he)
  have hcycle : ((RelativeCoefficients.complex Coefficient W).d n (n - 1)).hom
      (RelativeCoefficients.quotientMap Coefficient W n
        (((commonSmallChainInclusion U A V B Coefficient).f n).hom c)) = 0 :=
    (congrArg ((RelativeCoefficients.complex Coefficient W).d n (n - 1)).hom hv).symm.trans
      (ModuleHomology.cycle_condition _ n (ModuleHomology.mapCycles f n z))
  refine ⟨c, hcycle, ?_⟩
  exact (congrArg (ModuleHomology.cycleClass (RelativeCoefficients.complex Coefficient W) n)
    (Subtype.ext hv.symm)).trans ((ModuleHomology.homologyMap_cycleClass f n z).symm.trans
      ((congrArg (HomologicalComplex.homologyMap f n).hom hz).trans ha'))

end Wikipedia.HopfProblem.DegreeCollapse.CommonSmallIntegralRelative
