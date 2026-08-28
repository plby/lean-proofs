import Wikipedia.HopfProblem.DegreeCollapseIntegralRelativeCohomologyMaps
import Wikipedia.NoExoticSixSphere.RelativeMayerVietorisSubset

/-!
# Original integral relative connecting-map naturality

The actual subset morphism of the original small-chain row induces
the original reversed integral cochain morphism. Connecting naturality
for that genuine short exact row and the original union comparison
give naturality on the actual integral relative cohomology groups.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralRelativeCohomologyMayerVietoris

open SingularCohomologyFree NoExoticSixSphere

variable {X : Type} [TopologicalSpace X] {U V U' V' : Set X}
  (hU : U ⊆ U') (hV : V ⊆ V')

def smallSequenceSubsetMap : smallSequence U' V' ⟶ smallSequence U V :=
  IntegralDualSequence.sequenceMap
    (RelativeMayerVietoris.smallSequenceSubsetMap (ModuleCat.of ℤ ℤ) hU hV)

theorem smallConnecting_naturality (n : ℕ) (a : Cohomology (U' ∩ V') n) :
    (HomologicalComplex.homologyMap (dualMap
        (RelativeCoefficients.smallSubsetMap (ModuleCat.of ℤ ℤ) hU hV)) (n + 1)).hom
        (smallConnecting U' V' n a) =
      smallConnecting U V n ((HomologicalComplex.homologyMap (dualMap
        (RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ)
          (Set.inter_subset_inter hU hV))) n).hom a) := by
  exact congrArg (fun m => m.hom a)
    (HomologicalComplex.HomologySequence.δ_naturality (smallSequenceSubsetMap hU hV)
      (smallSequence_shortExact U' V') (smallSequence_shortExact U V) n (n + 1) rfl)

variable (hUo : IsOpen U) (hVo : IsOpen V) (hU'o : IsOpen U') (hV'o : IsOpen V')

theorem smallUnionEquiv_naturality (n : ℕ) (a : Cohomology (U' ∪ V') n) :
    (HomologicalComplex.homologyMap (dualMap
        (RelativeCoefficients.smallSubsetMap (ModuleCat.of ℤ ℤ) hU hV)) n).hom
        (smallUnionEquiv U' V' hU'o hV'o n a) =
      smallUnionEquiv U V hUo hVo n
        ((HomologicalComplex.homologyMap (dualMap
          (RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ)
            (Set.union_subset_union hU hV))) n).hom a) := by
  have he := congrArg (fun m => HomologicalComplex.homologyMap (dualMap m) n)
    (RelativeCoefficients.smallSubsetMap_quotient (ModuleCat.of ℤ ℤ) hU hV)
  rw [dualMap_comp, dualMap_comp,
    HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at he
  exact congrArg (fun m => m.hom a) he

/-- Naturality retains both actual integer pair pullbacks and the genuine connecting map. -/
theorem connecting_naturality (n : ℕ) (a : Cohomology (U' ∩ V') n) :
    (HomologicalComplex.homologyMap (dualMap
        (RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ)
          (Set.union_subset_union hU hV))) (n + 1)).hom
        (connecting U' V' hU'o hV'o n a) =
      connecting U V hUo hVo n ((HomologicalComplex.homologyMap (dualMap
        (RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ)
          (Set.inter_subset_inter hU hV))) n).hom a) := by
  let E := smallUnionEquiv U V hUo hVo (n + 1)
  let E' := smallUnionEquiv U' V' hU'o hV'o (n + 1)
  let s := (HomologicalComplex.homologyMap (dualMap
    (RelativeCoefficients.smallSubsetMap (ModuleCat.of ℤ ℤ) hU hV)) (n + 1)).hom
  let b := (HomologicalComplex.homologyMap (dualMap
    (RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ)
      (Set.inter_subset_inter hU hV))) n).hom a
  apply E.injective
  apply (smallUnionEquiv_naturality hU hV hUo hVo hU'o hV'o (n + 1)
    (connecting U' V' hU'o hV'o n a)).symm.trans
  change s (E' (E'.symm (smallConnecting U' V' n a))) = E (E.symm (smallConnecting U V n b))
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  exact smallConnecting_naturality hU hV n a

end Wikipedia.HopfProblem.DegreeCollapse.IntegralRelativeCohomologyMayerVietoris
