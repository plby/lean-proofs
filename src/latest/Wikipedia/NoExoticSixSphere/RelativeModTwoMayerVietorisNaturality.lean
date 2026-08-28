import Wikipedia.NoExoticSixSphere.RelativeMayerVietorisSubset
import Wikipedia.NoExoticSixSphere.ModTwoDualSequenceMap
import Wikipedia.NoExoticSixSphere.RelativeModTwoMayerVietoris

/-!
# Naturality of the original relative mod-two Mayer--Vietoris connecting map

Actual subset maps act on the original small-relative chain row and
its reversed dual. Connecting-map naturality for those short exact
cochain rows, followed by the original small-to-union comparison,
proves naturality on the genuine relative cohomology groups.
-/

noncomputable section

open CategoryTheory

namespace NoExoticSixSphere.RelativeModTwoMayerVietoris

open RelativeModTwoCochains (Cohomology)

variable {X : Type} [TopologicalSpace X] {U V U' V' : Set X}
  (hU : U ⊆ U') (hV : V ⊆ V')

/-- The actual reversed dual map of the subset morphism of original chain rows. -/
def smallSequenceSubsetMap : smallSequence U' V' ⟶ smallSequence U V :=
  ModTwoDualComplex.sequenceMap
    (RelativeMayerVietoris.smallSequenceSubsetMap (ModuleCat.of ℤ ℤ) hU hV)

/-- Naturality before transporting the genuine small-relative cohomology term. -/
theorem smallConnecting_naturality (n : ℕ) (a : Cohomology (U' ∩ V') n) :
    (HomologicalComplex.homologyMap (ModTwoDualComplex.map
        (RelativeCoefficients.smallSubsetMap (ModuleCat.of ℤ ℤ) hU hV)) (n + 1)).hom
        (smallConnecting U' V' n a) =
      smallConnecting U V n ((HomologicalComplex.homologyMap (ModTwoDualComplex.map
        (RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ)
          (Set.inter_subset_inter hU hV))) n).hom a) := by
  exact congrArg (fun m => m.hom a)
    (HomologicalComplex.HomologySequence.δ_naturality (smallSequenceSubsetMap hU hV)
      (smallSequence_shortExact U' V') (smallSequence_shortExact U V) n (n + 1) rfl)

variable (hUo : IsOpen U) (hVo : IsOpen V) (hU'o : IsOpen U') (hV'o : IsOpen V')

/-- The original open-union excision comparison commutes with actual subset pullback. -/
theorem smallUnionEquiv_naturality (n : ℕ) (a : Cohomology (U' ∪ V') n) :
    (HomologicalComplex.homologyMap (ModTwoDualComplex.map
        (RelativeCoefficients.smallSubsetMap (ModuleCat.of ℤ ℤ) hU hV)) n).hom
        (smallUnionEquiv U' V' hU'o hV'o n a) =
      smallUnionEquiv U V hUo hVo n
        ((HomologicalComplex.homologyMap (ModTwoDualComplex.map
          (RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ)
            (Set.union_subset_union hU hV))) n).hom a) := by
  have he := congrArg (fun m => HomologicalComplex.homologyMap (ModTwoDualComplex.map m) n)
    (RelativeCoefficients.smallSubsetMap_quotient (ModuleCat.of ℤ ℤ) hU hV)
  rw [ModTwoDualComplex.map_comp, ModTwoDualComplex.map_comp,
    HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at he
  exact congrArg (fun m => m.hom a) he

/-- Actual relative connecting maps commute with the original subset pullbacks. -/
theorem connecting_naturality (n : ℕ) (a : Cohomology (U' ∩ V') n) :
    (HomologicalComplex.homologyMap (ModTwoDualComplex.map
        (RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ)
          (Set.union_subset_union hU hV))) (n + 1)).hom
        (connecting U' V' hU'o hV'o n a) =
      connecting U V hUo hVo n ((HomologicalComplex.homologyMap (ModTwoDualComplex.map
        (RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ)
          (Set.inter_subset_inter hU hV))) n).hom a) := by
  let E := smallUnionEquiv U V hUo hVo (n + 1)
  let E' := smallUnionEquiv U' V' hU'o hV'o (n + 1)
  let s := (HomologicalComplex.homologyMap (ModTwoDualComplex.map
    (RelativeCoefficients.smallSubsetMap (ModuleCat.of ℤ ℤ) hU hV)) (n + 1)).hom
  let b := (HomologicalComplex.homologyMap (ModTwoDualComplex.map
    (RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ)
      (Set.inter_subset_inter hU hV))) n).hom a
  apply E.injective
  apply (smallUnionEquiv_naturality hU hV hUo hVo hU'o hV'o (n + 1)
    (connecting U' V' hU'o hV'o n a)).symm.trans
  change s (E' (E'.symm (smallConnecting U' V' n a))) = E (E.symm (smallConnecting U V n b))
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  exact smallConnecting_naturality hU hV n a

end NoExoticSixSphere.RelativeModTwoMayerVietoris
