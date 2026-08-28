import Wikipedia.NoExoticSixSphere.SingularSubcomplex
import Wikipedia.NoExoticSixSphere.SubcomplexChainSequence

/-!
# Actual small singular simplices and their native coefficient chains

The union of the two singular range subcomplexes consists of simplices
lying in one of the two subsets. The original intersection inclusions and
piece inclusions form a pushout with this union. Thus its native chains
have the actual small-chain short exact sequence for every coefficient
module, and the small-chain inclusion is a monomorphism.
-/

noncomputable section

open CategoryTheory Limits
open Wikipedia.HopfProblem SingularMayerVietoris

namespace NoExoticSixSphere.SingularSubcomplex

variable {X : Type} [TopologicalSpace X] (U V : Set X)

/-- The simplicial set of simplices lying wholly in at least one of the two subsets. -/
abbrev Small : SSet.{0} := (support U ⊔ support V : (singular X).Subcomplex)

abbrev intersectionLeft : singular (U ∩ V : Set X) ⟶ singular U :=
  TopCat.toSSet.map
    (TopCat.ofHom (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U)))

abbrev intersectionRight : singular (U ∩ V : Set X) ⟶ singular V :=
  TopCat.toSSet.map
    (TopCat.ofHom (ContinuousMap.inclusion (Set.inter_subset_right : U ∩ V ⊆ V)))

@[reassoc]
theorem intersectionLeft_inclusion : intersectionLeft U V ≫ inclusion U = inclusion (U ∩ V) := by
  rw [← TopCat.toSSet.map_comp]
  rfl

@[reassoc]
theorem intersectionRight_inclusion : intersectionRight U V ≫ inclusion V = inclusion (U ∩ V) := by
  rw [← TopCat.toSSet.map_comp]
  rfl

/-- The actual intersection singular set, identified with the intersection subcomplex. -/
def intersectionIso : singular (U ∩ V : Set X) ≅
    (support U ⊓ support V : (singular X).Subcomplex) :=
  supportIso (U ∩ V) ≪≫ SSet.Subcomplex.eqToIso (support_inter U V)

@[reassoc]
theorem intersectionIso_hom_inclusion :
    (intersectionIso U V).hom ≫ (support U ⊓ support V).ι = inclusion (U ∩ V) := rfl

theorem intersectionIso_left :
    (intersectionIso U V).hom ≫ SSet.Subcomplex.homOfLE
        (inf_le_left : support U ⊓ support V ≤ support U) =
      intersectionLeft U V ≫ (supportIso U).hom := by
  apply (cancel_mono (support U).ι).mp
  simp only [Category.assoc, SSet.Subcomplex.homOfLE_ι, supportIso_hom_inclusion,
    intersectionIso_hom_inclusion, intersectionLeft_inclusion]

theorem intersectionIso_right :
    (intersectionIso U V).hom ≫ SSet.Subcomplex.homOfLE
        (inf_le_right : support U ⊓ support V ≤ support V) =
      intersectionRight U V ≫ (supportIso V).hom := by
  apply (cancel_mono (support V).ι).mp
  simp only [Category.assoc, SSet.Subcomplex.homOfLE_ι, supportIso_hom_inclusion,
    intersectionIso_hom_inclusion, intersectionRight_inclusion]

def toSmallLeft : singular U ⟶ Small U V :=
  (supportIso U).hom ≫ SSet.Subcomplex.homOfLE (le_sup_left : support U ≤ support U ⊔ support V)

def toSmallRight : singular V ⟶ Small U V :=
  (supportIso V).hom ≫ SSet.Subcomplex.homOfLE (le_sup_right : support V ≤ support U ⊔ support V)

abbrev smallInclusion : Small U V ⟶ singular X := (support U ⊔ support V).ι

@[reassoc]
theorem toSmallLeft_inclusion : toSmallLeft U V ≫ smallInclusion U V = inclusion U := rfl

@[reassoc]
theorem toSmallRight_inclusion : toSmallRight U V ≫ smallInclusion U V = inclusion V := rfl

/-- The actual native singular sets form the small-simplex pushout. -/
theorem smallSquare :
    IsPushout (intersectionLeft U V) (intersectionRight U V) (toSmallLeft U V) (toSmallRight U V) :=
  (SSet.Subcomplex.BicartSq.isPushout
    (show SSet.Subcomplex.BicartSq (support U ⊓ support V) (support U) (support V)
      (support U ⊔ support V) from ⟨rfl, rfl⟩)).of_iso'
    (intersectionIso U V) (supportIso U) (supportIso V) (Iso.refl _)
    (intersectionIso_left U V) (intersectionIso_right U V)
    (by rw [Iso.refl_hom, Category.comp_id]; rfl)
    (by rw [Iso.refl_hom, Category.comp_id]; rfl)

variable (R : ModuleCat.{0} ℤ)

/-- The chain pushout uses native coefficient chains on the actual subspaces. -/
theorem smallChainSquare :
    IsPushout ((SimplicialCoefficients.chains R).map (intersectionLeft U V))
      ((SimplicialCoefficients.chains R).map (intersectionRight U V))
      ((SimplicialCoefficients.chains R).map (toSmallLeft U V))
      ((SimplicialCoefficients.chains R).map (toSmallRight U V)) :=
  (SimplicialCoefficients.chains R).map_isPushout (smallSquare U V)

instance intersectionLeft_mono : Mono (intersectionLeft U V) :=
  mono_of_mono_fac (intersectionLeft_inclusion U V)

/-- The actual native small-chain sequence is short exact for every coefficient module. -/
theorem smallChainSequence_shortExact : (smallChainSquare U V R).shortComplex.ShortExact :=
  SimplicialCoefficients.pushout_shortExact (smallChainSquare U V R)

instance smallChainInclusion_mono :
    Mono ((SimplicialCoefficients.chains R).map (smallInclusion U V)) := by
  infer_instance

@[reassoc]
theorem chainToSmallLeft_inclusion :
    (SimplicialCoefficients.chains R).map (toSmallLeft U V) ≫
        (SimplicialCoefficients.chains R).map (smallInclusion U V) =
      RelativeCoefficients.inclusion R U := by
  rw [← Functor.map_comp, toSmallLeft_inclusion]
  rfl

@[reassoc]
theorem chainToSmallRight_inclusion :
    (SimplicialCoefficients.chains R).map (toSmallRight U V) ≫
        (SimplicialCoefficients.chains R).map (smallInclusion U V) =
      RelativeCoefficients.inclusion R V := by
  rw [← Functor.map_comp, toSmallRight_inclusion]
  rfl

end NoExoticSixSphere.SingularSubcomplex
