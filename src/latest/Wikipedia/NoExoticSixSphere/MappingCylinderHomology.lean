import Wikipedia.NoExoticSixSphere.RelativeHomologyAcyclic
import Wikipedia.NoExoticSixSphere.DoubleMappingCylinderEndEmbedding
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy

/-!
# Homology of the actual mapping-cylinder pair

Projection onto the target is an explicit homotopy equivalence. The
original source is homeomorphic to its actual closed image in the
cylinder. Consequently a homology isomorphism has an acyclic genuine
mapping-cylinder pair, with no homotopy equivalence of the source assumed.
-/

noncomputable section

open CategoryTheory Topology
open Wikipedia.HopfProblem OrbitPair SingularMayerVietoris PeriodTorusHigherHomology

namespace NoExoticSixSphere.MappingCylinderHomology

variable {A B : TopCat.{0}} (f : A ⟶ B)

abbrev sourceImage : Set (MappingCylinder.space f) := Set.range (MappingCylinder.source f)

def sourceHomeomorph : A ≃ₜ sourceImage f :=
  (DoubleMappingCylinder.mappingCylinder_source_isClosedEmbedding f).isEmbedding.toHomeomorph

theorem sourceHomeomorph_val (a : A) :
    (sourceHomeomorph f a).val = MappingCylinder.source f a := rfl

theorem projection_source_homology (d : ℕ) (a : SingularHomology A d) :
    singularHomologyMap (MappingCylinder.projection f).hom d
        (singularHomologyMap (MappingCylinder.source f).hom d a) =
      singularHomologyMap f.hom d a := by
  have h : (MappingCylinder.projection f).hom.comp (MappingCylinder.source f).hom = f.hom :=
    congrArg TopCat.Hom.hom (MappingCylinder.source_projection f)
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp, h]

theorem source_homology_bijective_iff (d : ℕ) :
    Function.Bijective (singularHomologyMap (MappingCylinder.source f).hom d) ↔
      Function.Bijective (singularHomologyMap f.hom d) := by
  have h : (homotopyEquivHomologyEquiv (MappingCylinder.projectionEquiv f) d) ∘
      singularHomologyMap (MappingCylinder.source f).hom d = singularHomologyMap f.hom d :=
    funext (projection_source_homology f d)
  have he := Function.Bijective.of_comp_iff'
    (homotopyEquivHomologyEquiv (MappingCylinder.projectionEquiv f) d).bijective
    (singularHomologyMap (MappingCylinder.source f).hom d)
  rw [h] at he
  exact he.symm

theorem inclusion_source_homology (d : ℕ) (a : SingularHomology A d) :
    singularHomologyMap (subtypeInclusion (sourceImage f)) d
        (homeomorphHomologyEquiv (sourceHomeomorph f) d a) =
      singularHomologyMap (MappingCylinder.source f).hom d a := by
  change singularHomologyMap (subtypeInclusion (sourceImage f)) d
      (singularHomologyMap (sourceHomeomorph f).toHomotopyEquiv.toFun d a) = _
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp]
  rfl

theorem inclusion_homology_bijective_iff (d : ℕ) :
    Function.Bijective (singularHomologyMap (subtypeInclusion (sourceImage f)) d) ↔
      Function.Bijective (singularHomologyMap f.hom d) := by
  have h : singularHomologyMap (subtypeInclusion (sourceImage f)) d ∘
      homeomorphHomologyEquiv (sourceHomeomorph f) d =
        singularHomologyMap (MappingCylinder.source f).hom d :=
    funext (inclusion_source_homology f d)
  have he := Function.Bijective.of_comp_iff
    (singularHomologyMap (subtypeInclusion (sourceImage f)) d)
    (homeomorphHomologyEquiv (sourceHomeomorph f) d).bijective
  rw [h] at he
  exact he.symm.trans (source_homology_bijective_iff f d)

theorem relative_homology_subsingleton
    (h : ∀ d, Function.Bijective (singularHomologyMap f.hom d)) (d : ℕ) :
    Subsingleton (RelativeSingularHomology.Homology (sourceImage f) d) :=
  RelativeSingularHomology.subsingleton_of_inclusion_bijective (sourceImage f)
    (fun k ↦ (inclusion_homology_bijective_iff f k).mpr (h k)) d

end NoExoticSixSphere.MappingCylinderHomology
