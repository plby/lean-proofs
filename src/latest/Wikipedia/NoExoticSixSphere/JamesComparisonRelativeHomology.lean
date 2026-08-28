import Wikipedia.NoExoticSixSphere.JamesSphereHomologyComparison
import Wikipedia.NoExoticSixSphere.JamesComparisonCylinder
import Wikipedia.NoExoticSixSphere.MappingCylinderHomology

/-!
# The actual James mapping-cylinder pair is acyclic

The source is the actual closed image of the original James space.
The checked integral homology comparison and the genuine pair sequence
prove relative homology vanishing in every degree for positive sphere
dimension. This is not a relative homotopy-vanishing assertion.
-/

noncomputable section

open Wikipedia.HopfProblem SingularMayerVietoris

namespace NoExoticSixSphere.JamesSphere.ComparisonCylinder

abbrev sourceImage (n : ℕ) : Set (Cylinder n) :=
  MappingCylinderHomology.sourceImage (comparison n)

theorem source_inclusion_homology_bijective (n d : ℕ) (hn : 0 < n) :
    Function.Bijective (singularHomologyMap (subtypeInclusion (sourceImage n)) d) :=
  (MappingCylinderHomology.inclusion_homology_bijective_iff (comparison n) d).mpr
    (HomologyComparison.comparison_homology_bijective_of_pos n d hn)

theorem relative_homology_subsingleton (n d : ℕ) (hn : 0 < n) :
    Subsingleton (RelativeSingularHomology.Homology (sourceImage n) d) :=
  MappingCylinderHomology.relative_homology_subsingleton (comparison n)
    (fun k ↦ HomologyComparison.comparison_homology_bijective_of_pos n k hn) d

theorem relative_homology_eq_zero (n d : ℕ) (hn : 0 < n)
    (a : RelativeSingularHomology.Homology (sourceImage n) d) : a = 0 := by
  let := relative_homology_subsingleton n d hn
  exact Subsingleton.elim a 0

end NoExoticSixSphere.JamesSphere.ComparisonCylinder
