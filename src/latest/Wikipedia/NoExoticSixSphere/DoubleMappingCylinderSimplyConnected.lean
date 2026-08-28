import Wikipedia.NoExoticSixSphere.DoubleMappingCylinderOverlapEquivalence
import Wikipedia.NoExoticSixSphere.DoubleMappingCylinderEquivalence
import Wikipedia.HopfProblem.SphereHomologySimplyConnectedCover
import Wikipedia.HopfProblem.DegreeCollapsePointClassComponents

/-!
# Simple connectivity of the genuine double mapping cylinder

The actual lower and upper open pieces are homotopy equivalent to the
two end spaces; their overlap is equivalent to the attaching space.
The proved two-open-set van Kampen theorem therefore applies. When one
attaching map has homotopy extension, the actual collapse equivalence
transfers this conclusion to the ordinary pushout.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Set
open Wikipedia.HopfProblem OrbitPair FundamentalGroupVanKampen
open DegreeCollapse.MorseCancellation

namespace NoExoticSixSphere.DoubleMappingCylinder

variable {A X Y : TopCat.{0}} (e : A ⟶ X) (f : A ⟶ Y)
    [PathConnectedSpace A] [SimplyConnectedSpace X] [SimplyConnectedSpace Y]

theorem simplyConnectedSpace : SimplyConnectedSpace (space e f) := by
  let : SimplyConnectedSpace (lower e f) := (lowerEquiv e f).symm.simplyConnectedSpace
  let : SimplyConnectedSpace (upper e f) := (upperEquiv e f).symm.simplyConnectedSpace
  let : PathConnectedSpace (overlap e f) :=
    pathConnectedSpace_of_homotopyEquiv (overlapEquiv e f).symm
  let o : overlap e f := (overlapEquiv e f).toFun (Classical.arbitrary A)
  let D : TwoOpenCover (space e f) :=
    { U := ⟨lower e f, lower_isOpen e f⟩
      V := ⟨upper e f, upper_isOpen e f⟩
      cover := cover e f
      pathConnectedU := isPathConnected_iff_pathConnectedSpace.mpr inferInstance
      pathConnectedV := isPathConnected_iff_pathConnectedSpace.mpr inferInstance
      pathConnectedIntersection := isPathConnected_iff_pathConnectedSpace.mpr
        (inferInstanceAs (PathConnectedSpace (overlap e f)))
      base := o.val
      baseU := o.property.1
      baseV := o.property.2 }
  exact SphereHomology.twoOpenCover_simplyConnectedSpace D

theorem pushout_simplyConnectedSpace {P : TopCat.{0}} {i : X ⟶ P} {j : Y ⟶ P}
    (hP : IsPushout e f i j) (he : HomotopyExtension.HasHomotopyExtension e) :
    SimplyConnectedSpace P := by
  let := simplyConnectedSpace e f
  obtain ⟨E, _⟩ := exists_collapse_equiv e f hP he
  exact E.symm.simplyConnectedSpace

end NoExoticSixSphere.DoubleMappingCylinder
