import Wikipedia.NoExoticSixSphere.JamesSphereAttachingSmashCube
import Wikipedia.NoExoticSixSphere.JamesSphereOrderedLoopComparison

/-!
# The original attaching Hopf coordinate and the actual meridian commutator

The ordered James map is a sixth-homology isomorphism and its native
currying is the original comparison. Hurewicz naturality therefore
transfers the checked loop-space homology equality to the genuine
James adjoints. The original attaching class differs from the corrected
class at most by inversion, so their absolute Hopf coordinates agree
with that of the actual meridian commutator. No numerical coefficient
or torsion-coordinate identity is claimed here.
-/

noncomputable section

open scoped Topology unitInterval
open Wikipedia.HopfProblem SingularMayerVietoris

namespace NoExoticSixSphere.JamesSphere.AttachingSquare

theorem orderedLoopComparison_wordAdjoint
    (p : GenLoop (Fin 6) (Path (spherePole 4) (spherePole 4))
      (Path.refl (spherePole 4))) :
    HigherHomotopy.map (N := Fin 6) (orderedLoopComparison 3)
      (orderedLoopComparison_one 3)
      (SphereFourHopfHomology.wordAdjoint
        (Quotient.mk' (GeneralizedLoopCurrying.uncurry p))) = Quotient.mk' p := by
  apply (GeneralizedLoopCurrying.homotopyMulEquiv 6 (spherePole 4)).injective
  exact (orderedComparison_loopMap 3 (by decide) 6
    (SphereFourHopfHomology.wordAdjoint
      (Quotient.mk' (GeneralizedLoopCurrying.uncurry p)))).symm.trans
    (SphereFourHopfHomology.comparison_wordAdjoint
      (Quotient.mk' (GeneralizedLoopCurrying.uncurry p)))

theorem orderedLoopComparison_adjointClass
    (p : GenLoop (Fin 6) (Path (spherePole 4) (spherePole 4))
      (Path.refl (spherePole 4))) :
    singularHomologyMap (orderedLoopComparison 3) 6
      (SphereFourHopfHomology.adjointClass
        (Quotient.mk' (GeneralizedLoopCurrying.uncurry p))) =
      SixthHurewicz.hurewiczFunction (Path.refl (spherePole 4)) (Quotient.mk' p) := by
  exact (SixthHurewiczNative.natural (orderedLoopComparison 3) 1
    (Path.refl (spherePole 4)) (orderedLoopComparison_one 3)
    (SphereFourHopfHomology.wordAdjoint
      (Quotient.mk' (GeneralizedLoopCurrying.uncurry p)))).trans
    (congrArg (SixthHurewicz.hurewiczFunction (Path.refl (spherePole 4)))
      (orderedLoopComparison_wordAdjoint p))

theorem correctedSevenClass_adjointClass :
    SphereFourHopfHomology.adjointClass correctedSevenClass =
      SphereFourHopfHomology.adjointClass MeridianCommutator.fourClass := by
  apply (orderedLoopComparison_homology_bijective 3 6 (by decide)).injective
  have hf := orderedLoopComparison_adjointClass (correctedCube 3)
  have hg := orderedLoopComparison_adjointClass normalizedSmashCube
  rw [normalizedSmashCube_uncurry] at hg
  exact hf.trans (correctedCube_hurewicz.trans hg.symm)

theorem correctedSevenClass_hopf_coordinate :
    (SphereFourSeventh.groupEquiv correctedSevenClass).1.toAdd =
      (SphereFourSeventh.groupEquiv MeridianCommutator.fourClass).1.toAdd := by
  rw [SphereFourHopfHomology.coordinate_hurewicz,
    SphereFourHopfHomology.coordinate_hurewicz, correctedSevenClass_adjointClass]

theorem originalAttachingClass_hopf_natAbs :
    Int.natAbs SphereFiveEighth.relation.1.toAdd =
      Int.natAbs (SphereFourSeventh.groupEquiv MeridianCommutator.fourClass).1.toAdd := by
  have h := original_integer_coordinate_natAbs
    ((MonoidHom.fst (Multiplicative ℤ) (Multiplicative (ZMod 12))).comp
      SphereFourSeventh.groupEquiv.toMonoidHom)
  change Int.natAbs SphereFiveEighth.relation.1.toAdd =
    Int.natAbs (SphereFourSeventh.groupEquiv correctedSevenClass).1.toAdd at h
  exact h.trans (congrArg Int.natAbs correctedSevenClass_hopf_coordinate)

end NoExoticSixSphere.JamesSphere.AttachingSquare
