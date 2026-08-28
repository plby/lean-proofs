import Wikipedia.HomotopyGroupsOfSpheres.BalancedLoopMap
import Wikipedia.NoExoticSixSphere.InducedHomotopyMap
import Wikipedia.NoExoticSixSphere.LoopSpaceDimensionShift

/-!
# The balanced real map on native homotopy groups

This is the original balanced rotation map followed by the proved reference
congruence and ordinary cubical uncurrying. Its bijectivity is not asserted
here; that requires the remaining relative deformation theorem.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions

open QuaternionicSymmetricMatrices NoExoticSixSphere

def inducedCube {d : ℕ} (n : ℕ) (p : GenLoop (Fin d) (Space n) (standard n)) :
    GenLoop (Fin (d + 1)) (SpecialSpace (Index n)) specialIdentity :=
  GeneralizedLoopCurrying.uncurry
    (HigherHomotopy.genLoopMap (loopMap n) (loopMap_reference n) p)

theorem inducedCube_apply {d : ℕ} (n : ℕ) (p : GenLoop (Fin d) (Space n) (standard n))
    (t : Fin (d + 1) → I) :
    inducedCube n p t = referenceAction n (-halfAngle (t 0))
      (rotation (p (Fin.tail t)) ((t 0 : ℝ) * Real.pi)) := rfl

def degreeShiftHom (n d : ℕ) [NeZero d] :
    π_ d (Space n) (standard n) →* π_ (d + 1) (SpecialSpace (Index n)) specialIdentity :=
  (GeneralizedLoopCurrying.homotopyMulEquiv d
    (specialIdentity : SpecialSpace (Index n))).toMonoidHom.comp
      (HigherHomotopy.mapMonoidHom (loopMap n) (loopMap_reference n))

theorem degreeShiftHom_mk (n d : ℕ) [NeZero d]
    (p : GenLoop (Fin d) (Space n) (standard n)) :
    degreeShiftHom n d (Quotient.mk' p) = Quotient.mk' (inducedCube n p) := rfl

theorem pathMap_homotopicRel_iff_loopMap {X : Type*} [TopologicalSpace X]
    (n : ℕ) (f g : C(X, Space n)) (S : Set X) :
    Nonempty (((pathMap n).comp f).HomotopyRel ((pathMap n).comp g) S) ↔
      Nonempty (((loopMap n).comp f).HomotopyRel ((loopMap n).comp g) S) :=
  homotopicRel_iff_postcompose_homeomorph (loopHomeomorph n)
    ((pathMap n).comp f) ((pathMap n).comp g) S

end Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions
