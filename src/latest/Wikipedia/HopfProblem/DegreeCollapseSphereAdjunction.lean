import Wikipedia.HopfProblem.DegreeCollapseSphereLiftFamily
import Wikipedia.NoExoticSixSphere.LoopSpaceDimensionShift

/-!
# Actual sphere adjunction respects the original product suspension

The adjoint is descended from the original curried cube. Its path value
is the given sphere map evaluated on the original meridian, so
precomposition by the specified product suspension is exactly
precomposition of the adjoint by the original based map.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.DegreeCollapse.SphereAdjunction

open NoExoticSixSphere SmoothCube SphereLiftFamily CubicalSphereSuspension

variable {X : Type*} [TopologicalSpace X] {x : X}
variable {m n : ℕ} [NeZero m] [NeZero n]

def adjoint (f : BasedMap (n + 1) X x) : BasedMap n (Path x x) (Path.refl x) :=
  (basedEquiv (Nat.pos_of_neZero n)).symm
    (GeneralizedLoopCurrying.curry (toGenLoop f))

theorem adjoint_quotient (f : BasedMap (n + 1) X x)
    (u : Fin n → I) (t : I) :
    (adjoint f).val (quotient n u) t = f.val (quotient (n + 1) (Fin.cons t u)) := by
  change SmoothCube.descend (Nat.pos_of_neZero n)
    (GeneralizedLoopCurrying.curry (toGenLoop f)) (quotient n u) t = _
  rw [SmoothCube.descend_quotient]
  rfl

theorem adjoint_meridian (f : BasedMap (n + 1) X x) (z : Sphere n) (t : I) :
    (adjoint f).val z t = f.val (meridian n (t, z)) := by
  obtain ⟨u, rfl⟩ := quotient_surjective (Nat.pos_of_neZero n) z
  rw [adjoint_quotient, meridian_quotient]

theorem adjoint_native (f : BasedMap (n + 1) X x) :
    GeneralizedLoopCurrying.homotopyMulEquiv n x (sphereClass (adjoint f)) =
      sphereClass f := by
  have h : toGenLoop (adjoint f) = GeneralizedLoopCurrying.curry (toGenLoop f) :=
    (basedEquiv (Nat.pos_of_neZero n)).apply_symm_apply _
  change (Quotient.mk' (GeneralizedLoopCurrying.uncurry (toGenLoop (adjoint f))) :
    π_ (n + 1) X x) = Quotient.mk' (toGenLoop f)
  rw [h, GeneralizedLoopCurrying.uncurry_curry]

theorem adjoint_class (f : BasedMap (n + 1) X x) :
    sphereClass (adjoint f) =
      (GeneralizedLoopCurrying.homotopyMulEquiv n x).symm (sphereClass f) := by
  apply (GeneralizedLoopCurrying.homotopyMulEquiv n x).injective
  rw [MulEquiv.apply_symm_apply]
  exact adjoint_native f

theorem adjoint_compose (f : BasedMap (n + 1) X x)
    (g : SphereComposition.Based m n) :
    adjoint (compose f (productBasedMap g)) = compose (adjoint f) g := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  apply Path.ext
  funext t
  calc
    (adjoint (compose f (productBasedMap g))).val z t =
        f.val ((productBasedMap g).val (meridian m (t, z))) :=
      adjoint_meridian (compose f (productBasedMap g)) z t
    _ = f.val (meridian n (t, g.val z)) :=
      congrArg f.val (productBasedMap_meridian g t z)
    _ = (adjoint f).val (g.val z) t := (adjoint_meridian f (g.val z) t).symm

end Wikipedia.HopfProblem.DegreeCollapse.SphereAdjunction

