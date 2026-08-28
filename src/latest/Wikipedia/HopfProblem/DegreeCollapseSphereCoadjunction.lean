import Wikipedia.HopfProblem.DegreeCollapseSphereAdjunction
import Wikipedia.HopfProblem.DegreeCollapseGroupSpherePrecomposition

/-!
# Uncurrying actual based sphere-loop maps and suspended precomposition

Descend the original uncurried cube to the original sphere quotient.
Its native class is exactly the existing currying equivalence. The
proved meridian adjunction then retains suspended precomposition.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.SphereCoadjunction

open NoExoticSixSphere SmoothCube SphereLiftFamily CubicalSphereSuspension

variable {X : Type*} [TopologicalSpace X] {x : X}
  {m n : ℕ} [NeZero m] [NeZero n]

def unadjoint (q : BasedMap n (Path x x) (Path.refl x)) : BasedMap (n + 1) X x :=
  (basedEquiv (Nat.succ_pos n)).symm (GeneralizedLoopCurrying.uncurry (toGenLoop q))

omit [NeZero n] in
theorem unadjoint_toGenLoop (q : BasedMap n (Path x x) (Path.refl x)) :
    toGenLoop (unadjoint q) = GeneralizedLoopCurrying.uncurry (toGenLoop q) :=
  (basedEquiv (Nat.succ_pos n)).apply_symm_apply _

theorem unadjoint_native (q : BasedMap n (Path x x) (Path.refl x)) :
    sphereClass (unadjoint q) =
      GeneralizedLoopCurrying.homotopyMulEquiv n x (sphereClass q) :=
  congrArg Quotient.mk' (unadjoint_toGenLoop q)

theorem adjoint_unadjoint_class (q : BasedMap n (Path x x) (Path.refl x)) :
    sphereClass (SphereAdjunction.adjoint (unadjoint q)) = sphereClass q := by
  rw [SphereAdjunction.adjoint_class, unadjoint_native, MulEquiv.symm_apply_apply]

theorem unadjoint_precomposition (q : BasedMap n (Path x x) (Path.refl x))
    (g : SphereComposition.Based m n) :
    sphereClass (unadjoint (compose q g)) =
      sphereClass (compose (unadjoint q) (productBasedMap g)) := by
  rw [unadjoint_native, ← SphereAdjunction.adjoint_native
    (compose (unadjoint q) (productBasedMap g)), SphereAdjunction.adjoint_compose]
  exact congrArg (GeneralizedLoopCurrying.homotopyMulEquiv m x)
    (GroupSpherePrecomposition.compose_class_congr (adjoint_unadjoint_class q).symm g)

end Wikipedia.HopfProblem.DegreeCollapse.SphereCoadjunction
