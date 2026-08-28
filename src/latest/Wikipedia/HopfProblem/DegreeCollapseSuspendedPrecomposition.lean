import Wikipedia.HopfProblem.DegreeCollapseSphereCoadjunction

/-!
# Precomposition by the actual suspension preserves native group powers

On loop-valued sphere maps, pointwise path concatenation represents
the native product, as is seen by uncurrying in the leading cube
coordinate. Precomposition preserves that product. Transport through
the original currying equivalences gives a homomorphism for suspended
precomposition, without a topological-group assumption on the target.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.DegreeCollapse.SuspendedPrecomposition

open NoExoticSixSphere SmoothCube SphereLiftFamily CubicalSphereSuspension

variable {X : Type*} [TopologicalSpace X] {x : X}
  {m n : ℕ} [NeZero m] [NeZero n]

def loopProduct (p q : BasedMap n (Path x x) (Path.refl x)) :
    BasedMap n (Path x x) (Path.refl x) :=
  ⟨⟨fun z ↦ (q.val z).trans (p.val z), q.val.continuous.path_trans p.val.continuous⟩,
    by change (q.val (spherePole n)).trans (p.val (spherePole n)) = _
       rw [p.property, q.property, Path.refl_trans_refl]⟩

omit [NeZero n] in
theorem uncurry_loopProduct (p q : BasedMap n (Path x x) (Path.refl x)) :
    GeneralizedLoopCurrying.uncurry (toGenLoop (loopProduct p q)) =
      GenLoop.transAt (0 : Fin (n + 1))
        (GeneralizedLoopCurrying.uncurry (toGenLoop q))
        (GeneralizedLoopCurrying.uncurry (toGenLoop p)) := by
  apply GenLoop.ext
  intro u
  have ht (s : I) : Fin.tail (Function.update u 0 s) = Fin.tail u := by
    funext i
    exact Function.update_of_ne (Fin.succ_ne_zero i) _ _
  change (GeneralizedLoopCurrying.uncurry (toGenLoop (loopProduct p q))).val u =
    (GenLoop.transAt (0 : Fin (n + 1))
      (GeneralizedLoopCurrying.uncurry (toGenLoop q))
      (GeneralizedLoopCurrying.uncurry (toGenLoop p))).val u
  rw [GeneralizedLoopCurrying.transAt_apply]
  change (if (u 0 : ℝ) ≤ 1 / 2 then (q.val (quotient n (Fin.tail u))).extend (2 * u 0)
    else (p.val (quotient n (Fin.tail u))).extend (2 * u 0 - 1)) = _
  split_ifs
  · rw [GeneralizedLoopCurrying.uncurry_apply, ht, Function.update_self]
    rfl
  · rw [GeneralizedLoopCurrying.uncurry_apply, ht, Function.update_self]
    rfl

theorem loopProduct_class (p q : BasedMap n (Path x x) (Path.refl x)) :
    sphereClass (loopProduct p q) = sphereClass p * sphereClass q := by
  apply (GeneralizedLoopCurrying.homotopyMulEquiv n x).injective
  rw [map_mul]
  change Quotient.mk' (GeneralizedLoopCurrying.uncurry (toGenLoop (loopProduct p q))) = _
  rw [uncurry_loopProduct]
  exact (HomotopyGroup.mul_spec (i := (0 : Fin (n + 1)))).symm

def loopApply (g : SphereComposition.Based m n)
    (c : π_ n (Path x x) (Path.refl x)) : π_ m (Path x x) (Path.refl x) :=
  sphereClass (compose (Classical.choose (sphereClass_surjective (Nat.pos_of_neZero n) c)) g)

theorem loopApply_class (g : SphereComposition.Based m n)
    (p : BasedMap n (Path x x) (Path.refl x)) :
    loopApply g (sphereClass p) = sphereClass (compose p g) :=
  GroupSpherePrecomposition.compose_class_congr
    (Classical.choose_spec (sphereClass_surjective (Nat.pos_of_neZero n) (sphereClass p))) g

theorem loopApply_mul (g : SphereComposition.Based m n)
    (a b : π_ n (Path x x) (Path.refl x)) :
    loopApply g (a * b) = loopApply g a * loopApply g b := by
  obtain ⟨p, rfl⟩ := sphereClass_surjective (Nat.pos_of_neZero n) a
  obtain ⟨q, rfl⟩ := sphereClass_surjective (Nat.pos_of_neZero n) b
  rw [← loopProduct_class, loopApply_class, loopApply_class, loopApply_class]
  exact loopProduct_class (compose p g) (compose q g)

def loopHom (g : SphereComposition.Based m n) :
    π_ n (Path x x) (Path.refl x) →* π_ m (Path x x) (Path.refl x) where
  toFun := loopApply g
  map_mul' := loopApply_mul g
  map_one' := by
    apply mul_left_cancel (a := loopApply (x := x) g 1)
    simpa only [mul_one, one_mul] using (loopApply_mul (x := x) g 1 1).symm

def hom (g : SphereComposition.Based m n) : π_ (n + 1) X x →* π_ (m + 1) X x :=
  (GeneralizedLoopCurrying.homotopyMulEquiv m x).toMonoidHom.comp
    ((loopHom g).comp (GeneralizedLoopCurrying.homotopyMulEquiv n x).symm.toMonoidHom)

theorem hom_class (g : SphereComposition.Based m n) (f : BasedMap (n + 1) X x) :
    hom g (sphereClass f) = sphereClass (compose f (productBasedMap g)) := by
  change GeneralizedLoopCurrying.homotopyMulEquiv m x
    (loopApply g ((GeneralizedLoopCurrying.homotopyMulEquiv n x).symm (sphereClass f))) = _
  rw [← SphereAdjunction.adjoint_class f, loopApply_class,
    ← SphereAdjunction.adjoint_compose, SphereAdjunction.adjoint_native]

theorem compose_power (g : SphereComposition.Based m n) {f h : BasedMap (n + 1) X x}
    (k : ℤ) (he : sphereClass h = sphereClass f ^ k) :
    sphereClass (compose h (productBasedMap g)) =
      sphereClass (compose f (productBasedMap g)) ^ k := by
  rw [← hom_class, ← hom_class, he, map_zpow]

end Wikipedia.HopfProblem.DegreeCollapse.SuspendedPrecomposition
