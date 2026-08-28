import Wikipedia.NoExoticSixSphere.OrthogonalRankReduction

/-!
# Orthogonal stabilization and the exact remaining homotopy input

Stabilization extends an operator by the identity on one fixed unit-vector
line. The rank reduction is equivalent to a statement that these stabilized
maps are nullhomotopic. In particular, the missing rank-seven computation
concerns stabilized rank-six maps, not nullhomotopy of all rank-six maps.
-/

namespace NoExoticSixSphere

open GLOrthonormalization

namespace OrthogonalPaths

variable {n : ℕ} {X : Type*} [TopologicalSpace X]

/-- Left multiplication by a fixed orthogonal operator preserves homotopies. -/
theorem homotopic_leftMulMap (a : OrthogonalOperators n)
    {b c : C(X, OrthogonalOperators n)} (h : b.Homotopic c) :
    (mulMap (ContinuousMap.const X a) b).Homotopic
      (mulMap (ContinuousMap.const X a) c) :=
  (ContinuousMap.Homotopic.refl
    (⟨mul a, continuous_mul (fun _ ↦ a) id continuous_const continuous_id⟩ :
      C(OrthogonalOperators n, OrthogonalOperators n))).comp h

theorem mulMap_const (a b : OrthogonalOperators n) :
    mulMap (ContinuousMap.const X a) (ContinuousMap.const X b) =
      ContinuousMap.const X (mul a b) := rfl

end OrthogonalPaths

namespace OrthogonalStabilization

open OrthogonalPaths ColumnCoordinates ColumnFiber FixedColumnBlock

variable {r : ℕ}

local instance dimensionFact : Fact (Module.finrank ℝ (Vector (r + 1)) = r + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

variable (v : UnitSphere (Vector (r + 1)))

/-- Extend by the identity on the distinguished line. -/
noncomputable def stabilize (q : OrthogonalOperators r) : OrthogonalOperators (r + 1) :=
  reconstruct v v q

theorem stabilize_apply (q : OrthogonalOperators r) (w : Vector (r + 1)) :
    (stabilize v q).1.1 w = (split v).symm (block (toEquiv q) (split v w)) := rfl

theorem stabilize_column (q : OrthogonalOperators r) :
    (stabilize v q).1.1 (v : Vector (r + 1)) = (v : Vector (r + 1)) :=
  reconstruct_column v v q

theorem stabilize_identity : stabilize v (identity r) = identity (r + 1) := by
  apply Subtype.ext
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro w
  rw [stabilize_apply]
  have hb : block (toEquiv (identity r)) (split (r := r) v w) = split v w := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext <;> rfl
  rw [hb, LinearIsometryEquiv.symm_apply_apply]
  rfl

/-- The fixed coordinate change from the distinguished source line to another unit line. -/
noncomputable def columnChange (c : UnitSphere (Vector (r + 1))) :
    OrthogonalOperators (r + 1) :=
  ofEquiv ((split (r := r) v).trans (split c).symm)

theorem columnChange_apply (c : UnitSphere (Vector (r + 1))) (w : Vector (r + 1)) :
    (columnChange v c).1.1 w = (split (r := r) c).symm (split v w) := rfl

/-- A reconstruction with a different output column is a fixed left translate of stabilization. -/
theorem reconstruct_eq_mul_stabilize (c : UnitSphere (Vector (r + 1)))
    (q : OrthogonalOperators r) :
    reconstruct v c q = mul (columnChange v c) (stabilize v q) := by
  apply Subtype.ext
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro w
  change (reconstruct v c q).1.1 w = (columnChange v c).1.1 ((stabilize v q).1.1 w)
  rw [reconstruct_apply, columnChange_apply, stabilize_apply,
    LinearIsometryEquiv.apply_symm_apply]

variable {X : Type*} [TopologicalSpace X]

/-- Stabilize a continuous family. -/
noncomputable def stabilizeMap (a : C(X, OrthogonalOperators r)) :
    C(X, OrthogonalOperators (r + 1)) := reconstructMap v v a

theorem reconstructMap_eq_mul_stabilizeMap (c : UnitSphere (Vector (r + 1)))
    (a : C(X, OrthogonalOperators r)) :
    reconstructMap v c a =
      mulMap (ContinuousMap.const X (columnChange v c)) (stabilizeMap v a) := by
  apply ContinuousMap.ext
  intro x
  exact reconstruct_eq_mul_stabilize v c (a x)

/-- At the stable-range boundary, full vanishing is equivalent to nullhomotopy after one
stabilization. Neither side of this equivalence is asserted without proof. -/
theorem vanishing_iff_stabilizedVanishing {m : ℕ} (hmr : m < r) :
    (∀ a : C(Sphere m, OrthogonalOperators (r + 1)),
      ∃ q, a.Homotopic (ContinuousMap.const _ q)) ↔
    (∀ a : C(Sphere m, OrthogonalOperators r),
      ∃ q, (stabilizeMap v a).Homotopic (ContinuousMap.const _ q)) := by
  constructor
  · intro h a
    exact h (stabilizeMap v a)
  · intro h a
    obtain ⟨c, b, hab⟩ := exists_orthogonalRankReduction hmr v a
    obtain ⟨q, hbq⟩ := h b
    refine ⟨mul (columnChange v c) q, hab.trans ?_⟩
    rw [reconstructMap_eq_mul_stabilizeMap]
    simpa only [mulMap_const] using homotopic_leftMulMap (columnChange v c) hbq

end OrthogonalStabilization

end NoExoticSixSphere
