import Wikipedia.NoExoticSixSphere.StabilizedReflections
import Wikipedia.NoExoticSixSphere.SphereReflectionHomology

/-!
# A concrete frame twist with even evaluation and trivial stabilization

The product of reflection in a variable unit normal and reflection in a fixed
unit normal is based at the identity. Its distinguished column is the negative
reflection sphere map. In dimension four that column doubles integral H3.
After adding one identity coordinate, the actual operator family contracts to
identity by contracting both normals through the same closed hemisphere.

This constructs the family; it does not assert a geometric surgery retwisting
formula or existence of a filling.
-/

noncomputable section

namespace Wikipedia.HopfProblem.DegreeCollapse.ReflectionFrameTwist

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization
open NoExoticSixSphere.OrthogonalPaths NoExoticSixSphere.OrthogonalStabilization
open NoExoticSixSphere.ColumnCoordinates NoExoticSixSphere.ColumnFiber
open NoExoticSixSphere.FixedColumnBlock
open SingularMayerVietoris

variable {n : ℕ}

theorem reflection_mul_self (w : Vector n) :
    mul (reflection w) (reflection w) = identity n := by
  apply Subtype.ext
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  change (ℝ ∙ w)ᗮ.reflection ((ℝ ∙ w)ᗮ.reflection x) = x
  exact (ℝ ∙ w)ᗮ.reflection_reflection x

/-- The actual product of the two hyperplane reflections. -/
def twist (v : UnitSphere (Vector n)) : C(UnitSphere (Vector n), OrthogonalOperators n) :=
  mulMap reflectionMap (ContinuousMap.const _ (reflection v.val))

theorem twist_base (v : UnitSphere (Vector n)) : twist v v = identity n :=
  reflection_mul_self v.val

/-- The distinguished column is exactly the negative reflection map. -/
theorem twist_column (v : UnitSphere (Vector n)) :
    column v (twist v) = SphereReflection.negative v := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change (ℝ ∙ x.val)ᗮ.reflection ((ℝ ∙ v.val)ᗮ.reflection v.val) =
    -(ℝ ∙ x.val)ᗮ.reflection v.val
  rw [Submodule.reflection_orthogonalComplement_singleton_eq_neg, map_neg]

theorem stabilize_mul (z : UnitSphere (Vector (n + 1)))
    (a b : OrthogonalOperators n) :
    stabilize z (mul a b) = mul (stabilize z a) (stabilize z b) := by
  apply Subtype.ext
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro w
  change (stabilize z (mul a b)).1.1 w =
    (stabilize z a).1.1 ((stabilize z b).1.1 w)
  rw [stabilize_apply, stabilize_apply, stabilize_apply,
    LinearIsometryEquiv.apply_symm_apply]
  congr 1

variable {X : Type*} [TopologicalSpace X]

theorem stabilize_mulMap (z : UnitSphere (Vector (n + 1)))
    (a b : C(X, OrthogonalOperators n)) :
    stabilizeMap z (mulMap a b) = mulMap (stabilizeMap z a) (stabilizeMap z b) := by
  apply ContinuousMap.ext
  intro x
  exact stabilize_mul z (a x) (b x)

/-- Any pullback of this reflection product has an actual stable contraction. -/
theorem stabilized_twist_nullhomotopic (z : UnitSphere (Vector (n + 1)))
    (v : UnitSphere (Vector n)) (f : C(X, UnitSphere (Vector n))) :
    (stabilizeMap z ((twist v).comp f)).Homotopic
      (ContinuousMap.const X (identity (n + 1))) := by
  let a := reflectionMap.comp f
  let b : C(X, OrthogonalOperators n) := ContinuousMap.const X (reflection v.val)
  have hstart : (twist v).comp f = mulMap a b := rfl
  rw [hstart, stabilize_mulMap]
  obtain ⟨H⟩ := stabilized_reflectionFamily_nullhomotopic z f
  have hleft : (mulMap (stabilizeMap z a) (stabilizeMap z b)).Homotopic
      (mulMap (ContinuousMap.const X (reflection z.val)) (stabilizeMap z b)) :=
    ⟨mulHomotopy H (stabilizeMap z b)⟩
  have hright : (stabilizeMap z b).Homotopic
      (ContinuousMap.const X (reflection z.val)) :=
    stabilized_reflectionFamily_nullhomotopic z (ContinuousMap.const X v)
  have h := hleft.trans (homotopic_leftMulMap (reflection z.val) hright)
  simpa only [mulMap_const, reflection_mul_self] using h

/-- In rank four the actual evaluation map doubles integral third homology. -/
theorem twist_column_homology (v : UnitSphere (Vector 4))
    (a : SingularHomology (UnitSphere (Vector 4)) 3) :
    singularHomologyMap (column v (twist v)) 3 a = a + a := by
  rw [twist_column]
  exact SphereReflection.negative_homology_of_quaternion_isometry
    Quaternion.linearIsometryEquivTuple.symm v a

theorem marked_twist_column_homology (v : UnitSphere (Vector 4))
    (e : SingularHomology (UnitSphere (Vector 4)) 3 ≃ₗ[ℤ] ℤ)
    (a : SingularHomology (UnitSphere (Vector 4)) 3) :
    e (singularHomologyMap (column v (twist v)) 3 a) = 2 * e a := by
  rw [twist_column_homology, map_add, two_mul]

end Wikipedia.HopfProblem.DegreeCollapse.ReflectionFrameTwist
