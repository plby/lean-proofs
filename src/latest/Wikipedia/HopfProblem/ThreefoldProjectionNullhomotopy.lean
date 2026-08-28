import Wikipedia.HopfProblem.ThreefoldProjectionRoots
import Wikipedia.HopfProblem.QuaternionProjectiveMap
import Wikipedia.HopfProblem.QuaternionPuncturedRetraction
import Wikipedia.HopfProblem.QuaternionSphereExponent
import Wikipedia.HopfProblem.DegreeCollapseHomotopyEquivalence

/-!
# The actual threefold projection is null-homotopic

The global roots, projective factorization, and coordinate-power homotopies
reduce the result to two previously conditional inputs. Both are now proved:
the actual threefold is homotopy equivalent to the ordinary six-sphere, and
the native sixth homotopy group of the three-sphere has exponent twelve.
-/

noncomputable section

open scoped Topology Quaternion ContinuousMap

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.ProjectionHomotopy

open QuaternionCoordinatePowers QuaternionPowerNullhomotopy SixSphereCube

/-- The unchanged continuous projection of the actual glued threefold. -/
def projectionMap : C(Space, RiemannSphere) :=
  ⟨projectionSphere, projectionSphere_continuous⟩

/-- The globally constructed roots, regarded as a nonzero quaternion. -/
theorem rootPair_ne_zero (x : Space) : pair (Roots.root .three x) (Roots.root .four x) ≠ 0 := by
  intro h
  obtain ⟨h₃, h₄⟩ := (pair_eq_zero_iff _ _).mp h
  exact (Roots.roots_no_common_zero x).elim (fun hn => hn h₃) (fun hn => hn h₄)

def rootLift : C(Space, Punctured) where
  toFun x := ⟨pair (Roots.root .three x) (Roots.root .four x), rootPair_ne_zero x⟩
  continuous_toFun :=
    (pair_continuous.comp ((Roots.root .three).continuous.prodMk
      (Roots.root .four).continuous)).subtype_mk rootPair_ne_zero

/-- Exact factorization of the original projection, not an extra assumption. -/
theorem projection_factorization :
    projectiveMap.comp ((coordinatePower 3 4).comp rootLift) = projectionMap := by
  apply ContinuousMap.ext
  intro x
  change projectiveRatio (first ((coordinatePower 3 4) (rootLift x)).val)
    (first ((coordinatePower 3 4) (rootLift x)).val -
      second ((coordinatePower 3 4) (rootLift x)).val) = projectionSphere x
  rw [coordinatePower_val, first_pair, second_pair]
  change projectiveRatio (Roots.root .three x ^ 3)
    (Roots.root .three x ^ 3 - Roots.root .four x ^ 4) = projectionSphere x
  rw [Roots.cubic_root, Roots.quartic_root]
  exact (projectionSphere_reconstruction x).symm

/-- The general reduction, retaining its two explicit inputs for reuse. -/
theorem projection_nullhomotopic_of_equiv_of_exponent (e : StandardSphere ≃ₕ Space)
    (hexp : SphereExponentTwelve) : projectionMap.Nullhomotopic := by
  have hc := (coordinatePower_homotopic 3 4).comp (ContinuousMap.Homotopic.refl rootLift)
  obtain ⟨q, hq⟩ := twelfthPower_nullhomotopic e hexp rootLift
  have hraw : ((coordinatePower 3 4).comp rootLift).Nullhomotopic := ⟨q, hc.trans hq⟩
  have h := hraw.comp_right projectiveMap
  rw [projection_factorization] at h
  exact h

/-- Unconditionally, the actual threefold projection is null-homotopic. -/
theorem projection_nullhomotopic : projectionMap.Nullhomotopic :=
  projection_nullhomotopic_of_equiv_of_exponent
    DegreeCollapse.threefoldHomotopyEquiv.symm sphereExponentTwelve

/-- The same result for any specified identification of the source with S⁶. -/
theorem sphere_projection_nullhomotopic_of_equiv (e : StandardSphere ≃ₕ Space) :
    (projectionMap.comp e.toFun).Nullhomotopic :=
  projection_nullhomotopic.comp_left e.toFun

/-- No recognition or exponent hypothesis is needed for the proved sphere identification. -/
theorem sphere_projection_nullhomotopic :
    (projectionMap.comp DegreeCollapse.threefoldHomotopyEquiv.symm.toFun).Nullhomotopic :=
  sphere_projection_nullhomotopic_of_equiv DegreeCollapse.threefoldHomotopyEquiv.symm

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.ProjectionHomotopy
