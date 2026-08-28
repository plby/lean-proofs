import Wikipedia.HopfProblem.PeriodFamilyCircleOrbitProjection

/-!
# The actual fixed-period circle quotient homeomorphism

The source is the orbit quotient of the original complex period torus by
its original delta-circle action.  The target is the quotient of `ℂ × ℝ`
by the three displayed period generators, with its quotient topology.
The homeomorphism is induced by the literal real-linear map on covering
vectors; compactness is used only to verify continuity of its inverse.
-/

noncomputable section

open Topology

namespace Wikipedia.HopfProblem.PeriodFamilyCircleOrbit

/-- The literal projection descends through the actual circle-orbit relation. -/
def orbitModelMap (p : PeriodDomain) : CircleOrbit p → OrbitModel p :=
  Quotient.lift (torusProjection p) (by
    rintro x y ⟨t, rfl⟩
    exact torusProjection_circleFlow p t y)

@[simp] theorem orbitModelMap_projection (p : PeriodDomain) (x : p.Torus) :
    orbitModelMap p (circleOrbitProjection p x) = torusProjection p x := rfl

theorem orbitModelMap_continuous (p : PeriodDomain) : Continuous (orbitModelMap p) :=
  continuous_quot_lift _ (torusProjection_continuous p)

theorem orbitModelMap_injective (p : PeriodDomain) : Function.Injective (orbitModelMap p) := by
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro a b h
  exact Quotient.sound ((torusProjection_eq_iff p a b).mp h)

theorem orbitModelMap_surjective (p : PeriodDomain) : Function.Surjective (orbitModelMap p) := by
  intro z
  obtain ⟨x, rfl⟩ := torusProjection_surjective p z
  exact ⟨circleOrbitProjection p x, rfl⟩

/-- The original fibre's circle quotient is the marked three-period quotient. -/
def orbitModelHomeomorph (p : PeriodDomain) : CircleOrbit p ≃ₜ OrbitModel p :=
  Equiv.toHomeomorphOfContinuousClosed
    (Equiv.ofBijective (orbitModelMap p)
      ⟨orbitModelMap_injective p, orbitModelMap_surjective p⟩)
    (orbitModelMap_continuous p) (orbitModelMap_continuous p).isClosedMap

@[simp] theorem orbitModelHomeomorph_projection (p : PeriodDomain) (x : p.Torus) :
    orbitModelHomeomorph p (circleOrbitProjection p x) = torusProjection p x := rfl

/-- The homeomorphism uses the original complex covering vector and the stated `L`. -/
@[simp] theorem orbitModelHomeomorph_mkQ (p : PeriodDomain) (z : ComplexPlane₂) :
    orbitModelHomeomorph p (circleOrbitProjection p (p.lattice.mkQ z)) =
      orbitClass p (linearProjection p z) := rfl

@[simp] theorem orbitModelHomeomorph_symm_class (p : PeriodDomain) (z : ComplexPlane₂) :
    (orbitModelHomeomorph p).symm (orbitClass p (linearProjection p z)) =
      circleOrbitProjection p (p.lattice.mkQ z) := by
  rw [← orbitModelHomeomorph_mkQ, Homeomorph.symm_apply_apply]

theorem torusProjection_isOpenMap (p : PeriodDomain) : IsOpenMap (torusProjection p) :=
  (orbitModelHomeomorph p).isOpenMap.comp
    (circleOrbitProjection_isOpenQuotientMap p).isOpenMap

theorem torusProjection_isOpenQuotientMap (p : PeriodDomain) :
    IsOpenQuotientMap (torusProjection p) :=
  (orbitModelHomeomorph p).isOpenQuotientMap.comp
    (circleOrbitProjection_isOpenQuotientMap p)

theorem torusProjection_isQuotientMap (p : PeriodDomain) : IsQuotientMap (torusProjection p) :=
  (torusProjection_isOpenQuotientMap p).isQuotientMap

end Wikipedia.HopfProblem.PeriodFamilyCircleOrbit
