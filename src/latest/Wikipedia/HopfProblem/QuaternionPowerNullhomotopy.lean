import Wikipedia.HopfProblem.UnitQuaternionSphere
import Wikipedia.HopfProblem.SixSpherePowerNullhomotopy
import Wikipedia.HopfProblem.SixthHurewiczNativeMaps
import Mathlib.Data.ZMod.Basic

/-!
# An abstract exponent input and quaternion power null-homotopies

`SphereExponentTwelve` is explicitly a statement about Mathlib's native
sixth homotopy group of the literal Euclidean three-sphere. This reduction
takes it as a hypothesis, not an axiom. `QuaternionSphereExponent` proves
it from the unconditional group calculation. The transfer to unit quaternions
and actual null-homotopies of twelfth powers are proved below.

`ThreefoldProjectionNullhomotopy` supplies the geometric cubic/quartic
factorization and proves the final projection result unconditionally.
-/

noncomputable section

open scoped Topology ContinuousMap

namespace Wikipedia.HopfProblem.QuaternionPowerNullhomotopy

open UnitQuaternionSphere SixSphereCube

/-- The sole classical homotopy-group input, at a specified point of the standard sphere. -/
def SphereExponentTwelve : Prop :=
  ∀ a : π_ 6 (SphereHomology.UnitSphere 3) (sphereHomeomorph 1), a ^ 12 = 1

/-- The familiar `π₆(S³) ≃ ℤ/12` calculation supplies precisely the permitted input. -/
theorem sphereExponentTwelve_of_mulEquiv
    (e : π_ 6 (SphereHomology.UnitSphere 3) (sphereHomeomorph 1) ≃*
      Multiplicative (ZMod 12)) : SphereExponentTwelve := by
  intro a
  have h : e a ^ 12 = 1 := by
    change (12 : ℕ) • (e a).toAdd = 0
    simp only [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  exact e.injective ((map_pow e a 12).trans (h.trans (map_one e).symm))

private theorem homotopyMap_homeomorph_injective
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) (x : X) :
    Function.Injective (SixthHurewicz.homotopyMap (e : C(X, Y)) x) := by
  intro a b hab
  induction a using Quotient.inductionOn with
  | h p =>
    induction b using Quotient.inductionOn with
    | h q =>
      have h : GenLoop.Homotopic
          (SecondHurewicz.mapGenLoop (e : C(X, Y)) x p)
          (SecondHurewicz.mapGenLoop (e : C(X, Y)) x q) := Quotient.exact hab
      have hi := h.comp_continuousMap (e.symm : C(Y, X))
      apply Quotient.sound
      change p.val.HomotopicRel q.val (Cube.boundary (Fin 6))
      convert hi using 1 <;> ext u <;> exact (e.symm_apply_apply _).symm

/-- The ordinary sphere exponent implies the same exponent in the actual quaternion group. -/
theorem quaternion_exponent_twelve (hexp : SphereExponentTwelve) :
    ∀ a : π_ 6 UnitQuaternions 1, a ^ 12 = 1 := by
  let F := SixthHurewicz.homotopyMap
    (sphereHomeomorph : C(UnitQuaternions, SphereHomology.UnitSphere 3)) 1
  have hinj : Function.Injective F := homotopyMap_homeomorph_injective sphereHomeomorph 1
  intro a
  apply hinj
  exact (F.map_pow a 12).trans ((hexp (F a)).trans F.map_one.symm)

/-- Every twelfth power of an actual map `S⁶ → S³` is null-homotopic. -/
theorem twelfth_power_nullhomotopic (hexp : SphereExponentTwelve)
    (g : C(StandardSphere, UnitQuaternions)) : (g ^ 12).Nullhomotopic :=
  SixSpherePowerNullhomotopy.pow_nullhomotopic 12 (quaternion_exponent_twelve hexp) g

/-- Transport the twelfth-power conclusion along the allowed source homotopy equivalence. -/
theorem source_twelfth_power_nullhomotopic {X : Type*} [TopologicalSpace X]
    (e : StandardSphere ≃ₕ X) (hexp : SphereExponentTwelve)
    (g : C(X, UnitQuaternions)) : (g ^ 12).Nullhomotopic := by
  apply SixSpherePowerNullhomotopy.nullhomotopic_of_comp_equiv e
  have heq : (g ^ 12).comp e.toFun = (g.comp e.toFun) ^ 12 := by
    apply ContinuousMap.ext
    intro z
    rfl
  rw [heq]
  exact twelfth_power_nullhomotopic hexp (g.comp e.toFun)

end Wikipedia.HopfProblem.QuaternionPowerNullhomotopy
