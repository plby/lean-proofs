import Wikipedia.HopfProblem.HomotopyGroupPowerMap
import Wikipedia.HopfProblem.DegreeCollapseSphereHomotopy
import Mathlib.Topology.Homotopy.Contractible

/-!
# Null-homotopies from an explicit exponent of the native sixth homotopy group

The source is the literal Euclidean unit six-sphere used by the project.
An exponent for the actual sixth homotopy group of a topological group
gives actual null-homotopies of powers of sphere maps. A homotopy
equivalence of the source then transports the conclusion without any
smooth sphere-recognition theorem.

This is a reduction, not a proof that `π₆(S³)` has exponent twelve, nor a
construction of the required factorization of the threefold projection.
Both of those inputs must still be proved to apply this result there.
-/

noncomputable section

open scoped Topology ContinuousMap unitInterval

namespace Wikipedia.HopfProblem.SixSpherePowerNullhomotopy

open SixSphereCube HomotopyGroupPowerMap

variable {G : Type*} [TopologicalSpace G]

section Monoid

variable [Monoid G] [ContinuousMul G]

/-- Pull back a based map through the original quotient from the six-cube. -/
def sphereLoop (g : C(StandardSphere, G)) (hg : g sphereBasePoint = 1) :
    GenLoop (Fin 6) G 1 :=
  ⟨g.comp cubeSphereMap, fun u hu => by
    change g (cubeSphereMap u) = 1
    rw [cubeSphereMap_boundary u hu, hg]⟩

/-- Powering before or after descending the cube gives the same sphere map. -/
theorem factorMap_pow_sphereLoop (g : C(StandardSphere, G))
    (hg : g sphereBasePoint = 1) (m : ℕ) :
    factorMap (powLoop (sphereLoop g hg) m) = g ^ m := by
  symm
  apply factorMap_unique
  ext u
  rfl

/-- An exponent in native sixth homotopy supplies an actual based null-homotopy. -/
theorem based_pow_nullhomotopic (m : ℕ)
    (hexp : ∀ a : π_ 6 G 1, a ^ m = 1)
    (g : C(StandardSphere, G)) (hg : g sphereBasePoint = 1) :
    (g ^ m).Nullhomotopic := by
  have h := DegreeCollapse.factorMap_homotopicRel
    (powLoop_homotopic_const_of_exponent m hexp (sphereLoop g hg))
  rw [factorMap_pow_sphereLoop, factorMap_const] at h
  exact ⟨1, h.homotopic⟩

end Monoid

section Group

variable [Group G] [IsTopologicalGroup G] [PathConnectedSpace G]

/-- Remove the value at the distinguished point using the actual group operation. -/
def normalize (g : C(StandardSphere, G)) : C(StandardSphere, G) :=
  g * ContinuousMap.const _ (g sphereBasePoint)⁻¹

omit [PathConnectedSpace G] in
@[simp] theorem normalize_basePoint (g : C(StandardSphere, G)) :
    normalize g sphereBasePoint = 1 := by simp [normalize]

/-- Changing the base value by a path gives a homotopy of the actual powered maps. -/
theorem pow_homotopic_normalize_pow (g : C(StandardSphere, G)) (m : ℕ) :
    (g ^ m).Homotopic (normalize g ^ m) := by
  let p : Path (1 : G) (g sphereBasePoint)⁻¹ :=
    (PathConnectedSpace.joined 1 (g sphereBasePoint)⁻¹).somePath
  exact ⟨{
    toFun := fun tx => (g tx.2 * p tx.1) ^ m
    continuous_toFun := (g.continuous.comp continuous_snd |>.mul
      (p.continuous.comp continuous_fst)).pow m
    map_zero_left := fun z => by simp
    map_one_left := fun z => by simp [normalize]
  }⟩

/-- The exponent conclusion does not depend on the map preserving a chosen base point. -/
theorem pow_nullhomotopic (m : ℕ)
    (hexp : ∀ a : π_ 6 G 1, a ^ m = 1) (g : C(StandardSphere, G)) :
    (g ^ m).Nullhomotopic := by
  obtain ⟨y, hy⟩ := based_pow_nullhomotopic m hexp (normalize g) (normalize_basePoint g)
  exact ⟨y, (pow_homotopic_normalize_pow g m).trans hy⟩

end Group

section SourceEquivalence

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A null-homotopy after a homotopy equivalence is a null-homotopy of the original map. -/
theorem nullhomotopic_of_comp_equiv (e : StandardSphere ≃ₕ X) (f : C(X, Y))
    (hf : (f.comp e.toFun).Nullhomotopic) : f.Nullhomotopic := by
  obtain ⟨y, hy⟩ := hf.comp_left e.invFun
  refine ⟨y, ?_⟩
  have h : ((f.comp e.toFun).comp e.invFun).Homotopic f := by
    simpa only [ContinuousMap.comp_assoc, ContinuousMap.comp_id] using
      (ContinuousMap.Homotopic.refl f).comp e.right_inv
  exact h.symm.trans hy

variable [Group G] [IsTopologicalGroup G] [PathConnectedSpace G]

/-- The final topological reduction, with exponent and factorization explicitly exposed.
Neither hypothesis is discharged for the threefold projection in this file. -/
theorem nullhomotopic_of_power_factorization
    (e : StandardSphere ≃ₕ X) (f : C(X, Y)) (g : C(X, G)) (h : C(G, Y)) (m : ℕ)
    (hexp : ∀ a : π_ 6 G 1, a ^ m = 1)
    (hfactor : f.Homotopic (h.comp (g ^ m))) : f.Nullhomotopic := by
  have hp : (g ^ m).Nullhomotopic := by
    apply nullhomotopic_of_comp_equiv e
    have heq : (g ^ m).comp e.toFun = (g.comp e.toFun) ^ m := by ext z; rfl
    rw [heq]
    exact pow_nullhomotopic m hexp (g.comp e.toFun)
  obtain ⟨y, hy⟩ := hp.comp_right h
  exact ⟨y, hfactor.trans hy⟩

end SourceEquivalence

end Wikipedia.HopfProblem.SixSpherePowerNullhomotopy
