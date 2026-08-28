import Wikipedia.HomotopyGroupsOfSpheres.PointedMaps
import Wikipedia.HopfProblem.DegreeCollapseSphereCube
import Mathlib.Algebra.Group.Int.Units

/-!
# The actual cube-boundary quotient is a primitive sphere class

Every native cube descends through the genuine sphere quotient. If the sphere's
native homotopy group has an integral marking, this universal factorization
forces the quotient cube to have coordinate of absolute value one.
-/

noncomputable section

open scoped Topology unitInterval
open Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.SphereCubeGenerator

open Wikipedia.HopfProblem.DegreeCollapse.SphereCube

def quotientCube (n : ℕ) : GenLoop (Fin n) (Sphere n) (point n) :=
  ⟨quotient n, quotient_boundary n⟩

def quotientClass (n : ℕ) : π_ n (Sphere n) (point n) := ⟦quotientCube n⟧

theorem quotient_isQuotientMap {n : ℕ} (hn : 0 < n) : IsQuotientMap (quotient n) :=
  .of_surjective_continuous (quotient_surjective hn) (quotient n).continuous

variable {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}

theorem cube_constant_on_quotient_fibers (p : GenLoop (Fin n) X x)
    (u v : Fin n → I) (h : quotient n u = quotient n v) : p u = p v := by
  rcases (quotient_eq_iff n u v).mp h with h | ⟨hu, hv⟩
  · exact congrArg p h
  · exact (p.property u hu).trans (p.property v hv).symm

def descend (hn : 0 < n) (p : GenLoop (Fin n) X x) : C(Sphere n, X) :=
  (quotient_isQuotientMap hn).lift p.val (cube_constant_on_quotient_fibers p)

theorem descend_quotient (hn : 0 < n) (p : GenLoop (Fin n) X x) (u : Fin n → I) :
    descend hn p (quotient n u) = p u :=
  ContinuousMap.congr_fun ((quotient_isQuotientMap hn).lift_comp p.val
    (cube_constant_on_quotient_fibers p)) u

theorem descend_point (hn : 0 < n) (p : GenLoop (Fin n) X x) : descend hn p (point n) = x := by
  rw [← quotient_boundary n 0 (zero_boundary hn), descend_quotient]
  exact p.property 0 (zero_boundary hn)

theorem descend_native_class [NeZero n] (p : GenLoop (Fin n) X x) :
    pointedMap (descend (NeZero.pos n) p) (point n) x (descend_point (NeZero.pos n) p)
      (quotientClass n) = (⟦p⟧ : π_ n X x) := by
  have hm := pointedMap_mk (descend (NeZero.pos n) p) (point n) x
    (descend_point (NeZero.pos n) p) (quotientCube n)
  refine hm.trans ?_
  apply congrArg (fun q : GenLoop (Fin n) X x ↦ (⟦q⟧ : π_ n X x))
  apply GenLoop.ext
  intro u
  exact descend_quotient (NeZero.pos n) p u

/-- Primitivity follows from actual quotient descent, not an assigned normalization. -/
theorem quotientClass_coordinate_natAbs [NeZero n]
    (e : π_ n (Sphere n) (point n) ≃* Multiplicative ℤ) :
    Int.natAbs (e (quotientClass n)).toAdd = 1 := by
  let g := e.symm (Multiplicative.ofAdd 1)
  let k := (e (quotientClass n)).toAdd
  have hg : e g = Multiplicative.ofAdd 1 := e.apply_symm_apply _
  have hq : g ^ k = quotientClass n := by
    apply e.injective
    rw [map_zpow, hg]
    change Multiplicative.ofAdd (k • (1 : ℤ)) = Multiplicative.ofAdd k
    simp
  obtain ⟨p, hp⟩ := Quotient.exists_rep g
  let f := pointedMap (N := Fin n) (descend (NeZero.pos n) p) (point n) (point n)
    (descend_point (NeZero.pos n) p)
  have hf : f (quotientClass n) = g := (descend_native_class p).trans hp
  have hpow : e (f g) ^ k = Multiplicative.ofAdd 1 := by
    rw [← map_zpow, ← map_zpow, hq, hf, hg]
  have hi : k * (e (f g)).toAdd = 1 := by
    have h := congrArg Multiplicative.toAdd hpow
    change k • (e (f g)).toAdd = 1 at h
    simpa only [zsmul_eq_mul, Int.cast_id] using h
  have hn := congrArg Int.natAbs hi
  rw [Int.natAbs_mul] at hn
  exact Nat.eq_one_of_mul_eq_one_right hn

theorem quotientClass_generates [NeZero n]
    (e : π_ n (Sphere n) (point n) ≃* Multiplicative ℤ) :
    Function.Surjective (fun k : ℤ ↦ quotientClass n ^ k) := by
  let k := (e (quotientClass n)).toAdd
  have hk : k * k = 1 := Int.isUnit_mul_self
    (Int.isUnit_iff_natAbs_eq.mpr (quotientClass_coordinate_natAbs e))
  intro a
  refine ⟨(e a).toAdd * k, e.injective ?_⟩
  change e (quotientClass n ^ ((e a).toAdd * k)) = e a
  rw [map_zpow]
  change Multiplicative.ofAdd (((e a).toAdd * k) • k) = Multiplicative.ofAdd (e a).toAdd
  apply congrArg Multiplicative.ofAdd
  rw [zsmul_eq_mul, Int.cast_id, mul_assoc, hk, mul_one]

end Wikipedia.HomotopyGroupsOfSpheres.SphereCubeGenerator
