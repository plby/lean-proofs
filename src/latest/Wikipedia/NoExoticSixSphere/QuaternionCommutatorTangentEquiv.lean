import Wikipedia.NoExoticSixSphere.QuaternionCommutatorSourceChart
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Invertibility of the commutator derivative in the actual sphere tangent spaces
-/

noncomputable section

namespace NoExoticSixSphere.QuaternionCommutatorTangentEquiv

open Wikipedia.HomotopyGroupsOfSpheres
open QuaternionicFibration SphereCenteredCoordinates
open QuaternionCommutatorSourceChart QuaternionCommutatorAntipodal

local notation "ℍ" => Quaternion ℝ

abbrev TargetTangent := Tangent antipode

theorem mem_targetTangent (v : QuaternionPlane) : v ∈ TargetTangent ↔ v.fst.re = 0 := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
  simp [antipode, WithLp.prod_inner_apply, Quaternion.inner_def]

theorem ambientDerivative_mem (v : Parameters) : ambientDerivative v ∈ TargetTangent := by
  apply (mem_targetTangent _).mpr
  change (-v.2.1.val).re = 0
  rw [Quaternion.re_neg, imaginary_re, neg_zero]

theorem ambientDerivative_eq_zero (v : Parameters) (h : ambientDerivative v = 0) : v = 0 := by
  have hp : pairDerivative v = 0 :=
    pairToPlane.injective (h.trans (map_zero pairToPlane).symm)
  change (-v.2.1.val, (4 * v.1) • (1 : ℍ) + v.2.2.val) = (0, 0) at hp
  have hl : v.2.1.val = 0 := neg_eq_zero.mp (congrArg Prod.fst hp)
  have ha : v.1 = 0 := by
    have hh := congrArg (fun z : ℍ × ℍ ↦ z.2.re) hp
    simp only [Quaternion.re_add, Quaternion.re_smul, Quaternion.re_one,
      imaginary_re, smul_eq_mul, mul_one, add_zero, Quaternion.re_zero] at hh
    linarith
  have hr : v.2.2.val = 0 := by
    have hh := congrArg Prod.snd hp
    simpa only [ha, mul_zero, zero_smul, zero_add] using hh
  exact Prod.ext ha (Prod.ext (Subtype.ext hl) (Subtype.ext hr))

theorem ambientDerivative_injective : Function.Injective ambientDerivative := by
  intro v w h
  have hz : ambientDerivative (v - w) = 0 := by rw [map_sub, h, sub_self]
  exact sub_eq_zero.mp (ambientDerivative_eq_zero _ hz)

def tangentDerivative : Parameters →L[ℝ] TargetTangent :=
  ambientDerivative.codRestrict TargetTangent ambientDerivative_mem

theorem tangentDerivative_injective : Function.Injective tangentDerivative := by
  intro v w h
  exact ambientDerivative_injective (congrArg Subtype.val h)

theorem tangentDerivative_eq_projection :
    tangentDerivative = TargetTangent.orthogonalProjectionOnto.comp ambientDerivative := by
  apply ContinuousLinearMap.ext
  intro v
  exact (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self
    (⟨ambientDerivative v, ambientDerivative_mem v⟩ : TargetTangent)).symm

theorem imaginary_finrank : Module.finrank ℝ Imaginary = 3 := by
  letI : Fact (Module.finrank ℝ ℍ = 3 + 1) := ⟨Quaternion.finrank_eq_four⟩
  exact tangent_finrank center

theorem parameters_finrank : Module.finrank ℝ Parameters = 7 := by
  simp [Parameters, Module.finrank_prod, imaginary_finrank]

theorem target_finrank : Module.finrank ℝ TargetTangent = 7 := by
  letI : Fact (Module.finrank ℝ QuaternionPlane = 7 + 1) :=
    ⟨by simpa using planeCoordinates.toLinearEquiv.finrank_eq⟩
  exact tangent_finrank antipode

theorem tangentDerivative_bijective : Function.Bijective tangentDerivative :=
  ⟨tangentDerivative_injective,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (parameters_finrank.trans target_finrank.symm)).mp tangentDerivative_injective⟩

def tangentEquiv : Parameters ≃L[ℝ] TargetTangent :=
  (LinearEquiv.ofBijective tangentDerivative.toLinearMap
    tangentDerivative_bijective).toContinuousLinearEquiv

theorem tangentEquiv_apply (v : Parameters) : tangentEquiv v = tangentDerivative v := rfl

end NoExoticSixSphere.QuaternionCommutatorTangentEquiv
