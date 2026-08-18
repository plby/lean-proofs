/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section92MahlerVolumeConversion

/-!
# The singleton terminal realization

Primitive quotient descent is only needed when the source set has at least
two points.  A singleton has a direct rank-one presentation: use
multiplication by its element when that element is nonzero, and the identity
map for the zero singleton.  This closes the only cardinality edge case in
the uniform Section 4 package.
-/

namespace Erdos186.CFP.Bilu.Section92SingletonRealization

open Set MeasureTheory
open Mahler MinkowskiSecond
open Section4SmallCardinality
open Section9ContainerIntegration
open Section92MahlerVolumeConversion
open Section92PresentationDescent
open Section94SortedContainerAssembly

noncomputable section

set_option autoImplicit false

/-- A nonzero coefficient chosen uniformly for a singleton `{a}`. -/
def singletonCoefficient (a : ℤ) : ℤ := if a = 0 then 1 else a

theorem singletonCoefficient_ne_zero (a : ℤ) :
    singletonCoefficient a ≠ 0 := by
  by_cases ha : a = 0 <;> simp [singletonCoefficient, ha]

/-- Rank-one homomorphism used for the singleton source set. -/
def singletonMap (a : ℤ) : IntegralPoint 1 →+ ℤ where
  toFun z := singletonCoefficient a * z 0
  map_zero' := by simp
  map_add' x y := by simp [mul_add]

theorem singletonMap_injective (a : ℤ) :
    Function.Injective (singletonMap a) := by
  intro x y hxy
  apply funext
  intro i
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  subst i
  change singletonCoefficient a * x 0 =
    singletonCoefficient a * y 0 at hxy
  exact mul_left_cancel₀ (singletonCoefficient_ne_zero a) hxy

/-- The explicit unit-cube lift of the singleton element. -/
def singletonLift (a : ℤ) : IntegralPoint 1 :=
  if a = 0 then 0 else standardIntegralPoint 0

theorem singletonMap_singletonLift (a : ℤ) :
    singletonMap a (singletonLift a) = a := by
  by_cases ha : a = 0
  · simp [singletonMap, singletonLift, singletonCoefficient, ha]
  · simp [singletonMap, singletonLift, singletonCoefficient, ha,
      standardIntegralPoint]

/-- The rank-one unit cube contains the singleton lift. -/
theorem singletonLift_mem_unitBall (a : ℤ) :
    normSeminorm ℝ (Fin 1 → ℝ)
        (integralEmbed (singletonLift a)) ≤ 1 := by
  by_cases ha : a = 0
  · simp [singletonLift, ha]
  · rw [singletonLift, if_neg ha,
      integralEmbed_standardIntegralPoint, Pi.basisFun_apply]
    change ‖(Pi.single (0 : Fin 1) (1 : ℝ) : Fin 1 → ℝ)‖ ≤ 1
    rw [Pi.norm_single]
    norm_num

theorem singletonSeminorm_definite :
    IsDefinite (normSeminorm ℝ (Fin 1 → ℝ)) := by
  intro x hx
  exact norm_eq_zero.mp hx

theorem singletonSeminorm_admitsIndependent :
    AdmitsIndependent (normSeminorm ℝ (Fin 1 → ℝ)) 1 1 := by
  refine ⟨standardIntegralPoint,
    linearIndependent_integralEmbed_standard, ?_⟩
  intro i
  rw [integralEmbed_standardIntegralPoint, Pi.basisFun_apply]
  change ‖(Pi.single i (1 : ℝ) : Fin 1 → ℝ)‖ ≤ 1
  rw [Pi.norm_single]
  norm_num

theorem singletonSeminorm_unitBall_volume :
    volume {x : Fin 1 → ℝ |
      normSeminorm ℝ (Fin 1 → ℝ) x ≤ 1} = 2 := by
  have hset : {x : Fin 1 → ℝ |
      normSeminorm ℝ (Fin 1 → ℝ) x ≤ 1} =
      Set.Icc (fun _ ↦ (-1 : ℝ)) (fun _ ↦ (1 : ℝ)) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    change ‖x‖ ≤ 1 ↔ _
    rw [pi_norm_le_iff_of_nonempty, Pi.le_def, Pi.le_def]
    simp only [Real.norm_eq_abs, abs_le, forall_and]
  rw [hset, Real.volume_Icc_pi]
  norm_num [ENNReal.ofReal_ofNat]

/-- Canonical positive-volume body presentation of a singleton. -/
def singletonBodyPresentation (a : ℤ) :
    BodyPresentation ({a} : Finset ℤ) 1 where
  rank_pos := by omega
  seminorm := normSeminorm ℝ (Fin 1 → ℝ)
  definite := singletonSeminorm_definite
  full := singletonSeminorm_admitsIndependent
  map := singletonMap a
  lifts := by
    intro b hb
    have hba : b = a := by simpa using hb
    subst b
    exact ⟨singletonLift a, singletonLift_mem_unitBall a,
      singletonMap_singletonLift a⟩
  bodyVolume_pos := by
    change 0 < (volume {x : Fin 1 → ℝ |
      normSeminorm ℝ (Fin 1 → ℝ) x ≤ 1}).toReal
    rw [singletonSeminorm_unitBall_volume]
    norm_num [Measure.real]

theorem singletonBodyPresentation_enlargedInjective
    (s : ℕ) (a : ℤ) :
    EnlargedInjective s
      (⟨1, singletonBodyPresentation a⟩ :
        RankedBodyPresentation ({a} : Finset ℤ)) := by
  intro x _hx y _hy hxy
  exact singletonMap_injective a hxy

theorem bodyVolume_singletonBodyPresentation (a : ℤ) :
    bodyVolume
      (⟨1, singletonBodyPresentation a⟩ :
        RankedBodyPresentation ({a} : Finset ℤ)) = 2 := by
  change (volume {x : Fin 1 → ℝ |
    normSeminorm ℝ (Fin 1 → ℝ) x ≤ 1}).toReal = 2
  rw [singletonSeminorm_unitBall_volume]
  norm_num

/-- Every singleton has a uniform rank-one reduced realization. -/
theorem exists_reducedOuterRealization_of_card_eq_one
    {A : Finset ℤ} (s volumeConstant rankBound : ℕ)
    (hcard : A.card = 1) (hrankBound : 1 ≤ rankBound)
    (hconstant :
      2 * uniformMahlerOuterVolumeConstant rankBound ≤ volumeConstant) :
    Nonempty (ReducedOuterRealization
      s volumeConstant rankBound A) := by
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hcard
  let X : RankedBodyPresentation ({a} : Finset ℤ) :=
    ⟨1, singletonBodyPresentation a⟩
  apply exists_reducedOuterRealization_of_presentation X
    (singletonBodyPresentation_enlargedInjective s a)
  · intro D
    have hD :=
      MappedOuterContainer.source_volume_cast_le_uniform_mul_bodyVolume
        X hrankBound D
    have hvolume : bodyVolume X = 2 :=
      bodyVolume_singletonBodyPresentation a
    have hreal : (D.source.volume : ℝ) ≤ volumeConstant := by
      calc
        (D.source.volume : ℝ) ≤
            (uniformMahlerOuterVolumeConstant rankBound : ℝ) *
              bodyVolume X := hD
        _ = (2 * uniformMahlerOuterVolumeConstant rankBound : ℕ) := by
          rw [hvolume]
          norm_num [Nat.cast_mul, mul_comm]
        _ ≤ volumeConstant := by exact_mod_cast hconstant
    have hreal' : (D.source.volume : ℝ) ≤
        ((volumeConstant * ({a} : Finset ℤ).card : ℕ) : ℝ) := by
      simpa using hreal
    exact_mod_cast hreal'
  · exact hrankBound

end

end Erdos186.CFP.Bilu.Section92SingletonRealization

#print axioms
  Erdos186.CFP.Bilu.Section92SingletonRealization.exists_reducedOuterRealization_of_card_eq_one
