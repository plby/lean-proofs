import Wikipedia.HopfProblem.ToricFan
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Centred normal-crossing coordinates for a product

Let `I` be the coordinates vanishing at a point of `z₀z₁z₂ = 0`.
Multiply one coordinate in `I` by the product of the complementary
coordinates, then translate to the origin. The complementary product
is a unit on the chosen open neighbourhood. Both directions of this
coordinate change are explicitly constructed and proved holomorphic.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.NormalCrossingCoordinates

open ToricCharts ToricFan

def unitFactor (I : Finset (Fin 3)) (z : CoordinateSpace 3) : ℂ := ∏ j ∈ Iᶜ, z j

def unitDomain (I : Finset (Fin 3)) : Set (CoordinateSpace 3) := {z | unitFactor I z ≠ 0}

theorem unitFactor_holomorphic (I : Finset (Fin 3)) : ContDiff ℂ ω (unitFactor I) :=
  contDiff_prod (fun j _ => contDiff_apply ℂ ℂ j)

theorem unitDomain_open (I : Finset (Fin 3)) : IsOpen (unitDomain I) :=
  isOpen_ne_fun (unitFactor_holomorphic I).continuous continuous_const

theorem unitFactor_update (I : Finset (Fin 3)) (i : Fin 3) (hi : i ∈ I)
    (z : CoordinateSpace 3) (c : ℂ) : unitFactor I (Function.update z i c) = unitFactor I z :=
  Finset.prod_update_of_notMem (by simpa using hi) z c

def absorb (I : Finset (Fin 3)) (i : Fin 3) (z : CoordinateSpace 3) : CoordinateSpace 3 :=
  Function.update z i (unitFactor I z * z i)

def unabsorb (I : Finset (Fin 3)) (i : Fin 3) (z : CoordinateSpace 3) : CoordinateSpace 3 :=
  Function.update z i (z i / unitFactor I z)

theorem unitFactor_absorb (I : Finset (Fin 3)) (i : Fin 3) (hi : i ∈ I)
    (z : CoordinateSpace 3) : unitFactor I (absorb I i z) = unitFactor I z :=
  unitFactor_update I i hi z _

theorem unitFactor_unabsorb (I : Finset (Fin 3)) (i : Fin 3) (hi : i ∈ I)
    (z : CoordinateSpace 3) : unitFactor I (unabsorb I i z) = unitFactor I z :=
  unitFactor_update I i hi z _

theorem unabsorb_absorb (I : Finset (Fin 3)) (i : Fin 3) (hi : i ∈ I)
    {z : CoordinateSpace 3} (hz : z ∈ unitDomain I) : unabsorb I i (absorb I i z) = z := by
  ext j
  by_cases hj : j = i
  · subst j
    have hu : unitFactor I z ≠ 0 := hz
    simp [unabsorb, absorb, unitFactor_update I i hi, hu]
  · simp [unabsorb, absorb, Function.update_of_ne hj]

theorem absorb_unabsorb (I : Finset (Fin 3)) (i : Fin 3) (hi : i ∈ I)
    {z : CoordinateSpace 3} (hz : z ∈ unitDomain I) : absorb I i (unabsorb I i z) = z := by
  ext j
  by_cases hj : j = i
  · subst j
    have hu : unitFactor I z ≠ 0 := hz
    simp [unabsorb, absorb, unitFactor_update I i hi, div_eq_mul_inv,
      hu, mul_left_comm]
  · simp [unabsorb, absorb, Function.update_of_ne hj]

theorem absorb_holomorphic (I : Finset (Fin 3)) (i : Fin 3) : ContDiff ℂ ω (absorb I i) := by
  apply contDiff_pi.mpr
  intro j
  by_cases hj : j = i
  · subst j
    simpa only [absorb, Function.update_self] using
      (unitFactor_holomorphic I).mul (contDiff_apply ℂ ℂ i)
  · simpa only [absorb, Function.update_of_ne hj] using contDiff_apply ℂ ℂ j

theorem unabsorb_holomorphic (I : Finset (Fin 3)) (i : Fin 3) :
    ContDiffOn ℂ ω (unabsorb I i) (unitDomain I) := by
  apply contDiffOn_pi.mpr
  intro j
  by_cases hj : j = i
  · subst j
    intro z hz
    simpa only [unabsorb, Function.update_self, div_eq_mul_inv] using
      ((contDiff_apply ℂ ℂ i).contDiffWithinAt (s := unitDomain I)).mul
        ((unitFactor_holomorphic I).contDiffWithinAt.fun_inv
          (show unitFactor I z ≠ 0 from hz))
  · simpa only [unabsorb, Function.update_of_ne hj] using (contDiff_apply ℂ ℂ j).contDiffOn

def centeredChart (I : Finset (Fin 3)) (i : Fin 3) (hi : i ∈ I) (a : CoordinateSpace 3) :
    OpenPartialHomeomorph (CoordinateSpace 3) (CoordinateSpace 3) where
  toFun z := absorb I i z - a
  invFun w := unabsorb I i (w + a)
  source := unitDomain I
  target := {w | w + a ∈ unitDomain I}
  map_source' z hz := by
    change unitFactor I (absorb I i z - a + a) ≠ 0
    rw [sub_add_cancel, unitFactor_absorb I i hi]
    exact hz
  map_target' w hw := by
    change unitFactor I (unabsorb I i (w + a)) ≠ 0
    rw [unitFactor_unabsorb I i hi]
    exact hw
  left_inv' z hz := by simpa only [sub_add_cancel] using unabsorb_absorb I i hi hz
  right_inv' w hw := by rw [absorb_unabsorb I i hi hw, add_sub_cancel_right]
  open_source := unitDomain_open I
  open_target := (unitDomain_open I).preimage (continuous_id.add continuous_const)
  continuousOn_toFun := ((absorb_holomorphic I i).sub contDiff_const).continuous.continuousOn
  continuousOn_invFun := (unabsorb_holomorphic I i).continuousOn.comp
    (continuous_id.add continuous_const).continuousOn (fun _ hw => hw)

theorem centeredChart_holomorphic (I : Finset (Fin 3)) (i : Fin 3) (hi : i ∈ I)
    (a : CoordinateSpace 3) :
    ContDiffOn ℂ ω (centeredChart I i hi a) (centeredChart I i hi a).source :=
  ((absorb_holomorphic I i).sub contDiff_const).contDiffOn

theorem centeredChart_symm_holomorphic (I : Finset (Fin 3)) (i : Fin 3) (hi : i ∈ I)
    (a : CoordinateSpace 3) :
    ContDiffOn ℂ ω (centeredChart I i hi a).symm (centeredChart I i hi a).target :=
  (unabsorb_holomorphic I i).comp (contDiff_id.add contDiff_const).contDiffOn (fun _ hw => hw)

theorem centeredChart_center (I : Finset (Fin 3)) (i : Fin 3) (hi : i ∈ I)
    (a : CoordinateSpace 3) (ha : a i = 0) : centeredChart I i hi a a = 0 := by
  change Function.update a i (unitFactor I a * a i) - a = 0
  have he : Function.update a i (unitFactor I a * a i) = a := by
    apply Function.update_eq_self_iff.mpr
    rw [ha, mul_zero]
  rw [he, sub_self]

theorem mem_centeredChart_source (I : Finset (Fin 3)) (i : Fin 3) (hi : i ∈ I)
    (a : CoordinateSpace 3) (ha : ∀ j ∉ I, a j ≠ 0) : a ∈ (centeredChart I i hi a).source := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  exact ha j (Finset.mem_compl.mp hj)

theorem prod_absorb (I : Finset (Fin 3)) (i : Fin 3) (hi : i ∈ I) (z : CoordinateSpace 3) :
    ∏ j ∈ I, absorb I i z j = ∏ j, z j := by
  rw [absorb, Finset.prod_update_of_mem hi, mul_assoc,
    ← Finset.prod_eq_mul_prod_sdiff_singleton_of_mem hi z]
  exact Finset.prod_compl_mul_prod I z

theorem centeredChart_product (I : Finset (Fin 3)) (i : Fin 3) (hi : i ∈ I)
    (a : CoordinateSpace 3) (ha : ∀ j ∈ I, a j = 0) (z : CoordinateSpace 3) :
    ∏ j ∈ I, centeredChart I i hi a z j = Triangle.time z := by
  have he : (∏ j ∈ I, centeredChart I i hi a z j) = ∏ j ∈ I, absorb I i z j := by
    apply Finset.prod_congr rfl
    intro j hj
    change absorb I i z j - a j = absorb I i z j
    rw [ha j hj, sub_zero]
  rw [he, prod_absorb I i hi]
  simp [Triangle.time, Fin.prod_univ_succ, mul_assoc]

theorem centeredChart_symm_product (I : Finset (Fin 3)) (i : Fin 3) (hi : i ∈ I)
    (a : CoordinateSpace 3) (ha : ∀ j ∈ I, a j = 0) {w : CoordinateSpace 3}
    (hw : w ∈ (centeredChart I i hi a).target) :
    Triangle.time ((centeredChart I i hi a).symm w) = ∏ j ∈ I, w j := by
  rw [← centeredChart_product I i hi a ha, (centeredChart I i hi a).right_inv hw]

end Wikipedia.HopfProblem.NormalCrossingCoordinates
