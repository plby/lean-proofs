import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicPiSeven
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicCyclicQuotient

/-!
# Projected degrees are multiples of one actual generator degree

The checked integral marking of `π₇(Sp(2))` reduces the image calculation
to the degree of its actual chosen generator. No numerical value or
nonvanishing of that integer is asserted here.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicFibration

open QuaternionicColumns

def generatorProjectionDegree : ℤ := (projectionDegree piSevenSpTwoGenerator).toAdd

theorem projectionDegree_generator :
    projectionDegree piSevenSpTwoGenerator = Multiplicative.ofAdd generatorProjectionDegree := rfl

theorem projectionDegree_eq_generator_zpow (a : π_ 7 SpTwo 1) :
    projectionDegree a =
      (Multiplicative.ofAdd generatorProjectionDegree) ^ (piSevenSpTwoMulEquiv a).toAdd := by
  calc
    projectionDegree a =
        projectionDegree (piSevenSpTwoGenerator ^ (piSevenSpTwoMulEquiv a).toAdd) :=
      congrArg projectionDegree (piSevenSpTwoGenerator_zpow_coordinates a).symm
    _ = _ := map_zpow projectionDegree _ _

theorem projectionDegree_toAdd (a : π_ 7 SpTwo 1) :
    (projectionDegree a).toAdd = (piSevenSpTwoMulEquiv a).toAdd * generatorProjectionDegree := by
  rw [projectionDegree_eq_generator_zpow]
  change (piSevenSpTwoMulEquiv a).toAdd • generatorProjectionDegree = _
  exact zsmul_eq_mul _ _

theorem projectionDegree_range_eq_zpowers_generator :
    projectionDegree.range = Subgroup.zpowers (Multiplicative.ofAdd generatorProjectionDegree) := by
  ext k
  constructor
  · rintro ⟨a, rfl⟩
    rw [projectionDegree_eq_generator_zpow]
    exact Subgroup.zpow_mem_zpowers _ _
  · intro hk
    obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    exact ⟨piSevenSpTwoGenerator ^ l, map_zpow projectionDegree _ _⟩

theorem projected_degree_iff_generator_dvd (k : ℤ) :
    (∃ a : π_ 7 SpTwo 1, projectionDegree a = Multiplicative.ofAdd k) ↔
      generatorProjectionDegree ∣ k := by
  constructor
  · rintro ⟨a, ha⟩
    have he := projectionDegree_toAdd a
    rw [ha] at he
    exact ⟨(piSevenSpTwoMulEquiv a).toAdd, he.trans (mul_comm _ _)⟩
  · rintro ⟨l, hl⟩
    refine ⟨piSevenSpTwoGenerator ^ l, ?_⟩
    rw [map_zpow, projectionDegree_generator]
    change Multiplicative.ofAdd (l • generatorProjectionDegree) = Multiplicative.ofAdd k
    rw [zsmul_eq_mul, hl, mul_comm]
    simp

theorem boundaryClass_relation_iff_generator_degree_dvd (k : ℤ) :
    boundaryClass ^ k = 1 ↔ generatorProjectionDegree ∣ k :=
  (boundaryClass_zpow_eq_one_iff k).trans (projected_degree_iff_generator_dvd k)

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicFibration
