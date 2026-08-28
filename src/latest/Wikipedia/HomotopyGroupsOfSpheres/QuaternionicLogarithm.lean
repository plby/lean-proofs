import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicExponentialCoordinates

/-! # A genuine smooth local logarithm on the quaternionic operator group -/

noncomputable section

open scoped Manifold ContDiff
open Set

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns

namespace CayleyAtlas

variable {n : ℕ}

theorem atOperator_target (a : symplecticSubgroup n) : (atOperator a).target = univ := by
  ext K
  change (K ∈ univ ∧ symplecticCayley n K ∈ univ) ↔ K ∈ univ
  simp only [mem_univ, and_self]

def partialChart (a : symplecticSubgroup n) :
    PartialDiffeomorph 𝓘(ℝ, SkewSpace n) 𝓘(ℝ, SkewSpace n)
      (symplecticSubgroup n) (SkewSpace n) ∞ where
  toPartialEquiv := (atOperator a).toPartialEquiv
  open_source := (atOperator a).open_source
  open_target := (atOperator a).open_target
  contMDiffOn_toFun := contMDiffOn_chart
  contMDiffOn_invFun := contMDiffOn_chart_symm

theorem partialChart_one_apply (a : symplecticSubgroup n) :
    partialChart (1 : symplecticSubgroup n) a = cayleyChart n a := by
  change cayleyCoordinates n ((1 : symplecticSubgroup n)⁻¹ * a) = cayleyCoordinates n a
  rw [inv_one, one_mul]

end CayleyAtlas

namespace Exponential

open CayleyAtlas

variable {n : ℕ}

/-- Local invertibility is proved in the original symplectic atlas. -/
theorem isLocalDiffeomorphAt_exp_zero :
    IsLocalDiffeomorphAt 𝓘(ℝ, SkewSpace n) 𝓘(ℝ, SkewSpace n) ∞ (exp (n := n)) 0 := by
  obtain ⟨d, hd0, hdU, hdf⟩ := exists_coordinatePartialDiffeomorph (n := n)
  let c := partialChart (1 : symplecticSubgroup n)
  refine ⟨d.trans c.symm, ?_, ?_⟩
  · refine ⟨hd0, ?_⟩
    change d 0 ∈ (atOperator (1 : symplecticSubgroup n)).target
    rw [atOperator_target]
    exact mem_univ _
  · intro K hK
    have hKU := hdU hK.1
    have hce : c (exp K) = d K := by
      rw [hdf]
      exact (partialChart_one_apply (exp K)).trans (inCoordinates_eq_chart K hKU).symm
    have hsource : exp K ∈ c.source := by
      change exp K ∈ (atOperator (1 : symplecticSubgroup n)).source
      rw [atOperator_source]
      change (1 : symplecticSubgroup n)⁻¹ * exp K ∈ cayleyDomain n
      rw [inv_one, one_mul]
      exact hKU
    change exp K = c.symm (d K)
    rw [← hce]
    exact (c.left_inv' hsource).symm

/-- A smooth logarithm only on its proved open neighborhood of the identity. -/
def logarithmChart (n : ℕ) :
    PartialDiffeomorph 𝓘(ℝ, SkewSpace n) 𝓘(ℝ, SkewSpace n)
      (symplecticSubgroup n) (SkewSpace n) ∞ :=
  (isLocalDiffeomorphAt_exp_zero (n := n)).localInverse

theorem one_mem_logarithmChart_source (n : ℕ) : 1 ∈ (logarithmChart n).source := by
  have h : exp (0 : SkewSpace n) ∈ (logarithmChart n).source :=
    (isLocalDiffeomorphAt_exp_zero (n := n)).localInverse_mem_source
  rwa [exp_zero] at h

theorem zero_mem_logarithmChart_target (n : ℕ) : 0 ∈ (logarithmChart n).target :=
  (isLocalDiffeomorphAt_exp_zero (n := n)).localInverse_mem_target

theorem exp_logarithmChart (a : symplecticSubgroup n) (ha : a ∈ (logarithmChart n).source) :
    exp (logarithmChart n a) = a :=
  (isLocalDiffeomorphAt_exp_zero (n := n)).localInverse_right_inv ha

theorem logarithmChart_exp (K : SkewSpace n) (hK : K ∈ (logarithmChart n).target) :
    logarithmChart n (exp K) = K :=
  (isLocalDiffeomorphAt_exp_zero (n := n)).localInverse_left_inv hK

theorem logarithmChart_one (n : ℕ) : logarithmChart n 1 = 0 := by
  simpa only [exp_zero] using logarithmChart_exp (0 : SkewSpace n)
    (zero_mem_logarithmChart_target n)

end Exponential

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns
