import Wikipedia.HomotopyGroupsOfSpheres.CliffordBoundarySpinorSurjectivity
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicCandidateDegree
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicGeneratorDegree
import Mathlib.Data.ZMod.Basic

/-! # The actual projected-degree image is exactly twelve times the integers -/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicFibration

open ComplexCrossProductUnitary

theorem projected_degree_iff_candidate_dvd (k : ℤ) :
    (∃ a : π_ 7 SpTwo 1, projectionDegree a = Multiplicative.ofAdd k) ↔
      (projectionDegree sphereCandidateClass).toAdd ∣ k := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨m, rfl⟩ := CliffordBoundaryBott.sphereCandidate_generates a
    rw [map_zpow] at ha
    have hm := congrArg Multiplicative.toAdd ha
    change m • (projectionDegree sphereCandidateClass).toAdd = k at hm
    rw [Int.zsmul_eq_mul] at hm
    exact ⟨m, hm.symm.trans (mul_comm _ _)⟩
  · rintro ⟨m, hm⟩
    refine ⟨sphereCandidateClass ^ m, ?_⟩
    rw [map_zpow]
    change Multiplicative.ofAdd (m • (projectionDegree sphereCandidateClass).toAdd) =
      Multiplicative.ofAdd k
    rw [Int.zsmul_eq_mul, mul_comm, ← hm]

theorem projected_degree_iff_twelve_dvd (k : ℤ) :
    (∃ a : π_ 7 SpTwo 1, projectionDegree a = Multiplicative.ofAdd k) ↔ (12 : ℤ) ∣ k := by
  rw [projected_degree_iff_candidate_dvd, ← Int.natAbs_dvd,
    sphereCandidateClass_projectionDegree_natAbs]
  norm_num

theorem generatorProjectionDegree_natAbs : generatorProjectionDegree.natAbs = 12 := by
  have h₁ : (12 : ℤ) ∣ generatorProjectionDegree :=
    (projected_degree_iff_twelve_dvd generatorProjectionDegree).mp
      ⟨QuaternionicColumns.piSevenSpTwoGenerator, projectionDegree_generator⟩
  have h₂ : generatorProjectionDegree ∣ (12 : ℤ) :=
    (projected_degree_iff_generator_dvd 12).mp
      ((projected_degree_iff_twelve_dvd 12).mpr (dvd_refl 12))
  exact Int.natAbs_eq_of_dvd_dvd h₂ h₁

def degreeResidueHom : Multiplicative ℤ →* Multiplicative (ZMod 12) :=
  (Int.castAddHom (ZMod 12)).toMultiplicative

theorem degreeResidueHom_surjective : Function.Surjective degreeResidueHom := by
  intro a
  obtain ⟨k, hk⟩ := ZMod.intCast_surjective a.toAdd
  exact ⟨Multiplicative.ofAdd k, congrArg Multiplicative.ofAdd hk⟩

theorem projectionDegree_range_eq_residue_ker : projectionDegree.range = degreeResidueHom.ker := by
  ext k
  change (∃ a : π_ 7 SpTwo 1, projectionDegree a = Multiplicative.ofAdd k.toAdd) ↔
    degreeResidueHom k = 1
  rw [projected_degree_iff_twelve_dvd]
  change (12 : ℤ) ∣ k.toAdd ↔ (k.toAdd : ZMod 12) = 0
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd k.toAdd 12).symm

def degreeQuotientTwelveMulEquiv :
    (Multiplicative ℤ ⧸ projectionDegree.range) ≃* Multiplicative (ZMod 12) :=
  (QuotientGroup.quotientMulEquivOfEq projectionDegree_range_eq_residue_ker).trans
    (QuotientGroup.quotientKerEquivOfSurjective degreeResidueHom degreeResidueHom_surjective)

def piSixBaseMulEquiv :
    π_ 6 (Sphere 3) (fiberSphereHomeomorph 1) ≃* Multiplicative (ZMod 12) :=
  sphereDegreeQuotientMulEquiv.symm.trans degreeQuotientTwelveMulEquiv

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicFibration
