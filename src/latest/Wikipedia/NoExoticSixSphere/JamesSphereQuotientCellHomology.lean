import Wikipedia.NoExoticSixSphere.JamesSphereQuotientCellAttachment
import Wikipedia.NoExoticSixSphere.DoubleMappingCylinderHomologyRange

/-!
# Homology of the actual later James-quotient inclusions

The characteristic disk is attached along its genuine boundary. The
checked boundary homology and pushout comparison give injectivity off
the boundary dimension and surjectivity off the disk dimension, retaining
the original finite-stage transition map.
-/

noncomputable section

open CategoryTheory Set Topology
open Wikipedia.HopfProblem SingularMayerVietoris PeriodTorusHigherHomology

namespace NoExoticSixSphere.JamesSphere.FirstStageQuotient.CellAttachment

theorem boundary_homology_subsingleton (n k : ℕ) (hn : 0 < n) (d : ℕ)
    (hd : d ≠ 0) (hdm : d + 1 ≠ (k + 3) * n) :
    Subsingleton (SingularHomology (presentationMorphism n k ⁻¹' lower n k) d) := by
  change Subsingleton (SingularHomology (presentation n k ⁻¹' lower n k) d)
  rw [boundary_eq]
  have hm : 2 ≤ (k + 3) * n := by
    have h := Nat.mul_le_mul_right n (show 3 ≤ k + 3 by omega)
    omega
  exact NormedDiskHomology.boundary_homology_subsingleton ((k + 3) * n) d hm hd hdm

theorem transition_homology_injective (n k : ℕ) (hn : 0 < n) (d : ℕ)
    (hd : d ≠ 0) (hdm : d + 1 ≠ (k + 3) * n) :
    Function.Injective
      (singularHomologyMap (FiniteStage.transition n (Nat.le_succ (k + 1))) d) := by
  let : Subsingleton (SingularHomology (presentationMorphism n k ⁻¹' lower n k) d) :=
    boundary_homology_subsingleton n k hn d hd hdm
  have hi := DoubleMappingCylinder.pushout_right_homology_injective
    (QuotientAttachment.boundaryInclusion (presentationMorphism n k) (lower n k))
    (QuotientAttachment.boundaryMap (presentationMorphism n k) (lower n k))
    (isPushout n k hn) (boundary_hasHomotopyExtension n k) d
  rw [← transition_factor, singularHomologyMap_comp]
  exact hi.comp (homeomorphHomologyEquiv (lowerHomeomorph n k) d).injective

theorem transition_homology_surjective (n k : ℕ) (hn : 0 < n) (d : ℕ)
    (hd : 2 ≤ d) (hdm : d ≠ (k + 3) * n) :
    Function.Surjective
      (singularHomologyMap (FiniteStage.transition n (Nat.le_succ (k + 1))) d) := by
  cases d with
  | zero => omega
  | succ r =>
    let : Subsingleton (SingularHomology (presentationMorphism n k ⁻¹' lower n k) r) :=
      boundary_homology_subsingleton n k hn r (by omega) hdm
    let : Subsingleton
        (SingularHomology (NormedDiskHomology.Disk (Fin ((k + 3) * n) → ℝ)) (r + 1)) :=
      NormedDiskHomology.disk_homology_subsingleton ((k + 3) * n) (r + 1) (by omega)
    have hs := DoubleMappingCylinder.pushout_right_homology_surjective
      (QuotientAttachment.boundaryInclusion (presentationMorphism n k) (lower n k))
      (QuotientAttachment.boundaryMap (presentationMorphism n k) (lower n k))
      (isPushout n k hn) (boundary_hasHomotopyExtension n k) r
    rw [← transition_factor, singularHomologyMap_comp]
    exact hs.comp (homeomorphHomologyEquiv (lowerHomeomorph n k) (r + 1)).surjective

theorem transition_homology_bijective_range (n k : ℕ) (hn : 0 < n) (d : ℕ)
    (hd : 2 ≤ d) (hdm : d + 1 < 3 * n) :
    Function.Bijective
      (singularHomologyMap (FiniteStage.transition n (Nat.le_succ (k + 1))) d) := by
  have hm := Nat.mul_le_mul_right n (show 3 ≤ k + 3 by omega)
  exact ⟨transition_homology_injective n k hn d (by omega) (by omega),
    transition_homology_surjective n k hn d hd (by omega)⟩

theorem transition_homology_surjective_range (n k : ℕ) (hn : 0 < n) (d : ℕ)
    (hd : 2 ≤ d) (hdm : d < 3 * n) :
    Function.Surjective
      (singularHomologyMap (FiniteStage.transition n (Nat.le_succ (k + 1))) d) := by
  have hm := Nat.mul_le_mul_right n (show 3 ≤ k + 3 by omega)
  exact transition_homology_surjective n k hn d hd (by omega)

end NoExoticSixSphere.JamesSphere.FirstStageQuotient.CellAttachment
