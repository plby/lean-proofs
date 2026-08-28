import Wikipedia.NoExoticSixSphere.JamesSpherePuncturedStage
import Wikipedia.NoExoticSixSphere.DoubleMappingCylinderHomologyRange
import Wikipedia.NoExoticSixSphere.NormedDiskHomology

/-!
# Homology of the original successive James-stage inclusions

Use the actual characteristic-disk pushout before taking any quotient.
Its sphere boundary has the checked homotopy-extension property and
homology vanishing away from its dimension. Mayer--Vietoris therefore
controls the original inclusion of the preceding James stage.
-/

noncomputable section

open CategoryTheory Set Topology
open Wikipedia.HopfProblem SingularMayerVietoris PeriodTorusHigherHomology OrbitPair

namespace NoExoticSixSphere.JamesSphere.StageAttachment

theorem diskBoundary_hasHomotopyExtension (n k : ℕ) :
    HomotopyExtension.HasHomotopyExtension
      (PuncturedCellAttachment.boundary (E := PuncturedStage.Coordinates n k)) :=
  NormedDiskHomology.sphere_hasHomotopyExtension (PuncturedStage.Coordinates n k)

theorem inclusion_homology_injective (n k : ℕ) (hn : 2 ≤ n) (d : ℕ)
    (hd : d ≠ 0) (hdm : d + 1 ≠ (k + 1) * n) :
    Function.Injective (singularHomologyMap (inclusion n k).hom d) := by
  have hm : 2 ≤ (k + 1) * n := by
    have he := Nat.mul_le_mul_right n (show 1 ≤ k + 1 by omega)
    omega
  let : Subsingleton (SingularHomology
      (Metric.sphere (0 : PuncturedStage.Coordinates n k) 1) d) :=
    NormedDiskHomology.finiteSphere_homology_subsingleton ((k + 1) * n) d hm hd hdm
  have hi := DoubleMappingCylinder.pushout_right_homology_injective
    PuncturedCellAttachment.boundary (PuncturedStage.attaching n k)
    (PuncturedStage.isPushout n k (by omega)).flip (diskBoundary_hasHomotopyExtension n k) d
  have he : (inclusion n k).hom =
      (lowerInclusion n k).hom.comp (lowerHomeomorph n k : C(_, _)) := rfl
  rw [he, singularHomologyMap_comp]
  exact hi.comp (homeomorphHomologyEquiv (lowerHomeomorph n k) d).injective

theorem inclusion_homology_surjective (n k : ℕ) (hn : 2 ≤ n) (d : ℕ)
    (hd : 2 ≤ d) (hdm : d ≠ (k + 1) * n) :
    Function.Surjective (singularHomologyMap (inclusion n k).hom d) := by
  have hm : 2 ≤ (k + 1) * n := by
    have he := Nat.mul_le_mul_right n (show 1 ≤ k + 1 by omega)
    omega
  cases d with
  | zero => omega
  | succ r =>
    let : Subsingleton (SingularHomology
        (Metric.sphere (0 : PuncturedStage.Coordinates n k) 1) r) :=
      NormedDiskHomology.finiteSphere_homology_subsingleton ((k + 1) * n) r hm (by omega) hdm
    let : Subsingleton (SingularHomology
        (PuncturedCellAttachment.Disk (PuncturedStage.Coordinates n k)) (r + 1)) :=
      NormedDiskHomology.disk_homology_subsingleton ((k + 1) * n) (r + 1) (by omega)
    have hs := DoubleMappingCylinder.pushout_right_homology_surjective
      PuncturedCellAttachment.boundary (PuncturedStage.attaching n k)
      (PuncturedStage.isPushout n k (by omega)).flip (diskBoundary_hasHomotopyExtension n k) r
    have he : (inclusion n k).hom =
        (lowerInclusion n k).hom.comp (lowerHomeomorph n k : C(_, _)) := rfl
    rw [he, singularHomologyMap_comp]
    exact hs.comp (homeomorphHomologyEquiv (lowerHomeomorph n k) (r + 1)).surjective

theorem inclusion_homology_bijective_range (n k : ℕ) (hn : 2 ≤ n) (hk : 2 ≤ k)
    (d : ℕ) (hd : 2 ≤ d) (hdn : d + 1 < 3 * n) :
    Function.Bijective (singularHomologyMap (inclusion n k).hom d) := by
  have hm := Nat.mul_le_mul_right n (show 3 ≤ k + 1 by omega)
  exact ⟨inclusion_homology_injective n k hn d (by omega) (by omega),
    inclusion_homology_surjective n k hn d hd (by omega)⟩

theorem inclusion_homology_surjective_range (n k : ℕ) (hn : 2 ≤ n) (hk : 2 ≤ k)
    (d : ℕ) (hd : 2 ≤ d) (hdn : d < 3 * n) :
    Function.Surjective (singularHomologyMap (inclusion n k).hom d) := by
  have hm := Nat.mul_le_mul_right n (show 3 ≤ k + 1 by omega)
  exact inclusion_homology_surjective n k hn d hd (by omega)

end NoExoticSixSphere.JamesSphere.StageAttachment
