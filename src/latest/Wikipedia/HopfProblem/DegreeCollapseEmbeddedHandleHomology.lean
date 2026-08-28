import Wikipedia.HopfProblem.DegreeCollapseEmbeddedHandleCell
import Wikipedia.SmoothSixDPoincare.CellAttachmentHomologySequence
import Wikipedia.SmoothSixDPoincare.LinearExactTransport

/-!
# The homology sequence of an actual embedded whole handle

Transport the genuine cell-attachment sequence through the explicit core
deformation. Its maps on the old space and attaching sphere are exactly
the supplied continuous maps, with all three exactness statements proved.
-/

noncomputable section

open Set Function Topology Metric ContinuousMap

namespace Wikipedia.HopfProblem.DegreeCollapse.EmbeddedHandle

open Wikipedia.SmoothSixDPoincare PuncturedHandle MorseHandle
open SingularMayerVietoris PeriodTorusHigherHomology

variable {N P R X : Type}
  [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [TopologicalSpace R] [TopologicalSpace X] [T2Space X]
  (D : EmbeddedHandle N P R X)

def oldHomologyEquiv (n : ℕ) :
    SingularHomology R n ≃ₗ[ℤ] SingularHomology D.corePresentation.old n :=
  homotopyEquivHomologyEquiv D.oldHomeomorph.toHomotopyEquiv n

def coreHomologyEquiv (n : ℕ) :
    SingularHomology ↥(range D.oldMap ∪ range D.core) n ≃ₗ[ℤ] SingularHomology X n :=
  homotopyEquivHomologyEquiv D.coreHomotopyEquiv n

theorem attaching_compare (n : ℕ) (u : SingularHomology (UnitSphere N) n) :
    D.corePresentation.attachingHomologyMap n u =
      D.oldHomologyEquiv n (singularHomologyMap D.attaching n u) := by
  change singularHomologyMap D.corePresentation.attachingSphere n u = _
  rw [D.presentation_attaching, singularHomologyMap_comp, LinearMap.comp_apply]
  rfl

theorem old_compare (n : ℕ) (u : SingularHomology R n) :
    D.coreHomologyEquiv n (D.corePresentation.oldHomologyMap n (D.oldHomologyEquiv n u)) =
      singularHomologyMap D.oldMap n u := by
  have hmaps : (D.coreHomotopyEquiv.toFun.comp (subtypeInclusion D.corePresentation.old)).comp
      D.oldHomeomorph.toHomotopyEquiv.toFun = D.oldMap := by
    apply ContinuousMap.ext
    intro x
    rfl
  change singularHomologyMap D.coreHomotopyEquiv.toFun n
    (singularHomologyMap (subtypeInclusion D.corePresentation.old) n
      (singularHomologyMap D.oldHomeomorph.toHomotopyEquiv.toFun n u)) = _
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp,
    ← LinearMap.comp_apply, ← singularHomologyMap_comp, hmaps]

theorem exact_at_old (n : ℕ) (hn : n ≠ 0) :
    LinearMap.range (singularHomologyMap D.attaching n) =
      LinearMap.ker (singularHomologyMap D.oldMap n) := by
  refine HomologyTransport.exact_of_equivalences (LinearEquiv.refl ℤ _)
    (D.oldHomologyEquiv n).symm (D.coreHomologyEquiv n)
    (D.corePresentation.attachingHomologyMap n) (D.corePresentation.oldHomologyMap n)
    (singularHomologyMap D.attaching n) (singularHomologyMap D.oldMap n) ?_ ?_
    (D.corePresentation.cell_exact_at_old n hn)
  · intro u
    change singularHomologyMap D.attaching n u =
      (D.oldHomologyEquiv n).symm (D.corePresentation.attachingHomologyMap n u)
    rw [D.attaching_compare, LinearEquiv.symm_apply_apply]
  · intro u
    have h := D.old_compare n ((D.oldHomologyEquiv n).symm u)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm

def connecting (k : ℕ) : SingularHomology X (k + 1) →ₗ[ℤ]
    SingularHomology (UnitSphere N) k :=
  (D.corePresentation.cellConnectingMap k).comp (D.coreHomologyEquiv (k + 1)).symm.toLinearMap

theorem connecting_compare (k : ℕ)
    (u : SingularHomology ↥(range D.oldMap ∪ range D.core) (k + 1)) :
    D.connecting k (D.coreHomologyEquiv (k + 1) u) = D.corePresentation.cellConnectingMap k u := by
  change D.corePresentation.cellConnectingMap k
    ((D.coreHomologyEquiv (k + 1)).symm (D.coreHomologyEquiv (k + 1) u)) = _
  rw [LinearEquiv.symm_apply_apply]

theorem exact_at_ambient (k : ℕ) :
    LinearMap.range (singularHomologyMap D.oldMap (k + 1)) = LinearMap.ker (D.connecting k) := by
  refine HomologyTransport.exact_of_equivalences
    (D.oldHomologyEquiv (k + 1)).symm (D.coreHomologyEquiv (k + 1)) (LinearEquiv.refl ℤ _)
    (D.corePresentation.oldHomologyMap (k + 1)) (D.corePresentation.cellConnectingMap k)
    (singularHomologyMap D.oldMap (k + 1)) (D.connecting k) ?_ ?_
    (D.corePresentation.cell_exact_at_ambient k)
  · intro u
    have h := D.old_compare (k + 1) ((D.oldHomologyEquiv (k + 1)).symm u)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm
  · exact D.connecting_compare k

theorem exact_at_sphere (k : ℕ) (hk : k ≠ 0) :
    LinearMap.range (D.connecting k) = LinearMap.ker (singularHomologyMap D.attaching k) := by
  refine HomologyTransport.exact_of_equivalences (D.coreHomologyEquiv (k + 1))
    (LinearEquiv.refl ℤ _) (D.oldHomologyEquiv k).symm
    (D.corePresentation.cellConnectingMap k) (D.corePresentation.attachingHomologyMap k)
    (D.connecting k) (singularHomologyMap D.attaching k) ?_ ?_
    (D.corePresentation.cell_exact_at_sphere k hk)
  · exact D.connecting_compare k
  · intro u
    change singularHomologyMap D.attaching k u =
      (D.oldHomologyEquiv k).symm (D.corePresentation.attachingHomologyMap k u)
    rw [D.attaching_compare, LinearEquiv.symm_apply_apply]

theorem old_surjective (k : ℕ) [Subsingleton (SingularHomology (UnitSphere N) k)] :
    Surjective (singularHomologyMap D.oldMap (k + 1)) := by
  intro x
  have hx : x ∈ LinearMap.ker (D.connecting k) := Subsingleton.elim _ _
  rw [← D.exact_at_ambient k] at hx
  exact hx

theorem old_injective (k : ℕ) (hk : k ≠ 0)
    [Subsingleton (SingularHomology (UnitSphere N) k)] :
    Injective (singularHomologyMap D.oldMap k) := by
  apply LinearMap.ker_eq_bot.mp
  rw [← D.exact_at_old k hk]
  apply le_antisymm _ bot_le
  rintro x ⟨s, rfl⟩
  change singularHomologyMap D.attaching k s = 0
  rw [Subsingleton.elim s 0, map_zero]

end Wikipedia.HopfProblem.DegreeCollapse.EmbeddedHandle
