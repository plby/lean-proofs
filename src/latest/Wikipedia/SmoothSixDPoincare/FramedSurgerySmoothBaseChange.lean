import Wikipedia.SmoothSixDPoincare.FramedSurgeryBaseChangeBoundary
import Wikipedia.SmoothSixDPoincare.FramedSurgerySmoothBoundary
import Wikipedia.SmoothSixDPoincare.PartialDiffeomorphPatchIdentity

/-!
# A native boundary diffeomorphism extends across a matching framed surgery

The resulting diffeomorphism has precisely the open-quotient homeomorphism
already constructed. Its new handle patch and whole closed positive face
retain every original coordinate, and both boundaries use their native
smooth surgery atlases.
-/

noncomputable section

open Set Function Topology Metric
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.FramedSurgery

open PuncturedHandle

variable {E F G H X X' : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H}
  [TopologicalSpace X] [T2Space X] [ChartedSpace H X]
  [TopologicalSpace X'] [T2Space X'] [ChartedSpace H X']
  {m : ℕ} [Fact (Module.finrank ℝ E = m + 1)]
  (A : SmoothClosedFace (𝓡 m) J (UnitSphere E) F X)
  (A' : SmoothClosedFace (𝓡 m) J (UnitSphere E) F X')
  (n : ℕ) [Fact (Module.finrank ℝ F = n + 1)]
  (D : Diffeomorph J J X X' ∞) (hD : ∀ z, D (A.map z) = A'.map z)
  (P : SmoothBoundaryData A n) (Q : SmoothBoundaryData A' n)

theorem baseChangeBoundary_contMDiff :
    letI := P.charted
    letI := Q.charted
    ContMDiff J J ∞ (baseChangeBoundary A A' n D.toHomeomorph hD) := by
  let _ := P.charted
  let _ := Q.charted
  let d := baseChangeOldDiffeomorph A A' D hD
  let h := baseChangeBoundary A A' n D.toHomeomorph hD
  have hold : ContMDiffOn J J ∞ h P.oldPartial.target := by
    apply PartialChart.contMDiffOn_of_patchIdentity h P.oldPartial
      (d.toPartialDiffeomorph.trans Q.oldPartial)
    · intro x _
      refine ⟨mem_univ _, ?_⟩
      change d x ∈ Q.oldPartial.source
      rw [Q.old_source]
      trivial
    · intro x _
      exact (congrArg h (P.old_point x)).trans
        ((baseChangeBoundary_old A A' n D.toHomeomorph hD x).trans (Q.old_point (d x)).symm)
  have hnew : ContMDiffOn J J ∞ h P.newPartial.target := by
    apply PartialChart.contMDiffOn_of_patchIdentity h P.newPartial Q.newPartial
    · rw [P.new_source, Q.new_source]
    · intro y _
      exact (congrArg h (P.new_point y)).trans
        ((baseChangeBoundary_new A A' n D.toHomeomorph hD y).trans (Q.new_point y).symm)
  intro z
  rcases cover A n z with ⟨x, rfl⟩ | ⟨y, rfl⟩
  · have hx := P.oldPartial.map_source (P.old_source.symm ▸ mem_univ x)
    rw [P.old_point x] at hx
    exact hold.contMDiffAt (P.oldPartial.open_target.mem_nhds hx)
  · have hy := P.newPartial.map_source (P.new_source.symm ▸ mem_univ y)
    rw [P.new_point y] at hy
    exact hnew.contMDiffAt (P.newPartial.open_target.mem_nhds hy)

theorem baseChangeBoundary_symm_contMDiff :
    letI := P.charted
    letI := Q.charted
    ContMDiff J J ∞ (baseChangeBoundary A A' n D.toHomeomorph hD).symm := by
  let _ := P.charted
  let _ := Q.charted
  exact baseChangeBoundary_contMDiff A' A n D.symm
    (baseChange_symm_face A A' D.toHomeomorph hD) Q P

def baseChangeDiffeomorph :
    letI := P.charted
    letI := Q.charted
    Diffeomorph J J (Boundary A n) (Boundary A' n) ∞ := by
  let _ := P.charted
  let _ := Q.charted
  exact {
    toEquiv := (baseChangeBoundary A A' n D.toHomeomorph hD).toEquiv
    contMDiff_toFun := baseChangeBoundary_contMDiff A A' n D hD P Q
    contMDiff_invFun := baseChangeBoundary_symm_contMDiff A A' n D hD P Q }

theorem baseChangeDiffeomorph_toHomeomorph :
    letI := P.charted
    letI := Q.charted
    (baseChangeDiffeomorph A A' n D hD P Q).toHomeomorph =
      baseChangeBoundary A A' n D.toHomeomorph hD := rfl

theorem baseChangeDiffeomorph_old (x : oldPatch A) :
    letI := P.charted
    letI := Q.charted
    baseChangeDiffeomorph A A' n D hD P Q (oldMap A n x) =
      oldMap A' n (baseChangeOldHomeomorph A A' D.toHomeomorph hD x) := rfl

theorem baseChangeDiffeomorph_new (y : NewPatch E F) :
    letI := P.charted
    letI := Q.charted
    baseChangeDiffeomorph A A' n D hD P Q (newMap A n y) = newMap A' n y := rfl

theorem baseChangeDiffeomorph_closedNewMap (p : ClosedNewFace E F) :
    letI := P.charted
    letI := Q.charted
    baseChangeDiffeomorph A A' n D hD P Q (closedNewMap A n p) = closedNewMap A' n p := by
  let _ := P.charted
  let _ := Q.charted
  exact baseChangeBoundary_closedNewMap A A' n D.toHomeomorph hD p

end Wikipedia.SmoothSixDPoincare.FramedSurgery
