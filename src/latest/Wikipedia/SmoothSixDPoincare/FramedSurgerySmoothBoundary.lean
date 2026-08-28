import Wikipedia.SmoothSixDPoincare.FramedSurgeryModelChart
import Wikipedia.SmoothSixDPoincare.BoundarylessModelChange
import Wikipedia.SmoothSixDPoincare.OpenGluingPatchDiffeomorph
import Wikipedia.SmoothSixDPoincare.FramedSurgeryCompact

/-!
# A native smooth atlas on the actual compact surgery boundary

The common model is constructed from the original face-chart differential.
Both old and new patches retain their native smooth structures through
full-source partial diffeomorphisms with the exact original quotient maps.
The boundary topology is the already proved compact Hausdorff quotient.
-/

noncomputable section

open Set Function Topology Metric
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.FramedSurgery

open PuncturedHandle

variable {E F G H X : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless]
  [TopologicalSpace X] [T2Space X] [ChartedSpace H X] [IsManifold J ∞ X]
  {m : ℕ} [Fact (Module.finrank ℝ E = m + 1)]
  (A : SmoothClosedFace (𝓡 m) J (UnitSphere E) F X)
  (n : ℕ) [Fact (Module.finrank ℝ F = n + 1)]

structure SmoothBoundaryData where
  charted : ChartedSpace H (Boundary A n)
  smooth : letI := charted; IsManifold J ∞ (Boundary A n)
  oldPartial : letI := charted; PartialDiffeomorph J J (oldPatch A) (Boundary A n) ∞
  newPartial : letI := charted;
    PartialDiffeomorph (𝓘(ℝ, E).prod (𝓡 n)) J (NewPatch E F) (Boundary A n) ∞
  old_source : letI := charted; oldPartial.source = univ
  new_source : letI := charted; newPartial.source = univ
  old_point : letI := charted; ∀ x, oldPartial x = oldMap A n x
  new_point : letI := charted; ∀ y, newPartial y = newMap A n y

/-- Construct the smooth atlas and both exact native patch parametrizations. -/
theorem nonempty_smoothBoundaryData : Nonempty (SmoothBoundaryData A n) := by
  let _ : Nonempty H := ⟨J.symm 0⟩
  let _ := nonempty_overlap (E := E) (F := F) m n
  let _ : Nonempty (oldPatch A) := Nonempty.map (oldOverlap A) ‹Nonempty (Overlap E F)›
  let _ : Nonempty (NewPatch E F) := Nonempty.map (newOverlap m n) ‹Nonempty (Overlap E F)›
  let P := transitionPartial A n
  obtain ⟨Φ, hΦ, -⟩ := exists_modelChart A n
  let _ := BoundarylessModelChange.chartedSpace
    (I := 𝓘(ℝ, E).prod (𝓡 n)) (M := NewPatch E F) Φ hΦ
  let _ := BoundarylessModelChange.isManifold
    (I := 𝓘(ℝ, E).prod (𝓡 n)) (M := NewPatch E F) Φ hΦ
  let D := BoundarylessModelChange.diffeomorph
    (I := 𝓘(ℝ, E).prod (𝓡 n)) (M := NewPatch E F) Φ hΦ
  let e : PartialDiffeomorph J J (oldPatch A) (NewPatch E F) ∞ := {
    toPartialEquiv := (transition A n).toPartialEquiv
    open_source := (transition A n).open_source
    open_target := (transition A n).open_target
    contMDiffOn_toFun := by
      exact (D.symm.contMDiff.comp_contMDiffOn P.contMDiffOn).congr (fun _ _ => rfl)
    contMDiffOn_invFun := by
      exact (P.symm.contMDiffOn.comp D.contMDiff.contMDiffOn
        (fun _ hx => hx)).congr (fun _ _ => rfl) }
  let c := OpenGluing.chartedSpace (H := H) e.toOpenPartialHomeomorph
  let _ := c
  let _ := OpenGluing.isManifold e
  let L := OpenGluing.leftPartialDiffeomorph e
  let R := D.symm.toPartialDiffeomorph.trans (OpenGluing.rightPartialDiffeomorph e)
  refine ⟨{
    charted := c
    smooth := OpenGluing.isManifold e
    oldPartial := L
    newPartial := R
    old_source := rfl
    new_source := ?_
    old_point := fun _ => rfl
    new_point := fun _ => rfl }⟩
  exact eq_univ_of_forall fun _ => ⟨mem_univ _, mem_univ _⟩

end Wikipedia.SmoothSixDPoincare.FramedSurgery
