import Wikipedia.SmoothSixDPoincare.FramedSurgeryBoundary
import Wikipedia.SmoothSixDPoincare.OpenSubtypePartialDiffeomorph

/-!
# Smoothness of the actual framed-surgery transition

Both original overlap embeddings are upgraded without changing their total
topological maps or inverses. Their composite is the very same transition
used to construct the compact Hausdorff boundary, with its native (possibly
different) source and target models.
-/

noncomputable section

open Set Function Topology Metric
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.FramedSurgery

open PuncturedHandle

variable {E F G H X : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H} [TopologicalSpace X] [T2Space X] [ChartedSpace H X]
  {m : ℕ} [Fact (Module.finrank ℝ E = m + 1)]
  (A : SmoothClosedFace (𝓡 m) J (UnitSphere E) F X)

def oldOverlapPartial [Nonempty (Overlap E F)] :
    PartialDiffeomorph ((𝓡 m).prod 𝓘(ℝ, F)) J (Overlap E F) (oldPatch A) ∞ := by
  let _ : Nonempty (openPuncturedDisk F) := Nonempty.map Prod.snd ‹Nonempty (Overlap E F)›
  let _ : Nonempty (oldPatch A) := Nonempty.map (oldOverlap A) ‹Nonempty (Overlap E F)›
  let R := PartialChart.prod (Diffeomorph.refl (𝓡 m) (UnitSphere E) ∞).toPartialDiffeomorph
    (PartialChart.openInclusion (I := 𝓘(ℝ, F)) (openPuncturedDisk F))
  let S := PartialChart.openInclusion (I := J) (oldPatch A)
  let P := (R.trans A.chart).trans S.symm
  have hR (z : Overlap E F) : z ∈ R.source := ⟨mem_univ _, mem_univ _⟩
  have hC (z : Overlap E F) : R z ∈ A.chart.source :=
    A.source ⟨mem_univ _, mem_closedBall_zero_iff.mpr z.2.property.2.le⟩
  have hpoint (z : Overlap E F) : A.chart (R z) = (oldOverlap A z).val :=
    A.point z.1 ⟨z.2.val, mem_closedBall_zero_iff.mpr z.2.property.2.le⟩
  have hU (z : Overlap E F) : A.chart (R z) ∈ oldPatch A := by
    rw [hpoint]
    exact (oldOverlap A z).property
  have hsource : P.source = univ := by
    apply eq_univ_of_forall
    intro z
    refine ⟨⟨hR z, hC z⟩, ?_⟩
    change A.chart (R z) ∈ S.target
    rw [PartialChart.openInclusion_target]
    exact hU z
  apply PartialChart.fromOpenEmbedding (oldOverlap_isOpenEmbedding A) P hsource
  intro z
  apply Subtype.ext
  change (S.symm (A.chart (R z))).val = (oldOverlap A z).val
  exact (PartialChart.openInclusion_symm_coe (I := J) (oldPatch A) (hU z)).trans (hpoint z)

theorem oldOverlapPartial_toOpenPartialHomeomorph [Nonempty (Overlap E F)] :
    (oldOverlapPartial A).toOpenPartialHomeomorph =
      (oldOverlap_isOpenEmbedding A).toOpenPartialHomeomorph := rfl

section NewPartial

variable (m n : ℕ) [Fact (Module.finrank ℝ E = m + 1)]
  [Fact (Module.finrank ℝ F = n + 1)] [Nonempty (Overlap E F)]

def newOverlapPartial : PartialDiffeomorph ((𝓡 m).prod 𝓘(ℝ, F))
    (𝓘(ℝ, E).prod (𝓡 n)) (Overlap E F) (NewPatch E F) ∞ := by
  let _ : Nonempty (openPuncturedDisk E) :=
    Nonempty.map (fun z => (openExchange m n z).1) ‹Nonempty (Overlap E F)›
  let _ : Nonempty (openUnitDisk E) := ⟨⟨0, by simp [openUnitDisk]⟩⟩
  let Q := PartialChart.openInclusion (I := 𝓘(ℝ, E)) (openPuncturedDisk E)
  let S := PartialChart.openInclusion (I := 𝓘(ℝ, E)) (openUnitDisk E)
  let R := PartialChart.prod (Q.trans S.symm)
    (Diffeomorph.refl (𝓡 n) (UnitSphere F) ∞).toPartialDiffeomorph
  let P := (openExchange m n).toPartialDiffeomorph.trans R
  have hU (z : Overlap E F) : (openExchange m n z).1.val ∈ openUnitDisk E :=
    mem_ball_zero_iff.mpr (openExchange m n z).1.property.2
  have hsource : P.source = univ := by
    apply eq_univ_of_forall
    intro z
    refine ⟨mem_univ _, ⟨mem_univ _, ?_⟩, mem_univ _⟩
    change (openExchange m n z).1.val ∈ S.target
    rw [PartialChart.openInclusion_target]
    exact hU z
  apply PartialChart.fromOpenEmbedding (newOverlap_isOpenEmbedding m n) P hsource
  intro z
  refine Prod.ext ?_ rfl
  apply Subtype.ext
  change (S.symm (openExchange m n z).1.val).val = (openExchange m n z).1.val
  exact PartialChart.openInclusion_symm_coe (I := 𝓘(ℝ, E)) (openUnitDisk E) (hU z)

omit [FiniteDimensional ℝ E] in
theorem newOverlapPartial_toOpenPartialHomeomorph :
    (newOverlapPartial (E := E) (F := F) m n).toOpenPartialHomeomorph =
      (newOverlap_isOpenEmbedding m n).toOpenPartialHomeomorph := rfl

end NewPartial

variable (n : ℕ) [Fact (Module.finrank ℝ F = n + 1)]

/-- The original topological transition with both native smoothness proofs. -/
def transitionPartial : PartialDiffeomorph J (𝓘(ℝ, E).prod (𝓡 n))
    (oldPatch A) (NewPatch E F) ∞ := by
  let _ := nonempty_overlap (E := E) (F := F) m n
  exact (oldOverlapPartial A).symm.trans (newOverlapPartial m n)

theorem transitionPartial_toOpenPartialHomeomorph :
    (transitionPartial A n).toOpenPartialHomeomorph = transition A n := rfl

end Wikipedia.SmoothSixDPoincare.FramedSurgery
