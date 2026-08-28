import Wikipedia.SmoothSixDPoincare.FramedSurgerySmoothBoundary
import Wikipedia.SmoothSixDPoincare.SmoothClosedFaceOpenEmbedding

/-!
# Retain the original attaching neighborhoods through the smooth surgery boundary

A full framed chart avoiding the removed attaching core retains its exact
original point map in the new boundary. If its whole target avoids the old
attaching face, its retained target avoids the entire new patch as well.
-/

noncomputable section

open Set Function Topology Metric
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.FramedSurgery.SmoothBoundaryData

open PuncturedHandle

variable {E F G H X : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H} [TopologicalSpace X] [T2Space X] [ChartedSpace H X]
  {m : ℕ} [Fact (Module.finrank ℝ E = m + 1)]
  {A : SmoothClosedFace (𝓡 m) J (UnitSphere E) F X}
  {n : ℕ} [Fact (Module.finrank ℝ F = n + 1)] (P : SmoothBoundaryData A n)
  {D K B N : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [TopologicalSpace K]
  {I : ModelWithCorners ℝ D K} [TopologicalSpace B] [ChartedSpace K B]
  [NormedAddCommGroup N] [NormedSpace ℝ N]
  [CompactSpace (B × MorseHandle.UnitDisk N)]

def retainFace (C : SmoothClosedFace I J B N X) (hC : C.chart.target ⊆ oldPatch A) :
    letI := P.charted; SmoothClosedFace I J B N (Boundary A n) := by
  let _ := P.charted
  let _ : Nonempty (oldPatch A) :=
    Nonempty.map (oldOverlap A) (nonempty_overlap (E := E) (F := F) m n)
  exact (C.restrictToOpen (oldPatch A) hC).postcomposeOpen P.oldPartial P.old_source

theorem retainFace_map (C : SmoothClosedFace I J B N X) (hC : C.chart.target ⊆ oldPatch A)
    (z : B × MorseHandle.UnitDisk N) (x : oldPatch A) (hx : x.val = C.map z) :
    letI := P.charted; (P.retainFace C hC).map z = oldMap A n x := by
  let _ := P.charted
  let _ : Nonempty (oldPatch A) :=
    Nonempty.map (oldOverlap A) (nonempty_overlap (E := E) (F := F) m n)
  change P.oldPartial ((C.restrictToOpen (oldPatch A) hC).map z) = oldMap A n x
  rw [P.old_point]
  apply congrArg (oldMap A n)
  exact Subtype.ext hx.symm

theorem retainFace_chart_target (C : SmoothClosedFace I J B N X)
    (hC : C.chart.target ⊆ oldPatch A) :
    letI := P.charted
    (P.retainFace C hC).chart.target = oldMap A n '' {x : oldPatch A | x.val ∈ C.chart.target} := by
  let _ := P.charted
  let _ : Nonempty (oldPatch A) :=
    Nonempty.map (oldOverlap A) (nonempty_overlap (E := E) (F := F) m n)
  have h₁ := (C.restrictToOpen (oldPatch A) hC).postcomposeOpen_chart_target
    P.oldPartial P.old_source
  have h₂ := C.restrictToOpen_chart_target (oldPatch A) hC
  calc
    (P.retainFace C hC).chart.target =
        P.oldPartial '' (C.restrictToOpen (oldPatch A) hC).chart.target := h₁
    _ = P.oldPartial '' {x : oldPatch A | x.val ∈ C.chart.target} := congrArg _ h₂
    _ = oldMap A n '' {x : oldPatch A | x.val ∈ C.chart.target} := by
      exact congrArg (fun f : oldPatch A → Boundary A n =>
        f '' {x : oldPatch A | x.val ∈ C.chart.target}) (funext P.old_point)

theorem retainFace_chart_avoids_new (C : SmoothClosedFace I J B N X)
    (hC : C.chart.target ⊆ oldPatch A) (havoid : Disjoint C.chart.target (range A.map)) :
    letI := P.charted
    Disjoint (P.retainFace C hC).chart.target (range (newMap A n)) := by
  let _ := P.charted
  rw [P.retainFace_chart_target, disjoint_left]
  rintro q ⟨x, hx, rfl⟩ ⟨y, hy⟩
  obtain ⟨z, hz, -⟩ := (old_eq_new_iff A n x y).mp hy.symm
  apply disjoint_left.mp havoid hx
  exact ⟨(z.1, ⟨z.2.val, mem_closedBall_zero_iff.mpr z.2.property.2.le⟩),
    congrArg Subtype.val hz⟩

end Wikipedia.SmoothSixDPoincare.FramedSurgery.SmoothBoundaryData
