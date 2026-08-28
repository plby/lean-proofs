import Wikipedia.HopfProblem.HolomorphicAutomorphismCompactAtlasExistence
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Finite nested domains in the original complex atlas

Compactness supplies finitely many preferred charts whose inner coordinate
balls cover the manifold. Each has an outer ball and a larger closed ball
still inside the original chart target. In finite-dimensional complex
models, the inverse-chart images of the outer closed balls are compact.
-/

open Set Topology TopologicalSpace

namespace Wikipedia.HopfProblem.HolomorphicAutomorphism

/-- Finite native chart centers and radii, with an actual inner covering
and threefold coordinate margin in each unchanged preferred chart. -/
structure CompactAtlas (E M : Type*) [NormedAddCommGroup E] [TopologicalSpace M]
    [ChartedSpace E M] where
  centers : Finset M
  radius : M → ℝ
  positive : ∀ x ∈ centers, 0 < radius x
  large_ball_subset : ∀ x ∈ centers,
    Metric.closedBall (chartAt E x x) (3 * radius x) ⊆ (chartAt E x).target
  covering : ∀ y : M, ∃ x ∈ centers,
    y ∈ (chartAt E x).source ∧ chartAt E x y ∈ Metric.ball (chartAt E x x) (radius x)

theorem compactAtlas_nonempty (E M : Type*) [NormedAddCommGroup E] [TopologicalSpace M]
    [ChartedSpace E M] [CompactSpace M] : Nonempty (CompactAtlas E M) := by
  obtain ⟨r, hr, s, hs⟩ := exists_native_chart_radii_finite_cover E M
  exact ⟨⟨s, r, fun x _ => (hr x).1, fun x _ => (hr x).2, hs⟩⟩

/-- A finite nested cover constructed from the original preferred charts. -/
noncomputable def compactAtlas (E M : Type*) [NormedAddCommGroup E] [TopologicalSpace M]
    [ChartedSpace E M] [CompactSpace M] : CompactAtlas E M :=
  Classical.choice (compactAtlas_nonempty E M)

namespace CompactAtlas

variable {E M : Type*} [NormedAddCommGroup E] [TopologicalSpace M] [ChartedSpace E M]
  (A : CompactAtlas E M)

/-- The finite index type consists of the chosen actual chart centers. -/
abbrev Index : Type _ := {x : M // x ∈ A.centers}

instance : Fintype A.Index := inferInstanceAs (Fintype ↥A.centers)

def center (i : A.Index) : M := i.val

/-- This is the original preferred chart, not a replacement atlas. -/
def chart (i : A.Index) : OpenPartialHomeomorph M E := chartAt E (A.center i)

def centerCoord (i : A.Index) : E := A.chart i (A.center i)

theorem radius_pos (i : A.Index) : 0 < A.radius (A.center i) := A.positive i.val i.property

theorem closedBall_three_subset_target (i : A.Index) :
    Metric.closedBall (A.centerCoord i) (3 * A.radius (A.center i)) ⊆ (A.chart i).target :=
  A.large_ball_subset i.val i.property

theorem closedBall_two_subset_target (i : A.Index) :
    Metric.closedBall (A.centerCoord i) (2 * A.radius (A.center i)) ⊆ (A.chart i).target :=
  (Metric.closedBall_subset_closedBall (by linarith [A.radius_pos i])).trans
    (A.closedBall_three_subset_target i)

def innerCoordinates (i : A.Index) : Opens E :=
  ⟨Metric.ball (A.centerCoord i) (A.radius (A.center i)), Metric.isOpen_ball⟩

def outerCoordinates (i : A.Index) : Opens E :=
  ⟨Metric.ball (A.centerCoord i) (2 * A.radius (A.center i)), Metric.isOpen_ball⟩

theorem innerCoordinates_subset_target (i : A.Index) :
    (A.innerCoordinates i : Set E) ⊆ (A.chart i).target :=
  (Metric.ball_subset_closedBall.trans
    (Metric.closedBall_subset_closedBall (by linarith [A.radius_pos i]))).trans
      (A.closedBall_three_subset_target i)

theorem outerCoordinates_subset_target (i : A.Index) :
    (A.outerCoordinates i : Set E) ⊆ (A.chart i).target :=
  Metric.ball_subset_closedBall.trans (A.closedBall_two_subset_target i)

def innerOpen (i : A.Index) : Opens M :=
  ⟨(A.chart i).source ∩ (A.chart i) ⁻¹' (A.innerCoordinates i : Set E),
    (A.chart i).isOpen_inter_preimage (A.innerCoordinates i).isOpen⟩

def outerOpen (i : A.Index) : Opens M :=
  ⟨(A.chart i).source ∩ (A.chart i) ⁻¹' (A.outerCoordinates i : Set E),
    (A.chart i).isOpen_inter_preimage (A.outerCoordinates i).isOpen⟩

/-- The image of the closed outer coordinate ball in the unchanged manifold. -/
def closedPatch (i : A.Index) : Set M :=
  (A.chart i).symm '' Metric.closedBall (A.centerCoord i) (2 * A.radius (A.center i))

theorem mem_innerOpen_iff (i : A.Index) (y : M) :
    y ∈ A.innerOpen i ↔ y ∈ (A.chart i).source ∧
      A.chart i y ∈ Metric.ball (A.centerCoord i) (A.radius (A.center i)) := Iff.rfl

theorem mem_outerOpen_iff (i : A.Index) (y : M) :
    y ∈ A.outerOpen i ↔ y ∈ (A.chart i).source ∧
      A.chart i y ∈ Metric.ball (A.centerCoord i) (2 * A.radius (A.center i)) := Iff.rfl

theorem mem_closedPatch_iff (i : A.Index) (y : M) :
    y ∈ A.closedPatch i ↔ y ∈ (A.chart i).source ∧
      A.chart i y ∈ Metric.closedBall (A.centerCoord i) (2 * A.radius (A.center i)) := by
  rw [closedPatch, (A.chart i).symm_image_eq_source_inter_preimage
    (A.closedBall_two_subset_target i)]
  rfl

theorem innerOpen_subset_source (i : A.Index) :
    (A.innerOpen i : Set M) ⊆ (A.chart i).source := fun _ hy => hy.1

theorem outerOpen_subset_source (i : A.Index) :
    (A.outerOpen i : Set M) ⊆ (A.chart i).source := fun _ hy => hy.1

theorem closedPatch_subset_source (i : A.Index) :
    A.closedPatch i ⊆ (A.chart i).source := fun y hy => (A.mem_closedPatch_iff i y).mp hy |>.1

theorem center_mem_innerOpen (i : A.Index) : A.center i ∈ A.innerOpen i :=
  ⟨mem_chart_source E (A.center i), Metric.mem_ball_self (A.radius_pos i)⟩

theorem innerOpen_subset_outerOpen (i : A.Index) : A.innerOpen i ≤ A.outerOpen i := by
  intro y hy
  exact ⟨hy.1, Metric.ball_subset_ball (by linarith [A.radius_pos i]) hy.2⟩

theorem outerOpen_subset_closedPatch (i : A.Index) :
    (A.outerOpen i : Set M) ⊆ A.closedPatch i := by
  intro y hy
  exact (A.mem_closedPatch_iff i y).mpr ⟨hy.1, Metric.ball_subset_closedBall hy.2⟩

theorem innerOpen_eq_symm_image (i : A.Index) :
    (A.innerOpen i : Set M) = (A.chart i).symm '' (A.innerCoordinates i : Set E) :=
  ((A.chart i).symm_image_eq_source_inter_preimage (A.innerCoordinates_subset_target i)).symm

theorem outerOpen_eq_symm_image (i : A.Index) :
    (A.outerOpen i : Set M) = (A.chart i).symm '' (A.outerCoordinates i : Set E) :=
  ((A.chart i).symm_image_eq_source_inter_preimage (A.outerCoordinates_subset_target i)).symm

theorem symm_mem_innerOpen (i : A.Index) {z : E} (hz : z ∈ A.innerCoordinates i) :
    (A.chart i).symm z ∈ A.innerOpen i := by
  have ht := A.innerCoordinates_subset_target i hz
  refine ⟨(A.chart i).map_target ht, ?_⟩
  change A.chart i ((A.chart i).symm z) ∈ A.innerCoordinates i
  rw [(A.chart i).right_inv ht]
  exact hz

theorem symm_mem_outerOpen (i : A.Index) {z : E} (hz : z ∈ A.outerCoordinates i) :
    (A.chart i).symm z ∈ A.outerOpen i := by
  have ht := A.outerCoordinates_subset_target i hz
  refine ⟨(A.chart i).map_target ht, ?_⟩
  change A.chart i ((A.chart i).symm z) ∈ A.outerCoordinates i
  rw [(A.chart i).right_inv ht]
  exact hz

theorem chart_symm_inner (i : A.Index) {z : E} (hz : z ∈ A.innerCoordinates i) :
    A.chart i ((A.chart i).symm z) = z :=
  (A.chart i).right_inv (A.innerCoordinates_subset_target i hz)

theorem chart_symm_outer (i : A.Index) {z : E} (hz : z ∈ A.outerCoordinates i) :
    A.chart i ((A.chart i).symm z) = z :=
  (A.chart i).right_inv (A.outerCoordinates_subset_target i hz)

theorem symm_chart_inner (i : A.Index) {y : M} (hy : y ∈ A.innerOpen i) :
    (A.chart i).symm (A.chart i y) = y := (A.chart i).left_inv hy.1

theorem symm_chart_outer (i : A.Index) {y : M} (hy : y ∈ A.outerOpen i) :
    (A.chart i).symm (A.chart i y) = y := (A.chart i).left_inv hy.1

theorem chart_image_innerOpen (i : A.Index) :
    A.chart i '' (A.innerOpen i : Set M) = (A.innerCoordinates i : Set E) := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy.2
  · intro hz
    exact ⟨(A.chart i).symm z, A.symm_mem_innerOpen i hz, A.chart_symm_inner i hz⟩

theorem chart_image_outerOpen (i : A.Index) :
    A.chart i '' (A.outerOpen i : Set M) = (A.outerCoordinates i : Set E) := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy.2
  · intro hz
    exact ⟨(A.chart i).symm z, A.symm_mem_outerOpen i hz, A.chart_symm_outer i hz⟩

/-- Every original manifold point lies in one of the finite inner chart domains. -/
theorem covered (y : M) : ∃ i : A.Index, y ∈ A.innerOpen i := by
  obtain ⟨x, hx, hy⟩ := A.covering y
  exact ⟨⟨x, hx⟩, hy⟩

theorem covered_by_closedPatch (y : M) : ∃ i : A.Index, y ∈ A.closedPatch i := by
  obtain ⟨i, hi⟩ := A.covered y
  exact ⟨i, A.outerOpen_subset_closedPatch i (A.innerOpen_subset_outerOpen i hi)⟩

theorem iUnion_innerOpen : (⋃ i : A.Index, (A.innerOpen i : Set M)) = Set.univ := by
  ext y
  simp only [mem_iUnion, mem_univ, iff_true]
  exact A.covered y

theorem closedPatch_isCompact_of_proper [ProperSpace E] (i : A.Index) :
    IsCompact (A.closedPatch i) :=
  (isCompact_closedBall (A.centerCoord i) (2 * A.radius (A.center i))).image_of_continuousOn
    ((A.chart i).symm.continuousOn.mono (A.closedBall_two_subset_target i))

/-- The required compact outer control sets in finite-dimensional complex models. -/
theorem closedPatch_isCompact [NormedSpace ℂ E] [FiniteDimensional ℂ E] (i : A.Index) :
    IsCompact (A.closedPatch i) := by
  let : ProperSpace E := FiniteDimensional.proper ℂ E
  exact A.closedPatch_isCompact_of_proper i

theorem closedPatch_isClosed [NormedSpace ℂ E] [FiniteDimensional ℂ E] [T2Space M]
    (i : A.Index) : IsClosed (A.closedPatch i) := (A.closedPatch_isCompact i).isClosed

theorem closure_outerOpen_subset_closedPatch [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [T2Space M] (i : A.Index) :
    closure (A.outerOpen i : Set M) ⊆ A.closedPatch i :=
  closure_minimal (A.outerOpen_subset_closedPatch i) (A.closedPatch_isClosed i)

theorem closure_outerOpen_subset_source [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [T2Space M] (i : A.Index) :
    closure (A.outerOpen i : Set M) ⊆ (A.chart i).source :=
  (A.closure_outerOpen_subset_closedPatch i).trans (A.closedPatch_subset_source i)

/-- The inner domain has its closure strictly within the outer chart domain. -/
theorem closure_innerOpen_subset_outerOpen [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [T2Space M] (i : A.Index) :
    closure (A.innerOpen i : Set M) ⊆ (A.outerOpen i : Set M) := by
  let : ProperSpace E := FiniteDimensional.proper ℂ E
  let s : Set M :=
    (A.chart i).symm '' Metric.closedBall (A.centerCoord i) (A.radius (A.center i))
  have ht : Metric.closedBall (A.centerCoord i) (A.radius (A.center i)) ⊆
      (A.chart i).target :=
    (Metric.closedBall_subset_closedBall (by linarith [A.radius_pos i])).trans
      (A.closedBall_three_subset_target i)
  have hs : IsCompact s :=
    (isCompact_closedBall (A.centerCoord i) (A.radius (A.center i))).image_of_continuousOn
      ((A.chart i).symm.continuousOn.mono ht)
  have hin : (A.innerOpen i : Set M) ⊆ s := by
    intro y hy
    exact ⟨A.chart i y, Metric.ball_subset_closedBall hy.2, (A.chart i).left_inv hy.1⟩
  have hout : s ⊆ (A.outerOpen i : Set M) := by
    rintro y ⟨z, hz, rfl⟩
    exact A.symm_mem_outerOpen i
      (Metric.closedBall_subset_ball (by linarith [A.radius_pos i]) hz)
  exact (closure_minimal hin hs.isClosed).trans hout

end CompactAtlas

end Wikipedia.HopfProblem.HolomorphicAutomorphism
