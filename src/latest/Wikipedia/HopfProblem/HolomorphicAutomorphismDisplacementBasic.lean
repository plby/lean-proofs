import Wikipedia.HopfProblem.HolomorphicAutomorphismCompactAtlas
import Wikipedia.HopfProblem.HolomorphicAutomorphismCoordinates
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Actual displacements in a finite original-chart cover

The displacement of a genuine automorphism is measured in the finite product
of continuous-map spaces on the closed outer coordinate balls. The coordinate
expressions are the literal original-chart expressions wherever the actual
compact-open chart condition holds. The inner covering then detects the
identity without any additional faithfulness assumption.
-/

noncomputable section

open Set Filter Topology
open scoped Manifold

namespace Wikipedia.HopfProblem.HolomorphicAutomorphism.Displacement

variable {E M : Type*} [NormedAddCommGroup E] [TopologicalSpace M] [ChartedSpace E M]
  (A : CompactAtlas E M)

/-- The closed outer ball on which the actual coordinate displacement is measured. -/
def coordinateBall (i : A.Index) : Set E :=
  Metric.closedBall (A.centerCoord i) (2 * A.radius (A.center i))

theorem coordinateBall_subset_target (i : A.Index) :
    coordinateBall A i ⊆ (A.chart i).target := A.closedBall_two_subset_target i

theorem outerCoordinates_subset_coordinateBall (i : A.Index) :
    (A.outerCoordinates i : Set E) ⊆ coordinateBall A i := Metric.ball_subset_closedBall

theorem centerCoord_mem_coordinateBall (i : A.Index) :
    A.centerCoord i ∈ coordinateBall A i :=
  Metric.mem_closedBall_self (by linarith [A.radius_pos i])

instance coordinateBallNonempty (i : A.Index) : Nonempty (coordinateBall A i) :=
  ⟨⟨A.centerCoord i, centerCoord_mem_coordinateBall A i⟩⟩

variable [NormedSpace ℂ E] [FiniteDimensional ℂ E]

theorem coordinateBall_isCompact (i : A.Index) : IsCompact (coordinateBall A i) := by
  let : ProperSpace E := FiniteDimensional.proper ℂ E
  exact isCompact_closedBall _ _

instance coordinateBallCompactSpace (i : A.Index) : CompactSpace (coordinateBall A i) :=
  isCompact_iff_compactSpace.mp (coordinateBall_isCompact A i)

/-- All the finitely many actual coordinate expressions remain in their chart sources. -/
def good : Set (HolomorphicAutomorphism 𝓘(ℂ, E) M) :=
  {f | ∀ i : A.Index, f ∈ Coordinates.goodMaps (A.chart i) (coordinateBall A i)}

omit [FiniteDimensional ℂ E] in
theorem mem_good_iff (f : HolomorphicAutomorphism 𝓘(ℂ, E) M) :
    f ∈ good A ↔ ∀ i : A.Index,
      MapsTo f (A.closedPatch i) (A.chart i).source := Iff.rfl

theorem isOpen_good : IsOpen (good A) := by
  have he : good A = ⋂ i : A.Index,
      Coordinates.goodMaps (I := 𝓘(ℂ, E)) (A.chart i) (coordinateBall A i) := by
    ext f
    simp [good]
  rw [he]
  have h := isOpen_iInter_of_finite fun i : A.Index =>
    Coordinates.isOpen_goodMaps (I := 𝓘(ℂ, E)) (A.chart i)
      (coordinateBall_isCompact A i) (coordinateBall_subset_target A i)
  exact h

omit [FiniteDimensional ℂ E] in
theorem one_mem_good : (1 : HolomorphicAutomorphism 𝓘(ℂ, E) M) ∈ good A :=
  fun i => Coordinates.one_mem_goodMaps (A.chart i) (coordinateBall_subset_target A i)

theorem good_nhds_one : good A ∈ 𝓝 (1 : HolomorphicAutomorphism 𝓘(ℂ, E) M) :=
  (isOpen_good A).mem_nhds (one_mem_good A)

theorem eventually_good {α : Type*} {l : Filter α}
    {f : α → HolomorphicAutomorphism 𝓘(ℂ, E) M} (hf : Tendsto f l (𝓝 1)) :
    ∀ᶠ n in l, f n ∈ good A := hf.eventually (good_nhds_one A)

variable [LocallyCompactSpace M]

/-- The original coordinate variable as a continuous map on a closed outer ball. -/
def coordinateId (i : A.Index) : C(coordinateBall A i, E) :=
  ⟨Subtype.val, continuous_subtype_val⟩

omit [NormedSpace ℂ E] [FiniteDimensional ℂ E] [LocallyCompactSpace M] in
@[simp] theorem coordinateId_apply (i : A.Index) (z : coordinateBall A i) :
    coordinateId A i z = (z : E) := rfl

/-- The actual finite family of coordinate displacements, made total by the
continuous-expression defaults outside the chart-valid region. -/
def family (f : HolomorphicAutomorphism 𝓘(ℂ, E) M) :
    ∀ i : A.Index, C(coordinateBall A i, E) :=
  fun i => Coordinates.restrictedExpression (A.chart i) (coordinateBall A i) f -
    coordinateId A i

omit [FiniteDimensional ℂ E] in
theorem family_apply {f : HolomorphicAutomorphism 𝓘(ℂ, E) M} (hf : f ∈ good A)
    (i : A.Index) (z : coordinateBall A i) :
    family A f i z = Coordinates.expression (A.chart i) f z - (z : E) := by
  change Coordinates.restrictedExpression (A.chart i) (coordinateBall A i) f z -
    (z : E) = _
  rw [Coordinates.restrictedExpression_apply (A.chart i)
    (coordinateBall_subset_target A i) (hf i)]

omit [FiniteDimensional ℂ E] in
@[simp] theorem family_one : family A (1 : HolomorphicAutomorphism 𝓘(ℂ, E) M) = 0 := by
  funext i
  ext z
  rw [family_apply A (one_mem_good A)]
  simp only [Coordinates.expression_one (A.chart i)
    (coordinateBall_subset_target A i z.property), sub_self, Pi.zero_apply,
    ContinuousMap.zero_apply]

theorem family_continuousAt_one :
    ContinuousAt (family A) (1 : HolomorphicAutomorphism 𝓘(ℂ, E) M) := by
  apply continuousAt_pi.mpr
  intro i
  exact (Coordinates.restrictedExpression_continuousAt_one (A.chart i)
    (coordinateBall_isCompact A i) (coordinateBall_subset_target A i)).sub continuousAt_const

/-- The finite-product sup norm of the actual displacement family. -/
def delta (f : HolomorphicAutomorphism 𝓘(ℂ, E) M) : ℝ := ‖family A f‖

omit [LocallyCompactSpace M] in
theorem delta_nonneg (f : HolomorphicAutomorphism 𝓘(ℂ, E) M) : 0 ≤ delta A f := norm_nonneg _

@[simp] theorem delta_one : delta A (1 : HolomorphicAutomorphism 𝓘(ℂ, E) M) = 0 := by
  simp [delta]

theorem delta_continuousAt_one :
    ContinuousAt (delta A) (1 : HolomorphicAutomorphism 𝓘(ℂ, E) M) :=
  (family_continuousAt_one A).norm

theorem delta_tendsto_zero {α : Type*} {l : Filter α}
    {f : α → HolomorphicAutomorphism 𝓘(ℂ, E) M} (hf : Tendsto f l (𝓝 1)) :
    Tendsto (fun n => delta A (f n)) l (𝓝 0) := by
  simpa only [delta_one, Function.comp_def] using (delta_continuousAt_one A).tendsto.comp hf

/-- Each genuine pointwise coordinate difference is bounded by the finite sup norm. -/
theorem norm_expression_sub_le_delta {f : HolomorphicAutomorphism 𝓘(ℂ, E) M}
    (hf : f ∈ good A) (i : A.Index) {z : E} (hz : z ∈ coordinateBall A i) :
    ‖Coordinates.expression (A.chart i) f z - z‖ ≤ delta A f := by
  rw [← family_apply A hf i ⟨z, hz⟩]
  exact ((family A f i).norm_coe_le_norm ⟨z, hz⟩).trans (norm_le_pi_norm (family A f) i)

omit [FiniteDimensional ℂ E] in
/-- Zero displacement on the actual finite chart cover forces the native automorphism
itself to be the identity. -/
theorem eq_one_of_family_eq_zero {f : HolomorphicAutomorphism 𝓘(ℂ, E) M}
    (hf : f ∈ good A) (hzero : family A f = 0) : f = 1 := by
  ext y
  obtain ⟨i, hy⟩ := A.covered y
  have hk : y ∈ A.closedPatch i :=
    A.outerOpen_subset_closedPatch i (A.innerOpen_subset_outerOpen i hy)
  have hz : A.chart i y ∈ coordinateBall A i := (A.mem_closedPatch_iff i y).mp hk |>.2
  have hfy : f y ∈ (A.chart i).source := hf i hk
  have he : family A f i ⟨A.chart i y, hz⟩ = 0 := by
    rw [hzero]
    rfl
  rw [family_apply A hf] at he
  have he' := sub_eq_zero.mp he
  change A.chart i (f ((A.chart i).symm (A.chart i y))) = A.chart i y at he'
  rw [(A.chart i).left_inv hy.1] at he'
  exact (A.chart i).injOn hfy hy.1 he'

omit [FiniteDimensional ℂ E] in
theorem family_ne_zero {f : HolomorphicAutomorphism 𝓘(ℂ, E) M}
    (hf : f ∈ good A) (hne : f ≠ 1) : family A f ≠ 0 :=
  fun hzero => hne (eq_one_of_family_eq_zero A hf hzero)

theorem delta_eq_zero_iff {f : HolomorphicAutomorphism 𝓘(ℂ, E) M}
    (hf : f ∈ good A) : delta A f = 0 ↔ f = 1 := by
  constructor
  · intro hzero
    exact eq_one_of_family_eq_zero A hf (norm_eq_zero.mp hzero)
  · rintro rfl
    exact delta_one A

theorem delta_pos {f : HolomorphicAutomorphism 𝓘(ℂ, E) M}
    (hf : f ∈ good A) (hne : f ≠ 1) : 0 < delta A f :=
  norm_pos_iff.mpr (family_ne_zero A hf hne)

end Wikipedia.HopfProblem.HolomorphicAutomorphism.Displacement
