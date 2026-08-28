import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Continuity
import Mathlib.Topology.Separation.Hausdorff

/-!
# Disjoint coordinate discs around finitely many marked points

Hausdorff separation gives pairwise disjoint open neighborhoods of any
finite family of distinct marked points, inside arbitrary prescribed open
neighborhoods.  Genuine local coordinates then give smaller positive
coordinate discs, respecting prescribed radius bounds and retaining
pairwise disjointness.
-/

noncomputable section

open Set Filter Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold

variable {I X : Type*} [TopologicalSpace X]

/-- Finite marked points in a Hausdorff space have pairwise disjoint open
neighborhoods inside any supplied open neighborhoods. -/
theorem exists_pairwise_disjoint_opens [Finite I] [T2Space X]
    (p : I → X) (hp : Function.Injective p) (U : I → TopologicalSpace.Opens X)
    (hU : ∀ i, p i ∈ U i) :
    ∃ V : I → TopologicalSpace.Opens X,
      (∀ i, p i ∈ V i) ∧ (∀ i, V i ≤ U i) ∧
        Pairwise (fun i j => Disjoint (V i : Set X) (V j : Set X)) := by
  obtain ⟨W, hW, hdisj⟩ := (Set.finite_range p).t2_separation
  refine ⟨fun i => ⟨W (p i) ∩ U i, (hW (p i)).2.inter (U i).isOpen⟩,
    fun i => ⟨(hW (p i)).1, hU i⟩, fun _ => inter_subset_right, ?_⟩
  intro i j hij
  exact (hdisj (mem_range_self i) (mem_range_self j) (fun h => hij (hp h))).mono
    inter_subset_left inter_subset_left

/-- The actual open patch cut out by a coordinate disc, with the chart
source retained so that its inverse laws hold at every point. -/
def coordinateDisc (e : OpenPartialHomeomorph X ℂ) (r : ℝ) :
    TopologicalSpace.Opens X :=
  ⟨e.source ∩ e ⁻¹' Metric.ball 0 r, e.isOpen_inter_preimage Metric.isOpen_ball⟩

@[simp] theorem mem_coordinateDisc (e : OpenPartialHomeomorph X ℂ) (r : ℝ) (x : X) :
    x ∈ coordinateDisc e r ↔ x ∈ e.source ∧ e x ∈ Metric.ball 0 r := Iff.rfl

theorem center_mem_coordinateDisc (e : OpenPartialHomeomorph X ℂ) {p : X}
    (hp : p ∈ e.source) (h0 : e p = 0) {r : ℝ} (hr : 0 < r) :
    p ∈ coordinateDisc e r := by
  exact ⟨hp, h0 ▸ Metric.mem_ball_self hr⟩

/-- If the whole coordinate ball lies in the chart target, its inverse
image patch is literally the image of that ball under the inverse chart. -/
theorem coordinateDisc_eq_symm_image (e : OpenPartialHomeomorph X ℂ) {r : ℝ}
    (hr : Metric.ball 0 r ⊆ e.target) :
    (coordinateDisc e r : Set X) = e.symm '' Metric.ball 0 r :=
  (e.symm_image_eq_source_inter_preimage hr).symm

/-- A coordinate disc can be chosen inside any neighborhood of its
center and below any positive prescribed radius. -/
theorem exists_coordinateDisc_subset (e : OpenPartialHomeomorph X ℂ) {p : X}
    (hp : p ∈ e.source) (h0 : e p = 0) (U : TopologicalSpace.Opens X)
    (hU : p ∈ U) {R : ℝ} (hR : 0 < R) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧ Metric.ball 0 r ⊆ e.target ∧
      coordinateDisc e r ≤ U := by
  have hnhds : e.target ∩ e.symm ⁻¹' (U : Set X) ∈ 𝓝 (e p) :=
    inter_mem (e.open_target.mem_nhds (e.map_source hp))
      ((e.tendsto_symm hp).eventually (U.isOpen.mem_nhds hU))
  rw [h0] at hnhds
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  let ρ := min r (R / 2)
  have hρr : ρ ≤ r := min_le_left _ _
  have hρball : Metric.ball (0 : ℂ) ρ ⊆ e.target ∩ e.symm ⁻¹' (U : Set X) :=
    (Metric.ball_subset_ball hρr).trans hball
  refine ⟨ρ, lt_min hr (half_pos hR),
    (min_le_right _ _).trans_lt (half_lt_self hR),
    hρball.trans inter_subset_left, ?_⟩
  intro x hx
  have hmem := (hρball hx.2).2
  change e.symm (e x) ∈ (U : Set X) at hmem
  rw [e.left_inv hx.1] at hmem
  exact hmem

/-- Simultaneous coordinate discs around all the marked points can be
made pairwise disjoint, inside prescribed open neighborhoods, and smaller
than independently prescribed positive radius bounds. -/
theorem exists_pairwise_disjoint_coordinateDiscs [Finite I] [T2Space X]
    (p : I → X) (hp : Function.Injective p) (e : I → OpenPartialHomeomorph X ℂ)
    (hsource : ∀ i, p i ∈ (e i).source) (hzero : ∀ i, e i (p i) = 0)
    (U : I → TopologicalSpace.Opens X) (hU : ∀ i, p i ∈ U i)
    (R : I → ℝ) (hR : ∀ i, 0 < R i) :
    ∃ r : I → ℝ, (∀ i, 0 < r i ∧ r i < R i) ∧
      (∀ i, Metric.ball 0 (r i) ⊆ (e i).target) ∧
      (∀ i, coordinateDisc (e i) (r i) ≤ U i) ∧
      Pairwise (fun i j => Disjoint
        (coordinateDisc (e i) (r i) : Set X) (coordinateDisc (e j) (r j) : Set X)) := by
  obtain ⟨V, hpV, hVU, hVdisj⟩ := exists_pairwise_disjoint_opens p hp U hU
  have hdisc (i : I) := exists_coordinateDisc_subset (e i) (hsource i)
    (hzero i) (V i) (hpV i) (hR i)
  choose r hr hrR htarget hsubset using hdisc
  refine ⟨r, fun i => ⟨hr i, hrR i⟩, htarget,
    fun i => (hsubset i).trans (hVU i), ?_⟩
  intro i j hij
  exact (hVdisj hij).mono (hsubset i) (hsubset j)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold
