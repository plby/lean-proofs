import Wikipedia.HopfProblem.DegreeCollapseCornerRetraction
import Wikipedia.NoExoticSixSphere.RoundedSurgeryTrace

/-!
# The actual added collar region deforms into the original attachment

The deformation retains the source sphere coordinate, decreases transverse
norm, and increases height without crossing zero. It stays in the exact
compact added-parameter set. On its overlap with the original attachment
it is the identity; its endpoint is in that original attachment.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.TraceRetraction

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization EuclideanEmbedding
open EuclideanEmbedding.FramedAttachingProduct
open EuclideanEmbedding.FramedAttachingProduct.RoundedTrace CornerRetraction

theorem norm_deform_le {r t : ℝ} (hr : 0 < r) (ht : t ∈ Icc (0 : ℝ) 1)
    (p : Vector 3 × ℝ) : ‖(deform r t p).1‖ ≤ ‖p.1‖ := by
  have h := norm_sq_deform hr ht p
  have hm := mul_nonneg ht.1 (shift_nonneg r p)
  nlinarith [norm_nonneg p.1, norm_nonneg (deform r t p).1]

theorem height_deform_bounds {r t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (p : Vector 3 × ℝ) (hp : p.2 ≤ 0) : p.2 ≤ (deform r t p).2 ∧ (deform r t p).2 ≤ 0 := by
  have hm := mul_nonneg ht.1 (shift_nonneg r p)
  constructor
  · change p.2 ≤ p.2 + t * shift r p
    linarith
  · rcases eq_or_lt_of_le (shift_nonneg r p) with h | h
    · rw [deform_fixed_of_shift_zero h.symm]
      exact hp
    · have hb := (positive_shift_bounds h).2.2.1
      have htm : t * shift r p ≤ shift r p :=
        mul_le_of_le_one_left (shift_nonneg r p) ht.2
      change p.2 + t * shift r p ≤ 0
      linarith

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

def parameterDeform (t : ℝ) (p : (Sphere 3 × Vector 3) × ℝ) : (Sphere 3 × Vector 3) × ℝ :=
  let q := deform (UnroundedTrace.handleRadius A) t (p.1.2, p.2)
  ((p.1.1, q.1), q.2)

theorem continuous_parameterDeform :
    Continuous (fun z : ℝ × ((Sphere 3 × Vector 3) × ℝ) ↦ parameterDeform A z.1 z.2) := by
  have hc : Continuous (fun z : ℝ × ((Sphere 3 × Vector 3) × ℝ) ↦ (z.1, (z.2.1.2, z.2.2))) :=
    by fun_prop
  have h := (continuous_deform (UnroundedTrace.handleRadius_pos A)).comp hc
  have hs : Continuous (fun z : ℝ × ((Sphere 3 × Vector 3) × ℝ) ↦ z.2.1.1) := by fun_prop
  exact (hs.prodMk h.fst).prodMk h.snd

theorem parameterDeform_zero (p : (Sphere 3 × Vector 3) × ℝ) : parameterDeform A 0 p = p := by
  unfold parameterDeform
  rw [deform_zero]

theorem parameterDeform_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    {p : (Sphere 3 × Vector 3) × ℝ} (hp : p ∈ addedParameters A) :
    parameterDeform A t p ∈ addedParameters A := by
  have hn := norm_deform_le (UnroundedTrace.handleRadius_pos A) ht (p.1.2, p.2)
  have htime := height_deform_bounds (r := UnroundedTrace.handleRadius A) ht (p.1.2, p.2) hp.2.1.2
  refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
  · change ‖(deform (UnroundedTrace.handleRadius A) t (p.1.2, p.2)).1 - 0‖ ≤ outerRadius A
    rw [sub_zero]
    exact hn.trans (by simpa only [mem_closedBall, dist_zero_right] using hp.1)
  · exact hp.2.1.1.trans htime.1
  · exact htime.2
  · change 0 ≤ RoundedHandleCorner.level (bump A) (UnroundedTrace.handleRadius A)
      (deform (UnroundedTrace.handleRadius A) t (p.1.2, p.2))
    rw [level_deform (bump A) (UnroundedTrace.handleRadius_pos A) ht]
    exact add_nonneg hp.2.2 (mul_nonneg (mul_nonneg (by norm_num) ht.1) (shift_nonneg _ _))

theorem added_height_bound {p : (Sphere 3 × Vector 3) × ℝ} (hp : p ∈ addedParameters A) :
    ‖p.2‖ ≤ collarHeight A := by
  rw [Real.norm_eq_abs, abs_of_nonpos hp.2.1.2]
  have h := twice_outer_lt_height A
  linarith [hp.2.1.1]

theorem parameterDeform_fixed_on_overlap {p : (Sphere 3 × Vector 3) × ℝ}
    (hp : p ∈ addedParameters A) (hold : A.collarSheet p ∈ UnroundedTrace.ambientSet A)
    (t : ℝ) : parameterDeform A t p = p := by
  have hv : p.1.2 ∈ ball (0 : Vector 3) A.radius :=
    (closedBall_subset_ball (outerRadius_lt A)) hp.1
  have hc := (sheet_mem_unrounded_iff A p.1.1 hv (added_height_bound A hp)).mp hold
  unfold parameterDeform
  rw [deform_fixed_of_corner (UnroundedTrace.handleRadius_pos A).le hc]

theorem parameterDeform_one_mem_unrounded {p : (Sphere 3 × Vector 3) × ℝ}
    (hp : p ∈ addedParameters A) :
    A.collarSheet (parameterDeform A 1 p) ∈ UnroundedTrace.ambientSet A := by
  have hmem := parameterDeform_mem A (by norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) 1) hp
  have hv := (closedBall_subset_ball (outerRadius_lt A)) hmem.1
  apply (sheet_mem_unrounded_iff A (parameterDeform A 1 p).1.1 hv (added_height_bound A hmem)).mpr
  exact deform_one_mem_corner (UnroundedTrace.handleRadius_pos A) (p.1.2, p.2)

end Wikipedia.HopfProblem.DegreeCollapse.TraceRetraction
