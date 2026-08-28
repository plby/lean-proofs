import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.UnitInterval
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Explicit local retractions of the positive orthant

Subtracting a fraction of the smallest coordinate deforms the nonnegative
orthant onto its coordinate boundary, without increasing the coordinate
product.  A continuous distance cutoff makes this deformation supported
in a small closed ball about any boundary point.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspPositiveRetraction

/-- The real nonnegative coordinate octant, with its inherited sup metric. -/
abbrev Orthant := {r : Fin 3 → ℝ // ∀ i, 0 ≤ r i}

theorem orthant_isClosed : IsClosed {r : Fin 3 → ℝ | ∀ i, 0 ≤ r i} := by
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)

instance : ProperSpace Orthant := ProperSpace.of_isClosed orthant_isClosed

/-- The positive toric parameter in one nonnegative affine chart. -/
def height (r : Orthant) : ℝ := ∏ i, r.1 i

theorem height_nonneg (r : Orthant) : 0 ≤ height r :=
  Finset.prod_nonneg fun i _ => r.2 i

theorem height_eq_zero_iff (r : Orthant) : height r = 0 ↔ ∃ i, r.1 i = 0 := by
  simp only [height, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and]

theorem height_continuous : Continuous height := by
  unfold height
  exact continuous_finsetProd _ fun i _ => (continuous_apply i).comp continuous_subtype_val

/-- The amount subtracted at the endpoint of the orthant deformation. -/
def minimum (r : Orthant) : ℝ := min (r.1 0) (min (r.1 1) (r.1 2))

theorem minimum_nonneg (r : Orthant) : 0 ≤ minimum r :=
  le_min (r.2 0) (le_min (r.2 1) (r.2 2))

theorem minimum_le (r : Orthant) (i : Fin 3) : minimum r ≤ r.1 i := by
  fin_cases i
  · exact min_le_left _ _
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)

theorem minimum_eq_coordinate (r : Orthant) : ∃ i : Fin 3, minimum r = r.1 i := by
  rcases min_choice (r.1 0) (min (r.1 1) (r.1 2)) with h | h
  · exact ⟨0, h⟩
  · rcases min_choice (r.1 1) (r.1 2) with h' | h'
    · exact ⟨1, h.trans h'⟩
    · exact ⟨2, h.trans h'⟩

theorem minimum_eq_zero_iff (r : Orthant) : minimum r = 0 ↔ height r = 0 := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := minimum_eq_coordinate r
    exact (height_eq_zero_iff r).mpr ⟨i, hi.symm.trans h⟩
  · intro h
    obtain ⟨i, hi⟩ := (height_eq_zero_iff r).mp h
    exact le_antisymm (by simpa only [hi] using minimum_le r i) (minimum_nonneg r)

theorem minimum_continuous : Continuous minimum :=
  ((continuous_apply 0).comp continuous_subtype_val).min
    (((continuous_apply 1).comp continuous_subtype_val).min
      ((continuous_apply 2).comp continuous_subtype_val))

/-- Subtract the same fraction of the smallest coordinate in every coordinate. -/
def shrink (s : unitInterval) (r : Orthant) : Orthant :=
  ⟨fun i => r.1 i - (s : ℝ) * minimum r, fun i => sub_nonneg.mpr
    ((mul_le_of_le_one_left (minimum_nonneg r) s.2.2).trans (minimum_le r i))⟩

@[simp] theorem shrink_apply (s : unitInterval) (r : Orthant) (i : Fin 3) :
    (shrink s r).1 i = r.1 i - (s : ℝ) * minimum r := rfl

theorem shrink_continuous : Continuous (fun p : unitInterval × Orthant => shrink p.1 p.2) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  exact ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)).sub
    ((continuous_subtype_val.comp continuous_fst).mul (minimum_continuous.comp continuous_snd))

@[simp] theorem shrink_zero (r : Orthant) : shrink 0 r = r := by
  apply Subtype.ext
  funext i
  simp only [shrink_apply, Set.Icc.coe_zero, zero_mul, sub_zero]

theorem shrink_one_height (r : Orthant) : height (shrink 1 r) = 0 := by
  obtain ⟨i, hi⟩ := minimum_eq_coordinate r
  apply (height_eq_zero_iff _).mpr
  refine ⟨i, ?_⟩
  simp only [shrink_apply, Set.Icc.coe_one, one_mul, hi, sub_self]

theorem shrink_fixed (s : unitInterval) {r : Orthant} (hr : height r = 0) : shrink s r = r := by
  apply Subtype.ext
  funext i
  simp only [shrink_apply, (minimum_eq_zero_iff r).mpr hr, mul_zero, sub_zero]

theorem shrink_coordinate_le (s : unitInterval) (r : Orthant) (i : Fin 3) :
    (shrink s r).1 i ≤ r.1 i :=
  sub_le_self _ (mul_nonneg s.2.1 (minimum_nonneg r))

theorem shrink_height_le (s : unitInterval) (r : Orthant) : height (shrink s r) ≤ height r :=
  Finset.prod_le_prod (fun i _ => (shrink s r).2 i) (fun i _ => shrink_coordinate_le s r i)

theorem shrink_dist_eq (s : unitInterval) (r : Orthant) :
    dist (shrink s r) r = (s : ℝ) * minimum r := by
  rw [Subtype.dist_eq, dist_eq_norm]
  have he : (shrink s r).1 - r.1 = fun _ : Fin 3 => -((s : ℝ) * minimum r) := by
    funext i
    simp only [Pi.sub_apply, shrink_apply]
    ring
  rw [he, pi_norm_const, norm_neg, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg s.2.1 (minimum_nonneg r))]

theorem shrink_dist_le_minimum (s : unitInterval) (r : Orthant) :
    dist (shrink s r) r ≤ minimum r := by
  rw [shrink_dist_eq]
  exact mul_le_of_le_one_left (minimum_nonneg r) s.2.2

theorem minimum_le_dist_of_height_eq_zero (r : Orthant) {r₀ : Orthant}
    (hr₀ : height r₀ = 0) : minimum r ≤ dist r r₀ := by
  obtain ⟨i, hi⟩ := (height_eq_zero_iff r₀).mp hr₀
  calc
    minimum r ≤ r.1 i := minimum_le r i
    _ = ‖(r.1 - r₀.1) i‖ := by
      simp only [Pi.sub_apply, hi, sub_zero, Real.norm_eq_abs, abs_of_nonneg (r.2 i)]
    _ ≤ ‖r.1 - r₀.1‖ := norm_le_pi_norm _ i
    _ = dist r r₀ := (dist_eq_norm _ _).symm

theorem shrink_dist_le_twice_dist (s : unitInterval) (r : Orthant) {r₀ : Orthant}
    (hr₀ : height r₀ = 0) : dist (shrink s r) r₀ ≤ 2 * dist r r₀ := by
  calc
    dist (shrink s r) r₀ ≤ dist (shrink s r) r + dist r r₀ := dist_triangle _ _ _
    _ ≤ minimum r + dist r r₀ := add_le_add (shrink_dist_le_minimum s r) le_rfl
    _ ≤ dist r r₀ + dist r r₀ := add_le_add (minimum_le_dist_of_height_eq_zero r hr₀) le_rfl
    _ = 2 * dist r r₀ := (two_mul _).symm

/-- A linear distance bump, equal to one on the quarter-radius ball and
zero outside the third-radius ball when `R > 0`. -/
def cutoff (r₀ : Orthant) (R : ℝ) (r : Orthant) : ℝ :=
  max 0 (min 1 (4 - 12 * dist r r₀ / R))

theorem cutoff_nonneg (r₀ : Orthant) (R : ℝ) (r : Orthant) : 0 ≤ cutoff r₀ R r :=
  le_max_left _ _

theorem cutoff_le_one (r₀ : Orthant) (R : ℝ) (r : Orthant) : cutoff r₀ R r ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem cutoff_continuous (r₀ : Orthant) (R : ℝ) : Continuous (cutoff r₀ R) :=
  continuous_const.max (continuous_const.min
    (continuous_const.sub
      ((continuous_const.mul (continuous_id.dist continuous_const)).div_const R)))

theorem cutoff_eq_one_of_dist_le (r₀ : Orthant) {R : ℝ} (hR : 0 < R)
    {r : Orthant} (hr : dist r r₀ ≤ R / 4) : cutoff r₀ R r = 1 := by
  have hdiv : 12 * dist r r₀ / R ≤ 3 :=
    (div_le_iff₀ hR).mpr (by linarith)
  have h : 1 ≤ 4 - 12 * dist r r₀ / R := by linarith
  exact (congrArg (max (0 : ℝ)) (min_eq_left h)).trans (max_eq_right zero_le_one)

theorem cutoff_eq_zero_of_le_dist (r₀ : Orthant) {R : ℝ} (hR : 0 < R)
    {r : Orthant} (hr : R / 3 ≤ dist r r₀) : cutoff r₀ R r = 0 := by
  have hdiv : 4 ≤ 12 * dist r r₀ / R :=
    (le_div_iff₀ hR).mpr (by linarith)
  have h : 4 - 12 * dist r r₀ / R ≤ 0 := by linarith
  exact (congrArg (max (0 : ℝ)) (min_eq_right (h.trans zero_le_one))).trans (max_eq_left h)

/-- The cutoff as a valid homotopy parameter. -/
def cutoffParameter (r₀ : Orthant) (R : ℝ) (r : Orthant) : unitInterval :=
  ⟨cutoff r₀ R r, cutoff_nonneg r₀ R r, cutoff_le_one r₀ R r⟩

@[simp] theorem cutoffParameter_coe (r₀ : Orthant) (R : ℝ) (r : Orthant) :
    (cutoffParameter r₀ R r : ℝ) = cutoff r₀ R r := rfl

theorem cutoffParameter_continuous (r₀ : Orthant) (R : ℝ) :
    Continuous (cutoffParameter r₀ R) := (cutoff_continuous r₀ R).subtype_mk _

theorem cutoffParameter_eq_one_of_dist_le (r₀ : Orthant) {R : ℝ} (hR : 0 < R)
    {r : Orthant} (hr : dist r r₀ ≤ R / 4) : cutoffParameter r₀ R r = 1 :=
  Subtype.ext (cutoff_eq_one_of_dist_le r₀ hR hr)

theorem cutoffParameter_eq_zero_of_le_dist (r₀ : Orthant) {R : ℝ} (hR : 0 < R)
    {r : Orthant} (hr : R / 3 ≤ dist r r₀) : cutoffParameter r₀ R r = 0 :=
  Subtype.ext (cutoff_eq_zero_of_le_dist r₀ hR hr)

/-- The compactly supported local orthant deformation. -/
def localShrink (r₀ : Orthant) (R : ℝ) (s : unitInterval) (r : Orthant) : Orthant :=
  shrink (s * cutoffParameter r₀ R r) r

theorem localShrink_continuous (r₀ : Orthant) (R : ℝ) :
    Continuous (fun p : unitInterval × Orthant => localShrink r₀ R p.1 p.2) := by
  have hp : Continuous
      (fun p : unitInterval × Orthant => p.1 * cutoffParameter r₀ R p.2) := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp continuous_fst).mul
      ((cutoff_continuous r₀ R).comp continuous_snd)
  exact shrink_continuous.comp (hp.prodMk continuous_snd)

@[simp] theorem localShrink_zero (r₀ : Orthant) (R : ℝ) (r : Orthant) :
    localShrink r₀ R 0 r = r := by
  simp only [localShrink, zero_mul, shrink_zero]

theorem localShrink_fixed (r₀ : Orthant) (R : ℝ) (s : unitInterval)
    {r : Orthant} (hr : height r = 0) : localShrink r₀ R s r = r :=
  shrink_fixed _ hr

theorem localShrink_coordinate_le (r₀ : Orthant) (R : ℝ) (s : unitInterval)
    (r : Orthant) (i : Fin 3) : (localShrink r₀ R s r).1 i ≤ r.1 i :=
  shrink_coordinate_le _ r i

theorem localShrink_height_le (r₀ : Orthant) (R : ℝ) (s : unitInterval) (r : Orthant) :
    height (localShrink r₀ R s r) ≤ height r := shrink_height_le _ r

theorem localShrink_dist_le_minimum (r₀ : Orthant) (R : ℝ) (s : unitInterval) (r : Orthant) :
    dist (localShrink r₀ R s r) r ≤ minimum r := shrink_dist_le_minimum _ r

theorem localShrink_dist_le_twice_dist {r₀ : Orthant} (hr₀ : height r₀ = 0)
    (R : ℝ) (s : unitInterval) (r : Orthant) :
    dist (localShrink r₀ R s r) r₀ ≤ 2 * dist r r₀ := shrink_dist_le_twice_dist _ r hr₀

theorem localShrink_eq_self_of_le_dist (r₀ : Orthant) {R : ℝ} (hR : 0 < R)
    (s : unitInterval) {r : Orthant} (hr : R / 3 ≤ dist r r₀) :
    localShrink r₀ R s r = r := by
  rw [localShrink, cutoffParameter_eq_zero_of_le_dist r₀ hR hr, mul_zero, shrink_zero]

alias localShrink_eq_self_of_dist_ge := localShrink_eq_self_of_le_dist

theorem localShrink_eq_self_of_not_mem_closedBall (r₀ : Orthant) {R : ℝ} (hR : 0 < R)
    (s : unitInterval) {r : Orthant} (hr : r ∉ Metric.closedBall r₀ (R / 3)) :
    localShrink r₀ R s r = r :=
  localShrink_eq_self_of_le_dist r₀ hR s (not_le.mp hr).le

theorem localShrink_one_height_of_dist_le (r₀ : Orthant) {R : ℝ} (hR : 0 < R)
    {r : Orthant} (hr : dist r r₀ ≤ R / 4) : height (localShrink r₀ R 1 r) = 0 := by
  rw [localShrink, cutoffParameter_eq_one_of_dist_le r₀ hR hr, one_mul]
  exact shrink_one_height r

theorem localShrink_one_height_of_mem_ball (r₀ : Orthant) {R : ℝ} (hR : 0 < R)
    {r : Orthant} (hr : r ∈ Metric.ball r₀ (R / 4)) :
    height (localShrink r₀ R 1 r) = 0 :=
  localShrink_one_height_of_dist_le r₀ hR hr.le

theorem localShrink_mapsTo_ball {r₀ : Orthant} (hr₀ : height r₀ = 0)
    {R : ℝ} (hR : 0 < R) (s : unitInterval) :
    MapsTo (localShrink r₀ R s) (Metric.ball r₀ R) (Metric.ball r₀ R) := by
  intro r hr
  by_cases hd : dist r r₀ < R / 3
  · have hb := localShrink_dist_le_twice_dist hr₀ R s r
    change dist (localShrink r₀ R s r) r₀ < R
    linarith
  · rw [localShrink_eq_self_of_le_dist r₀ hR s (le_of_not_gt hd)]
    exact hr

theorem localShrink_map_ball {r₀ : Orthant} (hr₀ : height r₀ = 0)
    {R : ℝ} (hR : 0 < R) (s : unitInterval) {r : Orthant}
    (hr : r ∈ Metric.ball r₀ R) : localShrink r₀ R s r ∈ Metric.ball r₀ R :=
  localShrink_mapsTo_ball hr₀ hR s hr

theorem localShrink_moved_closure_isCompact (r₀ : Orthant) {R : ℝ} (hR : 0 < R) :
    IsCompact (closure {r : Orthant | ∃ s : unitInterval, localShrink r₀ R s r ≠ r}) := by
  apply (isCompact_closedBall r₀ (R / 3)).of_isClosed_subset isClosed_closure
  apply closure_minimal ?_ Metric.isClosed_closedBall
  rintro r ⟨s, hs⟩
  by_contra hr
  exact hs (localShrink_eq_self_of_not_mem_closedBall r₀ hR s hr)

end Wikipedia.HopfProblem.CuspPositiveRetraction
