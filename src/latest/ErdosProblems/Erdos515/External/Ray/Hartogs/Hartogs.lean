module
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Set.Function
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import ErdosProblems.Erdos515.External.Ray.Analytic.Analytic
import ErdosProblems.Erdos515.External.Ray.Hartogs.MaxLog
import ErdosProblems.Erdos515.External.Ray.Hartogs.Osgood
import ErdosProblems.Erdos515.External.Ray.Hartogs.Subharmonic
import ErdosProblems.Erdos515.External.Ray.Misc.Bound
import ErdosProblems.Erdos515.External.Ray.Misc.Bounds
import ErdosProblems.Erdos515.External.Ray.Misc.Max
import ErdosProblems.Erdos515.External.Ray.Misc.Multilinear
import ErdosProblems.Erdos515.External.Ray.Misc.Prod
import ErdosProblems.Erdos515.External.Ray.Misc.Prod
import ErdosProblems.Erdos515.External.Ray.Misc.Topology

/-!
## Hartogs' theorem for two variables: separately analytic functions are jointly analytic

Given `f : ℂ × ℂ → E` where `E` is a separable Banach space, analyticity along each axis at each
point in an open set implies joint analyticity.  This differs from Osgood's theorem in that
*no continuity assumption is required*.

Given such a function `f`, the proof proceeds in several stages:

1. If `f` is continuous, we're done (Osgood's theorem)
2. If `f` is bounded, it is continuous (and therefore analytic), by applying the Schwarz lemma
   along each axis in turn
3. By the Baire category theorem, if `f` is analytic in a polydisk
   `closedBall c0 r0 ×ˢ closedBall c1 r1`, then it is bounded (and therefore analytic) in some
   smaller strip `closedBall c0 r0 ×ˢ closedBall c1' r1'`, where `c1'` is close to `c1` and `r1'`
   is positive but might be very small.
4. Once we have analyticity in this strip, we use Hartogs' lemma (`SubharmonicOn.hartogs`) to
   show that the power series that works on this small strip actually converges on most of the
   original strip, including near `(c0,c1)`.  This is because (1) `log ‖ ‖` of the power series
   coefficients are uniformly bounded (since they work out to `r1'`), and pointwise bounded enough
   to reach near `r1` (since `f` is analytic along the full second axis).
5. Since we can choose `(c0,c1)` as desired, we're done.

References:
1. https://en.wikipedia.org/wiki/Hartogs's_theorem_on_separate_mAnalyticity
2. https://www-users.cse.umn.edu/~garrett/m/complex/hartogs.pdf
-/

open Complex (exp I log)
open Filter (atTop)
open Function (curry uncurry)
open MeasureTheory.MeasureSpace (volume)
open Metric (ball closedBall sphere isOpen_ball ball_subset_closedBall)
open Prod (swap)
open Set (univ)
open scoped Real NNReal ENNReal Topology
noncomputable section

section Hartogs

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {f : ℂ × ℂ → E}
variable {s : Set (ℂ × ℂ)}
variable {c0 c0' c1 z0 z1 w0 w1 : ℂ}
variable {r r0 r1 b e : ℝ}

/-- Separate analyticity along each axis at each point in a set -/
structure Har (f : ℂ × ℂ → E) (s : Set (ℂ × ℂ)) : Prop where
  fa0 : ∀ c0 c1, (c0, c1) ∈ s → AnalyticAt ℂ (fun z0 ↦ f (z0, c1)) c0
  fa1 : ∀ c0 c1, (c0, c1) ∈ s → AnalyticAt ℂ (fun z1 ↦ f (c0, z1)) c1

/-- We can swap axes in `Har` -/
lemma Har.flip (h : Har f s) : Har (f ∘ swap) (swap '' s) where
  fa0 := by
    intro c0 c1 cs; simp only [Function.comp_apply, Prod.swap_prod_mk]
    rw [swap_mem] at cs; exact h.fa1 c1 c0 cs
  fa1 := by
    intro c0 c1 cs; simp only [Function.comp_apply, Prod.swap_prod_mk]
    rw [swap_mem] at cs; exact h.fa0 c1 c0 cs

/-- `Har` shrinks to smaller sets -/
theorem Har.mono {s t : Set (ℂ × ℂ)} (ts : t ⊆ s) (h : Har f s) : Har f t :=
  { fa0 := fun _ _ m ↦ h.fa0 _ _ (ts m)
    fa1 := fun _ _ m ↦ h.fa1 _ _ (ts m) }

/-- Analyticity in the first coordinate -/
theorem Har.on0 (h : Har f (closedBall (c0, c1) r)) (z1r : z1 ∈ closedBall c1 r) :
    AnalyticOnNhd ℂ (fun z0 ↦ f (z0, z1)) (closedBall c0 r) := by
  intro z0 z0s; apply h.fa0 z0 z1
  rw [← closedBall_prod_same]
  simp only [Set.prodMk_mem_set_prod_eq, Metric.mem_closedBall] at z0s ⊢
  exact ⟨z0s, z1r⟩

/-- Analyticity in the second coordinate -/
theorem Har.on1 (h : Har f (closedBall (c0, c1) r)) (z0r : z0 ∈ closedBall c0 r) :
    AnalyticOnNhd ℂ (fun z1 ↦ f (z0, z1)) (closedBall c1 r) := by
  intro z1 z1s; apply h.fa1 z0 z1
  rw [← closedBall_prod_same]
  simp only [Set.prodMk_mem_set_prod_eq, Metric.mem_closedBall] at z1s ⊢
  exact ⟨z0r, z1s⟩

/-- If `f` is bounded, moving along the first axis changes the value only slightly -/
theorem Bounded.dist0 (h : Har f s) {z w : ℂ × ℂ} {b e r : ℝ} (bp : 0 < b) (ep : 0 < e) (rp : 0 < r)
    (rs : ball z (r / 2) ⊆ s) (wz : dist w z < min (r / 2) (e * r / b / 24))
    (fb : ∀ z, z ∈ s → ‖f z‖ ≤ b) : dist (f w) (f (z.fst, w.snd)) ≤ e / 4 := by
  generalize hu : min (r / 2) (e * r / b / 24) = u; rw [hu] at wz
  have up : 0 < u := by
    rw [← hu]; simp only [lt_min_iff]
    exact ⟨by bound, by bound⟩
  have ur : u ≤ r / 2 := by rw [← hu]; exact min_le_left _ _
  have ue : 6 * b / r * u ≤ e / 4 := by
    rw [← hu]
    calc 6 * b / r * min (r / 2) (e * r / b / 24)
      _ ≤ 6 * b / r * (e * r / b / 24) := by bound
      _ = b / b * (r / r) * (e / 4) := by ring
      _ = e / 4 := by field_simp [bp.ne', rp.ne']
  rw [ball_prod_same'] at rs
  rw [← Metric.mem_ball, ball_prod_same', Set.mem_prod] at wz
  have d : DifferentiableOn ℂ (fun t ↦ f (t, w.snd)) (ball z.fst (r / 2)) := by
    intro t ts; refine (h.fa0 t w.snd ?_).differentiableWithinAt
    exact rs (Set.mk_mem_prod ts (Metric.ball_subset_ball ur wz.right))
  have wf : w.fst ∈ ball z.fst (r / 2) := Metric.ball_subset_ball ur wz.left
  have m : Set.MapsTo (fun t ↦ f (t, w.snd)) (ball z.fst (r / 2))
      (ball (f (z.fst, w.snd)) (3 * b)) := by
    intro t ts; simp only [dist_eq_norm, Metric.mem_ball]; apply lt_of_le_of_lt (norm_sub_le _ _)
    have f0 : ‖f (t, w.snd)‖ ≤ b := by
      apply_rules [rs, Set.mk_mem_prod, Metric.ball_subset_ball ur, fb, wz.right]
    have f1 : ‖f (z.fst, w.snd)‖ ≤ b := by
      apply_rules [rs, Set.mk_mem_prod, Metric.ball_subset_ball ur, fb, Metric.mem_ball_self up,
        wz.right]
    calc ‖f (t, w.snd)‖ + ‖f (z.fst, w.snd)‖
      _ ≤ b + b := by linarith
      _ = 2 * b := by ring
      _ < 3 * b := mul_lt_mul_of_pos_right (by norm_num) bp
  have L := Complex.dist_le_div_mul_dist_of_mapsTo_ball d
    (m.mono_right Metric.ball_subset_closedBall) wf; simp only [Prod.mk.eta] at L
  refine _root_.trans L (_root_.trans ?_ ue); simp only [Metric.mem_ball] at wz
  rw [div_eq_mul_inv _ (2 : ℝ), div_mul_eq_div_div]; ring_nf
  bound

/-- If `f` is bounded, moving along the second axis changes the value only slightly -/
theorem Bounded.dist1 (h : Har f s) {z w : ℂ × ℂ} {b e r : ℝ} (bp : 0 < b) (ep : e > 0) (rp : r > 0)
    (rs : ball z r ⊆ s) (wz : dist w z < min (r / 2) (e * r / b / 24))
    (fb : ∀ z, z ∈ s → ‖f z‖ ≤ b) : dist (f (z.fst, w.snd)) (f z) ≤ e / 4 := by
  have wrs : ball w (r / 2) ⊆ s := by
    refine _root_.trans ?_ rs; apply Metric.ball_subset_ball'
    have rr := _root_.trans wz.le (min_le_left _ _)
    trans r / 2 + r / 2; linarith; ring_nf; apply le_refl
  have rs' : ball (swap w) (r / 2) ⊆ swap '' s := by rw [ball_swap]; exact Set.image_mono wrs
  have wz' : dist (swap z) (swap w) < min (r / 2) (e * r / b / 24) := by rwa [dist_swap, dist_comm]
  have fb' : ∀ z, z ∈ swap '' s → ‖(f ∘ swap) z‖ ≤ b := fun z zs ↦ fb z.swap (swap_mem'.mp zs)
  have d' := Bounded.dist0 h.flip bp ep rp rs' wz' fb'
  simp only [Function.comp_apply, Prod.swap_swap, Prod.fst_swap, Prod.snd_swap,
    Prod.swap_prod_mk] at d'
  rwa [dist_comm]

/-- `f` is analytic if it's bounded -/
theorem of_bounded [CompleteSpace E] (h : Har f s) (o : IsOpen s) {b : ℝ}
    (fb : ∀ z, z ∈ s → ‖f z‖ ≤ b) : AnalyticOnNhd ℂ f s := by
  suffices c : ContinuousOn f s by exact osgood o c h.fa0 h.fa1
  by_cases bp : b ≤ 0
  · have fz : ∀ z, z ∈ s → f z = 0 := fun z zs ↦
      norm_eq_zero.mp (le_antisymm (_root_.trans (fb z zs) bp) (norm_nonneg (f z)))
    rw [continuousOn_congr fz]; exact continuousOn_const
  simp only [not_le] at bp
  intro z zs
  rcases Metric.isOpen_iff.mp o z zs with ⟨r, rp, rs⟩
  rw [Metric.continuousWithinAt_iff]; intro e ep
  have up : min (r / 2) (e * r / b / 24) > 0 := by bound
  use min (r / 2) (e * r / b / 24), up
  intro w _ wz
  have s0 : dist (f w) (f (z.fst, w.snd)) ≤ e / 4 :=
    Bounded.dist0 h bp ep rp (_root_.trans (Metric.ball_subset_ball (by linarith)) rs) wz fb
  have s1 : dist (f (z.fst, w.snd)) (f z) ≤ e / 4 := Bounded.dist1 h bp ep rp rs wz fb
  calc dist (f w) (f z)
    _ ≤ dist (f w) (f (z.fst, w.snd)) + dist (f (z.fst, w.snd)) (f z) := dist_triangle _ _ _
    _ ≤ e / 4 + e / 4 := by linarith
    _ = e / 2 := by ring
    _ < e := by linarith

/-- A version of the Baire category theorem for open sets, rather than subtypes.

    I'm finding it very difficult to work with subtypes (sets coerced to Sort), so we instead
    prove one of the variants of Baire's theorem for an open set. -/
theorem NonemptyInterior.nonempty_interior_of_iUnion_of_closed {A B : Type} [TopologicalSpace A]
    [BaireSpace A] [Encodable B] {f : B → Set A} (hc : ∀ k, IsClosed (f k))
    (hU : (interior (⋃ k, f k)).Nonempty) : ∃ k, (interior (f k)).Nonempty := by
  set s := interior (⋃ k, f k)
  set f' : Option B → Set A := fun k ↦
    match k with
    | none => sᶜ
    | some k => f k
  have hc' : ∀ k, IsClosed (f' k) := by
    simp only [s, Option.forall, isClosed_compl_iff, isOpen_interior, true_and, f']
    exact fun k ↦ hc k
  have hU' : (⋃ k, f' k) = Set.univ := by
    apply Set.ext; intro x; refine ⟨fun _ ↦ Set.mem_univ _, ?_⟩; intro _; rw [Set.mem_iUnion]
    by_cases m : x ∈ s
    · rcases Set.mem_iUnion.mp (interior_subset m) with ⟨k, mk⟩
      use some k
    · use none; exact m
  have d := dense_iUnion_interior_of_closed hc' hU'
  rcases Dense.exists_mem_open d isOpen_interior hU with ⟨x, xi, xs⟩
  rcases Set.mem_iUnion.mp xi with ⟨k, xk⟩
  match k with
  | none => simp only [s, interior_compl, Set.mem_compl_iff, subset_closure xs,
      not_true_eq_false, f'] at xk
  | some k => exact ⟨k, Set.nonempty_of_mem xk⟩

/-- Special case of forall_and_distrib -/
theorem forall_const_and_distrib {A : Type} [Nonempty A] {p : Prop} {q : A → Prop} :
    (∀ x, p ∧ q x) ↔ p ∧ ∀ x, q x := by
  have d := @forall_and A (fun _ ↦ p) q; simp only [forall_const] at d; exact d

/-- Version of `isClosed_le` for `ContinuousOn` -/
theorem ContinuousOn.isClosed_le {A B : Type} [TopologicalSpace A] [TopologicalSpace B] [Preorder B]
    [OrderClosedTopology B] {s : Set A} {f g : A → B} (sc : IsClosed s) (fc : ContinuousOn f s)
    (gc : ContinuousOn g s) : IsClosed {x | x ∈ s ∧ f x ≤ g x} := by
  rw [Set.ofPred_and]; simp only [Set.ofPred_mem_eq]
  set t := {p : B × B | p.fst ≤ p.snd}
  set fg := fun x ↦ (f x, g x)
  have e : {x | f x ≤ g x} = fg ⁻¹' t := by aesop
  rw [e]
  exact ContinuousOn.preimage_isClosed_of_isClosed (ContinuousOn.prodMk fc gc) sc
    OrderClosedTopology.isClosed_le'

/-- If `f` is separately analytic on a polydisk, it is analytic on a subpolydisk that is full in
    one dimension.  Proof: Use the Baire category to find a subpolydisk on which `f` is bounded,
    whence it is analytic there by above. -/
theorem on_subdisk [CompleteSpace E] (h : Har f (closedBall (c0, c1) r)) (rp : r > 0) (ep : e > 0) :
    ∃ c0' t, t > 0 ∧ c0' ∈ closedBall c0 e ∧ AnalyticOnNhd ℂ f (ball c0' t ×ˢ ball c1 r) := by
  set re := min r e
  have esub : closedBall c0 re ⊆ closedBall c0 r :=
    Metric.closedBall_subset_closedBall (min_le_left _ _)
  generalize hS : (fun b : ℕ ↦
    {z0 | z0 ∈ closedBall c0 re ∧ ∀ z1, z1 ∈ closedBall c1 r → ‖f (z0, z1)‖ ≤ b}) = S
  have hc : ∀ b, IsClosed (S b) := by
    intro b; rw [← hS]; simp only [← forall_const_and_distrib]
    rw [Set.ofPred_forall]; apply isClosed_iInter; intro z1
    by_cases z1r : z1 ∉ closedBall c1 r
    · simp only [z1r, false_imp_iff, and_true, Set.ofPred_mem_eq, Metric.isClosed_closedBall]
    · rw [Set.not_notMem] at z1r
      simp only [z1r, true_imp_iff]
      refine ContinuousOn.isClosed_le Metric.isClosed_closedBall ?_ continuousOn_const
      apply ContinuousOn.norm
      exact ContinuousOn.mono (h.on0 z1r).continuousOn esub
  have hU : (interior (⋃ b, S b)).Nonempty := by
    refine Set.nonempty_of_mem
        (mem_interior.mpr ⟨ball c0 re, ?_, Metric.isOpen_ball, Metric.mem_ball_self (lt_min rp ep)⟩)
    rw [Set.subset_def]; intro z0 z0s; rw [Set.mem_iUnion]
    have z0s' := esub (ball_subset_closedBall z0s)
    rcases (isCompact_closedBall _ _).bddAbove_image (h.on1 z0s').continuousOn.norm with ⟨b, fb⟩
    simp only [mem_upperBounds, Set.forall_mem_image] at fb
    use Nat.ceil b; rw [← hS]; simp only [Set.mem_ofPred]
    refine ⟨ball_subset_closedBall z0s, ?_⟩
    simp only [Metric.mem_closedBall] at fb ⊢; intro z1 z1r
    exact _root_.trans (fb z1r) (Nat.le_ceil _)
  rcases NonemptyInterior.nonempty_interior_of_iUnion_of_closed hc hU with ⟨b, bi⟩
  rcases bi with ⟨c0', c0's⟩; use c0'
  rcases mem_interior.mp c0's with ⟨s', s's, so, c0s'⟩
  rcases Metric.isOpen_iff.mp so c0' c0s' with ⟨t, tp, ts⟩
  have tr : ball c0' t ⊆ closedBall c0 re := by
    rw [Set.subset_def]; intro z0 z0t
    have z0b := _root_.trans ts s's z0t
    rw [← hS] at z0b; simp only [Set.ofPred_and, Set.ofPred_mem_eq, Set.mem_inter_iff] at z0b
    exact z0b.left
  have c0e : c0' ∈ closedBall c0 e :=
    _root_.trans tr (Metric.closedBall_subset_closedBall (min_le_right _ _))
      (Metric.mem_ball_self tp)
  have fb : ∀ z, z ∈ ball c0' t ×ˢ ball c1 r → ‖f z‖ ≤ b := by
    intro z zs; rw [Set.mem_prod] at zs
    have zb := _root_.trans ts s's zs.left
    rw [← hS] at zb
    simp only [Metric.mem_ball, Metric.mem_closedBall, Set.mem_ofPred_eq] at zb zs
    have zb' := zb.right z.snd zs.right.le
    simp only [Prod.mk.eta] at zb'; exact zb'
  use t, tp, c0e
  refine of_bounded (h.mono ?_) (IsOpen.prod isOpen_ball isOpen_ball) fb
  rw [← closedBall_prod_same]
  exact Set.prod_mono (_root_.trans tr esub) Metric.ball_subset_closedBall

/-- Separate analyticity on a polydisk, full analyticity on a polydisk smaller in one direction.

    This records the situation in the stage of the proof after applying the Baire category theorem.
    -/
structure Uneven (f : ℂ × ℂ → E) (c0 c1 : ℂ) (r0 r1 : ℝ) : Prop where
  r0p : r0 > 0
  r1p : r1 > 0
  r01 : r0 ≤ r1
  h : Har f (closedBall (c0, c1) r1)
  a : AnalyticOnNhd ℂ f (ball c0 r0 ×ˢ ball c1 r1)

-- Teach `bound` about `Uneven`
attribute [bound_forward] Uneven.r0p Uneven.r1p Uneven.r01

/-- Exact diameter of complex ball -/
theorem diam_ball_eq {c : ℂ} {r : ℝ} (rp : r ≥ 0) : Metric.diam (ball c r) = 2 * r := by
  by_cases r0 : 0 = r
  · simp only [← r0, Metric.ball_zero, Metric.diam_empty, MulZeroClass.mul_zero]
  have rp' := Ne.lt_of_le r0 rp; clear r0
  apply le_antisymm (Metric.diam_ball rp)
  apply le_of_forall_small_le_add rp'; intro e ep er
  have m : ∀ t : ℝ, |t| ≤ 1 → c + t * (r - e / 2) ∈ ball c r := by
    intro t t1
    simp only [Complex.dist_eq, Metric.mem_ball, add_sub_cancel_left, norm_mul, Complex.norm_real]
    have re : r - e / 2 ≥ 0 := by linarith [_root_.trans (half_lt_self ep) er]
    calc |t| * ‖(↑r - ↑e / 2 : ℂ)‖
      _ = |t| * ‖(↑(r - e / 2) : ℂ)‖ := by
        simp only [Complex.ofReal_sub, Complex.ofReal_div]
        norm_num
      _ = |t| * (r - e / 2) := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg re]
      _ ≤ 1 * (r - e / 2) := mul_le_mul_of_nonneg_right t1 re
      _ = r - e / 2 := by ring
      _ < r - 0 := (sub_lt_sub_left (by linarith) r)
      _ = r := by ring
  have lo :=
    Metric.dist_le_diam_of_mem Metric.isBounded_ball (m 1 (by norm_num)) (m (-1) (by norm_num))
  have e : ‖(2 * ↑r - ↑e : ℂ)‖ = 2 * r - e := by
    have re : 2 * r - e ≥ 0 := by trans r - e; linarith; simp only [sub_nonneg, er.le]
    calc ‖(2 * ↑r - ↑e : ℂ)‖
      _ = ‖(↑(2 * r - e) : ℂ)‖ := by
        simp only [Complex.ofReal_sub, Complex.ofReal_mul]
        norm_num
      _ = 2 * r - e := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg re]
  simp only [Complex.dist_eq, Complex.ofReal_one, one_mul, Complex.ofReal_neg, neg_mul, neg_sub,
    add_sub_add_left_eq_sub] at lo
  ring_nf at lo; rw [mul_comm, e] at lo; linarith

/-- Exact diameter of complex closed ball -/
theorem diam_closedBall_eq {c : ℂ} {r : ℝ} (rp : r ≥ 0) : Metric.diam (closedBall c r) = 2 * r := by
  apply le_antisymm (Metric.diam_closedBall rp)
  trans Metric.diam (ball c r)
  rw [diam_ball_eq rp]
  exact Metric.diam_mono Metric.ball_subset_closedBall Metric.isBounded_closedBall

/-- If a ball is contained in a closed ball, the radii must be `≤` -/
theorem le_of_ball_subset_closedBall {z0 z1 : ℂ} {r0 r1 : ℝ} (r0p : r0 ≥ 0) (r1p : r1 ≥ 0) :
    ball z0 r0 ⊆ closedBall z1 r1 → r0 ≤ r1 := by
  intro s
  have m := Metric.diam_mono s Metric.isBounded_closedBall
  rw [diam_ball_eq r0p, diam_closedBall_eq r1p] at m; linarith

/-- Given separate analyticity on a polydisk, find an uneven subpolydisk s.t. fixing the
    unevenness covers the center. -/
theorem to_uneven [CompleteSpace E] (h : Har f (closedBall (c0, c1) r)) (rp : r > 0) :
    ∃ c0' r0 r1, ball c0' r1 ⊆ closedBall c0 r ∧ c0 ∈ ball c0' r1 ∧ Uneven f c0' c1 r0 r1 := by
  have r4p : r / 4 > 0 := by linarith
  rcases on_subdisk h rp r4p with ⟨c0', r0, r0p, m, a⟩
  simp only [Metric.mem_closedBall] at m
  have sub : closedBall c0' (r / 2) ⊆ closedBall c0 r := by
    apply Metric.closedBall_subset_closedBall'
    calc
      r / 2 + dist c0' c0 ≤ r / 2 + r / 4 := by linarith
      _ = 3 / 4 * r := by ring
      _ ≤ 1 * r := by linarith
      _ = r := by ring
  have r01 : min r0 (r / 2) ≤ r / 2 := by bound
  have c0m : c0 ∈ ball c0' (r / 2) := by
    simp only [Metric.mem_ball]; rw [dist_comm]; apply lt_of_le_of_lt m; bound
  have h' : Har f (closedBall (c0', c1) (r / 2)) := by
    refine Har.mono ?_ h; simp only [← closedBall_prod_same]; apply Set.prod_mono
    assumption; apply Metric.closedBall_subset_closedBall; linarith
  have a' : AnalyticOnNhd ℂ f (ball c0' (min r0 (r / 2)) ×ˢ ball c1 (r / 2)) := by
    apply a.mono; apply Set.prod_mono
    apply Metric.ball_subset_ball'
    simp only [dist_self, add_zero, min_le_iff, le_refl, true_or]
    apply Metric.ball_subset_ball; linarith
  use c0', min r0 (r / 2), r / 2, _root_.trans Metric.ball_subset_closedBall sub, c0m
  exact
    { r0p := by bound
      r1p := by bound
      r01
      h := h'
      a := a' }

/-- Power series terms along the first coordinate, arbitrary radius -/
@[nolint unusedArguments]
def unevenTerm' (_ : Uneven f c0 c1 r0 r1) (r : ℝ) (z1 : ℂ) (n : ℕ) : E :=
  (2 * π * I : ℂ)⁻¹ • ∮ z0 in C(c0, r), (z0 - c0)⁻¹ ^ n • (z0 - c0)⁻¹ • f (z0, z1)

/-- Power series terms along the first coordinate, `radius = r1` -/
def unevenTerm (u : Uneven f c0 c1 r0 r1) :=
  unevenTerm' u r1

/-- Power series along the first coordinate, arbitrary radius -/
def unevenSeries' (u : Uneven f c0 c1 r0 r1) (r : ℝ) (z1 : ℂ) : FormalMultilinearSeries ℂ ℂ E :=
  fun n ↦ ContinuousMultilinearMap.mkPiRing ℂ _ (unevenTerm' u r z1 n)

/-- Power series along the first coordinate, `radius = r1` -/
def unevenSeries (u : Uneven f c0 c1 r0 r1) :=
  unevenSeries' u r1

theorem unevenSeries_apply (u : Uneven f c0 c1 r0 r1) (r : ℝ) (z1 : ℂ) (n : ℕ) :
    (unevenSeries' u r z1 n fun _ ↦ 1) = unevenTerm' u r z1 n := by
  simp only [unevenSeries', ContinuousMultilinearMap.mkPiRing_apply, Finset.prod_const_one,
    one_smul]

theorem uneven_is_cauchy {u : Uneven f c0 c1 r0 r1} {r : ℝ} :
    unevenSeries' u r z1 = cauchyPowerSeries (fun z0 ↦ f (z0, z1)) c0 r := by
  funext; rw [unevenSeries', cauchyPowerSeries]; rfl

theorem Uneven.has_series [CompleteSpace E] (u : Uneven f c0 c1 r0 r1) {s : ℝ}
    (sp : 0 < s) (sr1 : s ≤ r1) (z1s : z1 ∈ closedBall c1 r1) :
    HasFPowerSeriesOnBall (fun z0 ↦ f (z0, z1)) (unevenSeries' u s z1) c0 (ENNReal.ofReal s) := by
  set sn := s.toNNReal
  have sns : s = sn := by simp only [Real.coe_toNNReal', sp.le, max_eq_left, sn]
  have snp : sn > 0 := Real.toNNReal_pos.mpr sp
  rw [uneven_is_cauchy]
  rw [sns, ← ENNReal.coe_nnreal_eq]
  refine DifferentiableOn.hasFPowerSeriesOnBall ?_ snp
  rw [← sns]
  refine DifferentiableOn.mono ?_ (Metric.closedBall_subset_closedBall sr1)
  exact AnalyticOnNhd.differentiableOn (u.h.on0 z1s)

theorem unevenTerm_eq [CompleteSpace E] (u : Uneven f c0 c1 r0 r1) {r : ℝ}
    (rp : r > 0) (rr1 : r ≤ r1) {z1 : ℂ} :
    z1 ∈ closedBall c1 r1 → unevenTerm' u r z1 = unevenTerm u z1 := by
  intro z1s; funext x
  have p0 := u.has_series rp rr1 z1s
  have p1 := u.has_series u.r1p (by rfl) z1s
  have h := HasFPowerSeriesAt.eq_formalMultilinearSeries p0.hasFPowerSeriesAt p1.hasFPowerSeriesAt
  clear p0 p1; simp only [unevenTerm, ←unevenSeries_apply, h]

theorem unevenSeries_eq [CompleteSpace E] (u : Uneven f c0 c1 r0 r1) {r : ℝ}
    (rp : r > 0) (rr1 : r ≤ r1) {z1 : ℂ} :
    z1 ∈ closedBall c1 r1 → unevenSeries' u r z1 = unevenSeries u z1 := by
  intro z1s; funext
  simp_rw [unevenSeries, unevenSeries', unevenTerm_eq u rp rr1 z1s,
    unevenTerm_eq u u.r1p (le_refl _) z1s]

theorem unevenSeries_norm (u : Uneven f c0 c1 r0 r1) {n : ℕ} :
    ‖unevenSeries u z1 n‖ = ‖unevenTerm u z1 n‖ := by
  rw [unevenSeries, unevenSeries', unevenTerm, ContinuousMultilinearMap.norm_mkPiRing]

/-- Our power series terms are uniformly bounded (away from the edges) -/
theorem unevenSeries_uniform_bound [CompleteSpace E] (u : Uneven f c0 c1 r0 r1) {s : ℝ}
    (sr : s < r1) :
    ∃ c a : ℝ, c > 0 ∧ a > 0 ∧ ∀ n z1, z1 ∈ closedBall c1 s →
      ‖unevenSeries u z1 n‖ ≤ c * a ^ n := by
  have fc : ContinuousOn f (sphere c0 (r0 / 2) ×ˢ closedBall c1 s) := by
    suffices fa' : AnalyticOnNhd ℂ f (sphere c0 (r0 / 2) ×ˢ closedBall c1 s) by exact fa'.continuousOn
    refine u.a.mono (Set.prod_mono ?_ ?_)
    · have rh : r0 / 2 < r0 := by linarith [u.r0p]
      exact _root_.trans Metric.sphere_subset_closedBall (Metric.closedBall_subset_ball rh)
    · exact Metric.closedBall_subset_ball (by linarith [u.r1p])
  rcases (((isCompact_sphere _ _).prod (isCompact_closedBall _ _)).bddAbove_image
    fc.norm).exists_ge 0 with ⟨b, bp, fb⟩
  simp only [Set.forall_mem_image] at fb
  use b + 1, (r0 / 2)⁻¹, lt_of_le_of_lt bp (lt_add_one _), inv_pos.mpr (half_pos u.r0p)
  intro n z1 z1s
  have r0hp : r0 / 2 > 0 := by linarith [u.r0p]
  have r0hr1 : r0 / 2 ≤ r1 := _root_.trans (by linarith [u.r0p]) u.r01
  set g := fun z0 ↦ f (z0, z1)
  have gc : ContinuousOn g (sphere c0 (r0 / 2)) :=
    ContinuousOn.comp fc (ContinuousOn.prodMk continuousOn_id continuousOn_const) fun z0 z0s ↦
      Set.mk_mem_prod z0s z1s
  have gb : ∀ z0, z0 ∈ sphere c0 (r0 / 2) → ‖g z0‖ ≤ b := fun z0 z0s ↦ fb (Set.mk_mem_prod z0s z1s)
  have cb := cauchy1_bound' r0hp b gc gb n; clear bp gc gb
  have e : (2 * π * I : ℂ)⁻¹ • (∮ z0 in C(c0, r0 / 2), (z0 - c0)⁻¹ ^ n • (z0 - c0)⁻¹ • g z0) =
      unevenTerm' u (r0 / 2) z1 n := rfl
  rw [e] at cb; clear e g
  rw [unevenTerm_eq u r0hp r0hr1 (Metric.closedBall_subset_closedBall sr.le z1s)] at cb
  rw [unevenSeries_norm u]; apply _root_.trans cb; bound

/-- Our power series terms are nonuniformly bounded as `O(s⁻¹^n)` for any `s < r1` -/
theorem unevenSeries_nonuniform_bound [CompleteSpace E] (u : Uneven f c0 c1 r0 r1) {s : ℝ}
    (sp : s > 0) (sr1 : s < r1) (z1s : z1 ∈ closedBall c1 r1) :
    ∃ c : ℝ, c > 0 ∧ ∀ n, ‖unevenSeries u z1 n‖ ≤ c * s⁻¹ ^ n := by
  have h := (Uneven.has_series u u.r1p (le_refl _) z1s).r_le
  rw [FormalMultilinearSeries.radius, le_iSup_iff] at h
  have sr := not_le_of_gt ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg sp.le).mpr sr1)
  specialize h (ENNReal.ofReal s); rw [imp_iff_not sr] at h
  simp only [not_forall, not_le, lt_iSup_iff] at h
  rcases h with ⟨t, c, th, st⟩
  have st' : s < ↑t := by
    rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff_of_nonneg sp.le] at st
    exact st
  have cp : c ≥ 0 := ge_trans (th 0) (by bound)
  use max 1 c, lt_of_lt_of_le (by norm_num) (le_max_left 1 c)
  intro n; specialize th n; rw [unevenSeries_eq u u.r1p (le_refl _) z1s] at th
  generalize hy : ‖unevenSeries u z1 n‖ = y; rw [hy] at th
  have tnz : (t : ℝ) ^ n ≠ 0 := pow_ne_zero _ (lt_trans sp st').ne'
  calc
    y = y * (↑t ^ n * (↑t ^ n)⁻¹) := by simp only [mul_inv_cancel₀ tnz, mul_one]
    _ = y * ↑t ^ n * (↑t ^ n)⁻¹ := by ring
    _ ≤ c * (↑t ^ n)⁻¹ := by bound
    _ ≤ c * (s ^ n)⁻¹ := by bound
    _ = c * s⁻¹ ^ n := by simp only [inv_pow]
    _ ≤ max 1 c * s⁻¹ ^ n := by bound

/-- `fun z0 ↦ (z0, 0)` as a continuous linear map -/
def idZeroLm : ℂ →L[ℂ] ℂ × ℂ :=
  ContinuousLinearMap.prod (ContinuousLinearMap.id ℂ ℂ) (0 : ℂ →L[ℂ] ℂ)

/-- Given a continuous multilinear map on two complex numbers, restrict to the slice along
    just the first -/
def ContinuousMultilinearMap.along0 {n : ℕ}
    (p : ContinuousMultilinearMap ℂ (fun _ : Fin n ↦ ℂ × ℂ) E) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n ↦ ℂ) E :=
  p.compContinuousLinearMap fun _ ↦ idZeroLm

/-- `.along0` reduces norms -/
theorem Along0.norm {n : ℕ} (p : ContinuousMultilinearMap ℂ (fun _ : Fin n ↦ ℂ × ℂ) E) :
    ‖p.along0‖ ≤ ‖p‖ := by
  have pp : 0 ≤ ‖p‖ := by bound
  apply p.along0.opNorm_le_bound pp
  intro m
  simp only [ContinuousMultilinearMap.along0,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have e : ∀ i : Fin n, ‖m i‖ = ‖idZeroLm (m i)‖ := by
    intro i
    simp only [idZeroLm, ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_id', id_eq,
      _root_.zero_apply, Prod.norm_def, norm_zero, norm_nonneg, sup_of_le_left]
  simp_rw [e]
  exact ContinuousMultilinearMap.le_opNorm p _

/-- `.along0` is linear -/
def Along0.linearMap (n : ℕ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n ↦ ℂ × ℂ) E →ₗ[ℂ]
      ContinuousMultilinearMap ℂ (fun _ : Fin n ↦ ℂ) E where
  toFun p := p.along0
  map_add' := by
    intro p q; simp_rw [ContinuousMultilinearMap.along0]
    apply ContinuousMultilinearMap.ext; intro m
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      _root_.add_apply]
  map_smul' := by
    intro s p; simp_rw [ContinuousMultilinearMap.along0]
    apply ContinuousMultilinearMap.ext; intro m
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      _root_.smul_apply, RingHom.id_apply]

/-- `.along0` is continuous linear -/
def Along0.continuousLinearMap (n : ℕ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n ↦ ℂ × ℂ) E →L[ℂ]
      ContinuousMultilinearMap ℂ (fun _ : Fin n ↦ ℂ) E := by
  refine LinearMap.mkContinuous (Along0.linearMap n) 1 ?_
  intro p; simp only [one_mul, Along0.linearMap]; exact Along0.norm p

/-- `.along0` for a whole power series -/
def FormalMultilinearSeries.along0 (p : FormalMultilinearSeries ℂ (ℂ × ℂ) E) :
    FormalMultilinearSeries ℂ ℂ E := fun n ↦ (p n).along0

/-- `.along0` increases radius of convergence -/
theorem Along0.radius (p : FormalMultilinearSeries ℂ (ℂ × ℂ) E) : p.radius ≤ p.along0.radius := by
  simp_rw [FormalMultilinearSeries.radius]
  refine iSup_mono ?_; intro r
  refine iSup_mono ?_; intro C
  refine iSup_mono' ?_; intro h
  have h' : ∀ n, ‖p.along0 n‖ * (r:ℝ)^n ≤ C := by
    intro n; refine le_trans ?_ (h n); apply mul_le_mul_of_nonneg_right
    exact Along0.norm (p n); bound
  use h'

/-- If `f : ℂ × ℂ → E` is analytic with series `p`, `fun z0 ↦ f (z0,z1)`
    is analytic with series `p.along0` -/
theorem HasFPowerSeriesAt.along0 {f : ℂ × ℂ → E} {c0 c1 : ℂ}
    {p : FormalMultilinearSeries ℂ (ℂ × ℂ) E} (fp : HasFPowerSeriesAt f p (c0, c1)) :
    HasFPowerSeriesAt (fun z0 ↦ f (z0, c1)) p.along0 c0 := by
  rcases fp with ⟨r, fpr⟩
  suffices h : HasFPowerSeriesOnBall (fun z0 ↦ f (z0, c1)) p.along0 c0 r by
    exact h.hasFPowerSeriesAt
  refine
    { r_le := le_trans fpr.r_le (Along0.radius p)
      r_pos := fpr.r_pos
      hasSum := ?_ }
  · intro w0 w0r
    simp_rw [FormalMultilinearSeries.along0, ContinuousMultilinearMap.along0, idZeroLm]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_id', id_eq,
      _root_.zero_apply]
    have w01r : (w0, (0 : ℂ)) ∈ Metric.eball (0 : ℂ × ℂ) r := by
      simpa only [Prod.edist_eq, Metric.mem_eball, Prod.fst_zero, Prod.snd_zero, edist_self,
        max_zero] using w0r
    convert fpr.hasSum w01r
    all_goals simp

/-- The map `p ↦ p.along0` is analytic -/
theorem Along0.analyticAt (n : ℕ) : ∀ {p},
      AnalyticAt ℂ (fun p : ContinuousMultilinearMap ℂ
        (fun _ : Fin n ↦ ℂ × ℂ) E => p.along0) p := by
  intro p
  have e : (fun p : ContinuousMultilinearMap ℂ (fun _ : Fin n ↦ ℂ × ℂ) E => p.along0) =ᶠ[𝓝 p]
      (Along0.continuousLinearMap n : (ContinuousMultilinearMap ℂ (fun _ : Fin n ↦ ℂ × ℂ) E →
        ContinuousMultilinearMap ℂ (fun _ : Fin n ↦ ℂ) E)) := by
    refine .of_forall ?_; intro _; rfl
  rw [analyticAt_congr e]; apply ContinuousLinearMap.analyticAt

/-- `unevenSeries u r1 z1` is analytic as a function of `z1` -/
theorem unevenSeries_analytic [CompleteSpace E] (u : Uneven f c0 c1 r0 r1) (n : ℕ) :
    AnalyticOnNhd ℂ (fun z1 ↦ unevenSeries u z1 n) (ball c1 r1) := by
  intro z1 z1s
  rcases u.a (c0, z1) (Set.mk_mem_prod (Metric.mem_ball_self u.r0p) z1s) with ⟨p, r, hp⟩
  have pa := (p.hasFPowerSeriesOnBall_changeOrigin n (lt_of_lt_of_le hp.r_pos hp.r_le)).analyticAt
  set g := fun w1 ↦ ((0 : ℂ), w1 - z1)
  have ga : AnalyticOnNhd ℂ g univ := by
    rw [Complex.analyticOnNhd_univ_iff_differentiable]
    exact (differentiable_const _).prodMk (differentiable_id.sub (differentiable_const _))
  have g0 : 0 = g z1 := by aesop
  rw [g0] at pa
  have ta := pa.comp (ga z1 (Set.mem_univ _))
  simp_rw [Function.comp_def] at ta; clear pa ga g0
  have pu : ∀ᶠ w1 in nhds z1, unevenSeries u w1 n = (p.changeOrigin (g w1)).along0 n := by
    rw [eventually_nhds_iff]
    set s' := r1 - dist z1 c1
    set s := min r (ENNReal.ofReal s')
    have s'p : s' > 0 := by simp only [Metric.mem_ball] at z1s; bound
    have sp : s > 0 := by bound
    have sr : s ≤ r := by bound
    have sb : Metric.eball z1 s ⊆ ball c1 r1 := by
      rw [Set.subset_def]; intro x xs
      simp only [Metric.mem_ball, Metric.mem_eball, lt_min_iff, edist_lt_ofReal, s] at xs z1s ⊢
      calc dist x c1
        _ ≤ dist x z1 + dist z1 c1 := by bound
        _ < s' + dist z1 c1 := (add_lt_add_left xs.right _)
        _ = r1 - dist z1 c1 + dist z1 c1 := rfl
        _ = r1 := by ring_nf
    use Metric.eball z1 s
    refine ⟨?_, Metric.isOpen_eball, Metric.mem_eball_self sp⟩
    intro w1 w1s
    have p0 : HasFPowerSeriesAt (fun z0 ↦ f (z0, w1)) (unevenSeries u w1) c0 := by
      have w1c : w1 ∈ closedBall c1 r1 := ball_subset_closedBall (sb w1s)
      refine (Uneven.has_series u u.r1p (le_refl _) w1c).hasFPowerSeriesAt
    have p1 : HasFPowerSeriesAt (fun z0 ↦ f (z0, w1)) (p.changeOrigin (g w1)).along0 c0 := by
      have wz : ↑‖((0 : ℂ), w1 - z1)‖₊ < r := by
        simp only [Metric.mem_eball, edist_dist, Complex.dist_eq, ofReal_norm,
          enorm_eq_nnnorm] at w1s
        simp only [Prod.nnnorm_mk, nnnorm_zero, zero_le, sup_of_le_right]
        exact lt_of_lt_of_le w1s sr
      convert (hp.changeOrigin wz).hasFPowerSeriesAt.along0
      · simp only [add_sub_cancel]
      · simp only [add_zero]
    rw [HasFPowerSeriesAt.eq_formalMultilinearSeries p0 p1]
  rw [analyticAt_congr pu]
  exact (Along0.analyticAt _).comp ta

/-- `unevenTerm u z1 n` is analytic as a function of `z1` -/
theorem unevenTerm.analytic [CompleteSpace E] (u : Uneven f c0 c1 r0 r1) (n : ℕ) :
    AnalyticOnNhd ℂ (fun z1 ↦ unevenTerm u z1 n) (ball c1 r1) := by
  have e : ∀ z1, unevenTerm u z1 n =
      (cmmapApplyCmap ℂ (fun _ : Fin n ↦ ℂ) E fun _ ↦ 1) (unevenSeries u z1 n) := by
    intro z1
    simp [unevenTerm, ← unevenSeries_apply, cmmapApplyCmap_apply, unevenSeries]
  simp_rw [e]
  exact ContinuousLinearMap.comp_analyticOnNhd _ (unevenSeries_analytic u n)

/-- The subharmonic functions we'll apply Hartogs's lemma to -/
def unevenLog (u : Uneven f c0 c1 r0 r1) (n : ℕ) (z1 : ℂ) : ℝ :=
  (↑n)⁻¹ * maxLog (-1) ‖r1 ^ n • unevenTerm u z1 n‖

/-- Uniform bound on `unevenTerm` in terms of `unevenLog` -/
theorem unevenLog_uniform_bound [CompleteSpace E] (u : Uneven f c0 c1 r0 r1) {s : ℝ} (sr : s < r1) :
    ∃ b : ℝ, ∀ n z1, z1 ∈ closedBall c1 s → unevenLog u n z1 ≤ b := by
  rcases unevenSeries_uniform_bound u sr with ⟨c, a, _, ap, h⟩
  use maxLog 0 (r1 * (max 1 c * a)); intro n z zs; specialize h n z zs
  simp_rw [unevenSeries_norm] at h; rw [unevenLog]
  by_cases n0 : n = 0
  · simp only [n0, CharP.cast_eq_zero, inv_zero, pow_zero, one_smul, zero_mul, le_maxLog]
  have np : n ≥ 1 := Nat.one_le_of_lt (Nat.pos_of_ne_zero n0)
  rw [inv_mul_le_iff₀ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero n0) : 0 < (n : ℝ))]
  apply maxLog_le; trans (0 : ℝ); norm_num; bound
  simp only [norm_smul, abs_of_pos u.r1p, norm_pow, Real.norm_eq_abs]
  trans r1 ^ n * (c * a ^ n); bound
  rw [Real.exp_nat_mul]
  trans (r1 * (max 1 c * a)) ^ n
  simp only [mul_pow]
  gcongr
  · bound
  · trans max 1 c
    · bound
    · bound
  · bound

/-- Nonuniform bound on `unevenTerm` in terms of `unevenLog` -/
theorem unevenLog_nonuniform_bound [CompleteSpace E] (u : Uneven f c0 c1 r0 r1)
    (z1s : z1 ∈ closedBall c1 r1) : ∀ d, d > 0 → ∀ᶠ n in atTop, unevenLog u n z1 ≤ d := by
  intro d dp
  rcases exists_between dp with ⟨e, ep, ed⟩
  set s := r1 / e.exp
  have sp : s > 0 := by bound
  have sr : s < r1 := by bound
  rcases unevenSeries_nonuniform_bound u sp sr z1s with ⟨c, cp, us⟩
  -- Choose m large enough to make c negligible
  rcases exists_nat_gt (max 1 (c.log / (d - e))) with ⟨m, mb⟩
  have mp : 0 < (m : ℝ) := lt_of_lt_of_le zero_lt_one (le_trans (by bound) mb.le)
  rw [Filter.eventually_atTop]; use m; intro n mn; specialize us n
  generalize ht : ‖unevenTerm u z1 n‖ = t
  rw [unevenSeries_norm, ht] at us
  clear z1s
  -- Prove the desired bound
  rw [unevenLog, inv_mul_le_iff₀ (lt_of_lt_of_le mp (Nat.cast_le.mpr mn))]
  apply maxLog_le; trans (0 : ℝ); norm_num; bound
  have nb : c.log / (d - e) ≤ n := le_trans (le_trans (by bound) mb.le) (Nat.cast_le.mpr mn)
  calc ‖r1 ^ n • unevenTerm u z1 n‖
    _ = r1 ^ n * t := by
      simp only [← ht, norm_smul, abs_of_pos u.r1p, norm_pow, Real.norm_eq_abs]
    _ ≤ r1 ^ n * (c * s⁻¹ ^ n) := by bound
    _ = r1 ^ n * (c * (e.exp ^ n / r1 ^ n)) := by rw [inv_div, div_pow]
    _ = r1 ^ n / r1 ^ n * c * e.exp ^ n := by ring
    _ = c * e.exp ^ n := by field_simp [(pow_pos u.r1p _).ne']
    _ = c * (↑n * e).exp := by rw [Real.exp_nat_mul]
    _ = c * (↑n * d - ↑n * (d - e)).exp := by ring_nf
    _ = c.log.exp * ((↑n * d).exp / (↑n * (d - e)).exp) := by rw [Real.exp_sub, Real.exp_log cp]
    _ = c.log.exp / (↑n * (d - e)).exp * (↑n * d).exp := by ring_nf
    _ = (c.log - ↑n * (d - e)).exp * (↑n * d).exp := by rw [Real.exp_sub]
    _ ≤ (c.log - c.log / (d - e) * (d - e)).exp * (↑n * d).exp := by bound
    _ ≤ (↑n * d).exp := by field_simp [(sub_pos.mpr ed).ne']; simp

/-- Our `maxLog` function is subharmonic -/
theorem uneven_nonuniform_subharmonic [CompleteSpace E] [SecondCountableTopology E]
    (u : Uneven f c0 c1 r0 r1) (n : ℕ) :
    SubharmonicOn (unevenLog u n) (ball c1 r1) := by
  refine SubharmonicOn.const_mul ?_ (by bound)
  apply AnalyticOnNhd.maxLog_norm_subharmonicOn _ (-1)
  rw [Complex.analyticOnNhd_iff_differentiableOn Metric.isOpen_ball]
  apply DifferentiableOn.const_smul
  rw [← Complex.analyticOnNhd_iff_differentiableOn Metric.isOpen_ball]
  apply unevenTerm.analytic u

/-- The nonuniform bound holds uniformly -/
theorem unevenSeries_strong_bound [CompleteSpace E] [SecondCountableTopology E]
    (u : Uneven f c0 c1 r0 r1) {s : ℝ} (sp : 0 < s) (sr : s < r1) :
    ∀ᶠ n in atTop, ∀ z1, z1 ∈ closedBall c1 s → ‖unevenSeries u z1 n‖ ≤ s⁻¹ ^ n := by
  rcases exists_between sr with ⟨t, ts, tr⟩
  have tp : t > 0 := _root_.trans ts sp
  have trs : closedBall c1 t ⊆ ball c1 r1 := Metric.closedBall_subset_ball tr
  have cs : closedBall c1 t ⊆ closedBall c1 r1 :=
    Metric.closedBall_subset_closedBall tr.le
  have ks : closedBall c1 s ⊆ interior (closedBall c1 t) := by
    rw [interior_closedBall _ tp.ne']; exact Metric.closedBall_subset_ball ts
  rcases unevenLog_uniform_bound u tr with ⟨b, fb⟩
  have H := SubharmonicOn.hartogs (fun n ↦ (uneven_nonuniform_subharmonic u n).mono trs) fb
      (fun z zs ↦ unevenLog_nonuniform_bound u (cs zs)) (isCompact_closedBall _ _) ks
  specialize H (r1 / s).log (by bound)
  refine H.mp ((Filter.eventually_gt_atTop 0).mp (.of_forall ?_))
  intro n np h z zs; specialize h z zs
  rw [unevenSeries_norm]
  rw [unevenLog, inv_mul_le_iff₀ (Nat.cast_pos.mpr np : 0 < (n : ℝ))] at h
  simp only [norm_smul, abs_of_pos u.r1p, norm_pow, Real.norm_eq_abs] at h
  have a := le_of_maxLog_le h
  rw [Real.exp_nat_mul, Real.exp_log (div_pos u.r1p sp), div_eq_mul_inv, mul_pow] at a
  --rw [Real.exp_nat_mul, Real.exp_log (div_pos u.r1p sp), div_eq_mul_inv, mul_pow, abs_pow,
  --  abs_of_pos u.r1p] at a
  exact (mul_le_mul_iff_right₀ (by bound)).mp a

/-- The nonuniform bound holds uniformly, without `∀ᶠ` -/
theorem unevenSeries_strong_bound' [CompleteSpace E] [SecondCountableTopology E]
    (u : Uneven f c0 c1 r0 r1) {s : ℝ} (sp : s > 0) (sr : s < r1) :
    ∃ c, c ≥ 0 ∧ ∀ n, ∀ z1, z1 ∈ closedBall c1 s → ‖unevenSeries u z1 n‖ ≤ c * s⁻¹ ^ n := by
  rcases Filter.eventually_atTop.mp (unevenSeries_strong_bound u sp sr) with ⟨n, h⟩
  set g := fun z1 ↦ partialSups (fun k ↦ s ^ k * ‖unevenSeries u z1 k‖) n
  have gc : ContinuousOn g (closedBall c1 s) := by
    apply ContinuousOn.partialSups; intro n; apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.norm
    exact (unevenSeries_analytic u n).continuousOn.mono (Metric.closedBall_subset_ball sr)
  rcases ((isCompact_closedBall _ _).bddAbove_image gc).exists_ge 0 with ⟨b, bp, gb⟩
  simp only [Set.forall_mem_image, partialSups_le_iff, g] at gb
  use max 1 b, le_max_of_le_right bp; intro k z zs
  by_cases kn : k ≤ n
  · specialize gb zs k kn
    calc ‖unevenSeries u z k‖
      _ = s⁻¹ ^ k * (s ^ k * ‖unevenSeries u z k‖) := by
        ring_nf; field_simp [(pow_pos sp _).ne']
        simp only [one_div, inv_pow, mul_assoc]
        rw [mul_inv_cancel₀ (pow_ne_zero k (ne_of_lt sp).symm)]
        simp
      _ ≤ s⁻¹ ^ k * b := by bound
      _ = b * s⁻¹ ^ k := by ring_nf
      _ ≤ max 1 b * s⁻¹ ^ k := by bound
  · simp only [not_le] at kn; apply le_trans (h k kn.le z zs)
    calc s⁻¹ ^ k
      _ = 1 * s⁻¹ ^ k := by simp only [one_mul]
      _ ≤ max 1 b * s⁻¹ ^ k := by bound

-- This should go somewhere else
theorem fst_snd_eq {A B : Type} (p : A × B) : (p.fst, p.snd) = p := by simp only [Prod.mk.eta]

/-- `f` is bounded away from the (now even!) edges -/
theorem uneven_bounded [CompleteSpace E] [SecondCountableTopology E]
    (u : Uneven f c0 c1 r0 r1) {s : ℝ} (sp : s > 0) (sr : s < r1) :
    ∃ b, b ≥ 0 ∧ ∀ z, z ∈ ball (c0, c1) s → ‖f z‖ ≤ b := by
  rcases exists_between sr with ⟨t, ts, tr⟩
  have tp : t > 0 := _root_.trans ts sp
  rcases unevenSeries_strong_bound' u tp tr with ⟨c, cp, ch⟩
  use c * (1 - s / t)⁻¹, by bound
  intro z zs
  simp only [Prod.dist_eq, Metric.mem_ball, max_lt_iff] at zs
  have z1t : z.2 ∈ closedBall c1 t := by
    simp only [Metric.mem_closedBall]; exact le_trans zs.2.le ts.le
  have z1r : z.2 ∈ closedBall c1 r1 := Metric.closedBall_subset_closedBall tr.le z1t
  have ds : z.1 - c0 ∈ Metric.ball (0 : ℂ) s := by
    simp only [Complex.dist_eq] at zs
    simp only [zs.1, mem_ball_zero_iff]
  have ds' : z.1 - c0 ∈ Metric.eball (0 : ℂ) (ENNReal.ofReal s) := by rwa [Metric.eball_ofReal]
  have hs := (u.has_series sp sr.le z1r).hasSum ds'
  simp only [unevenSeries_eq u sp sr.le z1r,
    FormalMultilinearSeries.apply_eq_pow_smul_coeff, add_sub_cancel, Prod.mk.eta] at hs
  set g := fun n : ℕ ↦ c * (s / t) ^ n
  have gs : HasSum g (c * (1 - s / t)⁻¹) := HasSum.mul_left _
    (hasSum_geometric_of_lt_one (by bound) (by bound))
  apply HasSum.norm_le_of_bounded hs gs
  intro n
  simp only [mem_ball_zero_iff] at ds
  simp only [norm_smul, norm_pow, ← FormalMultilinearSeries.norm_apply_eq_norm_coef]
  calc ‖z.1 - c0‖ ^ n * ‖unevenSeries u z.2 n‖
    _ ≤ s ^ n * (c * t⁻¹ ^ n) := by bound [ch n _ z1t]
    _ = c * (s ^ n * t⁻¹ ^ n) := by ring_nf
    _ = c * (s / t) ^ n := by rw [← mul_pow, ← div_eq_mul_inv]

end Hartogs

/-- Hartogs's theorem on `ℂ × ℂ`: separately analytic functions are jointly analytic -/
public theorem Pair.hartogs {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [SecondCountableTopology E] {f : ℂ × ℂ → E} {s : Set (ℂ × ℂ)} (so : IsOpen s)
    (fa0 : ∀ c0 c1, (c0, c1) ∈ s → AnalyticAt ℂ (fun z0 ↦ f (z0, c1)) c0)
    (fa1 : ∀ c0 c1, (c0, c1) ∈ s → AnalyticAt ℂ (fun z1 ↦ f (c0, z1)) c1) : AnalyticOnNhd ℂ f s := by
  have h : Har f s := ⟨fa0, fa1⟩
  intro c cs
  rcases Metric.isOpen_iff.mp so c cs with ⟨r, rp, rs⟩
  rcases exists_between rp with ⟨t, tp, tr⟩
  have bs : closedBall (c.1, c.2) t ⊆ s := by
    refine _root_.trans ?_ rs; simp only [fst_snd_eq]; exact Metric.closedBall_subset_ball tr
  rcases to_uneven (h.mono bs) tp with ⟨c0', r0, r1, us, c0s, u⟩
  have cr : ‖c.1 - c0'‖ < r1 := by
    simp only [Complex.dist_eq, Metric.mem_ball] at c0s; exact c0s
  rcases exists_between cr with ⟨v, vc, vr⟩
  rcases uneven_bounded u (lt_of_le_of_lt (norm_nonneg _) vc) vr with ⟨b, _, fb⟩
  have fa := of_bounded (h.mono ?_) Metric.isOpen_ball fb
  · apply fa
    simp only [Metric.mem_ball, Prod.dist_eq, Complex.dist_eq, dist_self, norm_nonneg,
      sup_of_le_left, vc]
  · refine _root_.trans ?_ bs
    simp_rw [← ball_prod_same, ← closedBall_prod_same, Set.prod_subset_prod_iff]; apply Or.inl
    use _root_.trans (Metric.ball_subset_ball vr.le) us
    have r1t := le_of_ball_subset_closedBall u.r1p.le tp.le us
    exact _root_.trans Metric.ball_subset_closedBall
        (Metric.closedBall_subset_closedBall (_root_.trans vr.le r1t))

/-- Hartog's theorem near a point: local separate analyticity implies `AnalyticAt` -/
public theorem Pair.hartogs_at {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [SecondCountableTopology E] {f : ℂ × ℂ → E} {c : ℂ × ℂ}
    (fa0 : ∀ᶠ p : ℂ × ℂ in 𝓝 c, AnalyticAt ℂ (fun z0 ↦ f (z0, p.2)) p.1)
    (fa1 : ∀ᶠ p : ℂ × ℂ in 𝓝 c, AnalyticAt ℂ (fun z1 ↦ f (p.1, z1)) p.2) : AnalyticAt ℂ f c := by
  rcases eventually_nhds_iff.mp (fa0.and fa1) with ⟨s, fa, o, cs⟩
  exact Pair.hartogs o (fun c0 c1 m ↦ (fa _ m).1) (fun c0 c1 m ↦ (fa _ m).2) c cs
