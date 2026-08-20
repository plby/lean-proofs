module
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Tactic.Bound
import ErdosProblems.Erdos515.External.Ray.Misc.Connected
import ErdosProblems.Erdos515.External.Ray.Misc.Topology

/-!
## Continuation of a function from a convex set to its closure

We give an abstract version of "analytic continuation" from a convex set to its compact closure,
assuming that local continuation is possible at each boundary point.  We do not refer to analytic
functions directly at all: instead we speak of functions which everywhere satisfy a predicate
`p : (E → α) → E → Prop` where `E` is a normed space and `α : Type`.

Convexity is used only to guarantee a "good open cover" in the sense of
https://ncatlab.org/nlab/show/good+open+cover: a family of neighborhoods such that intersections
of neighborhoods are contractable.  Since our base set `s` is convex, we can use balls as good
neighborhoods, and all intersections are convex and thus contractable.

It would be better to define good neighborhoods directly and show that nice spaces have them,
but this may require a lot of machinery to cover manifolds in particular: the nLab page uses
the existence of Riemannian metrics.
-/

open Classical
open Filter (Tendsto atTop)
open Metric (ball closedBall isOpen_ball mem_ball mem_ball_self closedBall_zero)
open Set
open scoped Real Topology
noncomputable section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {α : Type} {p : (E → α) → E → Prop} {s : Set E} {f : E → α} {z : E}

-- Continuation of a functional equation from an open convex set to its closure
section Continuation

/-- Information we need to continue a function from a convex set `s` to `closure s`, while
    preserving local properties of the function.  Such properties are represented by an abstract
    `p : (E → α) → E → Prop`, where `p f x` means `f` is a valid germ at `x`. -/
public structure Base (p : (E → α) → E → Prop) (s : Set E) (f : E → α) : Prop where
  /-- The base set is convex -/
  convex : Convex ℝ s
  /-- Its closure is compact, so that we can stitch together finitely many local continuations -/
  compact : IsCompact (closure s)
  /-- `p f x` is a local property of `f` near `x` -/
  congr : ∀ {f g x}, p f x → f =ᶠ[𝓝 x] g → p g x
  /-- `f` is valid near each `x ∈ s` -/
  start : ∀ᶠ x in 𝓝ˢ s, p f x
  /-- Given `x ∈ closure s`, we can continue `f` to a neighorhood of `x` -/
  point : ∀ {x}, x ∈ closure s → ∃ g, (∀ᶠ z in 𝓝 x, p g z) ∧ ∃ᶠ z in 𝓝 x, z ∈ s ∧ g z = f z
  /-- If `f0, f1` are valid on an open preconnected set, and match somewhere,
      they match everywhere -/
  unique : ∀ {f0 f1 : E → α} {t : Set E}, IsOpen t → IsPreconnected t →
    (∀ x, x ∈ t → p f0 x) → (∀ x, x ∈ t → p f1 x) → (∃ x, x ∈ t ∧ f0 x = f1 x) → EqOn f0 f1 t

/-- There is a ball around each `x ∈ closure s` with an associated defined `g` -/
lemma Base.ball (b : Base p s f) (x : closure s) :
    ∃ g r, 0 < r ∧ (∀ z, z ∈ ball (x : E) r → p g z) ∧ g =ᶠ[𝓝ˢ (s ∩ ball (x : E) r)] f := by
  rcases x with ⟨x, m⟩; simp only
  rcases b.point m with ⟨g, pg, e⟩
  rcases Metric.eventually_nhds_iff_ball.mp pg with ⟨r, rp, pg⟩
  rcases Filter.frequently_iff.mp e (Metric.ball_mem_nhds _ rp) with ⟨y, yb, ys, e⟩
  use g, r, rp, fun z zr ↦ pg z zr
  simp only [Filter.EventuallyEq, Filter.eventually_iff, mem_nhdsSet_iff_forall]
  intro z ⟨zs, zr⟩; simp only [← Filter.eventually_iff]
  have n : {z | p g z ∧ p f z} ∈ 𝓝ˢ (s ∩ Metric.ball x r) := by
    refine Filter.inter_mem ?_ ?_
    · exact nhdsSet_mono inter_subset_right (Filter.mem_of_superset isOpen_ball.mem_nhdsSet_self pg)
    · exact nhdsSet_mono inter_subset_left b.start
  rcases local_preconnected_nhdsSet (b.convex.inter (convex_ball _ _)).isPreconnected n with
    ⟨u, uo, iu, up, uc⟩
  have eq := b.unique uo uc (fun _ m ↦ (up m).1) (fun _ m ↦ (up m).2) ⟨y, iu ⟨ys, yb⟩, e⟩
  exact eq.eventuallyEq_of_mem (uo.mem_nhds (iu ⟨zs, zr⟩))

/-- A particular `g` that continues `f` near `x` -/
def Base.g (b : Base p s f) (x : closure s) : E → α :=
  choose (b.ball x)

/-- The radius on which `g` is valid around `x` -/
def Base.r (b : Base p s f) (x : closure s) : ℝ :=
  choose (choose_spec (b.ball x))

/-- The radius is positive -/
lemma Base.rp (b : Base p s f) (x : closure s) : 0 < b.r x :=
  (choose_spec (choose_spec (b.ball x))).1

/-- `g` is valid on `ball x r`-/
lemma Base.gp (b : Base p s f) (x : closure s) (m : z ∈ Metric.ball (x : E) (b.r x)) :
    p (b.g x) z :=
  (choose_spec (choose_spec (b.ball x))).2.1 _ m

/-- `g` matches `f` where they are both defined -/
lemma Base.gf (b : Base p s f) (x : closure s) :
    b.g x =ᶠ[𝓝ˢ (s ∩ Metric.ball (x : E) (b.r x))] f :=
  (choose_spec (choose_spec (b.ball x))).2.2

/-- There exists a finite subcover of the `g` balls -/
lemma Base.exists_cover (b : Base p s f) :
    ∃ c : Finset (closure s), closure s ⊆ ⋃ (x) (_ : x ∈ c), Metric.ball (x : E) (b.r x) := by
  refine b.compact.elim_finite_subcover (fun x : closure s ↦ Metric.ball (x : E) (b.r x))
    (fun _ ↦ isOpen_ball) ?_
  intro x m; exact mem_iUnion_of_mem ⟨x, m⟩ (mem_ball_self (b.rp ⟨x, m⟩))

/-- Choose a finite subcover of the `g` balls -/
def Base.c (b : Base p s f) : Finset (closure s) :=
  choose b.exists_cover

/-- The union of our chosen finite set of `g` balls -/
def Base.t (b : Base p s f) : Set E :=
  ⋃ (x) (_ : x ∈ b.c), Metric.ball (x : E) (b.r x)

/-- Map a point in the union of our ball cover to one ball that contains it -/
def Base.y (b : Base p s f) (m : z ∈ b.t) : closure s :=
  choose (mem_iUnion.mp m)

lemma Base.yt (b : Base p s f) (m : z ∈ b.t) : z ∈ Metric.ball (b.y m : E) (b.r (b.y m)) := by
  simp only [Base.t, Base.y, mem_iUnion] at m ⊢; exact choose_spec (choose_spec m)

lemma Base.ot (b : Base p s f) : IsOpen b.t :=
  isOpen_iUnion fun _ ↦ isOpen_iUnion fun _ ↦ isOpen_ball

theorem Base.cover (b : Base p s f) : closure s ⊆ b.t :=
  choose_spec b.exists_cover

/-- Given two intersecting balls centered in `closure s`, their intersection touches `s` -/
theorem Convex.inter_ball (c : Convex ℝ s) (x0 x1 : closure s) {r0 r1 : ℝ} (r0p : 0 < r0)
    (r1p : 0 < r1) (ne : ∃ z, z ∈ ball (x0 : E) r0 ∩ ball (x1 : E) r1) :
    ∃ w, w ∈ s ∩ ball (x0 : E) r0 ∩ ball (x1 : E) r1 := by
  rcases x0 with ⟨x0, m0⟩; rcases x1 with ⟨x1, m1⟩; simp only
  have x01 : ‖x1 - x0‖ < r0 + r1 := by
    rcases ne with ⟨z, m0, m1⟩; simp only [mem_ball, dist_eq_norm] at m0 m1
    calc ‖x1 - x0‖
      _ = ‖z - x0 - (z - x1)‖ := by abel_nf
      _ ≤ ‖z - x0‖ + ‖z - x1‖ := (norm_sub_le _ _)
      _ < r0 + r1 := add_lt_add m0 m1
  have sub : ∀ (x : E) {a b : ℝ}, 0 < a → 0 < b → (a / (a + b)) • x - x = -((b / (a + b)) • x) := by
    intro x a b ap bp; have rnz := (add_pos ap bp).ne'
    calc (a / (a + b)) • x - x
      _ = (a / (a + b) - (a + b) / (a + b)) • x := by simp only [one_smul, sub_smul, div_self rnz]
      _ = -((b / (a + b)) • x) := by rw [← sub_div, sub_add_cancel_left, neg_div, neg_smul]
  have le : ∀ {a : ℝ}, 0 < a → a / (r0 + r1) * ‖x1 - x0‖ < a := by
    intro a ap; apply lt_of_lt_of_le (mul_lt_mul_of_pos_left x01 (div_pos ap (add_pos r0p r1p)))
    rw [div_mul_cancel₀ _ (add_pos r0p r1p).ne']
  have e : ∀ᶠ p : E × E in 𝓝 (x0, x1),
      (r1 / (r0 + r1)) • p.1 + (r0 / (r0 + r1)) • p.2 ∈ ball x0 r0 ∩ ball x1 r1 := by
    refine ContinuousAt.eventually_mem ?_ ((isOpen_ball.inter isOpen_ball).mem_nhds ?_)
    · exact ((continuous_fst.const_smul _).add (continuous_snd.const_smul _)).continuousAt
    · simp only [mem_inter_iff, mem_ball, dist_eq_norm, ← sub_add_eq_add_sub _ x0 _,
        add_sub_assoc _ _ x1]
      nth_rw 1 [add_comm r0 r1]; simp only [sub _ r0p r1p, sub _ r1p r0p]
      simp only [add_comm r1 r0, neg_add_eq_sub, ← sub_eq_add_neg, ← smul_sub, norm_smul,
        Real.norm_eq_abs, abs_div, abs_of_pos r0p, abs_of_pos r1p, abs_of_pos (add_pos r0p r1p),
        norm_sub_rev (x0 : E) x1]
      use le r0p, le r1p
  have f : ∃ᶠ p : E × E in 𝓝 (x0, x1), p.1 ∈ s ∧ p.2 ∈ s := by
    simp only [nhds_prod_eq]; rw [Prod.frequently (p := fun x ↦ x ∈ s) (q := fun x ↦ x ∈ s)]
    use mem_closure_iff_frequently.mp m0, mem_closure_iff_frequently.mp m1
  rcases(f.and_eventually e).exists with ⟨⟨z0, z1⟩, ⟨m0, m1⟩, m⟩
  refine ⟨_, ⟨?_, m.1⟩, m.2⟩
  apply c m0 m1; bound; bound
  simp only [← add_div, add_comm r1 r0, div_self (add_pos r0p r1p).ne']

/-- Our full continuation `u` throughout `closure s` -/
public def Base.u (b : Base p s f) : E → α := fun z ↦
  if m : z ∈ b.t then b.g (b.y m) z else f z

/-- The continuation `u` is equal to each `g` -/
theorem Base.ug (b : Base p s f) (x : closure s) :
    EqOn b.u (b.g x) (b.t ∩ Metric.ball (x : E) (b.r x)) := by
  intro z ⟨zt, m⟩; simp only [Base.u, zt, dif_pos]
  refine b.unique (isOpen_ball.inter isOpen_ball)
    ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected
    (fun _ m ↦ b.gp _ (inter_subset_left m)) (fun _ m ↦ b.gp _ (inter_subset_right m))
    ?_ ⟨b.yt zt, m⟩
  rcases b.convex.inter_ball (b.y zt) x (b.rp _) (b.rp _) ⟨_, ⟨b.yt zt, m⟩⟩ with ⟨w, m⟩
  exact ⟨w, ⟨m.1.2, m.2⟩, _root_.trans ((b.gf _).self_of_nhdsSet ⟨m.1.1, m.1.2⟩)
    ((b.gf x).self_of_nhdsSet ⟨m.1.1, m.2⟩).symm⟩

/-- `u` is equal to our original `f` -/
public theorem Base.uf (b : Base p s f) : b.u =ᶠ[𝓝ˢ s] f := by
  simp only [Filter.EventuallyEq, Filter.eventually_iff, mem_nhdsSet_iff_forall]
  intro z m; simp only [← Filter.eventually_iff]
  set x : closure s := ⟨z, subset_closure m⟩
  have zs : z ∈ Metric.ball (x : E) (b.r x) := mem_ball_self (b.rp x)
  have ug := (b.ug x).eventuallyEq_of_mem ((b.ot.inter isOpen_ball).mem_nhds
    ⟨b.cover (subset_closure m), zs⟩)
  exact ug.trans ((b.gf x).filter_mono (nhds_le_nhdsSet ⟨m, zs⟩))

/-- `u` is valid in `𝓝ˢ (closure s)` -/
public theorem Base.up (b : Base p s f) : ∀ᶠ z in 𝓝ˢ (closure s), p b.u z := by
  apply Filter.eventually_of_mem (b.ot.mem_nhdsSet.mpr b.cover)
  intro x m; refine b.congr (b.gp (b.y m) (b.yt m)) ?_
  exact ((b.ug _).eventuallyEq_of_mem ((b.ot.inter isOpen_ball).mem_nhds ⟨m, b.yt m⟩)).symm

/-!
### Continuation throughout a ball, starting from a point
-/

variable [ProperSpace E]
variable {c : E} {s' : Set E} {r t : ℝ}

/-- Information we need to continue a function throughout an open ball. -/
public structure Continuation [NormedSpace ℝ E] [ProperSpace E] (p : (E → α) → E → Prop)
    (c : E) (r : ℝ) (fs : E → α) : Prop where
  /-- The radius is positive -/
  pos : 0 < r
  /-- `p f x` is a local property of `f` near `x` -/
  congr : ∀ {f g x}, p f x → f =ᶠ[𝓝 x] g → p g x
  /-- The seed `fs` is valid near `x` -/
  start : ∀ᶠ y in 𝓝 c, p fs y
  /-- Given `f` valid on convex `s`, we can continue `f` to a neighorhood of any `x ∈ closure s` -/
  point : ∀ {f t x}, 0 < t → t < r → (∀ᶠ x in 𝓝ˢ (ball c t), p f x) → x ∈ closedBall c t →
    ∃ g, (∀ᶠ z in 𝓝 x, p g z) ∧ ∃ᶠ z in 𝓝 x, z ∈ ball c t ∧ g z = f z
  /-- If `f0, f1` are valid on an open preconnected set, and match somewhere,
      they match everywhere -/
  unique : ∀ {f0 f1 : E → α} {t : Set E}, IsOpen t → IsPreconnected t →
    (∀ x, x ∈ t → p f0 x) → (∀ x, x ∈ t → p f1 x) → (∃ x, x ∈ t ∧ f0 x = f1 x) → EqOn f0 f1 t

namespace Continuation

variable {fs : E → α}
variable {i : Continuation p c r fs}
attribute [bound_forward] Continuation.pos

/-- We can grow out through a set `t` -/
@[expose] public def Grow (_ : Continuation p c r fs) (s : Set E) : Prop :=
  ∃ f, f c = fs c ∧ ∀ᶠ x in 𝓝ˢ s, p f x

/-- Grow is monotonic -/
lemma Grow.mono (g : i.Grow s) (sub : s' ⊆ s) : i.Grow s' := by
  obtain ⟨f, e, h⟩ := g
  exact ⟨f, e, h.filter_mono (nhdsSet_mono sub)⟩

/-- We can grow through a small open ball -/
lemma grow_small (i : Continuation p c r fs) : ∃ t > 0, t ≤ r ∧ i.Grow (ball c t) := by
  obtain ⟨t,t0,g⟩ := Metric.eventually_nhds_iff_ball.mp i.start
  refine ⟨min t r, by bound, by bound, fs, ?_⟩
  simp only [isOpen_ball.nhdsSet_eq, Filter.eventually_principal]
  aesop

/-- If we can grow up to `ball c r`, we can grow through the closure -/
lemma Grow.closed (g : i.Grow (ball c t)) (tr : t < r) : i.Grow (closedBall c t) := by
  by_cases t0 : t ≤ 0
  · obtain ⟨u,u0,ur,g⟩ := i.grow_small
    exact g.mono (Metric.closedBall_subset_ball (by linarith))
  simp only [not_le] at t0
  obtain ⟨f, e, pf⟩ := g
  have b : Base p (ball c t) f := {
    convex := convex_ball _ _
    compact := by
      apply (isCompact_closedBall c r).of_isClosed_subset isClosed_closure
      simp only [closure_ball _ t0.ne', Metric.closedBall_subset_closedBall tr.le]
    congr := i.congr
    start := pf
    point := fun {x m} ↦ i.point t0 tr pf (by simpa [closure_ball _ t0.ne'] using m)
    unique := i.unique }
  refine ⟨b.u, ?_, ?_⟩
  · exact (b.uf.self_of_nhdsSet (mem_ball_self t0)).trans e
  · refine b.up.filter_mono (nhdsSet_mono ?_)
    simp only [closure_ball _ t0.ne', subset_refl]

/-- If we can grow through a closed ball, we can grow through a larger open ball -/
lemma Grow.open (g : i.Grow (closedBall c t)) : ∃ u > t, i.Grow (ball c u) := by
  obtain ⟨f, e, h⟩ := g
  obtain ⟨s',o,sub,h⟩ := eventually_nhdsSet_iff_exists.mp h
  obtain ⟨u,lt,sub'⟩ := exists_ball_superset sub o
  refine ⟨u, lt, f, e, ?_⟩
  simp only [isOpen_ball.nhdsSet_eq, Filter.eventually_principal]
  intro x m
  exact h x (sub' m)

/-- If we grow up until everything before `t`, we grow to `t` -/
lemma Grow.sup {u : ℕ → ℝ} (mono : Monotone u) (tend : Tendsto u atTop (𝓝 t)) (t0 : 0 < t)
    (grow : ∀ n, i.Grow (ball c (u n))) : i.Grow (ball c t) := by
  have ut : ∀ n, u n ≤ t := fun n ↦ mono.ge_of_tendsto tend n
  have ex : ∀ t' < t, ∃ n, t' < u n := fun t' lt ↦ tend.exists_lt lt
  set n : E → ℕ := fun x ↦ if lt : ‖x - c‖ < t then Nat.find (ex _ lt) else Nat.find (ex 0 t0)
  have u0 : ∀ x, 0 < u (n x) := by
    intro x
    simp only [n]
    split_ifs with lt
    · exact lt_of_le_of_lt (norm_nonneg _) (Nat.find_spec (ex _ lt))
    · exact Nat.find_spec (ex 0 t0)
  have nlt : ∀ x, ‖x - c‖ < t → ‖x - c‖ < u (n x) := by
    intro x lt
    simp only [lt, n]
    exact Nat.find_spec (ex _ lt)
  set fn : E → E → α := fun x ↦ choose (grow (n x))
  have spec : ∀ x, fn x c = fs c ∧ ∀ᶠ y in 𝓝ˢ (ball c (u (n x))), p (fn x) y :=
    fun x ↦ choose_spec (grow (n x))
  set f : E → α := fun x ↦ fn x x
  refine ⟨f, (spec _).1, ?_⟩
  simp only [isOpen_ball.nhdsSet_eq, Filter.eventually_principal, mem_ball, dist_eq_norm]
  intro x xlt
  apply i.congr (f := fn x) (g := f)
  · specialize spec x
    simp only [isOpen_ball.nhdsSet_eq, Filter.eventually_principal, mem_ball, dist_eq_norm] at spec
    exact spec.2 x (nlt x xlt)
  · have elt : ∀ᶠ y in 𝓝 x, ‖y - c‖ < u (n x) :=
      ContinuousAt.eventually_lt (f := fun x ↦ ‖x - c‖) (by fun_prop) continuousAt_const (nlt x xlt)
    filter_upwards [elt] with y ylt
    have sx := (spec x).2
    have sy := (spec y).2
    simp only [isOpen_ball.nhdsSet_eq, Filter.eventually_principal, mem_ball, dist_eq_norm] at sx sy
    refine i.unique (f0 := fn x) (f1 := fn y) (t := ball c (min (u (n x)) (u (n y)))) isOpen_ball
      (convex_ball _ _).isPreconnected ?_ ?_ ⟨c, ?_⟩ ?_
    · intro z m
      apply sx
      simp only [mem_ball, dist_eq_norm, lt_inf_iff] at m
      exact m.1
    · intro z m
      apply sy
      simp only [mem_ball, dist_eq_norm, lt_inf_iff] at m
      exact m.2
    · simp [u0, (spec _).1]
    · have yt := lt_of_lt_of_le ylt (ut _)
      simp only [yt, ↓reduceDIte, mem_ball, dist_eq_norm, lt_inf_iff, ylt, true_and, gt_iff_lt, n]
      simpa using Nat.find_spec (ex _ yt)

/-- We can grow through the whole ball -/
public lemma grow : i.Grow (ball c r) := by
  set s : Set ℝ := {t | 0 < t ∧ t ≤ r ∧ i.Grow (ball c t)}
  have above : BddAbove s := bddAbove_def.mpr ⟨r, by aesop⟩
  obtain ⟨t0, t0p, t0r, g0⟩ := i.grow_small
  have start : t0 ∈ s := by aesop
  have ne : s.Nonempty := ⟨t0, start⟩
  have pos : 0 < sSup s := lt_csSup_of_lt above start t0p
  have sup_le : sSup s ≤ r := csSup_le ne (by aesop)
  have down : ∀ a b, 0 < a → a ≤ b → b ∈ s → a ∈ s := by
    intro a b a0 ab bs
    exact ⟨a0, le_trans ab bs.2.1, bs.2.2.mono (Metric.ball_subset_ball ab)⟩
  have self : sSup s ∈ s := by
    obtain ⟨u,mono,tend,grow⟩ := exists_seq_tendsto_sSup ne above
    exact ⟨pos, sup_le, Grow.sup mono tend pos (fun n ↦ (grow n).2.2)⟩
  by_cases sup_lt : sSup s < r
  · obtain ⟨t,sup_t,g⟩ := (self.2.2.closed sup_lt).open
    have lt : sSup s < min t r := by bound
    obtain ⟨u,su,utr⟩ := exists_between lt
    simp only [lt_inf_iff] at utr
    have us : u ∈ s := ⟨by linarith, by linarith, g.mono (Metric.ball_subset_ball utr.1.le)⟩
    linarith [le_csSup above us]
  · simp only [not_lt] at sup_lt
    exact (down r (sSup s) i.pos sup_lt self).2.2
