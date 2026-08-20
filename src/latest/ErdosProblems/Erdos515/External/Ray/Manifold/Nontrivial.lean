module
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Geometry.Manifold.ContMDiff.Defs
public import ErdosProblems.Erdos515.External.Ray.Analytic.Defs
public import ErdosProblems.Erdos515.External.Ray.Manifold.Defs
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic.Cases
import ErdosProblems.Erdos515.External.Ray.Analytic.Analytic
import ErdosProblems.Erdos515.External.Ray.Analytic.Holomorphic
import ErdosProblems.Erdos515.External.Ray.Manifold.Analytic
import ErdosProblems.Erdos515.External.Ray.Misc.Connected
import ErdosProblems.Erdos515.External.Ray.Misc.Topology
import ErdosProblems.Erdos515.External.Ray.Misc.TotallyDisconnected

/-!
## Nontriviality of analytic functions, and consequences

We define several structures representing global and local nontriviality (nonconstness)
of analytic and analytic functions, and in 1D or parameterized 1D:

1. `NontrivialAnalyticOn f s`: Near every point `z ∈ s`, `f` is locally analytic and nonconstant
1. `NontrivialMAnalyticOn f s`: The same for analytic functions between 1D analytic manifolds
2. `NontrivialMAnalyticAt f z`: Near `z`, `f` is analytic and nonconstant

These "everyone nontrivial" properties can be derived from properties at one point:

1. If an analytic function is nonconstant on a preconnected set, is it nontrivial there
2. Nonzero analytic derivative implies nontriviality
3. Nontriviality is preserved by composition
4. If a composition is nontrivial, both parts are nontrivial
5. `id` is nontrivial
6. Positive `orderAt` implies nontrivial

From these, we have a variety of consequences, such as:

1. Nontrivial functions have isolated zeros or other values.
2. The zeros (or preimages of another value) of a nontrivial function have a discrete topology
3. Pow is nontrivial, so roots of unity are totally disconnected
4. If a nontrivial function is constant on the image of a preconnected set, the image is a singleton
5. Near a point, analytic functions are either locally constant or locally ≠ to the point value
6. Locally constant functions are constant on preconnected sets
-/

open Classical
open Filter (Tendsto)
open Function (curry uncurry)
open Metric (ball closedBall isOpen_ball mem_ball mem_closedBall mem_ball_self
  mem_closedBall_self mem_sphere sphere)
open OneDimension
open Set
open scoped ContDiff OneDimension Real Topology Manifold
noncomputable section

variable {X : Type} [TopologicalSpace X]
variable {S : Type} [TopologicalSpace S] [ChartedSpace ℂ S]
variable {T : Type} [TopologicalSpace T] [ChartedSpace ℂ T]
variable {U : Type} [TopologicalSpace U] [ChartedSpace ℂ U]

section Nontrivial

variable {f : ℂ → ℂ} {s : Set ℂ}

/-- Nontrivial analytic functions have isolated values -/
theorem NontrivialAnalyticOn.isolated (n : NontrivialAnalyticOn f s) {z : ℂ} (zs : z ∈ s) :
    ∀ᶠ w in 𝓝[{z}ᶜ] z, f w ≠ f z := by
  have fa : AnalyticAt ℂ (fun w ↦ f w - f z) z := (n.analyticOn z zs).sub analyticAt_const
  cases' fa.eventually_eq_zero_or_eventually_ne_zero with h h
  · have b := h.and_frequently (n.nonconst z zs)
    simp only [sub_eq_zero, Ne, and_not_self_iff, Filter.frequently_false] at b
  · simp only [sub_ne_zero] at h; exact h

/-- Nontrivial analytic functions have isolated values -/
theorem NontrivialAnalyticOn.isolated' (n : NontrivialAnalyticOn f s) {z : ℂ} (zs : z ∈ s) (a : ℂ) :
    ∀ᶠ w in 𝓝[{z}ᶜ] z, f w ≠ a := by
  by_cases h : f z = a; simp only [← h]; exact n.isolated zs
  exact ((n.analyticOn _ zs).continuousAt.eventually_ne h).filter_mono nhdsWithin_le_nhds

/-- Nonconstant functions on preconnected sets are nontrivial -/
theorem IsPreconnected.nontrivialAnalyticOn (p : IsPreconnected s) (fa : AnalyticOnNhd ℂ f s)
    (ne : ∃ a b, a ∈ s ∧ b ∈ s ∧ f a ≠ f b) : NontrivialAnalyticOn f s :=
  { analyticOn := fa
    nonconst := by
      contrapose ne; simp only [not_forall, Filter.not_frequently, not_not] at ne
      rcases ne with ⟨z, zs, h⟩
      simp only [not_exists, exists_and_left, not_and, not_not]
      have h' := (h.filter_mono (nhdsWithin_le_nhds (s := {z}ᶜ))).frequently
      have e := fa.eqOn_of_preconnected_of_frequently_eq analyticOnNhd_const p zs h'
      intro x xs y ys; rw [e xs, e ys] }

/-- Nonconstant entire functions are nontrivial -/
theorem Entire.nontrivialAnalyticOn (fa : AnalyticOnNhd ℂ f univ) (ne : ∃ a b, f a ≠ f b) :
    NontrivialAnalyticOn f univ := by
  refine isPreconnected_univ.nontrivialAnalyticOn fa ?_; simpa only [Set.mem_univ, true_and]

/-- The roots of a nontrivial analytic function form a discrete topology -/
theorem NontrivialAnalyticOn.discreteTopology (n : NontrivialAnalyticOn f s) (a : ℂ) :
    DiscreteTopology (↥(s ∩ f ⁻¹' {a})) := by
  rw [discreteTopology_iff_isOpen_singleton]
  intro ⟨z, m⟩
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff] at m
  by_cases h : ∃ᶠ z in 𝓝[{z}ᶜ] z, f z = a
  · have i := (n.isolated' m.1 a).and_frequently h
    simp only [not_and_self_iff, Filter.frequently_const] at i
  · simp only [Filter.not_frequently, eventually_nhdsWithin_iff, Set.mem_compl_singleton_iff] at h
    rcases eventually_nhds_iff.mp h with ⟨t, t0, o, tz⟩
    simp only [isOpen_induced_iff]; use t, o
    apply Set.ext; intro ⟨w, m⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Subtype.mk_eq_mk]
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff] at m
    specialize t0 w
    simp only [m.2, imp_false, not_true, not_not] at t0
    use t0; intro wz; rw [wz]; exact tz

/-- pow is nontrivial -/
theorem powNontrivial {d : ℕ} (dp : 0 < d) : NontrivialAnalyticOn (fun z ↦ z ^ d) univ := by
  apply Entire.nontrivialAnalyticOn fun _ _ ↦ analyticAt_id.pow _; use 0, 1
  simp only [id, one_pow, zero_pow (Nat.pos_iff_ne_zero.mp dp), Pi.pow_def]; norm_num

/-- All roots of unity as a set -/
def allRootsOfUnity :=
  {z : ℂ | ∃ n : ℕ, n ≠ 0 ∧ z ^ n = 1}

/-- Roots of unity are nonzero -/
theorem allRootsOfUnity.ne_zero {z : ℂ} (m : z ∈ allRootsOfUnity) : z ≠ 0 := by
  rcases m with ⟨n, n0, z1⟩; contrapose z1
  simp only [z1, zero_pow n0]; exact zero_ne_one

/-- Roots of unity are totally disconnected -/
theorem IsTotallyDisconnected.allRootsOfUnity : IsTotallyDisconnected allRootsOfUnity := by
  apply IsCountable.isTotallyDisconnected
  simp only [_root_.allRootsOfUnity, ofPred_exists]; apply countable_iUnion; intro n
  by_cases n0 : n = 0
  simp only [n0, Ne, not_true, false_and, ofPred_false, countable_empty]
  simp only [Ne, n0, not_false_iff, true_and]
  have np : 0 < n := Nat.pos_of_ne_zero n0
  generalize hn' : (⟨n, np⟩ : ℕ+) = n'
  have e : {z : ℂ | z ^ n = 1} ⊆ (fun x : ℂˣ ↦ (x : ℂ)) '' (rootsOfUnity n' ℂ : Set ℂˣ) := by
    intro z e; simp only [mem_ofPred] at e
    simp only [mem_image, SetLike.mem_coe]
    by_cases z0 : z = 0
    · simp only [z0, zero_pow n0, zero_ne_one] at e
    · use Units.mk0 z z0
      simp [← hn', ← Units.val_inj, Units.val_pow_eq_pow_val, Units.val_mk0, e, Units.val_one,
        and_self]
  apply Set.Countable.mono e; clear e; apply Countable.image
  have : NeZero (n' : ℕ) := ⟨n'.2.ne'⟩
  have h : (rootsOfUnity (n' : ℕ) ℂ : Set ℂˣ).Finite :=
    Set.finite_coe_iff.mp (inferInstanceAs (Finite (rootsOfUnity (n' : ℕ) ℂ)))
  exact h.countable

/-- Given continuous `p : X → ℂ` on preconnected `X`, `p` is const if `f ∘ p` is const -/
theorem NontrivialAnalyticOn.const (n : NontrivialAnalyticOn f s) {p : X → ℂ} {t : Set X}
    (tc : IsPreconnected t) (pc : ContinuousOn p t) (ps : Set.MapsTo p t s) {a b : ℂ}
    (p1 : ∃ x, x ∈ t ∧ p x = a) (fp : ∀ x, x ∈ t → f (p x) = b) : ∀ x, x ∈ t → p x = a := by
  have disc : DiscreteTopology (↥(s ∩ f ⁻¹' {b})) := n.discreteTopology b
  rcases p1 with ⟨z, zt, z1⟩; simp only [← z1]
  intro x xt
  refine @IsPreconnected.constant_of_mapsTo _ _ _ tc _ _ _ disc.isDiscrete _ pc ?_ _ _ xt zt
  intro y yt; simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
  use ps yt, fp _ yt

/-- Given `p : X → ℂ`, `p^d = 1 → p = 1` given continuity, `X` preconnected,
    and `p = 1` somewhere -/
theorem eq_one_of_pow_eq_one {p : X → ℂ} {t : Set X} {d : ℕ} (pc : ContinuousOn p t)
    (tc : IsPreconnected t) (dp : d > 0) (pa : ∃ x, x ∈ t ∧ p x = 1)
    (pd : ∀ x, x ∈ t → p x ^ d = 1) : ∀ x, x ∈ t → p x = 1 :=
  (powNontrivial dp).const tc pc (Set.mapsTo_univ _ _) pa pd

/-- Given `p, q : X → ℂ`, `p^d = q^d → p ≠ 0 → p = q` -/
theorem eq_of_pow_eq {p q : X → ℂ} {t : Set X} {d : ℕ} (pc : ContinuousOn p t)
    (qc : ContinuousOn q t) (tc : IsPreconnected t) (dp : d > 0) (pq : ∃ x, x ∈ t ∧ p x = q x)
    (p0 : ∀ x, x ∈ t → p x ≠ 0) (pqd : ∀ x, x ∈ t → p x ^ d = q x ^ d) :
    ∀ x, x ∈ t → p x = q x := by
  generalize hr : (fun x ↦ q x / p x) = r
  have rc : ContinuousOn r t := by rw [← hr]; exact qc.div pc p0
  have h := eq_one_of_pow_eq_one rc tc dp ?_ ?_
  · intro x m
    rw [← hr] at h
    exact ((div_eq_one_iff_eq (p0 _ m)).mp (h _ m)).symm
  · rcases pq with ⟨x, m, e⟩; use x, m
    rw [← hr]
    exact (div_eq_one_iff_eq (p0 _ m)).mpr e.symm
  · intro x m
    simp only [div_pow, ← hr]
    rw [div_eq_one_iff_eq]
    · exact (pqd _ m).symm
    · exact pow_ne_zero _ (p0 _ m)

/-- At a point, a analytic function is either locally constant or locally different from its
    value at the point.  This is the `ContMDiffAt` version of
    `AnalyticAt.eventuallyEq_or_eventually_ne` -/
public theorem ContMDiffAt.eventually_eq_or_eventually_ne [T2Space T] {f g : S → T} {z : S}
    (fa : ContMDiffAt I I ω f z) (ga : ContMDiffAt I I ω g z) :
    (∀ᶠ w in 𝓝 z, f w = g w) ∨ ∀ᶠ w in 𝓝[{z}ᶜ] z, f w ≠ g w := by
  simp only [mAnalyticAt_iff_of_boundaryless, Function.comp_def] at fa ga
  rcases fa with ⟨fc, fa⟩; rcases ga with ⟨gc, ga⟩
  by_cases fg : f z ≠ g z
  · right; contrapose fg
    simp only [Filter.not_eventually, not_not] at fg
    exact tendsto_nhds_unique_of_frequently_eq fc gc (fg.filter_mono nhdsWithin_le_nhds)
  simp only [not_not] at fg
  cases' fa.eventually_eq_or_eventually_ne ga with e e
  · left; clear fa ga
    replace e := (continuousAt_extChartAt z).eventually e
    replace e := Filter.EventuallyEq.fun_comp e (_root_.extChartAt I (f z)).symm
    apply e.congr; simp only [Function.comp_def]; clear e
    apply (fc.eventually_mem (extChartAt_source_mem_nhds (I := I) (f z))).mp
    apply (gc.eventually_mem (extChartAt_source_mem_nhds (I := I) (g z))).mp
    refine eventually_nhds_iff.mpr ⟨(_root_.extChartAt I z).source,
      fun x m gm fm ↦ ?_, isOpen_extChartAt_source _, mem_extChartAt_source z⟩
    rw [← fg] at gm
    simp only [← fg, PartialEquiv.left_inv _ m, PartialEquiv.left_inv _ fm,
      PartialEquiv.left_inv _ gm]
  · right; clear fa ga
    simp only [eventually_nhdsWithin_iff, Set.mem_compl_singleton_iff] at e ⊢
    replace e := (continuousAt_extChartAt z).eventually e
    apply (fc.eventually_mem ((extChartAt_source_mem_nhds (I := I) (f z)))).mp
    apply (gc.eventually_mem ((extChartAt_source_mem_nhds (I := I) (g z)))).mp
    apply ((isOpen_extChartAt_source z).eventually_mem (mem_extChartAt_source (I := I) z)).mp
    refine e.mp (.of_forall ?_); clear e
    intro x h xm gm fm xz; rw [← fg] at gm
    simp only [← fg, PartialEquiv.left_inv _ xm] at h
    specialize h ((PartialEquiv.injOn _).ne xm (mem_extChartAt_source _) xz)
    rwa [← (PartialEquiv.injOn _).ne_iff fm gm]

/-- Locally constant functions are constant on preconnected sets -/
public theorem ContMDiffOn.const_of_locally_const [T2Space T] {f : S → T} {s : Set S}
    (fa : ContMDiffOn I I ω f s) {z : S} {a : T} (zs : z ∈ s) (o : IsOpen s) (p : IsPreconnected s)
    (c : ∀ᶠ w in 𝓝 z, f w = a) : ∀ w, w ∈ s → f w = a := by
  generalize ht : {z | z ∈ s ∧ ∀ᶠ w in 𝓝 z, f w = a} = t
  suffices st : s ⊆ t by rw [← ht] at st; exact fun z m ↦ (st m).2.self_of_nhds
  refine p.subset_of_closure_inter_subset ?_ ?_ ?_
  · rw [isOpen_iff_eventually]
    intro z m
    simp only [Set.mem_ofPred_eq, ← ht] at m ⊢
    exact ((o.eventually_mem m.1).and m.2.eventually_nhds).mp (.of_forall fun y h ↦ h)
  · use z; simp only [Set.mem_inter_iff, ← ht]; exact ⟨zs, zs, c⟩
  · intro z m; simp only [Set.mem_inter_iff, mem_closure_iff_frequently] at m
    have aa : ContMDiffAt I I ω (fun _ ↦ a) z := contMDiffAt_const
    cases' (fa.contMDiffAt (o.mem_nhds m.2)).eventually_eq_or_eventually_ne aa with h h
    · rw [← ht]; use m.2, h
    · simp only [eventually_nhdsWithin_iff, Set.mem_compl_singleton_iff] at h
      have m' := m.1; contrapose m'; simp only [Filter.not_frequently]
      refine h.mp (.of_forall ?_); intro x i
      by_cases xz : x = z; rwa [xz]; specialize i xz; contrapose i
      simp only [← ht] at i ⊢; exact i.2.self_of_nhds

/-- If `S` is locally connected, we don't need the open assumption in
    `ContMDiffOn.const_of_locally_const` -/
public theorem ContMDiffOnNhd.const_of_locally_const [LocallyConnectedSpace S] [T2Space T]
    [IsManifold I ω S] [IsManifold I ω T] {f : S → T}
    {s : Set S} (fa : ContMDiffOnNhd I I f s) {z : S} {a : T} (zs : z ∈ s) (p : IsPreconnected s)
    (c : ∀ᶠ w in 𝓝 z, f w = a) : ∀ w, w ∈ s → f w = a := by
  rcases local_preconnected_nhdsSet p (isOpen_mAnalyticAt.mem_nhdsSet.mpr fa)
    with ⟨u, uo, su, ua, uc⟩
  exact fun w ws ↦ ContMDiffOn.const_of_locally_const
    (fun _ m ↦ (ua m).contMDiffWithinAt) (su zs) uo uc c w (su ws)

/-- `NontrivialMAnalyticAt f z` implies `f z` is never locally repeated -/
public theorem NontrivialMAnalyticAt.eventually_ne [T2Space T] {f : S → T} {z : S}
    (n : NontrivialMAnalyticAt f z) : ∀ᶠ w in 𝓝 z, w ≠ z → f w ≠ f z := by
  have ca : ContMDiffAt I I ω (fun _ ↦ f z) z := contMDiffAt_const
  cases' n.mAnalyticAt.eventually_eq_or_eventually_ne ca with h h
  · have b := h.and_frequently n.nonconst
    simp only [and_not_self_iff, Filter.frequently_false] at b
  · simp only [eventually_nhdsWithin_iff, mem_compl_singleton_iff] at h; convert h

/-- Nontrivially at a point of a preconnected set implies nontriviality throughout the set -/
public theorem NontrivialMAnalyticAt.on_preconnected [T2Space T] {f : S → T} {s : Set S} {z : S}
    (fa : ContMDiffOn I I ω f s) (zs : z ∈ s) (o : IsOpen s) (p : IsPreconnected s)
    (n : NontrivialMAnalyticAt f z) : NontrivialMAnalyticOn f s := by
  intro w ws
  replace n := n.nonconst
  refine ⟨fa.contMDiffAt (o.mem_nhds ws), ?_⟩; contrapose n
  simp only [Filter.not_frequently, not_not] at n ⊢; generalize ha : f w = a
  rw [ha] at n
  rw [eventually_nhds_iff]; refine ⟨s, ?_, o, zs⟩
  have c := fa.const_of_locally_const ws o p n
  intro x m; rw [c _ m, c _ zs]

/-- If a `f` is nontrivial at `z`, it is nontrivial near `z` -/
theorem NontrivialMAnalyticAt.eventually [T2Space T] [IsManifold I ω S] [IsManifold I ω T]
    {f : S → T} {z : S} (n : NontrivialMAnalyticAt f z) :
    ∀ᶠ w in 𝓝 z, NontrivialMAnalyticAt f w := by
  have lc : LocallyConnectedSpace S := ChartedSpace.locallyConnectedSpace ℂ _
  rcases eventually_nhds_iff.mp n.mAnalyticAt.eventually with ⟨s, fa, os, zs⟩
  rcases locallyConnectedSpace_iff_subsets_isOpen_isConnected.mp lc z s (os.mem_nhds zs) with
    ⟨t, ts, ot, zt, ct⟩
  rw [eventually_nhds_iff]; refine ⟨t, ?_, ot, zt⟩
  refine n.on_preconnected (ContMDiffOn.mono ?_ ts) zt ot ct.isPreconnected
  exact fun x m ↦ (fa x m).contMDiffWithinAt

/-- If the derivative isn't zero, we're nontrivial -/
public theorem nontrivialMAnalyticAt_of_mfderiv_ne_zero [IsManifold I ω S] [IsManifold I ω T]
    {f : S → T} {z : S} (fa : ContMDiffAt I I ω f z) (d : mfderiv I I f z ≠ 0) :
    NontrivialMAnalyticAt f z := by
  refine ⟨fa, ?_⟩; contrapose d; simp only [Filter.not_frequently, not_not] at d ⊢
  generalize ha : f z = a; rw [ha] at d; apply HasMFDerivAt.mfderiv
  exact (hasMFDerivAt_const a _).congr_of_eventuallyEq d

/-- If `f` and `g` are nontrivial, `f ∘ g` is nontrivial -/
public theorem NontrivialMAnalyticAt.comp [T2Space U] {f : T → U} {g : S → T} {z : S}
    (fn : NontrivialMAnalyticAt f (g z)) (gn : NontrivialMAnalyticAt g z) :
    NontrivialMAnalyticAt (fun z ↦ f (g z)) z := by
  use fn.mAnalyticAt.comp _ gn.mAnalyticAt
  convert gn.nonconst.and_eventually (gn.mAnalyticAt.continuousAt.eventually fn.eventually_ne)
  tauto

/-- If `f ∘ g` is nontrivial, and `f, g` are analytic, `f, g` are nontrivial -/
public theorem NontrivialMAnalyticAt.anti {f : T → U} {g : S → T} {z : S}
    (h : NontrivialMAnalyticAt (fun z ↦ f (g z)) z) (fa : ContMDiffAt I I ω f (g z))
    (ga : ContMDiffAt I I ω g z) :
    NontrivialMAnalyticAt f (g z) ∧ NontrivialMAnalyticAt g z := by
  replace h := h.nonconst; refine ⟨⟨fa, ?_⟩, ⟨ga, ?_⟩⟩
  · contrapose h; simp only [Filter.not_frequently, not_not] at h ⊢
    exact (ga.continuousAt.eventually h).mp (.of_forall fun _ h ↦ h)
  · contrapose h; simp only [Filter.not_frequently, not_not] at h ⊢
    exact h.mp (.of_forall fun x h ↦ by rw [h])

/-- `id` is nontrivial -/
-- There's definitely a better way to prove this, but I'm blanking at the moment.
public theorem nontrivialMAnalyticAt_id [IsManifold I ω S] (z : S) :
    NontrivialMAnalyticAt (fun w ↦ w) z := by
  use contMDiffAt_id
  rw [Filter.frequently_iff]; intro s sz
  rcases mem_nhds_iff.mp sz with ⟨t, ts, ot, zt⟩
  generalize hu : (extChartAt I z).target ∩ (extChartAt I z).symm ⁻¹' t = u
  have uo : IsOpen u := by
    rw [← hu]
    exact (continuousOn_extChartAt_symm z).isOpen_inter_preimage (isOpen_extChartAt_target _) ot
  have zu : extChartAt I z z ∈ u := by
    simp only [mem_inter_iff, mem_extChartAt_target, true_and, mem_preimage,
      PartialEquiv.left_inv _ (mem_extChartAt_source z), zt, ← hu]
  rcases Metric.isOpen_iff.mp uo _ zu with ⟨r, rp, ru⟩
  generalize ha : extChartAt I z z + r / 2 = a
  have au : a ∈ u := by
    rw [← ha]; apply ru; simp only [Metric.mem_ball, Complex.dist_eq, add_sub_cancel_left]
    simp only [norm_div, Complex.norm_real, abs_of_pos rp, Complex.norm_two, Real.norm_eq_abs]
    exact half_lt_self rp
  use (extChartAt I z).symm a
  rw [← hu] at au
  use ts au.2
  rw [← (PartialEquiv.injOn _).ne_iff ((extChartAt I z).map_target au.1) (mem_extChartAt_source z)]
  rw [PartialEquiv.right_inv _ au.1, ← ha]
  simp only [Ne, add_eq_left, div_eq_zero_iff, Complex.ofReal_eq_zero, rp.ne']; norm_num

/-- If `orderAt f z ≠ 0` (`f` has a zero of positive order), then `f` is nontrivial at `z` -/
public theorem nontrivialMAnalyticAt_of_order {f : ℂ → ℂ} {z : ℂ} (fa : AnalyticAt ℂ f z)
    (h : orderAt f z ≠ 0) : NontrivialMAnalyticAt f z := by
  use fa.mAnalyticAt I I; contrapose h
  simp only [Filter.not_frequently, not_not] at h ⊢
  have fp : HasFPowerSeriesAt f (constFormalMultilinearSeries ℂ ℂ (f z)) z :=
    hasFPowerSeriesAt_const.congr (Filter.EventuallyEq.symm h)
  simp only [fp.orderAt_unique]; by_contra p0
  have b := FormalMultilinearSeries.apply_order_ne_zero' p0
  simp only [constFormalMultilinearSeries_apply_of_nonzero p0, Ne, not_true] at b

/-- `NontrivialAnalyticOn → NontrivialMAnalyticOn` over `ℂ` -/
theorem NontrivialAnalyticOn.nontrivialMAnalyticOn {f : ℂ → ℂ} {s : Set ℂ}
    (n : NontrivialAnalyticOn f s) : NontrivialMAnalyticOn f s := fun z m ↦
  { mAnalyticAt := (n.analyticOn z m).mAnalyticAt I I
    nonconst := n.nonconst z m }

/-- pow is nontrivial -/
theorem nontrivialMAnalyticAt_pow {d : ℕ} (d0 : d > 0) {z : ℂ} :
    NontrivialMAnalyticAt (fun z ↦ z ^ d) z :=
  (powNontrivial d0).nontrivialMAnalyticOn z (mem_univ _)

/-- Nontriviality is invariant to positive powers -/
theorem NontrivialMAnalyticAt.pow_iff {f : S → ℂ} {z : S} {d : ℕ} (fa : ContMDiffAt I I ω f z)
    (d0 : 0 < d) : NontrivialMAnalyticAt (fun z ↦ f z ^ d) z ↔ NontrivialMAnalyticAt f z := by
  refine ⟨?_, (nontrivialMAnalyticAt_pow d0).comp⟩
  have pa : ContMDiffAt I I ω (fun z ↦ z ^ d) (f z) := (contMDiff_pow d).contMDiffAt
  intro h; refine (NontrivialMAnalyticAt.anti ?_ pa fa).2; exact h

/-- Nontriviality depends only locally on `f` -/
public theorem NontrivialMAnalyticAt.congr {f g : S → T} {z : S} (n : NontrivialMAnalyticAt f z)
    (e : f =ᶠ[𝓝 z] g) : NontrivialMAnalyticAt g z := by
  use n.mAnalyticAt.congr_of_eventuallyEq e.symm
  refine n.nonconst.mp (e.mp (.of_forall fun w ew n ↦ ?_))
  rwa [← ew, ← e.self_of_nhds]

section EqOfLocallyEq

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]
variable {A : Type} [TopologicalSpace A] {J : ModelWithCorners ℂ E A} [J.Boundaryless]
variable {B : Type} [TopologicalSpace B] {K : ModelWithCorners ℂ F B}
variable {M : Type} [TopologicalSpace M] [ChartedSpace A M]
variable {N : Type} [TopologicalSpace N] [ChartedSpace B N]

/-- If two analytic functions are equal locally, they are equal on preconnected sets.

    This is a manifold version of `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`.
    This is the one higher dimension result in this file, which shows up in that `e`
    requires `f =ᶠ[𝓝 x] g` everywhere near a point rather than only frequent equality
    as would be required in 1D. -/
public theorem ContMDiffOnNhd.eq_of_locally_eq [CompleteSpace F] {f g : M → N} [T2Space N]
   {s : Set M} (fa : ContMDiffOnNhd J K f s) (ga : ContMDiffOnNhd J K g s) (sp : IsPreconnected s)
    (e : ∃ x, x ∈ s ∧ f =ᶠ[𝓝 x] g) : f =ᶠ[𝓝ˢ s] g := by
  generalize ht :  {x | f =ᶠ[𝓝 x] g} = t
  suffices h : s ⊆ interior t by
    simp only [subset_interior_iff_mem_nhdsSet, ← Filter.eventually_iff, ← ht] at h
    exact h.mp (.of_forall fun _ e ↦ e.self_of_nhds)
  apply sp.relative_clopen
  · rw [← ht]; exact e
  · intro x ⟨_, xt⟩
    simp only [mem_interior_iff_mem_nhds, ← ht] at xt ⊢
    exact xt.eventually_nhds
  · intro x ⟨xs, xt⟩; rw [mem_closure_iff_frequently] at xt
    have ex' : ∃ᶠ y in 𝓝 x, f y = g y := by
      rw [← ht] at xt; exact xt.mp (.of_forall fun _ e ↦ e.self_of_nhds)
    have ex : f x = g x :=
      tendsto_nhds_unique_of_frequently_eq (fa.continuousAt xs) (ga.continuousAt xs) ex'
    generalize hd : (fun y : E ↦
      extChartAt K (f x) (f ((extChartAt J x).symm y)) -
        extChartAt K (g x) (g ((extChartAt J x).symm y))) = d
    generalize hz : extChartAt J x x = z
    suffices h : d =ᶠ[𝓝 z] 0 by
      simp only [← hz, ← map_extChartAt_nhds_of_boundaryless x, Filter.eventually_map, Filter.EventuallyEq,
        ← ht] at h ⊢
      refine
        h.mp (((isOpen_extChartAt_source x).eventually_mem
        (mem_extChartAt_source (I := J) x)).mp ?_)
      apply ((fa.continuousAt xs).eventually_mem
          ((isOpen_extChartAt_source _).mem_nhds (mem_extChartAt_source (I := K) (f x)))).mp
      apply ((ga.continuousAt xs).eventually_mem ((isOpen_extChartAt_source _).mem_nhds
          (mem_extChartAt_source (I := K) (g x)))).mp
      refine .of_forall fun y gm fm m e ↦ ?_
      rw [← hd, Pi.zero_apply, sub_eq_zero, (extChartAt J x).left_inv m, ex] at e
      rw [ex] at fm; exact (extChartAt K (g x)).injOn fm gm e
    have d0 : ∃ᶠ y in 𝓝 z, d =ᶠ[𝓝 y] 0 := by
      rw [← hz]
      have xt' : ∃ᶠ y in 𝓝 x, (extChartAt J x).symm (extChartAt J x y) ∈ t := by
        apply xt.mp
        apply ((isOpen_extChartAt_source x).eventually_mem (mem_extChartAt_source (I := J) x)).mp
        refine .of_forall fun y m e ↦ ?_; rw [(extChartAt J x).left_inv m]; exact e
      apply (Filter.Tendsto.frequently (p := fun y ↦ (extChartAt J x).symm y ∈ t)
          (continuousAt_extChartAt x) xt').mp
      apply ((isOpen_extChartAt_target x).eventually_mem (mem_extChartAt_target x)).mp
      refine .of_forall fun y m e ↦ ?_; simp only [← ht] at e
      apply ((continuousAt_extChartAt_symm'' m).eventually e).mp
      refine .of_forall fun z e ↦ ?_
      simp only [← hd, Pi.zero_apply, sub_eq_zero, ex, e]
    have da : AnalyticAt ℂ d z := by
      rw [← hd, ← hz]
      exact (mAnalyticAt_iff_of_boundaryless.mp (fa _ xs)).2.sub
        (mAnalyticAt_iff_of_boundaryless.mp (ga _ xs)).2
    clear hd ex ex' xt t e fa ga f g xs hz x sp ht
    -- Forget about manifolds
    rcases da.exists_ball_analyticOnNhd with ⟨r, rp, da⟩
    rcases Filter.frequently_iff.mp d0 (isOpen_ball.mem_nhds (mem_ball_self rp)) with ⟨z0, m0, ze⟩
    refine eventually_nhds_iff.mpr ⟨_, ?_, isOpen_ball, mem_ball_self rp⟩
    exact da.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball _ _).isPreconnected m0 ze

end EqOfLocallyEq
