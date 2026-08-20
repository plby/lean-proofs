module
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Connected.PathConnected
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Tactic.Cases
import ErdosProblems.Erdos515.External.Ray.Misc.Set
import ErdosProblems.Erdos515.External.Ray.Misc.Topology

/-!
## Basic result about connected sets

Our main results are

1. Downward intersections are compact, preconnected sets are preconnected
2. Limit points at the ends of rays are preconnected
3. `f ⁻¹' s` is path connected if `f ⁻¹' frontier s` is, for compact `s`
-/

open Filter (Tendsto atTop atBot)
open Function (curry uncurry)
open Metric (ball closedBall isOpen_ball ball_mem_nhds mem_ball_self nonempty_ball sphere)
open Set
open scoped NNReal Topology Real
noncomputable section

variable {α : Type}
variable {X : Type} [TopologicalSpace X]
variable {I : Type} [TopologicalSpace I] [ConditionallyCompleteLinearOrder I]
variable [DenselyOrdered I] [OrderTopology I]

theorem closure_inter_subset_compl {s u v : Set X} (vo : IsOpen v) (d : Disjoint u v) :
    closure (s ∩ u) ⊆ vᶜ := by
  rw [← vo.isClosed_compl.closure_eq]; apply closure_mono
  exact _root_.trans inter_subset_right (Disjoint.subset_compl_left d.symm)

theorem isClosed_closed_inter {s u v : Set X} (sc : IsClosed s) (vo : IsOpen v) (d : Disjoint u v)
    (suv : s ⊆ u ∪ v) : IsClosed (s ∩ u) := by
  rw [←closure_subset_iff_isClosed, ←sdiff_eq_empty]
  by_contra h
  simp only [← ne_eq, ← nonempty_iff_ne_empty] at h
  rcases h with ⟨x, h⟩; simp only [mem_sdiff, mem_inter_iff, not_and] at h
  have sus : closure (s ∩ u) ⊆ s := by
    nth_rw 2 [← sc.closure_eq]; apply closure_mono; apply inter_subset_left
  have xs := sus h.1
  have m := not_or.mpr ⟨h.2 xs, notMem_of_mem_compl (closure_inter_subset_compl vo d h.1)⟩
  rw [← mem_union _ _ _] at m; exact notMem_subset suv m xs

/-- In a `NormalSpace`, `s` is preconnected iff for any two disjoint open sets that cover it,
    `s` is contained in one of them.  This is an open version of
    `isPreconnected_iff_subset_of_disjoint_closed`. -/
theorem isPreconnected_iff_subset_of_fully_disjoint_open [NormalSpace X] {s : Set X}
    (sc : IsClosed s) :
    IsPreconnected s ↔ ∀ u v, IsOpen u → IsOpen v → s ⊆ u ∪ v → Disjoint u v → s ⊆ u ∨ s ⊆ v := by
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed sc]; constructor
  · intro h u v uo vo suv uv
    have suc : IsClosed (s ∩ u) := isClosed_closed_inter sc vo uv suv
    have svc : IsClosed (s ∩ v) := isClosed_closed_inter sc uo uv.symm ((union_comm u v).subst suv)
    have h0 : s ⊆ s ∩ u ∪ s ∩ v := by
      simp only [←inter_union_distrib_left]; exact subset_inter (subset_refl _) suv
    have h1 : Disjoint (s ∩ u) (s ∩ v) := Disjoint.inter_left' _ (Disjoint.inter_right' _ uv)
    cases' h (s ∩ u) (s ∩ v) suc svc h0 h1 with su sv
    · left; exact (subset_inter_iff.mp su).2
    · right; exact (subset_inter_iff.mp sv).2
  · intro h u v uc vc suv uv
    rcases NormalSpace.normal u v uc vc uv with ⟨u', v', uo, vo, uu, vv, uv'⟩
    cases' h u' v' uo vo (_root_.trans suv (union_subset_union uu vv)) uv' with h h
    · left; intro x m; cases' (mem_union _ _ _).mp (suv m) with mu mv
      exact mu; exfalso; exact disjoint_left.mp uv' (h m) (vv mv)
    · right; intro x m; cases' (mem_union _ _ _).mp (suv m) with mu mv
      exfalso; exact disjoint_right.mp uv' (h m) (uu mu); exact mv

/-- Directed intersections of preconnected compact sets are preconnected -/
public theorem IsPreconnected.directed_iInter {I : Type} {s : I → Set X} [Nonempty I] [T4Space X]
    (d : Directed (· ⊇ ·) s) (p : ∀ a, IsPreconnected (s a)) (c : ∀ a, IsCompact (s a)) :
    IsPreconnected (⋂ a, s a) := by
  contrapose p
  have ci : IsClosed (⋂ a, s a) := isClosed_iInter fun i ↦ (c i).isClosed
  simp only [isPreconnected_iff_subset_of_fully_disjoint_open ci, not_forall] at p
  simp only [isPreconnected_iff_subset_of_fully_disjoint_open (c _).isClosed, not_forall]
  rcases p with ⟨u, v, uo, vo, suv, uv, no⟩
  have e : ∃ a, s a ⊆ u ∪ v := by
    by_contra h; simp only [not_exists, Set.not_subset] at h
    suffices n : (⋂ a, s a \ (u ∪ v)).Nonempty by
      rcases n with ⟨x, n⟩; simp only [mem_iInter, mem_sdiff, forall_and, forall_const] at n
      rw [← mem_iInter] at n; simp only [suv n.1, not_true] at n; exact n.2
    apply IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    intro a b; rcases d a b with ⟨c, ac, bc⟩
    use c, (sdiff_subset_sdiff_left ac.le).ge, (sdiff_subset_sdiff_left bc.le).ge
    intro a; rcases h a with ⟨x, xa, xuv⟩; exact ⟨x, mem_sdiff_of_mem xa xuv⟩
    intro a; exact (c a).diff (uo.union vo)
    intro a; exact ((c a).diff (uo.union vo)).isClosed
  rcases e with ⟨a, auv⟩
  use a, u, v, uo, vo, auv, uv
  contrapose no
  cases' no with su sv
  left; exact _root_.trans (iInter_subset _ _) su
  right; exact _root_.trans (iInter_subset _ _) sv

/-- The limit points of a ray `atTop` are preconnected, where a ray is a map from a linearly
    ordered, conditionally complete space. -/
theorem IsPreconnected.limits_atTop [CompactSpace X] [T4Space X] {P : Type} [SemilatticeSup P]
    [TopologicalSpace P] [Nonempty P] (p : ∀ a : P, IsPreconnected (Ici a))
    {r : P → X} (rc : Continuous r) : IsPreconnected {x | MapClusterPt x atTop r} := by
  generalize hs : (fun a ↦ closure (r '' Ici a)) = s
  have m : Antitone s := by
    intro a b ab; rw [← hs]; exact closure_mono (monotone_image (Ici_subset_Ici.mpr ab))
  have d : Directed (· ⊇ ·) s := by
    intro a b; exact ⟨a ⊔ b, (m le_sup_left).ge, (m le_sup_right).ge⟩
  have p : ∀ a, IsPreconnected (s a) := by
    intro a; rw [← hs]; exact ((p _).image _ rc.continuousOn).closure
  have c : ∀ a, IsCompact (s a) := by
    intro a; rw [← hs]; exact isClosed_closure.isCompact
  have e : {x | MapClusterPt x atTop r} = ⋂ a, s a := by
    ext x
    simp only [mem_ofPred, mem_iInter, mapClusterPt_iff_frequently, mem_closure_iff_nhds,
      Set.Nonempty, @forall_comm P, ← hs]
    apply forall_congr'; intro t
    simp only [mem_inter_iff, mem_image, mem_Ici, @and_comm (_ ∈ t), exists_exists_and_eq_and,
      Filter.frequently_atTop]
  rw [e]; exact IsPreconnected.directed_iInter d p c

/-- The limit points of a ray `atBot` are preconnected (the other direction of the ray in
    `IsPreconnected.limits_atTop`) -/
theorem IsPreconnected.limits_atBot [CompactSpace X] [T4Space X] {P : Type} [SemilatticeInf P]
    [TopologicalSpace P] [Nonempty P] (p : ∀ a : P, IsPreconnected (Iic a))
    {r : P → X} (rc : Continuous r) : IsPreconnected {x | MapClusterPt x atBot r} := by
  set r' : Pᵒᵈ → X := r
  have rc' : Continuous r' := rc
  have p' : ∀ a : Pᵒᵈ, IsPreconnected (Ici a) := fun a ↦ p a
  exact IsPreconnected.limits_atTop p' rc'

/-- The limits points near `a` of an open curve from `Ioc a b` are preconnected -/
-- Ideally I'd use `IsPreconnected.limits_atTop` to prove this, but when I tried that
-- I hit horrible instance resolution mismatches.
public theorem IsPreconnected.limits_Ioc [CompactSpace X] [T4Space X] {r : ℝ → X} {a b : ℝ}
    (rc : ContinuousOn r (Ioc a b)) : IsPreconnected {x | MapClusterPt x (𝓝[Ioc a b] a) r} := by
  by_cases ab : ¬a < b
  · simp only [Ioc_eq_empty ab, nhdsWithin_empty, MapClusterPt, Filter.map_bot, ClusterPt.bot,
      ofPred_false, isPreconnected_empty]
  simp only [not_not] at ab
  generalize hs : (fun t : Ioc a b ↦ closure (r '' Ioc a t)) = s
  have n : Nonempty (Ioc a b) := ⟨b, right_mem_Ioc.mpr ab⟩
  have m : Monotone s := by
    intro a b ab; rw [← hs]; refine closure_mono (monotone_image ?_)
    exact Ioc_subset_Ioc (le_refl _) (Subtype.coe_le_coe.mpr ab)
  have d : Directed (· ⊇ ·) s := fun a b ↦
    ⟨min a b, (m (min_le_left _ _)).ge, (m (min_le_right _ _)).ge⟩
  have p : ∀ t, IsPreconnected (s t) := by
    intro ⟨t, m⟩; rw [← hs]; refine (isPreconnected_Ioc.image _ (rc.mono ?_)).closure
    simp only [mem_Ioc] at m
    simp only [Ioc_subset_Ioc_iff m.1, m.2, le_refl, true_and]
  have c : ∀ t, IsCompact (s t) := by intro t; rw [← hs]; exact isClosed_closure.isCompact
  have e : {x | MapClusterPt x (𝓝[Ioc a b] a) r} = ⋂ t, s t := by
    apply Set.ext; intro x
    simp only [mem_ofPred, mem_iInter, mapClusterPt_iff_frequently, mem_closure_iff_nhds,
      Set.Nonempty, @forall_comm _ (Set X), ← hs]
    apply forall_congr'; intro u
    simp only [Filter.frequently_iff, @forall_comm _ (u ∈ 𝓝 x)]; apply forall_congr'; intro _
    simp only [mem_inter_iff, nhdsWithin_Ioc_eq_nhdsGT ab]
    constructor
    · intro h ⟨t, m⟩
      have tm : Ioc a t ∈ 𝓝[Ioi a] a := by
        apply Ioc_mem_nhdsGT_of_mem
        simp only [mem_Ioc] at m; simp only [mem_Ico]; use le_refl _, m.1
      rcases h tm with ⟨v, vm, vu⟩; exact ⟨r v, vu, mem_image_of_mem _ vm⟩
    · intro h v vm
      rcases mem_nhdsGT_iff_exists_Ioc_subset.mp vm with ⟨w, wa, wv⟩
      simp only [mem_Ioi] at wa
      have m : min w b ∈ Ioc a b := by simp only [mem_Ioc]; use lt_min wa ab, min_le_right _ _
      rcases h ⟨_, m⟩ with ⟨x, xu, rx⟩
      simp only [mem_image, mem_Ioc, le_min_iff] at rx
      rcases rx with ⟨c, ⟨ac, cw, _⟩, cx⟩
      use c, wv (mem_Ioc.mpr ⟨ac, cw⟩); rwa [cx]
  rw [e]; exact IsPreconnected.directed_iInter d p c

/-- Nonempty, relatively clopen subsets of preconnected sets are empty or the full set -/
public theorem IsPreconnected.relative_clopen {s t : Set X} (sp : IsPreconnected s)
    (ne : (s ∩ t).Nonempty) (op : s ∩ t ⊆ interior t) (cl : s ∩ closure t ⊆ t) :
    s ⊆ interior t := by
  generalize hu : (fun x : s ↦ (x : X)) ⁻¹' t = u
  have uo : IsOpen u := by
    rw [← subset_interior_iff_isOpen]; intro ⟨x, m⟩ h
    simp only [mem_preimage, ← hu] at h
    have n := op ⟨m, h⟩
    simp only [mem_interior_iff_mem_nhds, preimage_coe_mem_nhds_subtype, ← hu] at n ⊢
    exact nhdsWithin_le_nhds n
  have uc : IsClosed u := by
    rw [← closure_eq_iff_isClosed]; refine subset_antisymm ?_ subset_closure
    rw [← hu]
    refine _root_.trans (continuous_subtype_val.closure_preimage_subset _) ?_
    intro ⟨x, m⟩ h; exact cl ⟨m, h⟩
  have p : IsPreconnected (univ : Set s) := (Subtype.preconnectedSpace sp).isPreconnected_univ
  cases' disjoint_or_subset_of_isClopen p ⟨uc, uo⟩ with h h
  · simp only [univ_disjoint, preimage_eq_empty_iff, Subtype.range_coe, ← hu] at h
    exfalso; exact ne.not_disjoint h.symm
  · rw [← Subtype.coe_preimage_self, ← hu, preimage_subset_preimage_iff] at h
    exact _root_.trans (subset_inter (subset_refl _) h) op
    simp only [Subtype.range_coe, subset_refl]

/-- `ContinuousOn` images of preconnected sets are preconnected (this is a version of
    `IsPathConnected.image` assuming only `ContinuousOn`) -/
public theorem IsPathConnected.image_of_continuousOn {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {s : Set X} (sc : IsPathConnected s) {f : X → Y} (fc : ContinuousOn f s) :
    IsPathConnected (f '' s) := by
  have uc : IsPathConnected (univ : Set s) := by
    convert sc.preimage_coe (subset_refl _); apply Set.ext; intro x
    simp only [mem_univ, mem_preimage, Subtype.mem]
  have e : f '' s = s.domRestrict f '' univ := by
    apply Set.ext; intro y; constructor
    intro ⟨x, m, e⟩; use⟨x, m⟩, mem_univ _, e
    intro ⟨⟨x, m⟩, _, e⟩; use x, m, e
  rw [e]; exact uc.image (continuousOn_iff_continuous_domRestrict.mp fc)

/-- Circles are path connected -/
public theorem Complex.isPathConnected_sphere {z : ℂ} {r : ℝ} (r0 : 0 ≤ r) :
    IsPathConnected (sphere z r) := by
  rw [← abs_of_nonneg r0, ← image_circleMap_Ioc z r]
  refine IsPathConnected.image ?_ (continuous_circleMap _ _)
  exact (convex_Ioc 0 (2 * π)).isPathConnected (nonempty_Ioc.mpr Real.two_pi_pos)

/-- Path connectedness of `f ⁻¹' frontier s` implies path connectedness of `f ⁻¹' s`,
    for compact `s`.

    Proof: Walk out of s until we hit the frontier, then move within the frontier.
    Unfortunately this seems very tedious to write out, so I'm clearly missing some tricks. -/
public theorem IsPathConnected.of_frontier {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [PathConnectedSpace X] {f : X → Y} {s : Set Y}
    (pc : IsPathConnected (f ⁻¹' frontier s)) (fc : Continuous f) (sc : IsClosed s) :
    IsPathConnected (f ⁻¹' s) := by
  have pc' := pc; rcases pc' with ⟨b, fb, j⟩; use b
  simp only [mem_preimage] at fb j ⊢
  have bs : f b ∈ s := sc.frontier_subset fb
  use bs; intro x fx
  have p := PathConnectedSpace.somePath x b
  generalize hu : Icc (0 : ℝ) 1 ∩ ⋂ (a) (_ : f (p.extend a) ∉ s), Iic a = u
  have bdd : BddAbove u := by rw [← hu, bddAbove_def]; use 1; intro t ⟨m, _⟩; exact m.2
  have un : u.Nonempty := by
    rw [← hu]; use 0, left_mem_Icc.mpr zero_le_one; simp only [mem_iInter₂, mem_Iic]; intro a m
    contrapose m; simp only [p.extend_of_le_zero (not_le.mp m).le, fx]
  have uc : IsClosed u := by
    rw [← hu]; apply isClosed_Icc.inter; apply isClosed_iInter; intro a; apply isClosed_iInter
    intro _; exact isClosed_Iic
  generalize ht : sSup u = t
  have tu : t ∈ u := by rw [← uc.closure_eq, ← ht]; exact csSup_mem_closure un bdd
  have m : t ∈ Icc (0 : ℝ) 1 := by rw [← hu] at tu; exact tu.1
  have lo : ∀ a, a ≤ t → f (p.extend a) ∈ s := by
    intro a h; contrapose h; simp only [not_le]
    replace h : ∀ᶠ b in 𝓝 a, f (p.extend b) ∉ s :=
      (fc.comp p.continuous_extend).continuousAt.eventually_mem (sc.isOpen_compl.mem_nhds h)
    simp only [← hu, mem_inter_iff, mem_iInter₂, mem_Iic] at tu ⊢
    rcases ((frequently_lt_nhds a).and_eventually h).exists with ⟨c, ca, cs⟩
    exact lt_of_le_of_lt (tu.2 c cs) ca
  by_cases t1 : t = 1
  · use p.symm; intro a; simp only [p.symm_apply, Function.comp, mem_preimage]
    rw [← Path.extend_extends']; apply lo; rw [t1]; unit_interval
  replace t1 : t < 1 := Ne.lt_of_le t1 m.2
  have ft : f (p ⟨t, m⟩) ∈ frontier s := by
    simp only [frontier, mem_sdiff, sc.closure_eq]; constructor
    · convert lo t (le_refl _)
      simp only [Path.extend_apply _ m]
    · have e : p ⟨t, m⟩ = p.extend t := by
        simp only [Path.extend, IccExtend, ContinuousMap.coe_mk, Function.comp_apply, projIcc,
          min_eq_right m.2, max_eq_right m.1]
      rw [e]; clear e; simp only [← ht]
      by_contra h
      rw [ht] at h
      have o : IsOpen (f ∘ p.extend ⁻¹' interior s) :=
        isOpen_interior.preimage (fc.comp p.continuous_extend)
      rcases (nhds_basis_Ioo t).mem_iff.mp (o.mem_nhds h) with ⟨⟨x, y⟩, ⟨xt, ty⟩, h⟩
      simp only [subset_def, mem_Ioo, and_imp, mem_preimage, Function.comp] at xt ty h
      rcases exists_between (lt_min ty t1) with ⟨z, tz, zy1⟩; rcases lt_min_iff.mp zy1 with ⟨zy, z1⟩
      suffices h : z ∈ u by linarith [le_csSup bdd h]
      rw [← hu]; refine ⟨⟨_root_.trans m.1 tz.le, z1.le⟩, ?_⟩
      simp only [mem_iInter₂, mem_Iic]; intro w ws
      contrapose ws; simp only [not_le] at ws ⊢
      by_cases xw : x < w; refine interior_subset (h _ xw (_root_.trans ws zy))
      simp only [not_lt] at xw; exact lo _ (_root_.trans xw xt.le)
  -- Walk from b to p t
  refine ((pc.joinedIn _ ft b fb).mono (preimage_mono sc.frontier_subset)).symm.trans
    (JoinedIn.symm ?_)
  -- Walk from x to p t
  generalize hq : (fun a : unitInterval ↦ p.extend (min a t)) = q
  have qc : Continuous q := by
    rw [← hq]; exact p.continuous_extend.comp (continuous_subtype_val.min continuous_const)
  refine ⟨⟨⟨q,qc⟩,?_,?_⟩,?_⟩
  · simp only [← hq]; simp only [Icc.coe_zero, min_eq_left m.1, p.extend_zero]
  · simp only [← hq]
    simp only [Path.extend, Icc.coe_one, min_eq_right m.2, ContinuousMap.coe_mk, IccExtend_apply,
      max_eq_right m.1]
  · intro ⟨a, n⟩; simp only [mem_preimage, Path.coe_mk_mk, ← hq]
    exact lo _ (min_le_right _ _)

theorem IsPathConnected.of_frontier' {X : Type} [TopologicalSpace X] [PathConnectedSpace X]
    {s : Set X} (pc : IsPathConnected (frontier s)) (sc : IsClosed s) : IsPathConnected s :=
  IsPathConnected.of_frontier pc continuous_id sc

/-- If open, preconnected `s` intersects `t` but does not touch `frontier t`, then `s ⊆ t` -/
theorem IsPreconnected.subset_of_disjoint_frontier {s t : Set X} (sp : IsPreconnected s)
    (os : IsOpen s) (ot : IsOpen t) (i : Disjoint (frontier t) s) (n : (s ∩ t).Nonempty) :
    s ⊆ t := by
  have e : s = s ∩ t ∪ (s \ closure t) := by
    simp only [closure_eq_interior_union_frontier, ot.interior_eq, union_comm t, diff_union,
      inter_union_sdiff, i.sdiff_eq_right]
  have d : s ∩ (s ∩ t ∩ (s \ closure t)) = ∅ := by
    ext x
    simp only [mem_inter_iff, mem_sdiff, mem_empty_iff_false, iff_false, not_and, not_not, and_imp,
      forall_self_imp]
    intro _ m _
    exact subset_closure m
  rcases isPreconnected_iff_subset_of_disjoint.mp sp (s ∩ t) (s \ closure t) (os.inter ot)
    (os.sdiff isClosed_closure) (by simp only [← e, subset_refl]) d with h | h
  · exact subset_trans h inter_subset_right
  · obtain ⟨_, xs, xt⟩ := n
    have xd := h xs
    simp [subset_closure xt] at xd

/-- Two intersecting, open, preconnected sets with common frontier are the same -/
public theorem IsPreconnected.eq_of_frontier_eq {s t : Set X} (sp : IsPreconnected s)
    (tp : IsPreconnected t) (os : IsOpen s) (ot : IsOpen t) (f : frontier s = frontier t)
    (n : (s ∩ t).Nonempty) : s = t := by
  apply subset_antisymm
  · exact sp.subset_of_disjoint_frontier os ot (f ▸ disjoint_frontier_iff_isOpen.mpr os) n
  · exact tp.subset_of_disjoint_frontier ot os (f ▸ disjoint_frontier_iff_isOpen.mpr ot)
      (inter_comm _ _ ▸ n)
