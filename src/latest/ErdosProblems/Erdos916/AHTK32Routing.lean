/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos916.AHTWatkinsMesner
import ErdosProblems.Erdos916.AHTSourceLemma62

/-!
# The clean two-fan splice used in the `K_{3,2}` routing argument

This file isolates the final, purely path-theoretic operation in the
`K_{3,2}` case of AHT Lemma 4.5.  The paths from an outside vertex to the
theta are first stopped at their first theta vertices.  Once two such paths
have been selected and a path in the theta between their ends has been
found, the outside paths and the theta path form a simple cycle.
-/

attribute [local instance] Classical.propDecidable

namespace Erdos916

open SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

namespace AHTK32Routing

/-- Two paths meeting only in their common end concatenate to a path. -/
private theorem Walk.IsPath.append_of_inter_eq_endpoint
    {a b c : V} {p : G.Walk a b} {q : G.Walk b c}
    (hp : p.IsPath) (hq : q.IsPath)
    (hinter : ∀ x, x ∈ p.support → x ∈ q.support → x = b) :
    (p.append q).IsPath := by
  rw [Walk.isPath_def, Walk.support_append, List.nodup_append]
  have hpN := hp.support_nodup
  have hqN := hq.support_nodup
  refine ⟨hpN, hqN.tail, ?_⟩
  intro x hxp y hyq hxy
  subst y
  have hxb : x = b := hinter x hxp (List.mem_of_mem_tail hyq)
  subst x
  rw [q.support_eq_cons] at hqN
  exact (List.nodup_cons.mp hqN).1 hyq

/-- Two paths with the same distinct ends, meeting nowhere else, form a
simple cycle when the first path has a displayed internal vertex. -/
private theorem Walk.IsPath.isCycle_append_reverse_of_meet_only_ends
    {s t w : V} {p q : G.Walk s t} (hp : p.IsPath) (hq : q.IsPath)
    (hw : w ∈ p.support) (hws : w ≠ s) (hwt : w ≠ t)
    (hmeet : ∀ a, a ∈ p.support → a ∈ q.support →
      a = s ∨ a = t) :
    (p.append q.reverse).IsCycle := by
  apply hp.isCycle_append hq.reverse
  · rw [List.disjoint_left]
    intro a hap haqr
    have hap' : a ∈ p.support := List.mem_of_mem_tail hap
    have haq' : a ∈ q.support := by
      have : a ∈ q.reverse.support := List.mem_of_mem_tail haqr
      simpa only [Walk.support_reverse, List.mem_reverse] using this
    rcases hmeet a hap' haq' with rfl | rfl
    · have hnd := hp.support_nodup
      rw [← p.cons_tail_support] at hnd
      exact (List.nodup_cons.mp hnd).1 hap
    · have hnd := hq.reverse.support_nodup
      rw [← q.reverse.cons_tail_support] at hnd
      exact (List.nodup_cons.mp hnd).1 haqr
  · left
    by_contra hlen
    have hle : p.length ≤ 1 := by omega
    have hends : p.support = [s, t] ∨ s = t := by
      cases p with
      | nil => exact Or.inr rfl
      | @cons _ a _ hadj r =>
          cases r with
          | nil => simp
          | @cons _ b _ hab r => simp at hle
    rcases hends with hsupp | hst
    · have hwst : w = s ∨ w = t := by simpa [hsupp] using hw
      exact hwst.elim hws hwt
    · subst t
      have hpnil : p = .nil := Walk.isPath_iff_eq_nil.mp hp
      subst p
      exact hws (by simpa using hw)

/-- **Clean two-fan splice.**

`left` and `right` are the two arms from distinct vertices `e,f` of a
subgraph to an outside vertex `b`.  They meet only at `b`.  The path `inside`
lies in the subgraph, joins `e` to `f`, and meets the arms only at its
respective ends.  Hence their union is a simple cycle.  Every pair of named
vertices on `inside` lies on that cycle together with `b`.

In the AHT application, `inside` is the path supplied by the elementary
six-half-route argument in a `WatkinsMesnerK32Source`; `u,v` are two of its
three terminals. -/
theorem hasCycleThroughThree_of_cleanTwoFan
    {e f b u v : V}
    (left : G.Walk e b) (right : G.Walk f b)
    (inside : G.Walk e f)
    (hleft : left.IsPath) (hright : right.IsPath)
    (hinside : inside.IsPath)
    (hef : e ≠ f) (hbe : b ≠ e) (hbf : b ≠ f)
    (harms : ∀ w, w ∈ left.support → w ∈ right.support → w = b)
    (hleft_inside : ∀ w, w ∈ left.support →
      w ∈ inside.support → w = e)
    (hright_inside : ∀ w, w ∈ right.support →
      w ∈ inside.support → w = f)
    (hu : u ∈ inside.support) (hv : v ∈ inside.support) :
    HasCycleThroughThree G b u v := by
  let outside : G.Walk e f := left.append right.reverse
  have houtside : outside.IsPath := by
    apply Walk.IsPath.append_of_inter_eq_endpoint hleft hright.reverse
    intro w hwleft hwright
    apply harms w hwleft
    simpa only [Walk.support_reverse, List.mem_reverse] using hwright
  have hbOutside : b ∈ outside.support := by
    simp only [outside, Walk.mem_support_append_iff]
    exact Or.inl left.end_mem_support
  have hmeet : ∀ w, w ∈ outside.support →
      w ∈ inside.support → w = e ∨ w = f := by
    intro w hwout hwin
    have hwcases : w ∈ left.support ∨ w ∈ right.support := by
      simpa only [outside, Walk.mem_support_append_iff, Walk.support_reverse,
        List.mem_reverse] using hwout
    rcases hwcases with hwleft | hwright
    · exact Or.inl (hleft_inside w hwleft hwin)
    · exact Or.inr (hright_inside w hwright hwin)
  let C : G.Walk e e := outside.append inside.reverse
  have hC : C.IsCycle := by
    exact Walk.IsPath.isCycle_append_reverse_of_meet_only_ends
      houtside hinside hbOutside hbe hbf hmeet
  refine ⟨e, C, hC, ?_, ?_, ?_⟩
  · simpa only [C, Walk.mem_support_append_iff] using Or.inl hbOutside
  · simpa only [C, Walk.mem_support_append_iff, Walk.support_reverse,
      List.mem_reverse] using Or.inr hu
  · simpa only [C, Walk.mem_support_append_iff, Walk.support_reverse,
      List.mem_reverse] using Or.inr hv

/-! ## The theta support and clean fans into it -/

/-- The vertex set of the three routes of a Watkins--Mesner `K_{3,2}`
source. -/
def K32Support {x y z : V} (T : WatkinsMesnerK32Source G x y z) : Set V :=
  {w | w ∈ T.xRoute.support ∨ w ∈ T.yRoute.support ∨
    w ∈ T.zRoute.support}

@[simp] theorem mem_K32Support {x y z w : V}
    (T : WatkinsMesnerK32Source G x y z) :
    w ∈ K32Support T ↔
      w ∈ T.xRoute.support ∨ w ∈ T.yRoute.support ∨
        w ∈ T.zRoute.support := by
  rfl

/-- Three pairwise internally disjoint arms, already stopped at their first
vertices in the `K_{3,2}` source.  This is the exact output expected from
the first-hit cleanup of the original three-fan.

The arms are oriented from their theta ends to the common outside end so
that two selected arms concatenate directly. -/
structure CleanThreeFan {x y z : V}
    (T : WatkinsMesnerK32Source G x y z) (b : V) where
  endpoint : Fin 3 → V
  endpoint_injective : Function.Injective endpoint
  endpoint_mem : ∀ i, endpoint i ∈ K32Support T
  arm : ∀ i, G.Walk (endpoint i) b
  arm_isPath : ∀ i, (arm i).IsPath
  arms_meet_only_endpoint : Pairwise fun i j ↦
    ∀ w, w ∈ (arm i).support → w ∈ (arm j).support → w = b
  arm_meets_support_only_start : ∀ i w, w ∈ (arm i).support →
    w ∈ K32Support T → w = endpoint i

/-- Stop three raw arms at their first vertices in the theta. -/
theorem exists_cleanThreeFan_of_rawArms
    {x y z b : V} (T : WatkinsMesnerK32Source G x y z)
    (terminal : Fin 3 → V)
    (terminal_mem : ∀ i, terminal i ∈ K32Support T)
    (raw : ∀ i, G.Walk (terminal i) b)
    (raw_isPath : ∀ i, (raw i).IsPath)
    (raw_meet_only_b : Pairwise fun i j ↦
      ∀ w, w ∈ (raw i).support → w ∈ (raw j).support → w = b)
    (hb : b ∉ K32Support T) :
    Nonempty (CleanThreeFan T b) := by
  let X : Finset V := Finset.univ.filter fun w ↦ w ∈ K32Support T
  have hbX : b ∉ X := by
    intro hbmem
    apply hb
    simpa only [X, Finset.mem_filter, Finset.mem_univ, true_and] using hbmem
  have htX : ∀ i, terminal i ∈ X := by
    intro i
    simpa [X] using terminal_mem i
  choose endpoint hendX q hq hqsub hqfirst using fun i ↦
    exists_initialPath_to_finset X hbX (htX i) (raw i).reverse
      (raw_isPath i).reverse
  let arm : ∀ i, G.Walk (endpoint i) b := fun i ↦ (q i).reverse
  have hendMem : ∀ i, endpoint i ∈ K32Support T := by
    intro i
    simpa [X] using hendX i
  have harmPath : ∀ i, (arm i).IsPath := by
    intro i
    exact (hq i).reverse
  have harmSub : ∀ i w, w ∈ (arm i).support →
      w ∈ (raw i).support := by
    intro i w hw
    have hwq : w ∈ (q i).support := by
      simpa only [arm, Walk.support_reverse, List.mem_reverse] using hw
    have hwrawrev : w ∈ (raw i).reverse.support := hqsub i w hwq
    simpa only [Walk.support_reverse, List.mem_reverse] using hwrawrev
  have harmsg : Pairwise fun i j ↦
      ∀ w, w ∈ (arm i).support → w ∈ (arm j).support → w = b := by
    intro i j hij w hwi hwj
    exact raw_meet_only_b hij w (harmSub i w hwi) (harmSub j w hwj)
  have hendInj : Function.Injective endpoint := by
    intro i j hij
    by_contra hne
    have hiarm : endpoint i ∈ (arm i).support := (arm i).start_mem_support
    have hjarm : endpoint j ∈ (arm j).support := (arm j).start_mem_support
    have hib : endpoint i = b :=
      harmsg hne (endpoint i) hiarm (hij.symm ▸ hjarm)
    exact hb (hib ▸ hendMem i)
  refine ⟨{
    endpoint := endpoint
    endpoint_injective := hendInj
    endpoint_mem := hendMem
    arm := arm
    arm_isPath := harmPath
    arms_meet_only_endpoint := harmsg
    arm_meets_support_only_start := ?_ }⟩
  intro i w hwarm hwX
  have hwq : w ∈ (q i).support := by
    simpa only [arm, Walk.support_reverse, List.mem_reverse] using hwarm
  apply hqfirst i w hwq
  simpa [X] using hwX

/-- Two different routes of the theta form a cycle.  A named internal
vertex of the first route witnesses the nondegeneracy required by
`Walk.IsCycle`. -/
private theorem cycle_of_two_k32_routes
    {A B p : V} {P Q : G.Walk A B}
    (hP : P.IsPath) (hQ : Q.IsPath)
    (hp : p ∈ P.support) (hpA : p ≠ A) (hpB : p ≠ B)
    (hmeet : ∀ w, w ∈ P.support → w ∈ Q.support →
      w = A ∨ w = B) :
    (P.append Q.reverse).IsCycle := by
  exact Walk.IsPath.isCycle_append_reverse_of_meet_only_ends
    hP hQ hp hpA hpB hmeet

/-- If the fan end `b` is already in the theta, two of the three terminal
routes themselves give the required cycle. -/
theorem cycleThroughTwoTerminals_of_mem_K32Support
    {x y z b : V} (T : WatkinsMesnerK32Source G x y z)
    (hb : b ∈ K32Support T) :
    HasCycleThroughThree G b x y ∨
      HasCycleThroughThree G b x z ∨
      HasCycleThroughThree G b y z := by
  rcases hb with hbX | hbY | hbZ
  · left
    let C : G.Walk T.branchA T.branchA :=
      T.xRoute.append T.yRoute.reverse
    have hC : C.IsCycle := cycle_of_two_k32_routes
      T.xRoute_isPath T.yRoute_isPath T.x_mem
      T.x_internal.1 T.x_internal.2 T.xRoute_inter_yRoute
    exact ⟨T.branchA, C, hC, by simp [C, hbX], by simp [C, T.x_mem],
      by simp [C, T.y_mem]⟩
  · left
    let C : G.Walk T.branchA T.branchA :=
      T.xRoute.append T.yRoute.reverse
    have hC : C.IsCycle := cycle_of_two_k32_routes
      T.xRoute_isPath T.yRoute_isPath T.x_mem
      T.x_internal.1 T.x_internal.2 T.xRoute_inter_yRoute
    exact ⟨T.branchA, C, hC, by simp [C, hbY], by simp [C, T.x_mem],
      by simp [C, T.y_mem]⟩
  · right; left
    let C : G.Walk T.branchA T.branchA :=
      T.xRoute.append T.zRoute.reverse
    have hC : C.IsCycle := cycle_of_two_k32_routes
      T.xRoute_isPath T.zRoute_isPath T.x_mem
      T.x_internal.1 T.x_internal.2 T.xRoute_inter_zRoute
    exact ⟨T.branchA, C, hC, by simp [C, hbZ], by simp [C, T.x_mem],
      by simp [C, T.z_mem]⟩

/-! ## Completing one half-route to a branch vertex -/

/-- If `e` is between the `A`-branch and the named terminal `t` on a
simple `A`--`B` route, the rest of the route is a simple `e`--`B` path
through `t`. -/
private structure ToRightBranch {A B t : V} (P : G.Walk A B) (e : V) where
  start_mem_route : e ∈ P.support
  before : G.Walk A e
  path : G.Walk e B
  before_eq_takeUntil : before = P.takeUntil e start_mem_route
  before_isPath : before.IsPath
  isPath : path.IsPath
  decomp : before.append path = P
  pieces_meet_only_start : ∀ w, w ∈ before.support →
    w ∈ path.support → w = e
  terminal_mem : t ∈ path.support
  support_subset : ∀ w, w ∈ path.support → w ∈ P.support
  left_mem_imp_start : A ∈ path.support → A = e
  right_mem_before_imp_end : B ∈ before.support → B = e

private theorem exists_toRightBranch
    {A B t e : V} (P : G.Walk A B) (hP : P.IsPath)
    (ht : t ∈ P.support)
    (he : e ∈ (P.takeUntil t ht).support) :
    Nonempty (ToRightBranch (t := t) P e) := by
  let pref : G.Walk A t := P.takeUntil t ht
  let before : G.Walk A e := pref.takeUntil e he
  let middle : G.Walk e t := pref.dropUntil e he
  let after : G.Walk t B := P.dropUntil t ht
  let q : G.Walk e B := middle.append after
  have hdecomp : before.append q = P := by
    simp only [before, q, middle, after, Walk.append_assoc, pref,
      Walk.take_spec]
  have hwhole : (before.append q).IsPath := by
    rw [hdecomp]
    exact hP
  have hq : q.IsPath := Walk.IsPath.of_append_right hwhole
  have hbefore : before.IsPath := Walk.IsPath.of_append_left hwhole
  have heP : e ∈ P.support := P.support_takeUntil_subset_support ht he
  have hbeforeEq : before = P.takeUntil e heP := by
    exact P.takeUntil_takeUntil ht he
  have hmeetPieces : ∀ w, w ∈ before.support →
      w ∈ q.support → w = e := by
    intro w hwbefore hwq
    have hwcases : w = e ∨ w ∈ q.support.tail := by
      rw [← q.cons_tail_support] at hwq
      exact List.mem_cons.mp hwq
    rcases hwcases with hwe | hwtail
    · exact hwe
    · rw [Walk.isPath_def, Walk.support_append, List.nodup_append] at hwhole
      exact (hwhole.2.2 w hwbefore w hwtail rfl).elim
  refine ⟨{
    start_mem_route := heP
    before := before
    path := q
    before_eq_takeUntil := hbeforeEq
    before_isPath := hbefore
    isPath := hq
    decomp := hdecomp
    pieces_meet_only_start := hmeetPieces
    terminal_mem := ?_
    support_subset := ?_
    left_mem_imp_start := ?_
    right_mem_before_imp_end := ?_ }⟩
  · simp only [q, Walk.mem_support_append_iff]
    exact Or.inl middle.end_mem_support
  · intro w hw
    have : w ∈ (before.append q).support := by
      simp only [Walk.mem_support_append_iff]
      exact Or.inr hw
    rwa [hdecomp] at this
  · intro hA
    by_contra hAe
    have hAtail : A ∈ q.support.tail := by
      rw [← q.cons_tail_support] at hA
      exact (List.mem_cons.mp hA).resolve_left hAe
    have hAbefore : A ∈ before.support := before.start_mem_support
    rw [Walk.isPath_def, Walk.support_append, List.nodup_append] at hwhole
    exact hwhole.2.2 A hAbefore A hAtail rfl
  · intro hB
    by_contra hBe
    have hBtail : B ∈ q.support.tail := q.end_mem_tail_support_of_ne (Ne.symm hBe)
    rw [Walk.isPath_def, Walk.support_append, List.nodup_append] at hwhole
    exact hwhole.2.2 B hB B hBtail rfl

/-- If `e` is between the named terminal `t` and the `B`-branch on a
simple `A`--`B` route, the initial part of the route, reversed, is a simple
`e`--`A` path through `t`. -/
private structure ToLeftBranch {A B t : V} (P : G.Walk A B) (e : V) where
  path : G.Walk e A
  isPath : path.IsPath
  terminal_mem : t ∈ path.support
  support_subset : ∀ w, w ∈ path.support → w ∈ P.support
  right_mem_imp_start : B ∈ path.support → B = e

private theorem exists_toLeftBranch
    {A B t e : V} (P : G.Walk A B) (hP : P.IsPath)
    (ht : t ∈ P.support)
    (he : e ∈ (P.dropUntil t ht).support) :
    Nonempty (ToLeftBranch (t := t) P e) := by
  let pref : G.Walk A t := P.takeUntil t ht
  let suff : G.Walk t B := P.dropUntil t ht
  let middle : G.Walk t e := suff.takeUntil e he
  let after : G.Walk e B := suff.dropUntil e he
  let q0 : G.Walk A e := pref.append middle
  let q : G.Walk e A := q0.reverse
  have hdecomp : q0.append after = P := by
    rw [← Walk.append_assoc]
    simp only [q0, pref, middle, after, suff, Walk.take_spec]
  have hwhole : (q0.append after).IsPath := by
    rw [hdecomp]
    exact hP
  have hq0 : q0.IsPath := Walk.IsPath.of_append_left hwhole
  have hq : q.IsPath := hq0.reverse
  refine ⟨{
    path := q
    isPath := hq
    terminal_mem := ?_
    support_subset := ?_
    right_mem_imp_start := ?_ }⟩
  · have htq0 : t ∈ q0.support := by
      simp only [q0, Walk.mem_support_append_iff]
      exact Or.inl pref.end_mem_support
    simpa only [q, Walk.support_reverse, List.mem_reverse] using htq0
  · intro w hw
    have hwq0 : w ∈ q0.support := by
      simpa only [q, Walk.support_reverse, List.mem_reverse] using hw
    have : w ∈ (q0.append after).support := by
      simp only [Walk.mem_support_append_iff]
      exact Or.inl hwq0
    rwa [hdecomp] at this
  · intro hB
    have hBq0 : B ∈ q0.support := by
      simpa only [q, Walk.support_reverse, List.mem_reverse] using hB
    by_contra hBe
    have hBtail : B ∈ after.support.tail :=
      after.end_mem_tail_support_of_ne (Ne.symm hBe)
    rw [Walk.isPath_def, Walk.support_append, List.nodup_append] at hwhole
    exact hwhole.2.2 B hBq0 B hBtail rfl

/-! ## Two different theta routes -/

/-- The path inside two theta routes which will be spliced to an external
two-fan. -/
structure PairInsidePath
    {A B p q e f : V} (P Q : G.Walk A B) where
  path : G.Walk e f
  isPath : path.IsPath
  p_mem : p ∈ path.support
  q_mem : q ∈ path.support
  support_subset : ∀ w, w ∈ path.support →
    w ∈ P.support ∨ w ∈ Q.support

/-- Different routes, with both selected vertices on their `A`-halves. -/
private theorem exists_pairInsidePath_of_leftHalves
    {A B p q e f : V} (P Q : G.Walk A B)
    (hP : P.IsPath) (hQ : Q.IsPath)
    (hp : p ∈ P.support) (hq : q ∈ Q.support)
    (he : e ∈ (P.takeUntil p hp).support)
    (hf : f ∈ (Q.takeUntil q hq).support)
    (hef : e ≠ f)
    (hmeet : ∀ w, w ∈ P.support → w ∈ Q.support →
      w = A ∨ w = B) :
    Nonempty (PairInsidePath (p := p) (q := q) (e := e) (f := f) P Q) := by
  obtain ⟨EP⟩ := exists_toRightBranch P hP hp he
  obtain ⟨FQ⟩ := exists_toRightBranch Q hQ hq hf
  let inside : G.Walk e f := EP.path.append FQ.path.reverse
  have hinter : ∀ w, w ∈ EP.path.support →
      w ∈ FQ.path.reverse.support → w = B := by
    intro w hwP hwQr
    have hwQ : w ∈ FQ.path.support := by
      simpa only [Walk.support_reverse, List.mem_reverse] using hwQr
    rcases hmeet w (EP.support_subset w hwP) (FQ.support_subset w hwQ) with
      hwA | hwB
    · have hAe : A = e := EP.left_mem_imp_start (hwA ▸ hwP)
      have hAf : A = f := FQ.left_mem_imp_start (hwA ▸ hwQ)
      exact (hef (hAe.symm.trans hAf)).elim
    · exact hwB
  have hi : inside.IsPath := by
    exact Walk.IsPath.append_of_inter_eq_endpoint EP.isPath FQ.isPath.reverse hinter
  refine ⟨{
    path := inside
    isPath := hi
    p_mem := ?_
    q_mem := ?_
    support_subset := ?_ }⟩
  · simp only [inside, Walk.mem_support_append_iff]
    exact Or.inl EP.terminal_mem
  · simp only [inside, Walk.mem_support_append_iff, Walk.support_reverse,
      List.mem_reverse]
    exact Or.inr FQ.terminal_mem
  · intro w hw
    have hw' : w ∈ EP.path.support ∨ w ∈ FQ.path.support := by
      simpa only [inside, Walk.mem_support_append_iff, Walk.support_reverse,
        List.mem_reverse] using hw
    exact hw'.elim
      (fun h ↦ Or.inl (EP.support_subset w h))
      (fun h ↦ Or.inr (FQ.support_subset w h))

/-- Different routes, with both selected vertices on their `B`-halves. -/
private theorem exists_pairInsidePath_of_rightHalves
    {A B p q e f : V} (P Q : G.Walk A B)
    (hP : P.IsPath) (hQ : Q.IsPath)
    (hp : p ∈ P.support) (hq : q ∈ Q.support)
    (he : e ∈ (P.dropUntil p hp).support)
    (hf : f ∈ (Q.dropUntil q hq).support)
    (hef : e ≠ f)
    (hmeet : ∀ w, w ∈ P.support → w ∈ Q.support →
      w = A ∨ w = B) :
    Nonempty (PairInsidePath (p := p) (q := q) (e := e) (f := f) P Q) := by
  obtain ⟨EP⟩ := exists_toLeftBranch P hP hp he
  obtain ⟨FQ⟩ := exists_toLeftBranch Q hQ hq hf
  let inside : G.Walk e f := EP.path.append FQ.path.reverse
  have hinter : ∀ w, w ∈ EP.path.support →
      w ∈ FQ.path.reverse.support → w = A := by
    intro w hwP hwQr
    have hwQ : w ∈ FQ.path.support := by
      simpa only [Walk.support_reverse, List.mem_reverse] using hwQr
    rcases hmeet w (EP.support_subset w hwP) (FQ.support_subset w hwQ) with
      hwA | hwB
    · exact hwA
    · have hBe : B = e := EP.right_mem_imp_start (hwB ▸ hwP)
      have hBf : B = f := FQ.right_mem_imp_start (hwB ▸ hwQ)
      exact (hef (hBe.symm.trans hBf)).elim
  have hi : inside.IsPath := by
    exact Walk.IsPath.append_of_inter_eq_endpoint EP.isPath FQ.isPath.reverse hinter
  refine ⟨{
    path := inside
    isPath := hi
    p_mem := ?_
    q_mem := ?_
    support_subset := ?_ }⟩
  · simp only [inside, Walk.mem_support_append_iff]
    exact Or.inl EP.terminal_mem
  · simp only [inside, Walk.mem_support_append_iff, Walk.support_reverse,
      List.mem_reverse]
    exact Or.inr FQ.terminal_mem
  · intro w hw
    have hw' : w ∈ EP.path.support ∨ w ∈ FQ.path.support := by
      simpa only [inside, Walk.mem_support_append_iff, Walk.support_reverse,
        List.mem_reverse] using hw
    exact hw'.elim
      (fun h ↦ Or.inl (EP.support_subset w h))
      (fun h ↦ Or.inr (FQ.support_subset w h))

/-! ## Two selected vertices on the same theta route -/

/-- Along one walk, either of two support vertices occurs no later than the
other.  This is the small order fact needed in the same-route subcase. -/
private theorem mem_takeUntil_or_mem_takeUntil
    {A B e f : V} (P : G.Walk A B)
    (he : e ∈ P.support) (hf : f ∈ P.support) :
    f ∈ (P.takeUntil e he).support ∨
      e ∈ (P.takeUntil f hf).support := by
  simp only [Walk.takeUntil_eq_take, Walk.support_copy, Walk.support_take,
    List.mem_take_iff_idxOf_lt hf, List.mem_take_iff_idxOf_lt he]
  omega

/-- Same route, both selected vertices on its `A`-half.  The complementary
arc goes from the later selected vertex to `B`, backwards along a second
route to `A`, and then to the earlier selected vertex. -/
theorem exists_pairInsidePath_sameRoute_leftHalf
    {A B p q e f : V} (P Q : G.Walk A B)
    (hP : P.IsPath) (hQ : Q.IsPath)
    (hp : p ∈ P.support) (hq : q ∈ Q.support)
    (he : e ∈ (P.takeUntil p hp).support)
    (hf : f ∈ (P.takeUntil p hp).support)
    (hef : e ≠ f)
    (hmeet : ∀ w, w ∈ P.support → w ∈ Q.support →
      w = A ∨ w = B) :
    Nonempty (PairInsidePath (p := p) (q := q) (e := e) (f := f) P Q) := by
  have build (e f : V)
      (he : e ∈ (P.takeUntil p hp).support)
      (hf : f ∈ (P.takeUntil p hp).support)
      (hef : e ≠ f)
      (hfBefore : f ∈
        ((P.takeUntil p hp).takeUntil e he).support) :
      Nonempty (PairInsidePath (p := p) (q := q) (e := e) (f := f) P Q) := by
    obtain ⟨EP⟩ := exists_toRightBranch P hP hp he
    have hfEPBefore : f ∈ EP.before.support := by
      rw [EP.before_eq_takeUntil, ← P.takeUntil_takeUntil hp he]
      exact hfBefore
    let early : G.Walk A f := EP.before.takeUntil f hfEPBefore
    have hearly : early.IsPath := EP.before_isPath.takeUntil hfEPBefore
    have heNotEarly : e ∉ early.support := by
      have hendCut :
          EP.before.takeUntil e EP.before.end_mem_support = EP.before := by
        have hdrop := EP.before_isPath.dropUntil EP.before.end_mem_support
        have hnil : EP.before.dropUntil e EP.before.end_mem_support =
            (.nil : G.Walk e e) := Walk.isPath_iff_eq_nil.mp hdrop
        have hspec := EP.before.take_spec EP.before.end_mem_support
        simpa only [hnil, Walk.append_nil] using hspec
      have hfCut : f ∈
          (EP.before.takeUntil e EP.before.end_mem_support).support := by
        rw [hendCut]
        exact hfEPBefore
      exact EP.before.notMem_support_takeUntil_support_takeUntil_subset
        hef.symm EP.before.end_mem_support hfCut
    have heA : e ≠ A := by
      intro heA
      subst e
      have hnil : EP.before = (.nil : G.Walk A A) :=
        Walk.isPath_iff_eq_nil.mp EP.before_isPath
      have hfA : f = A := by
        simpa only [hnil, Walk.support_nil, List.mem_singleton] using hfEPBefore
      exact hef hfA.symm
    have hearlySub : ∀ w, w ∈ early.support → w ∈ P.support := by
      intro w hw
      have hwbefore : w ∈ EP.before.support :=
        EP.before.support_takeUntil_subset_support hfEPBefore hw
      have : w ∈ (EP.before.append EP.path).support := by
        simp only [Walk.mem_support_append_iff]
        exact Or.inl hwbefore
      rwa [EP.decomp] at this
    let around : G.Walk e A := EP.path.append Q.reverse
    have haround : around.IsPath := by
      apply Walk.IsPath.append_of_inter_eq_endpoint EP.isPath hQ.reverse
      intro w hwP hwQr
      have hwQ : w ∈ Q.support := by
        simpa only [Walk.support_reverse, List.mem_reverse] using hwQr
      rcases hmeet w (EP.support_subset w hwP) hwQ with hwA | hwB
      · exact (heA (EP.left_mem_imp_start (hwA ▸ hwP)).symm).elim
      · exact hwB
    let inside : G.Walk e f := around.append early
    have hinside : inside.IsPath := by
      apply Walk.IsPath.append_of_inter_eq_endpoint haround hearly
      intro w hwAround hwEarly
      have hwcases : w ∈ EP.path.support ∨ w ∈ Q.support := by
        simpa only [around, Walk.mem_support_append_iff, Walk.support_reverse,
          List.mem_reverse] using hwAround
      rcases hwcases with hwEP | hwQ
      · have hwBefore : w ∈ EP.before.support :=
          EP.before.support_takeUntil_subset_support hfEPBefore hwEarly
        have hwe : w = e := EP.pieces_meet_only_start w hwBefore hwEP
        exact (heNotEarly (hwe ▸ hwEarly)).elim
      · rcases hmeet w (hearlySub w hwEarly) hwQ with hwA | hwB
        · exact hwA
        · have hBearly : B ∈ early.support := hwB ▸ hwEarly
          have hBe : B = e :=
            EP.right_mem_before_imp_end
              (EP.before.support_takeUntil_subset_support hfEPBefore
                hBearly)
          exact (heNotEarly (hBe ▸ hBearly)).elim
    refine ⟨{
      path := inside
      isPath := hinside
      p_mem := ?_
      q_mem := ?_
      support_subset := ?_ }⟩
    · simp only [inside, around, Walk.mem_support_append_iff]
      exact Or.inl (Or.inl EP.terminal_mem)
    · simp only [inside, around, Walk.mem_support_append_iff,
        Walk.support_reverse, List.mem_reverse]
      exact Or.inl (Or.inr hq)
    · intro w hw
      have hwcases : w ∈ around.support ∨ w ∈ early.support := by
        simpa only [inside, Walk.mem_support_append_iff] using hw
      rcases hwcases with hwAround | hwEarly
      · have : w ∈ EP.path.support ∨ w ∈ Q.support := by
          simpa only [around, Walk.mem_support_append_iff, Walk.support_reverse,
            List.mem_reverse] using hwAround
        exact this.imp_left (EP.support_subset w)
      · exact Or.inl (hearlySub w hwEarly)
  let pref := P.takeUntil p hp
  have heP : e ∈ P.support := P.support_takeUntil_subset_support hp he
  have hfP : f ∈ P.support := P.support_takeUntil_subset_support hp hf
  rcases mem_takeUntil_or_mem_takeUntil pref he hf with hfe | hef'
  · exact build e f he hf hef hfe
  · obtain ⟨R⟩ := build f e hf he hef.symm hef'
    exact ⟨{
      path := R.path.reverse
      isPath := R.isPath.reverse
      p_mem := by simpa using R.p_mem
      q_mem := by simpa using R.q_mem
      support_subset := by
        intro w hw
        apply R.support_subset w
        simpa only [Walk.support_reverse, List.mem_reverse] using hw }⟩

/-- On a simple path, cutting at the final vertex changes nothing. -/
private theorem Walk.IsPath.takeUntil_end_eq
    {A B : V} {P : G.Walk A B} (hP : P.IsPath) :
    P.takeUntil B P.end_mem_support = P := by
  have hdrop : (P.dropUntil B P.end_mem_support).IsPath :=
    hP.dropUntil P.end_mem_support
  have hnil : P.dropUntil B P.end_mem_support = (.nil : G.Walk B B) :=
    Walk.isPath_iff_eq_nil.mp hdrop
  have hspec := P.take_spec P.end_mem_support
  simpa only [hnil, Walk.append_nil] using hspec

/-- Reversing the suffix after `t` gives exactly the prefix ending at `t`
of the reversed simple path. -/
private theorem reverse_dropUntil_eq_takeUntil_reverse
    {A B t : V} (P : G.Walk A B) (hP : P.IsPath)
    (ht : t ∈ P.support) :
    (P.dropUntil t ht).reverse =
      P.reverse.takeUntil t (by simpa using ht) := by
  let L : G.Walk A t := P.takeUntil t ht
  let R : G.Walk t B := P.dropUntil t ht
  have hrev : R.reverse.append L.reverse = P.reverse := by
    have h := congrArg Walk.reverse (P.take_spec ht)
    simpa only [L, R, Walk.reverse_append] using h
  have htake := Walk.takeUntil_append_of_mem_left
    R.reverse L.reverse R.reverse.end_mem_support
  have hR : R.IsPath := hP.dropUntil ht
  have hRrevEnd : R.reverse.takeUntil t R.reverse.end_mem_support = R.reverse :=
    Walk.IsPath.takeUntil_end_eq hR.reverse
  have hcut :
      (R.reverse.append L.reverse).takeUntil t
          (Walk.support_subset_support_append_left
            R.reverse L.reverse R.reverse.end_mem_support) = R.reverse :=
    htake.trans hRrevEnd
  calc
    R.reverse =
        (R.reverse.append L.reverse).takeUntil t
          (Walk.support_subset_support_append_left
            R.reverse L.reverse R.reverse.end_mem_support) := hcut.symm
    _ = P.reverse.takeUntil t (by simpa using ht) := by
      simpa only [hrev]

/-- Same route, both selected vertices on its `B`-half.  Reverse the two
routes and apply the already-proved `A`-half construction. -/
theorem exists_pairInsidePath_sameRoute_rightHalf
    {A B p q e f : V} (P Q : G.Walk A B)
    (hP : P.IsPath) (hQ : Q.IsPath)
    (hp : p ∈ P.support) (hq : q ∈ Q.support)
    (he : e ∈ (P.dropUntil p hp).support)
    (hf : f ∈ (P.dropUntil p hp).support)
    (hef : e ≠ f)
    (hmeet : ∀ w, w ∈ P.support → w ∈ Q.support →
      w = A ∨ w = B) :
    Nonempty (PairInsidePath (p := p) (q := q) (e := e) (f := f) P Q) := by
  have hpR : p ∈ P.reverse.support := by simpa using hp
  have hqR : q ∈ Q.reverse.support := by simpa using hq
  have heR : e ∈ (P.reverse.takeUntil p hpR).support := by
    rw [← reverse_dropUntil_eq_takeUntil_reverse P hP hp]
    simpa using he
  have hfR : f ∈ (P.reverse.takeUntil p hpR).support := by
    rw [← reverse_dropUntil_eq_takeUntil_reverse P hP hp]
    simpa using hf
  have hmeetR : ∀ w, w ∈ P.reverse.support →
      w ∈ Q.reverse.support → w = B ∨ w = A := by
    intro w hwP hwQ
    have hwP' : w ∈ P.support := by simpa using hwP
    have hwQ' : w ∈ Q.support := by simpa using hwQ
    rcases hmeet w hwP' hwQ' with hwA | hwB
    · exact Or.inr hwA
    · exact Or.inl hwB
  obtain ⟨R⟩ := exists_pairInsidePath_sameRoute_leftHalf
    P.reverse Q.reverse hP.reverse hQ.reverse hpR hqR heR hfR hef hmeetR
  exact ⟨{
    path := R.path
    isPath := R.isPath
    p_mem := R.p_mem
    q_mem := R.q_mem
    support_subset := by
      intro w hw
      rcases R.support_subset w hw with hwP | hwQ
      · exact Or.inl (by simpa using hwP)
      · exact Or.inr (by simpa using hwQ) }⟩

/-! ## Uniform indexing of the three theta routes -/

private def k32Route {x y z : V} (T : WatkinsMesnerK32Source G x y z) :
    Fin 3 → G.Walk T.branchA T.branchB
  | 0 => T.xRoute
  | 1 => T.yRoute
  | 2 => T.zRoute

private def k32Terminal {x y z : V}
    (T : WatkinsMesnerK32Source G x y z) : Fin 3 → V
  | 0 => x
  | 1 => y
  | 2 => z

private theorem k32Route_isPath {x y z : V}
    (T : WatkinsMesnerK32Source G x y z) (i : Fin 3) :
    (k32Route T i).IsPath := by
  fin_cases i <;> simp [k32Route, T.xRoute_isPath, T.yRoute_isPath,
    T.zRoute_isPath]

private theorem k32Terminal_mem {x y z : V}
    (T : WatkinsMesnerK32Source G x y z) (i : Fin 3) :
    k32Terminal T i ∈ (k32Route T i).support := by
  fin_cases i <;> simp [k32Route, k32Terminal, T.x_mem, T.y_mem, T.z_mem]

private theorem k32Terminal_internal {x y z : V}
    (T : WatkinsMesnerK32Source G x y z) (i : Fin 3) :
    k32Terminal T i ≠ T.branchA ∧ k32Terminal T i ≠ T.branchB := by
  fin_cases i <;> simp [k32Terminal, T.x_internal, T.y_internal, T.z_internal]

private theorem k32Route_inter {x y z : V}
    (T : WatkinsMesnerK32Source G x y z) {i j : Fin 3} (hij : i ≠ j) :
    ∀ w, w ∈ (k32Route T i).support →
      w ∈ (k32Route T j).support →
      w = T.branchA ∨ w = T.branchB := by
  fin_cases i <;> fin_cases j
  all_goals simp at hij
  · simpa [k32Route] using T.xRoute_inter_yRoute
  · simpa [k32Route] using T.xRoute_inter_zRoute
  · intro w hwY hwX
    exact T.xRoute_inter_yRoute w hwX hwY
  · simpa [k32Route] using T.yRoute_inter_zRoute
  · intro w hwZ hwX
    exact T.xRoute_inter_zRoute w hwX hwZ
  · intro w hwZ hwY
    exact T.yRoute_inter_zRoute w hwY hwZ

private theorem exists_k32Route_of_mem_support {x y z w : V}
    (T : WatkinsMesnerK32Source G x y z) (hw : w ∈ K32Support T) :
    ∃ i : Fin 3, w ∈ (k32Route T i).support := by
  rcases hw with hwX | hwY | hwZ
  · exact ⟨0, by simpa [k32Route]⟩
  · exact ⟨1, by simpa [k32Route]⟩
  · exact ⟨2, by simpa [k32Route]⟩

private theorem k32Route_support_subset {x y z : V}
    (T : WatkinsMesnerK32Source G x y z) (i : Fin 3) :
    ∀ w, w ∈ (k32Route T i).support → w ∈ K32Support T := by
  fin_cases i
  · intro w hw
    exact Or.inl hw
  · intro w hw
    exact Or.inr (Or.inl hw)
  · intro w hw
    exact Or.inr (Or.inr hw)

private def otherRoute (i : Fin 3) : Fin 3 := if i = 0 then 1 else 0

private theorem otherRoute_ne (i : Fin 3) : otherRoute i ≠ i := by
  fin_cases i <;> simp [otherRoute]

/-- An inside path together with the two distinct theta terminals it
contains. -/
private structure K32InsidePath {x y z e f : V}
    (T : WatkinsMesnerK32Source G x y z) where
  first : Fin 3
  second : Fin 3
  first_ne_second : first ≠ second
  path : G.Walk e f
  isPath : path.IsPath
  first_mem : k32Terminal T first ∈ path.support
  second_mem : k32Terminal T second ∈ path.support
  support_subset : ∀ w, w ∈ path.support → w ∈ K32Support T

/-- Two selected theta vertices lying on the same side of their respective
named terminals have an inside path through two distinct terminals.  This
includes the ordering subcase in which both vertices lie on one route. -/
private theorem exists_k32InsidePath_of_sameSide
    {x y z e f : V} (T : WatkinsMesnerK32Source G x y z)
    (r s : Fin 3)
    (he : e ∈ (k32Route T r).support)
    (hf : f ∈ (k32Route T s).support)
    (hef : e ≠ f)
    (leftSide : Prop)
    (heSide : leftSide →
      e ∈ ((k32Route T r).takeUntil (k32Terminal T r)
        (k32Terminal_mem T r)).support)
    (hfSide : leftSide →
      f ∈ ((k32Route T s).takeUntil (k32Terminal T s)
        (k32Terminal_mem T s)).support)
    (heRight : ¬leftSide →
      e ∈ ((k32Route T r).dropUntil (k32Terminal T r)
        (k32Terminal_mem T r)).support)
    (hfRight : ¬leftSide →
      f ∈ ((k32Route T s).dropUntil (k32Terminal T s)
        (k32Terminal_mem T s)).support) :
    Nonempty (K32InsidePath (e := e) (f := f) T) := by
  by_cases hrs : r = s
  · subst s
    let k := otherRoute r
    have hkr : r ≠ k := (otherRoute_ne r).symm
    have hmeet := k32Route_inter T hkr
    by_cases hleft : leftSide
    · obtain ⟨R⟩ := exists_pairInsidePath_sameRoute_leftHalf
        (k32Route T r) (k32Route T k)
        (k32Route_isPath T r) (k32Route_isPath T k)
        (k32Terminal_mem T r) (k32Terminal_mem T k)
        (heSide hleft) (hfSide hleft) hef hmeet
      exact ⟨{
        first := r
        second := k
        first_ne_second := hkr
        path := R.path
        isPath := R.isPath
        first_mem := R.p_mem
        second_mem := R.q_mem
        support_subset := by
          intro w hw
          rcases R.support_subset w hw with hwr | hwk
          · exact k32Route_support_subset T r w hwr
          · exact k32Route_support_subset T k w hwk }⟩
    · obtain ⟨R⟩ := exists_pairInsidePath_sameRoute_rightHalf
        (k32Route T r) (k32Route T k)
        (k32Route_isPath T r) (k32Route_isPath T k)
        (k32Terminal_mem T r) (k32Terminal_mem T k)
        (heRight hleft) (hfRight hleft) hef hmeet
      exact ⟨{
        first := r
        second := k
        first_ne_second := hkr
        path := R.path
        isPath := R.isPath
        first_mem := R.p_mem
        second_mem := R.q_mem
        support_subset := by
          intro w hw
          rcases R.support_subset w hw with hwr | hwk
          · exact k32Route_support_subset T r w hwr
          · exact k32Route_support_subset T k w hwk }⟩
  · have hmeet := k32Route_inter T hrs
    by_cases hleft : leftSide
    · obtain ⟨R⟩ := exists_pairInsidePath_of_leftHalves
        (k32Route T r) (k32Route T s)
        (k32Route_isPath T r) (k32Route_isPath T s)
        (k32Terminal_mem T r) (k32Terminal_mem T s)
        (heSide hleft) (hfSide hleft) hef hmeet
      exact ⟨{
        first := r
        second := s
        first_ne_second := hrs
        path := R.path
        isPath := R.isPath
        first_mem := R.p_mem
        second_mem := R.q_mem
        support_subset := by
          intro w hw
          rcases R.support_subset w hw with hwr | hws
          · exact k32Route_support_subset T r w hwr
          · exact k32Route_support_subset T s w hws }⟩
    · obtain ⟨R⟩ := exists_pairInsidePath_of_rightHalves
        (k32Route T r) (k32Route T s)
        (k32Route_isPath T r) (k32Route_isPath T s)
        (k32Terminal_mem T r) (k32Terminal_mem T s)
        (heRight hleft) (hfRight hleft) hef hmeet
      exact ⟨{
        first := r
        second := s
        first_ne_second := hrs
        path := R.path
        isPath := R.isPath
        first_mem := R.p_mem
        second_mem := R.q_mem
        support_subset := by
          intro w hw
          rcases R.support_subset w hw with hwr | hws
          · exact k32Route_support_subset T r w hwr
          · exact k32Route_support_subset T s w hws }⟩

private theorem hasCycleThroughThree_swap_last
    {a b c : V} (h : HasCycleThroughThree G a b c) :
    HasCycleThroughThree G a c b := by
  obtain ⟨r, C, hC, ha, hb, hc⟩ := h
  exact ⟨r, C, hC, ha, hc, hb⟩

private theorem terminalPair_cycle_disjunction
    {x y z b : V} (T : WatkinsMesnerK32Source G x y z)
    {i j : Fin 3} (hij : i ≠ j)
    (h : HasCycleThroughThree G b (k32Terminal T i) (k32Terminal T j)) :
    HasCycleThroughThree G b x y ∨
      HasCycleThroughThree G b x z ∨
      HasCycleThroughThree G b y z := by
  fin_cases i <;> fin_cases j
  all_goals simp at hij
  · exact Or.inl (by simpa [k32Terminal] using h)
  · exact Or.inr (Or.inl (by simpa [k32Terminal] using h))
  · exact Or.inl (by simpa [k32Terminal] using
      (hasCycleThroughThree_swap_last h))
  · exact Or.inr (Or.inr (by simpa [k32Terminal] using h))
  · exact Or.inr (Or.inl (by simpa [k32Terminal] using
      (hasCycleThroughThree_swap_last h)))
  · exact Or.inr (Or.inr (by simpa [k32Terminal] using
      (hasCycleThroughThree_swap_last h)))

/-- **The six-half-route lemma.**  Three clean arms into a
Watkins--Mesner `K_{3,2}` source force a cycle through their common end and
two of the three named terminals.  The proof assigns each first-hit vertex
to one route and to one of the two halves cut at that route's terminal.
Two of the three hits have the same side; the preceding lemmas construct
the required inside path both when their routes differ and when they are
the same. -/
theorem cycleThroughTwoTerminals_of_cleanThreeFan
    {x y z b : V} (T : WatkinsMesnerK32Source G x y z)
    (F : CleanThreeFan T b) (hb : b ∉ K32Support T) :
    HasCycleThroughThree G b x y ∨
      HasCycleThroughThree G b x z ∨
      HasCycleThroughThree G b y z := by
  choose routeChoice hendRoute using fun i ↦
    exists_k32Route_of_mem_support T (F.endpoint_mem i)
  let Left : Fin 3 → Prop := fun i ↦
    F.endpoint i ∈
      ((k32Route T (routeChoice i)).takeUntil
        (k32Terminal T (routeChoice i))
        (k32Terminal_mem T (routeChoice i))).support
  have hcover (i : Fin 3) : Left i ∨
      F.endpoint i ∈
        ((k32Route T (routeChoice i)).dropUntil
          (k32Terminal T (routeChoice i))
          (k32Terminal_mem T (routeChoice i))).support := by
    have hmem : F.endpoint i ∈
        (((k32Route T (routeChoice i)).takeUntil
          (k32Terminal T (routeChoice i))
          (k32Terminal_mem T (routeChoice i))).append
        ((k32Route T (routeChoice i)).dropUntil
          (k32Terminal T (routeChoice i))
          (k32Terminal_mem T (routeChoice i)))).support := by
      rw [Walk.take_spec]
      exact hendRoute i
    simpa only [Left, Walk.mem_support_append_iff] using hmem
  have hpigeon : ∃ i j : Fin 3, i ≠ j ∧ (Left i ↔ Left j) := by
    by_cases h01 : Left 0 ↔ Left 1
    · exact ⟨0, 1, by decide, h01⟩
    by_cases h02 : Left 0 ↔ Left 2
    · exact ⟨0, 2, by decide, h02⟩
    refine ⟨1, 2, by decide, ?_⟩
    tauto
  obtain ⟨i, j, hij, hside⟩ := hpigeon
  have hef : F.endpoint i ≠ F.endpoint j := by
    intro h
    exact hij (F.endpoint_injective h)
  by_cases hleft : Left i
  · have hleftj : Left j := hside.mp hleft
    obtain ⟨R⟩ := exists_k32InsidePath_of_sameSide T
      (routeChoice i) (routeChoice j) (hendRoute i) (hendRoute j) hef
      (Left i) (fun _ ↦ hleft) (fun _ ↦ hleftj)
      (fun h ↦ (h hleft).elim) (fun h ↦ (h hleft).elim)
    have hbe : b ≠ F.endpoint i := by
      intro h
      exact hb (h.symm ▸ F.endpoint_mem i)
    have hbf : b ≠ F.endpoint j := by
      intro h
      exact hb (h.symm ▸ F.endpoint_mem j)
    have hcycle : HasCycleThroughThree G b
        (k32Terminal T R.first) (k32Terminal T R.second) :=
      hasCycleThroughThree_of_cleanTwoFan
        (F.arm i) (F.arm j) R.path
        (F.arm_isPath i) (F.arm_isPath j) R.isPath
        hef hbe hbf (F.arms_meet_only_endpoint hij)
        (fun w hwarm hwR ↦
          F.arm_meets_support_only_start i w hwarm (R.support_subset w hwR))
        (fun w hwarm hwR ↦
          F.arm_meets_support_only_start j w hwarm (R.support_subset w hwR))
        R.first_mem R.second_mem
    exact terminalPair_cycle_disjunction T R.first_ne_second hcycle
  · have hleftj : ¬Left j := by
      intro hj
      exact hleft (hside.mpr hj)
    have hrighti := (hcover i).resolve_left hleft
    have hrightj := (hcover j).resolve_left hleftj
    obtain ⟨R⟩ := exists_k32InsidePath_of_sameSide T
      (routeChoice i) (routeChoice j) (hendRoute i) (hendRoute j) hef
      (Left i) (fun h ↦ (hleft h).elim) (fun h ↦ (hleft h).elim)
      (fun _ ↦ hrighti) (fun _ ↦ hrightj)
    have hbe : b ≠ F.endpoint i := by
      intro h
      exact hb (h.symm ▸ F.endpoint_mem i)
    have hbf : b ≠ F.endpoint j := by
      intro h
      exact hb (h.symm ▸ F.endpoint_mem j)
    have hcycle : HasCycleThroughThree G b
        (k32Terminal T R.first) (k32Terminal T R.second) :=
      hasCycleThroughThree_of_cleanTwoFan
        (F.arm i) (F.arm j) R.path
        (F.arm_isPath i) (F.arm_isPath j) R.isPath
        hef hbe hbf (F.arms_meet_only_endpoint hij)
        (fun w hwarm hwR ↦
          F.arm_meets_support_only_start i w hwarm (R.support_subset w hwR))
        (fun w hwarm hwR ↦
          F.arm_meets_support_only_start j w hwarm (R.support_subset w hwR))
        R.first_mem R.second_mem
    exact terminalPair_cycle_disjunction T R.first_ne_second hcycle

private def threeTerminals (x y z : V) : Fin 3 → V
  | 0 => x
  | 1 => y
  | 2 => z

private def threeArms {x y z b : V}
    (px : G.Walk x b) (py : G.Walk y b) (pz : G.Walk z b) :
    ∀ i, G.Walk (threeTerminals x y z i) b
  | 0 => px
  | 1 => py
  | 2 => pz

/-- The direct form used in AHT Lemma 4.5.  Three pairwise internally
disjoint paths from the theta terminals to `b` force a cycle through `b`
and two terminals.  If `b` is already in the theta, two theta routes give
the cycle; otherwise the raw arms are stopped at their first theta hits and
the six-half-route lemma applies. -/
theorem cycleThroughTwoTerminals_of_k32Source_and_threeArms
    {x y z b : V} (T : WatkinsMesnerK32Source G x y z)
    (px : G.Walk x b) (py : G.Walk y b) (pz : G.Walk z b)
    (hpx : px.IsPath) (hpy : py.IsPath) (hpz : pz.IsPath)
    (hxy : ∀ w, w ∈ px.support → w ∈ py.support → w = b)
    (hxz : ∀ w, w ∈ px.support → w ∈ pz.support → w = b)
    (hyz : ∀ w, w ∈ py.support → w ∈ pz.support → w = b) :
    HasCycleThroughThree G b x y ∨
      HasCycleThroughThree G b x z ∨
      HasCycleThroughThree G b y z := by
  by_cases hb : b ∈ K32Support T
  · exact cycleThroughTwoTerminals_of_mem_K32Support T hb
  · let terminal := threeTerminals x y z
    let raw := threeArms px py pz
    have hterminal : ∀ i, terminal i ∈ K32Support T := by
      intro i
      fin_cases i <;> simp [terminal, threeTerminals, K32Support,
        T.x_mem, T.y_mem, T.z_mem]
    have hrawPath : ∀ i, (raw i).IsPath := by
      intro i
      fin_cases i
      · exact hpx
      · exact hpy
      · exact hpz
    have hrawMeet : Pairwise fun i j ↦
        ∀ w, w ∈ (raw i).support → w ∈ (raw j).support → w = b := by
      intro i j hij
      fin_cases i <;> fin_cases j
      all_goals simp at hij
      · intro w hwX hwY
        exact hxy w hwX hwY
      · intro w hwX hwZ
        exact hxz w hwX hwZ
      · intro w hwY hwX
        exact hxy w hwX hwY
      · intro w hwY hwZ
        exact hyz w hwY hwZ
      · intro w hwZ hwX
        exact hxz w hwX hwZ
      · intro w hwZ hwY
        exact hyz w hwY hwZ
    obtain ⟨F⟩ := exists_cleanThreeFan_of_rawArms T terminal hterminal
      raw hrawPath hrawMeet hb
    exact cycleThroughTwoTerminals_of_cleanThreeFan T F hb

end AHTK32Routing

end Erdos916
