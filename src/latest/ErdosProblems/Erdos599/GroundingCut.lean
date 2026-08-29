/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.PopularSwitching

/-!
# The cut, fragments, and blocking points in the grounding argument

This file formalizes the order-theoretic core of Aharoni--Berger
Assertions 8.18 and 8.21.  A cut in the auxiliary web has an old-vertex
part `CV` and a represented-ladder-edge part `CE`.  Removing `CE` cuts the
ladder paths into maximal surviving fragments.  A blockable fragment either
meets the escape region `RR`, in which case its blocking point is its first
`RR` vertex, or is finite, in which case its blocking point is its terminal
vertex.

The final theorem in the file isolates the only decoder needed by the
finite-descent proof of Assertion 8.18: an original source--terminal-cut
path avoiding `BB` must decode to a cut-avoiding auxiliary source--target
path.  The contradiction with auxiliary separation is then formal and
contains no graph-theoretic output as a premise.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingCut

open DirectedPath

universe u v

variable {V : Type u} {I : Type v} {Gamma : DWeb V}

abbrev Input (Gamma : DWeb V) (I : Type v) : Type (max u v) :=
  PopularAuxiliary.Input Gamma I
abbrev LV (L : Input Gamma I) : Type (max u v) :=
  PopularAuxiliary.Input.LambdaVertex V I

/-! ## The two parts of the auxiliary cut -/

/-- `C_V`: the original vertices represented by old vertices of `C`. -/
def CV (L : Input Gamma I) (C : Set (LV L)) : Set V :=
  L.oldPart C

/-- `C_E`: the edges of the ladder warp represented by vertices of `C`.
The intersection with `familyEdges` makes the source definition literal
even for a set containing irrelevant edge tags. -/
def CE (L : Input Gamma I) (C : Set (LV L)) : Set (V × V) :=
  L.edgePart C ∩ L.familyEdges

@[simp] theorem mem_CV {L : Input Gamma I} {C : Set (LV L)} {x : V} :
    x ∈ CV L C ↔ PopularAuxiliary.Input.LambdaVertex.old x ∈ C :=
  Iff.rfl

@[simp] theorem mem_CE {L : Input Gamma I} {C : Set (LV L)} {e : V × V} :
    e ∈ CE L C ↔
      PopularAuxiliary.Input.LambdaVertex.edge e.1 e.2 ∈ C ∧
        e ∈ L.familyEdges :=
  Iff.rfl

theorem CE_subset_familyEdges (L : Input Gamma I) (C : Set (LV L)) :
    CE L C ⊆ L.familyEdges :=
  Set.inter_subset_right

/-! ## The intrinsic order on a finite path or ray -/

/-- A vertex occurs at the indicated traversal index.  Finite paths use
their support list; rays use their defining injection `ℕ → V`. -/
def OccursAt (P : Gamma.DPath) (n : ℕ) (x : V) : Prop :=
  match P with
  | .inl p => ∃ h : n < p.walk.support.length, p.walk.support[n] = x
  | .inr r => r n = x

theorem mem_support_iff_exists_occursAt (P : Gamma.DPath) (x : V) :
    x ∈ P.support ↔ ∃ n, OccursAt P n x := by
  cases P with
  | inl p =>
      change x ∈ p.walk.support ↔
        ∃ n, ∃ h : n < p.walk.support.length, p.walk.support[n] = x
      exact List.mem_iff_getElem
  | inr r =>
      change x ∈ Set.range r.toFun ↔ ∃ n, r n = x
      rfl

theorem occursAt_mem_support {P : Gamma.DPath} {n : ℕ} {x : V}
    (h : OccursAt P n x) : x ∈ P.support :=
  (mem_support_iff_exists_occursAt P x).2 ⟨n, h⟩

/-- The non-strict order of vertices along a path. -/
def BeforeEq (P : Gamma.DPath) (x y : V) : Prop :=
  ∃ m n, OccursAt P m x ∧ OccursAt P n y ∧ m ≤ n

/-- Strict order along a path. -/
def Before (P : Gamma.DPath) (x y : V) : Prop :=
  BeforeEq P x y ∧ x ≠ y

theorem beforeEq_refl {P : Gamma.DPath} {x : V} (hx : x ∈ P.support) :
    BeforeEq P x x := by
  obtain ⟨n, hn⟩ := (mem_support_iff_exists_occursAt P x).1 hx
  exact ⟨n, n, hn, hn, le_rfl⟩

theorem beforeEq_total {P : Gamma.DPath} {x y : V}
    (hx : x ∈ P.support) (hy : y ∈ P.support) :
    BeforeEq P x y ∨ BeforeEq P y x := by
  obtain ⟨m, hm⟩ := (mem_support_iff_exists_occursAt P x).1 hx
  obtain ⟨n, hn⟩ := (mem_support_iff_exists_occursAt P y).1 hy
  rcases le_total m n with hmn | hnm
  · exact Or.inl ⟨m, n, hm, hn, hmn⟩
  · exact Or.inr ⟨n, m, hn, hm, hnm⟩

/-- Every nonempty subset of the support has a first vertex. -/
theorem exists_first_vertex (P : Gamma.DPath) (S : Set V)
    (hS : (P.support ∩ S).Nonempty) :
    ∃ x, x ∈ P.support ∩ S ∧
      ∀ y, y ∈ P.support ∩ S → BeforeEq P x y := by
  classical
  let Q : ℕ → Prop := fun n ↦ ∃ x, OccursAt P n x ∧ x ∈ S
  have hQ : ∃ n, Q n := by
    obtain ⟨x, hxP, hxS⟩ := hS
    obtain ⟨n, hn⟩ := (mem_support_iff_exists_occursAt P x).1 hxP
    exact ⟨n, x, hn, hxS⟩
  let n := Nat.find hQ
  obtain ⟨x, hnx, hxS⟩ := Nat.find_spec hQ
  refine ⟨x, ⟨occursAt_mem_support hnx, hxS⟩, ?_⟩
  intro y hy
  obtain ⟨m, hmy⟩ := (mem_support_iff_exists_occursAt P y).1 hy.1
  have hmQ : Q m := ⟨y, hmy, hy.2⟩
  exact ⟨n, m, hnx, hmy, Nat.find_min' hQ hmQ⟩

/-- The first vertex of `S` on `P`. -/
def firstVertex (P : Gamma.DPath) (S : Set V)
    (hS : (P.support ∩ S).Nonempty) : V :=
  Classical.choose (exists_first_vertex P S hS)

theorem firstVertex_mem (P : Gamma.DPath) (S : Set V)
    (hS : (P.support ∩ S).Nonempty) :
    firstVertex P S hS ∈ P.support ∩ S :=
  (Classical.choose_spec (exists_first_vertex P S hS)).1

theorem firstVertex_beforeEq (P : Gamma.DPath) (S : Set V)
    (hS : (P.support ∩ S).Nonempty) {y : V}
    (hy : y ∈ P.support ∩ S) :
    BeforeEq P (firstVertex P S hS) y :=
  (Classical.choose_spec (exists_first_vertex P S hS)).2 y hy

theorem beforeEq_terminal {P : Gamma.DPath} {t x : V}
    (ht : P.terminal? = some t) (hx : x ∈ P.support) :
    BeforeEq P x t := by
  rcases P with p | r
  · change (some p.finish : Option V) = some t at ht
    have ht' : p.finish = t := Option.some.inj ht
    obtain ⟨m, hm⟩ := (mem_support_iff_exists_occursAt (.inl p) x).1 hx
    have hn : OccursAt (.inl p : Gamma.DPath) (p.walk.support.length - 1) t := by
      have hlen : 0 < p.walk.support.length :=
        List.length_pos_iff_ne_nil.2 p.walk.support_ne_nil
      refine ⟨Nat.sub_lt (by omega) (by omega), ?_⟩
      exact (List.getLast_eq_getElem p.walk.support_ne_nil).symm.trans
        (p.walk.getLast_support.trans ht')
    refine ⟨m, p.walk.support.length - 1, hm, hn, ?_⟩
    rcases hm with ⟨hmLen, _⟩
    omega
  · change (none : Option V) = some t at ht
    cases ht

/-! ## Fragments after deleting represented ladder edges -/

/-- Two vertices of one ladder path remain connected after deleting `CE`.
Since a directed ladder path is linearly ordered, either orientation of the
surviving finite interval is admitted in this symmetric component relation.

The witness is required to use parent edges, not merely parent vertices.
Without this condition the ambient three-vertex graph with parent path
`0 → 1 → 2`, deleted edge `1 → 2`, and extra chord `0 → 2` would
declare `0` and `2` surviving-connected, although no surviving subpath of
the parent has support `{0, 2}`.  In that example the old definition had no
maximal `Fragment` containing `2`. -/
def SurvivingConnected (L : Input Gamma I) (C : Set (LV L))
    (parent : Gamma.DPath) (x y : V) : Prop :=
  ∃ q : FinitePath Gamma.graph,
    ((q.start = x ∧ q.finish = y) ∨ (q.start = y ∧ q.finish = x)) ∧
      q.support ⊆ parent.support ∧ q.edgeSet ⊆ parent.edgeSet ∧
        Disjoint q.edgeSet (CE L C)

/-- A maximal component of a ladder path after the represented edges in
`CE` are deleted.  `Fragment` already records containment in its parent;
the final equality is the maximality condition. -/
def IsDeletedFragment (L : Input Gamma I) (C : Set (LV L))
    (P : L.Fragment) : Prop :=
  Disjoint P.path.edgeSet (CE L C) ∧
    P.path.support =
      {x | x ∈ P.parent.support ∧
        SurvivingConnected L C P.parent P.path.initial x}

/-- The family `G = Y - C_E` of maximal surviving fragments. -/
def fragments (L : Input Gamma I) (C : Set (LV L)) : Set L.Fragment :=
  {P | IsDeletedFragment L C P}

/-- A fragment can be assigned a blocking point exactly when it meets the
escape region or is finite.  In the Section 8 application, Assertion 8.15
and the definition of `H_empty` establish this dichotomy for every member
of the source's `G_0`. -/
def IsBlockable (L : Input Gamma I) (C : Set (LV L))
    (P : L.Fragment) : Prop :=
  PopularAuxiliary.Input.Fragment.MeetsEscape L C P ∨ P.path.IsFinite

/-- `G_0`, represented extensionally as the blockable surviving fragments.
This is the exact portion of `G \ H_empty` used from Assertion 8.17 onward. -/
def G0 (L : Input Gamma I) (C : Set (LV L)) : Set L.Fragment :=
  fragments L C ∩ {P | IsBlockable L C P}

theorem fragment_meeting_escape_mem_G0
    (L : Input Gamma I) (C : Set (LV L)) (P : L.Fragment)
    (hfragment : P ∈ fragments L C)
    (hescape : PopularAuxiliary.Input.Fragment.MeetsEscape L C P) :
    P ∈ G0 L C :=
  ⟨hfragment, Or.inl hescape⟩

theorem mem_G0_isBlockable {L : Input Gamma I} {C : Set (LV L)}
    {P : L.Fragment} (hP : P ∈ G0 L C) : IsBlockable L C P :=
  hP.2

/-! ## Blocking points and the cut `BB` -/

/-- `bl(P)`: the first vertex of `RR` on `P`, if one exists, and the
terminal vertex otherwise.  The impossible residual case (a ray missing
`RR`) is totalized by the initial vertex; it cannot occur for `P ∈ G0`. -/
def blockingPoint (L : Input Gamma I) (C : Set (LV L))
    (P : L.Fragment) : V := by
  classical
  exact
    if h : PopularAuxiliary.Input.Fragment.MeetsEscape L C P then
      firstVertex P.path (L.escapeRegion C) h
    else
      P.path.terminal?.getD P.path.initial

theorem blockingPoint_eq_first_of_meetsEscape
    (L : Input Gamma I) (C : Set (LV L)) (P : L.Fragment)
    (h : PopularAuxiliary.Input.Fragment.MeetsEscape L C P) :
    blockingPoint L C P =
      firstVertex P.path (L.escapeRegion C) h := by
  simp [blockingPoint, h]

theorem blockingPoint_mem_escapeRegion_of_meetsEscape
    (L : Input Gamma I) (C : Set (LV L)) (P : L.Fragment)
    (h : PopularAuxiliary.Input.Fragment.MeetsEscape L C P) :
    blockingPoint L C P ∈ L.escapeRegion C := by
  rw [blockingPoint_eq_first_of_meetsEscape L C P h]
  exact (firstVertex_mem P.path (L.escapeRegion C) h).2

theorem blockingPoint_mem_support
    (L : Input Gamma I) (C : Set (LV L)) (P : L.Fragment)
    (hP : IsBlockable L C P) :
    blockingPoint L C P ∈ P.path.support := by
  rcases hP with hescape | hfinite
  · rw [blockingPoint_eq_first_of_meetsEscape L C P hescape]
    exact (firstVertex_mem P.path (L.escapeRegion C) hescape).1
  · obtain ⟨t, ht⟩ := hfinite
    by_cases hescape :
        PopularAuxiliary.Input.Fragment.MeetsEscape L C P
    · rw [blockingPoint_eq_first_of_meetsEscape L C P hescape]
      exact (firstVertex_mem P.path (L.escapeRegion C) hescape).1
    · simp only [blockingPoint, dif_neg hescape, ht]
      exact P.path.terminal_mem_support t ht

theorem blockingPoint_beforeEq_escape
    (L : Input Gamma I) (C : Set (LV L)) (P : L.Fragment)
    (h : PopularAuxiliary.Input.Fragment.MeetsEscape L C P) {y : V}
    (hyP : y ∈ P.path.support) (hyRR : y ∈ L.escapeRegion C) :
    BeforeEq P.path (blockingPoint L C P) y := by
  rw [blockingPoint_eq_first_of_meetsEscape L C P h]
  exact firstVertex_beforeEq P.path (L.escapeRegion C) h ⟨hyP, hyRR⟩

theorem blockingPoint_eq_terminal_of_not_meetsEscape
    (L : Input Gamma I) (C : Set (LV L)) (P : L.Fragment)
    (hescape : ¬ PopularAuxiliary.Input.Fragment.MeetsEscape L C P) {t : V}
    (ht : P.path.terminal? = some t) :
    blockingPoint L C P = t := by
  simp [blockingPoint, hescape, ht]

theorem beforeEq_blockingPoint_of_not_meetsEscape
    (L : Input Gamma I) (C : Set (LV L)) (P : L.Fragment)
    (hescape : ¬ PopularAuxiliary.Input.Fragment.MeetsEscape L C P) {t x : V}
    (ht : P.path.terminal? = some t) (hx : x ∈ P.path.support) :
    BeforeEq P.path x (blockingPoint L C P) := by
  rw [blockingPoint_eq_terminal_of_not_meetsEscape L C P hescape ht]
  exact beforeEq_terminal ht hx

/-- `BL`, the set of blocking points of surviving fragments. -/
def BL (L : Input Gamma I) (C : Set (LV L)) : Set V :=
  blockingPoint L C '' G0 L C

/-- `BB = C_V ∪ BL`. -/
def BB (L : Input Gamma I) (C : Set (LV L)) : Set V :=
  CV L C ∪ BL L C

theorem mem_BL_iff {L : Input Gamma I} {C : Set (LV L)} {x : V} :
    x ∈ BL L C ↔ ∃ P ∈ G0 L C, blockingPoint L C P = x := by
  rfl

theorem BL_covered_by_G0 {L : Input Gamma I} {C : Set (LV L)} {x : V}
    (hx : x ∈ BL L C) :
    ∃ P ∈ G0 L C,
      x = blockingPoint L C P ∧ x ∈ P.path.support := by
  obtain ⟨P, hP, hPx⟩ := hx
  refine ⟨P, hP, hPx.symm, ?_⟩
  rw [← hPx]
  exact blockingPoint_mem_support L C P hP.2

theorem CV_subset_BB (L : Input Gamma I) (C : Set (LV L)) :
    CV L C ⊆ BB L C :=
  Set.subset_union_left

theorem BL_subset_BB (L : Input Gamma I) (C : Set (LV L)) :
    BL L C ⊆ BB L C :=
  Set.subset_union_right

/-! ## Assertion 8.21: the order obstruction -/

/-- An avoiding auxiliary path transports target reachability backwards
from its finish to its start. -/
theorem canReachTargetAvoiding_of_avoiding_path
    (L : Input Gamma I) (C : Set (LV L))
    (p : FinitePath L.lambda.graph) {x y : LV L}
    (hstart : p.start = x) (hfinish : p.finish = y)
    (hp : L.lambda.Avoids p C)
    (hy : L.lambda.CanReachTargetAvoiding C y) :
    L.lambda.CanReachTargetAvoiding C x := by
  obtain ⟨q, hq, hqavoid⟩ := hy
  obtain ⟨r, hrstart, hrfinish, hravoid⟩ :=
    PopularSwitching.exists_avoiding_path_of_avoiding_paths
      p q (hfinish.trans hq.1.symm) hp hqavoid
  exact ⟨r, ⟨hrstart.trans hstart, hrfinish ▸ hq.2⟩, hravoid⟩

/-- Concrete Assertion 8.21.  `backwardDecode` is the local, pathwise
decoder: if the last contact `x` lies strictly after the first escaping
vertex of its ladder fragment, reversing the intervening surviving ladder
segment gives a cut-avoiding auxiliary path from `old x` to `old bl(P)`.
Auxiliary separation then forces `x ≤_P bl(P)`.

In the no-escape branch `bl(P)` is the terminal vertex, so the conclusion
is purely the linear order on the fragment and no decoder is used. -/
theorem assertion8_21
    (L : Input Gamma I) (C : Set (LV L))
    (hC : Popular.IsSeparator L.lambda C)
    (P : L.Fragment) (hP : P ∈ G0 L C)
    (q : FinitePath L.lambda.graph)
    (hqstart : q.start ∈ L.lambda.source)
    (hqavoid : L.lambda.Avoids q C) {x : V}
    (hqfinish : q.finish = .old x)
    (hxP : x ∈ P.path.support)
    (backwardDecode : Before P.path (blockingPoint L C P) x →
      L.RelaxedEscape C (blockingPoint L C P) →
      ∃ r : FinitePath L.lambda.graph,
        r.start = .old x ∧
        r.finish ∈ L.lambda.target ∧
        L.lambda.Avoids r C) :
    BeforeEq P.path x (blockingPoint L C P) := by
  by_cases hescape :
      PopularAuxiliary.Input.Fragment.MeetsEscape L C P
  · have hblockSupport : blockingPoint L C P ∈ P.path.support :=
      blockingPoint_mem_support L C P (Or.inl hescape)
    rcases beforeEq_total hxP hblockSupport with hxb | hbx
    · exact hxb
    · by_cases heq : blockingPoint L C P = x
      · simpa [heq] using beforeEq_refl hxP
      · obtain ⟨E⟩ :=
          blockingPoint_mem_escapeRegion_of_meetsEscape L C P hescape
        obtain ⟨r, hrstart, hrfinish, hravoid⟩ :=
          backwardDecode ⟨hbx, heq⟩ E
        obtain ⟨s, hsstart, hsfinish, hsavoid⟩ :=
          PopularSwitching.exists_avoiding_path_of_avoiding_paths
            q r (hqfinish.trans hrstart.symm) hqavoid hravoid
        exact False.elim <|
          PopularAuxiliary.Input.no_avoiding_source_target_path
            L.lambda C hC s (hsstart ▸ hqstart)
              (hsfinish ▸ hrfinish) hsavoid
  · have hfinite : P.path.IsFinite := hP.2.resolve_left hescape
    obtain ⟨t, ht⟩ := hfinite
    exact beforeEq_blockingPoint_of_not_meetsEscape L C P hescape ht hxP

/-! ## Assertion 8.18 after the finite descent decoder -/

/-- The precise decoder conclusion produced by the finite last-encounter
descent in Assertion 8.18.  It is deliberately a pathwise statement rather
than an assumed separator: every original source--`terminalCut` path which
avoids `BB` yields the forbidden auxiliary path in `Lambda - C`. -/
def FiniteDescentDecoder (L : Input Gamma I) (C : Set (LV L)) : Prop :=
  ∀ R : FinitePath Gamma.graph,
    R.start ∈ Gamma.source → R.finish ∈ L.terminalCut →
    Gamma.Avoids R (BB L C) →
    ∃ q : FinitePath L.lambda.graph,
      q.start ∈ L.lambda.source ∧ q.finish ∈ L.lambda.target ∧
        L.lambda.Avoids q C

/-- Assertion 8.18.  Once the literal finite-descent decoder is supplied,
auxiliary separation proves that `BB` meets every source--terminal-cut path;
the already separating terminal frontier then makes `BB` an original
source--target separator. -/
theorem assertion8_18
    (L : Input Gamma I) (C : Set (LV L))
    (hC : Popular.IsSeparator L.lambda C)
    (hterminal : Popular.IsSeparator Gamma L.terminalCut)
    (hdecode : FiniteDescentDecoder L C) :
    Popular.IsSeparator Gamma (BB L C) := by
  apply PopularSwitching.isSeparator_of_meets_paths_to_separator hterminal
  intro R hsource hcut
  by_contra hnotMeet
  have havoid : Gamma.Avoids R (BB L C) :=
    (Gamma.avoids_iff_not_meets R (BB L C)).2 hnotMeet
  obtain ⟨q, hqsource, hqtarget, hqavoid⟩ :=
    hdecode R hsource hcut havoid
  exact PopularAuxiliary.Input.no_avoiding_source_target_path
    L.lambda C hC q hqsource hqtarget hqavoid

end GroundingCut
end Erdos599
