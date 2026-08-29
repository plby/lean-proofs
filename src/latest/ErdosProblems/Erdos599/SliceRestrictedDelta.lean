/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ExtensionClause
import ErdosProblems.Erdos599.QuotientMaximal
import ErdosProblems.Erdos599.SafeLinkGroundFinal
import ErdosProblems.Erdos599.SingularContinuation

/-!
# The restricted web in Assertion 9.10

This file models the web denoted by `Delta` in the proof of Aharoni--Berger
Assertion 9.10.  After a half-way family has stopped, let `D` be its terminal
frontier, let `C` be the separating stop-over, let `T` be a later ladder
frontier, and let `F` be the family of old-ladder suffixes from `D` to `T`.
The paper does not use the whole quotient graph at this point.  It induces on

`(roof T \ strictRoof C) union vertexSet F`

and gives the resulting web source `D` and target `T`.  Keeping the
`vertexSet F` summand is essential: an old-ladder suffix is allowed to pass
through the strict roof of `C`.

The second part is the concrete form of source Corollary 3.6.  A hindrance
survives quotienting by a set whose roof misses the source.  Consequently an
unhindered quotient reflects unhinderedness back to the original web.  This
is exactly the reflection used with `C \ D` in Assertion 9.10.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SliceRestrictedDelta

open DirectedPath

universe u

variable {V : Type u}

/-- The literal vertex region in the displayed definition of `Delta` in
Assertion 9.10. -/
def carrier (Q : DWeb V) (C T : Set V) (F : Set Q.DPath) : Set V :=
  (Q.roof T \ Q.strictRoof C) ∪ Q.vertexSet F

/-- The restricted web of Assertion 9.10, before the harmless global
source/target normalization.  The graph is genuinely induced on `carrier`;
it is not merely the quotient graph with its source changed. -/
def delta (Q : DWeb V) (C D T : Set V) (F : Set Q.DPath) : DWeb V where
  graph := DWeb.inducedGraph Q.graph (carrier Q C T F)
  source := D
  target := T

/-- The source's standing Assumption 2.1 applied to the derived restricted
web.  Unlike the raw induced graph, it has no arcs entering the intermediate
source `D` or leaving the intermediate target `T`. -/
def normalizedDelta (Q : DWeb V) (C D T : Set V)
    (F : Set Q.DPath) : DWeb V :=
  (delta Q C D T F).normalized

@[simp] theorem delta_source (Q : DWeb V) (C D T : Set V)
    (F : Set Q.DPath) : (delta Q C D T F).source = D := rfl

@[simp] theorem delta_target (Q : DWeb V) (C D T : Set V)
    (F : Set Q.DPath) : (delta Q C D T F).target = T := rfl

@[simp] theorem normalizedDelta_source (Q : DWeb V) (C D T : Set V)
    (F : Set Q.DPath) : (normalizedDelta Q C D T F).source = D := rfl

@[simp] theorem normalizedDelta_target (Q : DWeb V) (C D T : Set V)
    (F : Set Q.DPath) : (normalizedDelta Q C D T F).target = T := rfl

@[simp] theorem delta_adj_iff (Q : DWeb V) (C D T : Set V)
    (F : Set Q.DPath) (x y : V) :
    (delta Q C D T F).graph.Adj x y ↔
      Q.graph.Adj x y ∧ x ∈ carrier Q C T F ∧
        y ∈ carrier Q C T F :=
  Iff.rfl

@[simp] theorem normalizedDelta_adj_iff (Q : DWeb V) (C D T : Set V)
    (F : Set Q.DPath) (x y : V) :
    (normalizedDelta Q C D T F).graph.Adj x y ↔
      (Q.graph.Adj x y ∧ x ∈ carrier Q C T F ∧
        y ∈ carrier Q C T F) ∧ y ∉ D ∧ x ∉ T :=
  Iff.rfl

/-- The right-hand side of the graph identity displayed in Assertion 9.10:
the quotient by `C`, restricted to the old roof of the later frontier `T`,
with source `C` and target `T`. -/
def roofQuotientWeb (Q : DWeb V) (C T : Set V) : DWeb V where
  graph := DWeb.inducedGraph (Q.quotient C).graph (Q.roof T)
  source := C
  target := T

/-- The normalized form of the right-hand side `(Q / C)[roof T]`. -/
def normalizedRoofQuotientWeb (Q : DWeb V) (C T : Set V) : DWeb V :=
  (roofQuotientWeb Q C T).normalized

@[simp] theorem roofQuotientWeb_source (Q : DWeb V) (C T : Set V) :
    (roofQuotientWeb Q C T).source = C := rfl

@[simp] theorem roofQuotientWeb_target (Q : DWeb V) (C T : Set V) :
    (roofQuotientWeb Q C T).target = T := rfl

@[simp] theorem normalizedRoofQuotientWeb_source
    (Q : DWeb V) (C T : Set V) :
    (normalizedRoofQuotientWeb Q C T).source = C := rfl

@[simp] theorem normalizedRoofQuotientWeb_target
    (Q : DWeb V) (C T : Set V) :
    (normalizedRoofQuotientWeb Q C T).target = T := rfl

@[simp] theorem roofQuotientWeb_adj_iff (Q : DWeb V) (C T : Set V)
    (x y : V) :
    (roofQuotientWeb Q C T).graph.Adj x y ↔
      (Q.quotient C).graph.Adj x y ∧ x ∈ Q.roof T ∧ y ∈ Q.roof T :=
  Iff.rfl

@[simp] theorem normalizedRoofQuotientWeb_adj_iff
    (Q : DWeb V) (C T : Set V) (x y : V) :
    (normalizedRoofQuotientWeb Q C T).graph.Adj x y ↔
      ((Q.quotient C).graph.Adj x y ∧ x ∈ Q.roof T ∧
        y ∈ Q.roof T) ∧ y ∉ C ∧ x ∉ T :=
  Iff.rfl

/-- Forget the roof-induced restriction and view a path again in `Q / C`. -/
def liftRoofQuotientPath (Q : DWeb V) (C T : Set V)
    (p : (roofQuotientWeb Q C T).DPath) : (Q.quotient C).DPath :=
  p.lift fun {_ _} (e : (roofQuotientWeb Q C T).graph.Adj _ _) ↦ e.1

@[simp] theorem support_liftRoofQuotientPath (Q : DWeb V)
    (C T : Set V) (p : (roofQuotientWeb Q C T).DPath) :
    (liftRoofQuotientPath Q C T p).support = p.support := by
  unfold liftRoofQuotientPath
  exact DirectedPath.Path.support_lift
    (fun {_ _} (e : (roofQuotientWeb Q C T).graph.Adj _ _) ↦ e.1) p

@[simp] theorem initial_liftRoofQuotientPath (Q : DWeb V)
    (C T : Set V) (p : (roofQuotientWeb Q C T).DPath) :
    (liftRoofQuotientPath Q C T p).initial = p.initial := by
  rcases p with p | p <;> rfl

@[simp] theorem terminal_liftRoofQuotientPath (Q : DWeb V)
    (C T : Set V) (p : (roofQuotientWeb Q C T).DPath) :
    (Q.quotient C).terminal? (liftRoofQuotientPath Q C T p) =
      (roofQuotientWeb Q C T).terminal? p := by
  rcases p with p | p <;> rfl

/-- Lift a whole family out of the roof-induced subweb. -/
def liftRoofQuotientFamily (Q : DWeb V) (C T : Set V)
    (W : Set (roofQuotientWeb Q C T).DPath) :
    Set (Q.quotient C).DPath :=
  liftRoofQuotientPath Q C T '' W

@[simp] theorem initialSet_liftRoofQuotientFamily (Q : DWeb V)
    (C T : Set V) (W : Set (roofQuotientWeb Q C T).DPath) :
    (Q.quotient C).initialSet (liftRoofQuotientFamily Q C T W) =
      (roofQuotientWeb Q C T).initialSet W := by
  ext x
  constructor
  · rintro ⟨p, ⟨q, hq, rfl⟩, hpx⟩
    exact ⟨q, hq, by simpa using hpx⟩
  · rintro ⟨q, hq, hqx⟩
    exact ⟨liftRoofQuotientPath Q C T q, ⟨q, hq, rfl⟩,
      by simpa using hqx⟩

@[simp] theorem terminalFrontier_liftRoofQuotientFamily (Q : DWeb V)
    (C T : Set V) (W : Set (roofQuotientWeb Q C T).DPath) :
    (Q.quotient C).terminalFrontier (liftRoofQuotientFamily Q C T W) =
      (roofQuotientWeb Q C T).terminalFrontier W := by
  ext x
  constructor
  · rintro ⟨p, ⟨q, hq, rfl⟩, hpx⟩
    exact ⟨q, hq, by simpa using hpx⟩
  · rintro ⟨q, hq, hqx⟩
    exact ⟨liftRoofQuotientPath Q C T q, ⟨q, hq, rfl⟩,
      by simpa using hqx⟩

theorem IsWarp.liftRoofQuotientFamily
    (Q : DWeb V) (C T : Set V)
    {W : Set (roofQuotientWeb Q C T).DPath}
    (hW : (roofQuotientWeb Q C T).IsWarp W) :
    (Q.quotient C).IsWarp (liftRoofQuotientFamily Q C T W) := by
  rintro p ⟨p₀, hp₀, rfl⟩ q ⟨q₀, hq₀, rfl⟩ hpq
  change Disjoint
    (liftRoofQuotientPath Q C T p₀).support
    (liftRoofQuotientPath Q C T q₀).support
  rw [support_liftRoofQuotientPath, support_liftRoofQuotientPath]
  apply hW hp₀ hq₀
  intro h
  exact hpq (congrArg (liftRoofQuotientPath Q C T) h)

/-- Before its first hit on `T`, a quotient path which starts under the old
roof of `T` stays under that roof.  The proof deliberately uses the ambient
`Q` roof, not the generally different roof computed in `Q / C`. -/
theorem firstHit_support_subset_roof
    (Q : DWeb V) (C T : Set V)
    (p : DirectedPath.FinitePath (Q.quotient C).graph)
    (hstart : p.start ∈ Q.roof T)
    (hmeet : p.walk.Meets T) :
    (p.firstHit T hmeet).support ⊆ Q.roof T := by
  let f := p.firstHit T hmeet
  let q : DirectedPath.FinitePath Q.graph :=
    f.lift fun {_ _} (e : (Q.quotient C).graph.Adj _ _) ↦ e.1
  have hqf : q.support = f.support := by
    dsimp only [q]
    exact DirectedPath.FinitePath.support_lift
      (fun {_ _} (e : (Q.quotient C).graph.Adj _ _) ↦ e.1) f
  have hqroof : q.support ⊆ Q.roof T := by
    apply Q.pathSupportRoof (.inl q : Q.DPath) T
    · change q.start ∈ Q.roof T
      simpa only [q, f, DirectedPath.FinitePath.lift,
        DirectedPath.FinitePath.firstHit] using hstart
    · intro t ht
      change some q.finish = some t at ht
      have hfinish : q.finish = t := Option.some.inj ht
      rw [← hfinish]
      change f.finish ∈ T
      exact p.firstHit_finish_mem T hmeet
    · intro x hx
      apply Set.mem_singleton_iff.2
      by_contra hxfinish
      have hxf : x ∈ f.support := by
        have hxq : x ∈ q.support := hx.1
        rwa [hqf] at hxq
      have hxfinish' : x ≠ f.finish := by
        simpa only [q, DirectedPath.FinitePath.lift] using hxfinish
      have hxlast : x ≠ f.walk.support.getLast f.walk.support_ne_nil := by
        intro h
        apply hxfinish'
        exact h.trans f.walk.getLast_support
      have hxdrop : x ∈ f.walk.support.dropLast :=
        List.mem_dropLast_of_mem_of_ne_getLast hxf hxlast
      exact p.firstHit_no_mem_before T hmeet hxdrop hx.2
  intro x hx
  apply hqroof
  rw [hqf]
  exact hx

/-- Ambient version of `firstHit_support_subset_roof`. -/
theorem firstHit_support_subset_roof_ambient
    (Q : DWeb V) (T : Set V)
    (p : DirectedPath.FinitePath Q.graph)
    (hstart : p.start ∈ Q.roof T)
    (hmeet : p.walk.Meets T) :
    (p.firstHit T hmeet).support ⊆ Q.roof T := by
  let f := p.firstHit T hmeet
  apply Q.pathSupportRoof (.inl f : Q.DPath) T
  · change f.start ∈ Q.roof T
    simpa only [f, DirectedPath.FinitePath.firstHit] using hstart
  · intro t ht
    change some f.finish = some t at ht
    have hfinish : f.finish = t := Option.some.inj ht
    rw [← hfinish]
    exact p.firstHit_finish_mem T hmeet
  · intro x hx
    apply Set.mem_singleton_iff.2
    by_contra hxfinish
    have hxlast : x ≠ f.walk.support.getLast f.walk.support_ne_nil := by
      intro h
      apply hxfinish
      exact h.trans f.walk.getLast_support
    have hxdrop : x ∈ f.walk.support.dropLast :=
      List.mem_dropLast_of_mem_of_ne_getLast hx.1 hxlast
    exact p.firstHit_no_mem_before T hmeet hxdrop hx.2

/-- Observation 3.2 in the precise form used by Assertion 9.10: a wave in
the `roof T` restriction of `Q / C` lifts to a wave in `Q / C`.  The source
identity and the fact that `C` is under `T` are stated explicitly. -/
theorem isWave_liftRoofQuotientFamily
    (Q : DWeb V) {C T : Set V}
    (hsource : (Q.quotient C).source = C)
    (hCroof : C ⊆ Q.roof T)
    {W : Set (roofQuotientWeb Q C T).DPath}
    (hW : (roofQuotientWeb Q C T).IsWave W) :
    (Q.quotient C).IsWave (liftRoofQuotientFamily Q C T W) := by
  refine ⟨IsWarp.liftRoofQuotientFamily Q C T hW.1, ?_, ?_⟩
  · rw [initialSet_liftRoofQuotientFamily, hsource]
    exact hW.2.1
  · intro a haSource p hp
    have haC : a ∈ C := hsource ▸ haSource
    have haRoof : a ∈ Q.roof T := hCroof haC
    let pq : DirectedPath.FinitePath Q.graph :=
      p.lift fun {_ _} (e : (Q.quotient C).graph.Adj _ _) ↦ e.1
    have hpq : Q.IsTargetPathFrom a pq := by
      refine ⟨?_, ?_⟩
      · simpa only [pq, DirectedPath.FinitePath.lift] using hp.1
      · change p.finish ∈ Q.target
        exact hp.2
    obtain ⟨t, htpq, htT⟩ := haRoof pq hpq
    have htSupp : t ∈ p.support := by
      simpa only [pq, DirectedPath.FinitePath.support_lift] using htpq
    have hmeet : p.walk.Meets T := ⟨t, htSupp, htT⟩
    let f := p.firstHit T hmeet
    have hpStartRoof : p.start ∈ Q.roof T := by
      rwa [hp.1]
    have hfRoof : f.support ⊆ Q.roof T :=
      firstHit_support_subset_roof Q C T p hpStartRoof hmeet
    let hrestrict : ∀ {x y : V}, (Q.quotient C).graph.Adj x y →
        x ∈ f.support → y ∈ f.support →
          (roofQuotientWeb Q C T).graph.Adj x y :=
      fun {_ _} e hx hy ↦ ⟨e, hfRoof hx, hfRoof hy⟩
    let r : DirectedPath.FinitePath (roofQuotientWeb Q C T).graph :=
      f.restrictGraphOnSupport hrestrict
    have hrTarget : (roofQuotientWeb Q C T).IsTargetPathFrom a r := by
      refine ⟨?_, ?_⟩
      · change f.start = a
        simpa only [f, DirectedPath.FinitePath.firstHit] using hp.1
      · change f.finish ∈ T
        exact p.firstHit_finish_mem T hmeet
    obtain ⟨z, hzr, hzW⟩ := hW.2.2 haC r hrTarget
    refine ⟨z, ?_, ?_⟩
    · apply p.firstHit_support_subset T hmeet
      have hrSupport : r.support = f.support :=
        DirectedPath.FinitePath.support_restrictGraphOnSupport f
          hrestrict
      rwa [hrSupport] at hzr
    · rw [terminalFrontier_liftRoofQuotientFamily]
      exact hzW

/-- Unhinderedness passes from `Q / C` to the exact induced roof subweb
appearing on the right of the Assertion 9.10 quotient identity. -/
theorem roofQuotientWeb_isUnhindered
    (Q : DWeb V) {C T : Set V}
    (hsource : (Q.quotient C).source = C)
    (hCroof : C ⊆ Q.roof T)
    (hQ : (Q.quotient C).IsUnhindered) :
    (roofQuotientWeb Q C T).IsUnhindered := by
  rw [(roofQuotientWeb Q C T).isUnhindered_iff]
  intro W hW
  have hlift : (Q.quotient C).IsWave
      (liftRoofQuotientFamily Q C T W) :=
    isWave_liftRoofQuotientFamily Q hsource hCroof hW
  have hinitial := (Q.quotient C).isUnhindered_iff.mp hQ _ hlift
  rw [initialSet_liftRoofQuotientFamily] at hinitial
  exact hinitial.trans hsource

/-- The normalized roof restriction is likewise unhindered. -/
theorem normalizedRoofQuotientWeb_isUnhindered
    (Q : DWeb V) {C T : Set V}
    (hsource : (Q.quotient C).source = C)
    (hCroof : C ⊆ Q.roof T)
    (hQ : (Q.quotient C).IsUnhindered) :
    (normalizedRoofQuotientWeb Q C T).IsUnhindered := by
  exact (roofQuotientWeb_isUnhindered Q hsource hCroof hQ).normalized

theorem vertexSet_subset_carrier (Q : DWeb V) (C T : Set V)
    (F : Set Q.DPath) : Q.vertexSet F ⊆ carrier Q C T F :=
  Set.subset_union_right

/-- Retype one old suffix as a path in the induced web. -/
def restrictPath (Q : DWeb V) (C D T : Set V) (F : Set Q.DPath)
    (p : Q.DPath) (hp : p.support ⊆ carrier Q C T F) :
    (delta Q C D T F).DPath :=
  p.restrictGraphOnSupport fun e hx hy ↦ ⟨e, hp hx, hp hy⟩

/-- Forget the induced-graph restriction. -/
def liftPath (Q : DWeb V) (C D T : Set V) (F : Set Q.DPath)
    (p : (delta Q C D T F).DPath) : Q.DPath :=
  p.lift fun {_ _} (e : (delta Q C D T F).graph.Adj _ _) ↦ e.1

@[simp] theorem liftPath_restrictPath (Q : DWeb V) (C D T : Set V)
    (F : Set Q.DPath) (p : Q.DPath)
    (hp : p.support ⊆ carrier Q C T F) :
    liftPath Q C D T F (restrictPath Q C D T F p hp) = p := by
  exact @SafeLinkGroundFinal.DirectedPath.Path.lift_restrictGraphOnSupport
    V Q.graph (delta Q C D T F).graph p
    (fun {x y} (e : Q.graph.Adj x y) hx hy ↦
      (show (delta Q C D T F).graph.Adj x y from
        ⟨e, hp hx, hp hy⟩))
    (fun {_ _} e ↦ e.1)

@[simp] theorem support_restrictPath (Q : DWeb V) (C D T : Set V)
    (F : Set Q.DPath) (p : Q.DPath)
    (hp : p.support ⊆ carrier Q C T F) :
    (restrictPath Q C D T F p hp).support = p.support := by
  exact Path.support_restrictGraphOnSupport p
    (fun {x y} (e : Q.graph.Adj x y) hx hy ↦
      (show (delta Q C D T F).graph.Adj x y from
        ⟨e, hp hx, hp hy⟩))

@[simp] theorem initial_restrictPath (Q : DWeb V) (C D T : Set V)
    (F : Set Q.DPath) (p : Q.DPath)
    (hp : p.support ⊆ carrier Q C T F) :
    (restrictPath Q C D T F p hp).initial = p.initial := by
  exact Path.initial_restrictGraphOnSupport p
    (fun {x y} (e : Q.graph.Adj x y) hx hy ↦
      (show (delta Q C D T F).graph.Adj x y from
        ⟨e, hp hx, hp hy⟩))

@[simp] theorem terminal_restrictPath (Q : DWeb V) (C D T : Set V)
    (F : Set Q.DPath) (p : Q.DPath)
    (hp : p.support ⊆ carrier Q C T F) :
    (delta Q C D T F).terminal? (restrictPath Q C D T F p hp) =
      Q.terminal? p := by
  rcases p with p | p <;> rfl

/-- Every member of the distinguished suffix family lies in the displayed
carrier by construction. -/
theorem member_support_subset_carrier (Q : DWeb V) (C T : Set V)
    (F : Set Q.DPath) {p : Q.DPath} (hp : p ∈ F) :
    p.support ⊆ carrier Q C T F := by
  intro x hxp
  exact Set.mem_union_right _ ⟨p, hp, hxp⟩

/-- The suffix family, retyped in the exact restricted web. -/
def restrictedFamily (Q : DWeb V) (C D T : Set V)
    (F : Set Q.DPath) : Set (delta Q C D T F).DPath :=
  Set.range fun p : F ↦
    restrictPath Q C D T F p.1
      (member_support_subset_carrier Q C T F p.2)

theorem restrictMember_injective (Q : DWeb V) (C D T : Set V)
    (F : Set Q.DPath) :
    Function.Injective (fun p : F ↦
      restrictPath Q C D T F p.1
        (member_support_subset_carrier Q C T F p.2)) := by
  intro p q hpq
  apply Subtype.ext
  have h := congrArg (liftPath Q C D T F) hpq
  simpa only [liftPath_restrictPath] using h

/-- Endpoint purity is unchanged by restriction to an induced graph
containing the path. -/
theorem isPathBetween_restrictPath
    (Q : DWeb V) (C D T : Set V) (F : Set Q.DPath)
    {A B : Set V} {p : Q.DPath}
    (hp : p.support ⊆ carrier Q C T F)
    (hpath : IsPathBetween Q A B p) :
    IsPathBetween (delta Q C D T F) A B
      (restrictPath Q C D T F p hp) := by
  rcases hpath with ⟨q, rfl, hends, hsource⟩
  let hq : ∀ {x y : V}, Q.graph.Adj x y →
      x ∈ q.support → y ∈ q.support →
        (delta Q C D T F).graph.Adj x y :=
    fun {_ _} e hx hy ↦ ⟨e, hp hx, hp hy⟩
  let q' : FinitePath (delta Q C D T F).graph :=
    q.restrictGraphOnSupport hq
  refine ⟨q', rfl, ?_, ?_⟩
  · rw [show q'.support = q.support by
      exact FinitePath.support_restrictGraphOnSupport q hq]
    exact hends
  · rw [show q'.support = q.support by
      exact FinitePath.support_restrictGraphOnSupport q hq]
    exact hsource

/-- An ambient suffix linkage retypes verbatim as a linkage in the exact
induced `Delta`. -/
theorem restrictedFamily_isLinkageBetween
    (Q : DWeb V) {C D T A : Set V} {F : Set Q.DPath}
    (hF : IsLinkageBetween Q A T F) :
    IsLinkageBetween (delta Q C D T F) A T
      (restrictedFamily Q C D T F) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro p ⟨p₀, rfl⟩ q ⟨q₀, rfl⟩ hpq
    have hp₀q₀ : p₀.1 ≠ q₀.1 := by
      intro h
      apply hpq
      have hp₀q₀ : p₀ = q₀ := Subtype.ext h
      subst q₀
      rfl
    change Disjoint
      (restrictPath Q C D T F p₀.1
        (member_support_subset_carrier Q C T F p₀.2)).support
      (restrictPath Q C D T F q₀.1
        (member_support_subset_carrier Q C T F q₀.2)).support
    rw [support_restrictPath, support_restrictPath]
    exact hF.isWarp p₀.2 q₀.2 hp₀q₀
  · rintro p ⟨p₀, rfl⟩
    obtain ⟨q, hq⟩ := hF.finiteCharacter p₀.2
    rcases p₀ with ⟨p, hpF⟩
    change p = (.inl q : Q.DPath) at hq
    subst p
    let hsupport : q.support ⊆ carrier Q C T F :=
      member_support_subset_carrier Q C T F hpF
    let q' : FinitePath (delta Q C D T F).graph :=
      q.restrictGraphOnSupport fun {_ _} e hx hy ↦
        ⟨e, hsupport hx, hsupport hy⟩
    refine ⟨q', ?_⟩
    rfl
  · ext x
    constructor
    · rintro ⟨p, ⟨p₀, rfl⟩, hpx⟩
      rw [initial_restrictPath] at hpx
      rw [← hF.initialSet_eq]
      exact ⟨p₀.1, p₀.2, hpx⟩
    · intro hx
      rw [← hF.initialSet_eq] at hx
      obtain ⟨p, hpF, hpx⟩ := hx
      let p₀ : F := ⟨p, hpF⟩
      refine ⟨restrictPath Q C D T F p
          (member_support_subset_carrier Q C T F hpF), ⟨p₀, rfl⟩, ?_⟩
      simpa only [initial_restrictPath] using hpx
  · rintro x ⟨p, ⟨p₀, rfl⟩, hpx⟩
    apply hF.terminalFrontier_subset
    exact ⟨p₀.1, p₀.2, by simpa only [terminal_restrictPath] using hpx⟩
  · rintro p ⟨p₀, rfl⟩
    exact isPathBetween_restrictPath Q C D T F
      (member_support_subset_carrier Q C T F p₀.2)
      (hF.endpointPure p₀.1 p₀.2)

/-- The generic roof estimate for the suffix family.  Unlike the common
source-specialized version, its initial set may be an intermediate
frontier.  The hypotheses are precisely the three inputs to
`pathSupportRoof`: the starts already lie under `T`, terminals lie in `T`,
and a suffix meets `T` only at its terminal. -/
theorem linkage_vertexSet_subset_roof_of_initial
    (Q : DWeb V) {A T : Set V} {F : Set Q.DPath}
    (hF : IsLinkageBetween Q A T F)
    (hAroof : A ⊆ Q.roof T)
    (hclean : SingularContinuation.TerminalCleanAt Q F T) :
    Q.vertexSet F ⊆ Q.roof T := by
  rintro x ⟨p, hpF, hxp⟩
  apply Q.pathSupportRoof p T
  · apply hAroof
    have hinit : p.initial ∈ Q.initialSet F := ⟨p, hpF, rfl⟩
    rw [hF.initialSet_eq] at hinit
    exact hinit
  · intro t ht
    apply hF.terminalFrontier_subset
    exact ⟨p, hpF, ht⟩
  · intro y hy
    rw [hclean p hpF y hy.1 hy.2]
    exact Set.mem_singleton y
  · exact hxp

/-! ## Exact quotient geometry -/

/-- A convenient local form of the retained-carrier calculation.  Once the
two strict roofs agree on the displayed carrier, and the suffix family lies
under `T`, subtracting the new strict roof leaves precisely the old annulus
`roof T \ strictRoof C`. -/
theorem retainedCarrier_eq_of_strictRoof_on_carrier
    (Q : DWeb V) {C D T : Set V} (F : Set Q.DPath)
    (hFroof : Q.vertexSet F ⊆ Q.roof T)
    (hstrict :
      carrier Q C T F ∩
          (normalizedDelta Q C D T F).strictRoof (C \ D) =
        carrier Q C T F ∩ Q.strictRoof C) :
    carrier Q C T F \
        (normalizedDelta Q C D T F).strictRoof (C \ D) =
      Q.roof T \ Q.strictRoof C := by
  ext x
  constructor
  · intro hx
    have hxRoof : x ∈ Q.roof T := by
      rcases hx.1 with hxAnnulus | hxF
      · exact hxAnnulus.1
      · exact hFroof hxF
    refine ⟨hxRoof, ?_⟩
    intro hxStrict
    have hxOld : x ∈ carrier Q C T F ∩ Q.strictRoof C :=
      ⟨hx.1, hxStrict⟩
    rw [← hstrict] at hxOld
    exact hx.2 hxOld.2
  · intro hx
    have hxCarrier : x ∈ carrier Q C T F :=
      Or.inl ⟨hx.1, hx.2⟩
    refine ⟨hxCarrier, ?_⟩
    intro hxStrict
    have hxNew : x ∈ carrier Q C T F ∩
        (normalizedDelta Q C D T F).strictRoof (C \ D) :=
      ⟨hxCarrier, hxStrict⟩
    rw [hstrict] at hxNew
    exact hx.2 hxNew.2

/-- Split form of the localized strict-roof geometry.  The annular summand
must survive the new quotient, while the part of a suffix lying in the old
strict roof must be removed.  These are the two path-geometric statements
which the separating stop-over and suffix chronology provide. -/
theorem strictRoof_on_carrier_eq_of_annulus_suffix
    (Q : DWeb V) {C D T : Set V} (F : Set Q.DPath)
    (hFroof : Q.vertexSet F ⊆ Q.roof T)
    (hannulus : Disjoint (Q.roof T \ Q.strictRoof C)
      ((normalizedDelta Q C D T F).strictRoof (C \ D)))
    (hsuffix : Q.vertexSet F ∩ Q.strictRoof C ⊆
      (normalizedDelta Q C D T F).strictRoof (C \ D)) :
    carrier Q C T F ∩
        (normalizedDelta Q C D T F).strictRoof (C \ D) =
      carrier Q C T F ∩ Q.strictRoof C := by
  ext x
  constructor
  · intro hx
    refine ⟨hx.1, ?_⟩
    by_contra hxOld
    have hxRoof : x ∈ Q.roof T := by
      rcases hx.1 with hxAnnulus | hxF
      · exact hxAnnulus.1
      · exact hFroof hxF
    exact Set.disjoint_left.1 hannulus ⟨hxRoof, hxOld⟩ hx.2
  · intro hx
    refine ⟨hx.1, ?_⟩
    have hxF : x ∈ Q.vertexSet F := by
      rcases hx.1 with hxAnnulus | hxF
      · exact False.elim (hxAnnulus.2 hx.2)
      · exact hxF
    exact hsuffix ⟨hxF, hx.2⟩

/-- The quotient identity in Assertion 9.10, with its genuinely geometric
content isolated in one carrier equality.  After quotienting by `C \ D`,
the retained vertices of the displayed `Delta` carrier must be exactly
`roof T \ strictRoof C`.  Together with trimming of `C` inside `Delta` and
the normalized no-incoming-source condition, this determines every field of
the two webs, not only their path relations. -/
theorem quotient_eq_roofQuotientWeb
    (Q : DWeb V) {C D T : Set V} (F : Set Q.DPath)
    (hDC : D ⊆ C)
    (hNoEnter : (delta Q C D T F).NoEdgeEnters D)
    (htrim : IsTrimmedSeparator (delta Q C D T F) C)
    (hcarrier :
      carrier Q C T F \
          (delta Q C D T F).strictRoof (C \ D) =
        Q.roof T \ Q.strictRoof C) :
    (delta Q C D T F).quotient (C \ D) =
      roofQuotientWeb Q C T := by
  rw [DWeb.mk.injEq]
  refine ⟨?_, ?_, rfl⟩
  · ext x y
    change
      (((Q.graph.Adj x y ∧ x ∈ carrier Q C T F ∧
          y ∈ carrier Q C T F) ∧
          x ∉ (delta Q C D T F).strictRoof (C \ D) ∧
          y ∉ (delta Q C D T F).strictRoof (C \ D) ∧
          y ∉ C \ D) ↔
        ((Q.graph.Adj x y ∧ x ∉ Q.strictRoof C ∧
          y ∉ Q.strictRoof C ∧ y ∉ C) ∧
          x ∈ Q.roof T ∧ y ∈ Q.roof T))
    constructor
    · rintro ⟨hxy, hxStrict, hyStrict, hyDiff⟩
      have hxRetained : x ∈ carrier Q C T F \
          (delta Q C D T F).strictRoof (C \ D) :=
        ⟨hxy.2.1, hxStrict⟩
      have hyRetained : y ∈ carrier Q C T F \
          (delta Q C D T F).strictRoof (C \ D) :=
        ⟨hxy.2.2, hyStrict⟩
      have hxRoof : x ∈ Q.roof T \ Q.strictRoof C := by
        rw [← hcarrier]
        exact hxRetained
      have hyRoof : y ∈ Q.roof T \ Q.strictRoof C := by
        rw [← hcarrier]
        exact hyRetained
      refine ⟨⟨hxy.1, hxRoof.2, hyRoof.2, ?_⟩,
        hxRoof.1, hyRoof.1⟩
      intro hyC
      by_cases hyD : y ∈ D
      · exact hNoEnter hxy hyD
      · exact hyDiff ⟨hyC, hyD⟩
    · rintro ⟨⟨hxy, hxStrict, hyStrict, hyC⟩, hxRoof, hyRoof⟩
      have hxRetained : x ∈ carrier Q C T F \
          (delta Q C D T F).strictRoof (C \ D) := by
        rw [hcarrier]
        exact ⟨hxRoof, hxStrict⟩
      have hyRetained : y ∈ carrier Q C T F \
          (delta Q C D T F).strictRoof (C \ D) := by
        rw [hcarrier]
        exact ⟨hyRoof, hyStrict⟩
      exact ⟨⟨hxy, hxRetained.1, hyRetained.1⟩,
        hxRetained.2, hyRetained.2, fun hy ↦ hyC hy.1⟩
  · have hUnion : D ∪ (C \ D) = C := by
      ext x
      constructor
      · rintro (hx | hx)
        · exact hDC hx
        · exact hx.1
      · intro hxC
        by_cases hxD : x ∈ D
        · exact Or.inl hxD
        · exact Or.inr ⟨hxC, hxD⟩
    change (delta Q C D T F).essential (D ∪ (C \ D)) = C
    rw [hUnion]
    exact htrim

/-- The assumption-faithful quotient identity.  Normalizing both derived
webs removes the otherwise unjustified requirement that the raw induced
graph have no edge entering the intermediate frontier `D`. -/
theorem normalizedQuotient_eq_normalizedRoofQuotientWeb
    (Q : DWeb V) {C D T : Set V} (F : Set Q.DPath)
    (hDC : D ⊆ C)
    (htrim : IsTrimmedSeparator (normalizedDelta Q C D T F) C)
    (hcarrier :
      carrier Q C T F \
          (normalizedDelta Q C D T F).strictRoof (C \ D) =
        Q.roof T \ Q.strictRoof C) :
    (normalizedDelta Q C D T F).quotient (C \ D) =
      normalizedRoofQuotientWeb Q C T := by
  rw [DWeb.mk.injEq]
  refine ⟨?_, ?_, rfl⟩
  · ext x y
    change
      (((((Q.graph.Adj x y ∧ x ∈ carrier Q C T F ∧
          y ∈ carrier Q C T F) ∧ y ∉ D ∧ x ∉ T) ∧
          x ∉ (normalizedDelta Q C D T F).strictRoof (C \ D) ∧
          y ∉ (normalizedDelta Q C D T F).strictRoof (C \ D) ∧
          y ∉ C \ D)) ↔
        ((((Q.graph.Adj x y ∧ x ∉ Q.strictRoof C ∧
          y ∉ Q.strictRoof C ∧ y ∉ C) ∧
          x ∈ Q.roof T ∧ y ∈ Q.roof T) ∧
          y ∉ C ∧ x ∉ T)))
    constructor
    · rintro ⟨hxy, hxStrict, hyStrict, hyDiff⟩
      have hxRetained : x ∈ carrier Q C T F \
          (normalizedDelta Q C D T F).strictRoof (C \ D) :=
        ⟨hxy.1.2.1, hxStrict⟩
      have hyRetained : y ∈ carrier Q C T F \
          (normalizedDelta Q C D T F).strictRoof (C \ D) :=
        ⟨hxy.1.2.2, hyStrict⟩
      have hxRoof : x ∈ Q.roof T \ Q.strictRoof C := by
        rw [← hcarrier]
        exact hxRetained
      have hyRoof : y ∈ Q.roof T \ Q.strictRoof C := by
        rw [← hcarrier]
        exact hyRetained
      have hyC : y ∉ C := by
        intro hyC
        by_cases hyD : y ∈ D
        · exact hxy.2.1 hyD
        · exact hyDiff ⟨hyC, hyD⟩
      exact ⟨⟨⟨hxy.1.1, hxRoof.2, hyRoof.2, hyC⟩,
        hxRoof.1, hyRoof.1⟩, hyC, hxy.2.2⟩
    · rintro ⟨⟨⟨hxy, hxStrict, hyStrict, hyC⟩,
        hxRoof, hyRoof⟩, -, hxT⟩
      have hxRetained : x ∈ carrier Q C T F \
          (normalizedDelta Q C D T F).strictRoof (C \ D) := by
        rw [hcarrier]
        exact ⟨hxRoof, hxStrict⟩
      have hyRetained : y ∈ carrier Q C T F \
          (normalizedDelta Q C D T F).strictRoof (C \ D) := by
        rw [hcarrier]
        exact ⟨hyRoof, hyStrict⟩
      exact ⟨⟨⟨hxy, hxRetained.1, hyRetained.1⟩,
        fun hyD ↦ hyC (hDC hyD), hxT⟩,
        hxRetained.2, hyRetained.2, fun hy ↦ hyC hy.1⟩
  · have hUnion : D ∪ (C \ D) = C := by
      ext x
      constructor
      · rintro (hx | hx)
        · exact hDC hx
        · exact hx.1
      · intro hxC
        by_cases hxD : x ∈ D
        · exact Or.inl hxD
        · exact Or.inr ⟨hxC, hxD⟩
    change (normalizedDelta Q C D T F).essential
      (D ∪ (C \ D)) = C
    rw [hUnion]
    exact htrim

/-! ## Source Corollary 3.6: quotient reflection -/

/-- A source vertex outside the initial set of a wave remains outside the
initial set after taking the concrete general wave quotient, provided the
source is disjoint from the roof of the commitment set. -/
theorem not_mem_initialSet_generalWaveQuotient
    (G : DWeb V) {X : Set V} {W : Set G.DPath} {a : V}
    (hdisjoint : Disjoint G.source (G.roof X))
    (haSource : a ∈ G.source) (haMissing : a ∉ G.initialSet W) :
    a ∉ (G.quotient X).initialSet (G.generalWaveQuotient X W) := by
  intro ha
  rw [DWeb.generalWaveQuotient, G.initialSet_admissibleWarpQuotient] at ha
  rcases ha with ha | ha
  · obtain ⟨q, hq, hqa⟩ := ha
    obtain ⟨p, hpW, hpfinish, rfl⟩ := hq
    simp only [DWeb.terminalRoofSuffix] at hqa
    split at hqa
    next hmeet =>
      have haRoof : a ∈ G.roof X := by
        rw [← hqa]
        exact p.lastHit_start_mem _ _
      exact Set.disjoint_left.1 hdisjoint haSource haRoof
    next _ =>
      apply haMissing
      exact ⟨.inl p, hpW, hqa⟩
  · exact Set.disjoint_left.1 hdisjoint haSource
      (G.subset_roof X (G.essential_subset X ha.1))

/-- Source Corollary 3.6 in the normalized same-vertex formalization: if
the old source misses `roof X`, a hindrance remains a hindrance after
quotienting by `X`. -/
theorem hindrance_generalWaveQuotient
    (G : DWeb V) {X : Set V} {W : Set G.DPath}
    (hNoEnter : G.NoEdgeEnters G.source)
    (hdisjoint : Disjoint G.source (G.roof X))
    (hW : G.IsHindrance W) :
    (G.quotient X).IsHindrance (G.generalWaveQuotient X W) := by
  refine ⟨G.isWave_generalWaveQuotient hNoEnter hW.1, ?_⟩
  intro hinitial
  have hmissing : (G.source \ G.initialSet W).Nonempty := by
    by_contra hempty
    apply hW.2
    apply Set.Subset.antisymm hW.1.2.1
    intro a ha
    by_contra haInitial
    exact hempty ⟨a, ha, haInitial⟩
  obtain ⟨a, haSource, haMissing⟩ := hmissing
  have haNotRoof : a ∉ G.roof X :=
    Set.disjoint_left.1 hdisjoint haSource
  have haQuotientSource : a ∈ (G.quotient X).source := by
    rw [G.quotient_source_eq_union_sdiff_strictRoof_of_noEdgeEnters_general
      hNoEnter]
    exact ⟨Or.inl haSource, fun haStrict ↦ haNotRoof haStrict.1⟩
  have haNotInitial := not_mem_initialSet_generalWaveQuotient G
    hdisjoint haSource haMissing
  exact haNotInitial (hinitial.symm ▸ haQuotientSource)

/-- Contrapositive form used in Assertion 9.10. -/
theorem isUnhindered_of_quotient
    (G : DWeb V) {X : Set V}
    (hNoEnter : G.NoEdgeEnters G.source)
    (hdisjoint : Disjoint G.source (G.roof X))
    (hquotient : (G.quotient X).IsUnhindered) :
    G.IsUnhindered := by
  rintro ⟨W, hW⟩
  exact hquotient ⟨G.generalWaveQuotient X W,
    hindrance_generalWaveQuotient G hNoEnter hdisjoint hW⟩

/-- A trimmed set makes any subset of it which omits `d` unroofable from
`d`.  This is the elementary verification of the side condition in
Corollary 3.6 for `X = C \ D`. -/
theorem disjoint_subset_roof_sdiff_of_trimmed
    (G : DWeb V) {C D : Set V}
    (htrim : IsTrimmedSeparator G C) (hDC : D ⊆ C) :
    Disjoint D (G.roof (C \ D)) := by
  apply Set.disjoint_left.2
  intro d hdD hdRoof
  have hdC : d ∈ C := hDC hdD
  have hdEssential : d ∈ G.essential C := by
    rw [htrim]
    exact hdC
  apply hdEssential.2
  apply G.roof_mono (show C \ D ⊆ C \ {d} by
    intro x hx
    exact ⟨hx.1, fun hxd ↦ hx.2 (hxd ▸ hdD)⟩)
  exact hdRoof

/-- A pathwise constructor for trimmedness.  This is the convenient target
for the stop-over geometry: for each `c`, construct one normalized-Delta
path to the later frontier which avoids every other point of `C`. -/
theorem isTrimmedSeparator_of_avoiding_paths
    (G : DWeb V) {C : Set V}
    (hpath : ∀ c ∈ C, ∃ p : DirectedPath.FinitePath G.graph,
      G.IsTargetPathFrom c p ∧ G.Avoids p (C \ {c})) :
    IsTrimmedSeparator G C := by
  apply Set.Subset.antisymm (G.essential_subset C)
  intro c hc
  refine ⟨hc, (G.not_mem_roof_iff (C \ {c}) c).2 ?_⟩
  exact hpath c hc

/-- Ambient trimmedness and the height relation `C ⊆ roof T` imply that
`C` remains trimmed in the normalized restricted web.  The witness for
`c ∈ C` is its ambient `C \ {c}`-avoiding target path, stopped at the first
hit on `T`; every vertex of that prefix lies in the annular carrier. -/
theorem normalizedDelta_isTrimmedSeparator
    (Q : DWeb V) {C D T : Set V} (F : Set Q.DPath)
    (hDC : D ⊆ C)
    (hCtrim : IsTrimmedSeparator Q C)
    (hCroof : C ⊆ Q.roof T) :
    IsTrimmedSeparator (normalizedDelta Q C D T F) C := by
  apply isTrimmedSeparator_of_avoiding_paths
  intro c hc
  have hcEssential : c ∈ Q.essential C := by
    rw [hCtrim]
    exact hc
  obtain ⟨p, hpTarget, hpAvoid⟩ :=
    (Q.not_mem_roof_iff (C \ {c}) c).1 hcEssential.2
  have hcRoofT : c ∈ Q.roof T := hCroof hc
  have hpMeetT : p.walk.Meets T := hcRoofT p hpTarget
  let f := p.firstHit T hpMeetT
  have hfRoofT : f.support ⊆ Q.roof T :=
    firstHit_support_subset_roof_ambient Q T p
      (by simpa only [hpTarget.1] using hcRoofT) hpMeetT
  have hpAvoid' : RelationalRoof.Avoids Q.graph.Adj p
      (C \ {p.start}) := by
    intro x hxp hxC
    apply Set.disjoint_left.1 hpAvoid hxp
    simpa only [hpTarget.1] using hxC
  have hfAvoidStrict : ∀ {x}, x ∈ f.support →
      x ∉ Q.strictRoof C := by
    intro x hxf hxStrict
    have hxp : x ∈ p.support := p.firstHit_support_subset T hpMeetT hxf
    by_cases hxc : x = c
    · subst x
      exact Set.disjoint_left.1 (Q.disjoint_strictRoof_essential C)
        hxStrict hcEssential
    · have hxne : x ≠ p.start := by
        intro hx
        exact hxc (hx.trans hpTarget.1)
      have hxNotRoof :=
        RelationalRoof.not_mem_roof_of_later_mem_targetPath
          Q.graph.Adj Q.target p hpTarget hpAvoid' hxp hxne
      exact hxNotRoof hxStrict.1
  have hfCarrier : f.support ⊆ carrier Q C T F := by
    intro x hxf
    exact Or.inl ⟨hfRoofT hxf, hfAvoidStrict hxf⟩
  let hrestrict : ∀ {x y : V}, Q.graph.Adj x y →
      x ∈ f.support → y ∈ f.support →
        (delta Q C D T F).graph.Adj x y :=
    fun {_ _} e hx hy ↦ ⟨e, hfCarrier hx, hfCarrier hy⟩
  let fd : DirectedPath.FinitePath (delta Q C D T F).graph :=
    f.restrictGraphOnSupport hrestrict
  have hfdSupport : fd.support = f.support :=
    DirectedPath.FinitePath.support_restrictGraphOnSupport f hrestrict
  have hfdWalkSupport : fd.walk.support = f.walk.support := by
    dsimp only [fd, DirectedPath.FinitePath.restrictGraphOnSupport]
    exact DirectedPath.Walk.support_restrictGraphOnSupport f.walk _
  have hsource : ∀ {x}, x ∈ fd.walk.support.tail →
      x ∉ (delta Q C D T F).source := by
    intro x hxtail hxD
    change x ∈ D at hxD
    have hxfd : x ∈ fd.support := List.mem_of_mem_tail hxtail
    have hxf : x ∈ f.support := hfdSupport ▸ hxfd
    have hxp : x ∈ p.support := p.firstHit_support_subset T hpMeetT hxf
    have hxne : x ≠ c := by
      intro hxc
      have hheadNe := fd.isPath.rel_head_tail hxtail
      apply hheadNe
      have hfdStart : fd.start = c := by
        change f.start = c
        simpa only [f, DirectedPath.FinitePath.firstHit] using hpTarget.1
      exact fd.walk.head_support.trans (hfdStart.trans hxc.symm)
    exact Set.disjoint_left.1 hpAvoid hxp ⟨hDC hxD, hxne⟩
  have htarget : ∀ {x}, x ∈ fd.walk.support.dropLast →
      x ∉ (delta Q C D T F).target := by
    intro x hxdrop hxT
    change x ∈ T at hxT
    rw [hfdWalkSupport] at hxdrop
    exact p.firstHit_no_mem_before T hpMeetT hxdrop hxT
  let r : DirectedPath.FinitePath (normalizedDelta Q C D T F).graph :=
    { start := fd.start
      finish := fd.finish
      walk := (delta Q C D T F).normalizeWalk fd.walk hsource htarget
      isPath := by
        change ((delta Q C D T F).normalizeWalk
          fd.walk hsource htarget).support.Nodup
        rw [(delta Q C D T F).support_normalizeWalk]
        exact fd.isPath }
  refine ⟨r, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · change fd.start = c
      change f.start = c
      simpa only [f, DirectedPath.FinitePath.firstHit] using hpTarget.1
    · change fd.finish ∈ T
      change f.finish ∈ T
      exact p.firstHit_finish_mem T hpMeetT
  · apply Set.disjoint_left.2
    intro x hxr hxC
    have hxrfd : x ∈ fd.support := by
      change x ∈ ((delta Q C D T F).normalizeWalk
        fd.walk hsource htarget).support at hxr
      rwa [(delta Q C D T F).support_normalizeWalk] at hxr
    have hxf : x ∈ f.support := hfdSupport ▸ hxrfd
    have hxp : x ∈ p.support := p.firstHit_support_subset T hpMeetT hxf
    exact Set.disjoint_left.1 hpAvoid hxp hxC

/-- Every vertex of the old annulus has a target path in the normalized
restricted web which avoids all other vertices of `C`.  This is the path
form of the fact that the annular summand survives quotienting by
`C \ D`.  Notice that no property of the distinguished suffix family is
needed: the whole witness is contained in `roof T \ strictRoof C`, hence in
the first summand of `carrier`. -/
theorem exists_normalizedDelta_targetPath_avoiding_C_except
    (Q : DWeb V) {C D T : Set V} (F : Set Q.DPath)
    (hDC : D ⊆ C) {x : V}
    (hxRoofT : x ∈ Q.roof T)
    (hxNotStrict : x ∉ Q.strictRoof C) :
    ∃ p : DirectedPath.FinitePath
        (normalizedDelta Q C D T F).graph,
      (normalizedDelta Q C D T F).IsTargetPathFrom x p ∧
        (normalizedDelta Q C D T F).Avoids p (C \ {x}) := by
  have hxNotRoofExcept : x ∉ Q.roof (C \ {x}) := by
    by_cases hxC : x ∈ C
    · have hxRoofC : x ∈ Q.roof C := Q.subset_roof C hxC
      have hxEssential : x ∈ Q.essential C := by
        by_contra hxNotEssential
        exact hxNotStrict ⟨hxRoofC, hxNotEssential⟩
      exact hxEssential.2
    · have hxNotRoofC : x ∉ Q.roof C := by
        intro hxRoofC
        apply hxNotStrict
        refine ⟨hxRoofC, ?_⟩
        intro hxEssential
        exact hxC (Q.essential_subset C hxEssential)
      intro hxRoofExcept
      exact hxNotRoofC (Q.roof_mono Set.sdiff_subset hxRoofExcept)
  obtain ⟨p, hpTarget, hpAvoid⟩ :=
    (Q.not_mem_roof_iff (C \ {x}) x).1 hxNotRoofExcept
  have hpMeetT : p.walk.Meets T := hxRoofT p hpTarget
  let f := p.firstHit T hpMeetT
  have hfRoofT : f.support ⊆ Q.roof T :=
    firstHit_support_subset_roof_ambient Q T p
      (by simpa only [hpTarget.1] using hxRoofT) hpMeetT
  have hpAvoid' : RelationalRoof.Avoids Q.graph.Adj p
      (C \ {p.start}) := by
    intro y hyp hyC
    apply Set.disjoint_left.1 hpAvoid hyp
    simpa only [hpTarget.1] using hyC
  have hfAvoidStrict : ∀ {y}, y ∈ f.support →
      y ∉ Q.strictRoof C := by
    intro y hyf hyStrict
    have hyp : y ∈ p.support := p.firstHit_support_subset T hpMeetT hyf
    by_cases hyx : y = x
    · subst y
      exact hxNotStrict hyStrict
    · have hyne : y ≠ p.start := by
        intro hy
        exact hyx (hy.trans hpTarget.1)
      have hyNotRoof :=
        RelationalRoof.not_mem_roof_of_later_mem_targetPath
          Q.graph.Adj Q.target p hpTarget hpAvoid' hyp hyne
      exact hyNotRoof hyStrict.1
  have hfCarrier : f.support ⊆ carrier Q C T F := by
    intro y hyf
    exact Or.inl ⟨hfRoofT hyf, hfAvoidStrict hyf⟩
  let hrestrict : ∀ {y z : V}, Q.graph.Adj y z →
      y ∈ f.support → z ∈ f.support →
        (delta Q C D T F).graph.Adj y z :=
    fun {_ _} e hy hz ↦ ⟨e, hfCarrier hy, hfCarrier hz⟩
  let fd : DirectedPath.FinitePath (delta Q C D T F).graph :=
    f.restrictGraphOnSupport hrestrict
  have hfdSupport : fd.support = f.support :=
    DirectedPath.FinitePath.support_restrictGraphOnSupport f hrestrict
  have hfdWalkSupport : fd.walk.support = f.walk.support := by
    dsimp only [fd, DirectedPath.FinitePath.restrictGraphOnSupport]
    exact DirectedPath.Walk.support_restrictGraphOnSupport f.walk _
  have hsource : ∀ {y}, y ∈ fd.walk.support.tail →
      y ∉ (delta Q C D T F).source := by
    intro y hytail hyD
    change y ∈ D at hyD
    have hyfd : y ∈ fd.support := List.mem_of_mem_tail hytail
    have hyf : y ∈ f.support := hfdSupport ▸ hyfd
    have hyp : y ∈ p.support := p.firstHit_support_subset T hpMeetT hyf
    have hyne : y ≠ x := by
      intro hyx
      have hheadNe := fd.isPath.rel_head_tail hytail
      apply hheadNe
      have hfdStart : fd.start = x := by
        change f.start = x
        simpa only [f, DirectedPath.FinitePath.firstHit] using hpTarget.1
      exact fd.walk.head_support.trans (hfdStart.trans hyx.symm)
    exact Set.disjoint_left.1 hpAvoid hyp ⟨hDC hyD, hyne⟩
  have htarget : ∀ {y}, y ∈ fd.walk.support.dropLast →
      y ∉ (delta Q C D T F).target := by
    intro y hydrop hyT
    change y ∈ T at hyT
    rw [hfdWalkSupport] at hydrop
    exact p.firstHit_no_mem_before T hpMeetT hydrop hyT
  let r : DirectedPath.FinitePath
      (normalizedDelta Q C D T F).graph :=
    { start := fd.start
      finish := fd.finish
      walk := (delta Q C D T F).normalizeWalk fd.walk hsource htarget
      isPath := by
        change ((delta Q C D T F).normalizeWalk
          fd.walk hsource htarget).support.Nodup
        rw [(delta Q C D T F).support_normalizeWalk]
        exact fd.isPath }
  refine ⟨r, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · change fd.start = x
      change f.start = x
      simpa only [f, DirectedPath.FinitePath.firstHit] using hpTarget.1
    · change fd.finish ∈ T
      change f.finish ∈ T
      exact p.firstHit_finish_mem T hpMeetT
  · apply Set.disjoint_left.2
    intro y hyr hyC
    have hyrfd : y ∈ fd.support := by
      change y ∈ ((delta Q C D T F).normalizeWalk
        fd.walk hsource htarget).support at hyr
      rwa [(delta Q C D T F).support_normalizeWalk] at hyr
    have hyf : y ∈ f.support := hfdSupport ▸ hyrfd
    have hyp : y ∈ p.support := p.firstHit_support_subset T hpMeetT hyf
    exact Set.disjoint_left.1 hpAvoid hyp hyC

/-- The annular summand of the Assertion 9.10 carrier is disjoint from the
strict roof removed by the new quotient.  This is the generic half of the
localized strict-roof calculation; only the corresponding assertion for
the old-strict part of a suffix needs the ladder chronology. -/
theorem annulus_disjoint_normalizedDelta_strictRoof
    (Q : DWeb V) {C D T : Set V} (F : Set Q.DPath)
    (hDC : D ⊆ C) :
    Disjoint (Q.roof T \ Q.strictRoof C)
      ((normalizedDelta Q C D T F).strictRoof (C \ D)) := by
  apply Set.disjoint_left.2
  intro x hxAnnulus hxStrict
  obtain ⟨p, hpTarget, hpAvoid⟩ :=
    exists_normalizedDelta_targetPath_avoiding_C_except
      Q F hDC hxAnnulus.1 hxAnnulus.2
  by_cases hxCD : x ∈ C \ D
  · have hxEssential : x ∈
        (normalizedDelta Q C D T F).essential (C \ D) := by
      refine ⟨hxCD, ((normalizedDelta Q C D T F).not_mem_roof_iff
        ((C \ D) \ {x}) x).2 ⟨p, hpTarget, ?_⟩⟩
      apply Set.disjoint_left.2
      intro y hyp hy
      exact Set.disjoint_left.1 hpAvoid hyp ⟨hy.1.1, hy.2⟩
    exact Set.disjoint_left.1
      ((normalizedDelta Q C D T F).disjoint_strictRoof_essential (C \ D))
      hxStrict hxEssential
  · have hxNotRoof : x ∉
        (normalizedDelta Q C D T F).roof (C \ D) := by
      apply ((normalizedDelta Q C D T F).not_mem_roof_iff
        (C \ D) x).2
      refine ⟨p, hpTarget, ?_⟩
      apply Set.disjoint_left.2
      intro y hyp hy
      apply Set.disjoint_left.1 hpAvoid hyp
      exact ⟨hy.1, fun hyx ↦ hxCD (hyx ▸ hy)⟩
    exact hxNotRoof hxStrict.1

/-- Exact retained-carrier identity with the only suffix-specific geometry
exposed as a hypothesis.  The annular half is automatic from `D ⊆ C`. -/
theorem retainedCarrier_eq_of_suffix_strictRoof
    (Q : DWeb V) {C D T : Set V} (F : Set Q.DPath)
    (hDC : D ⊆ C)
    (hFroof : Q.vertexSet F ⊆ Q.roof T)
    (hsuffix : Q.vertexSet F ∩ Q.strictRoof C ⊆
      (normalizedDelta Q C D T F).strictRoof (C \ D)) :
    carrier Q C T F \
        (normalizedDelta Q C D T F).strictRoof (C \ D) =
      Q.roof T \ Q.strictRoof C := by
  apply retainedCarrier_eq_of_strictRoof_on_carrier Q F hFroof
  apply strictRoof_on_carrier_eq_of_annulus_suffix Q F hFroof
  · exact annulus_disjoint_normalizedDelta_strictRoof Q F hDC
  · exact hsuffix

/-- The exact quotient-reflection step for the restricted web. -/
theorem delta_isUnhindered_of_quotient
    (Q : DWeb V) {C D T : Set V} (F : Set Q.DPath)
    (hNoEnter : (delta Q C D T F).NoEdgeEnters D)
    (htrim : IsTrimmedSeparator (delta Q C D T F) C)
    (hDC : D ⊆ C)
    (hquotient :
      ((delta Q C D T F).quotient (C \ D)).IsUnhindered) :
    (delta Q C D T F).IsUnhindered := by
  apply isUnhindered_of_quotient (delta Q C D T F) hNoEnter
  · exact disjoint_subset_roof_sdiff_of_trimmed
      (delta Q C D T F) htrim hDC
  · exact hquotient

/-- The quotient-reflection step with the paper's Corollary 3.6 side
condition exposed directly.  This is useful before the terminal-clean
geometry has been packaged as a trimmedness statement in `Delta`. -/
theorem delta_isUnhindered_of_quotient_disjoint
    (Q : DWeb V) {C D T : Set V} (F : Set Q.DPath)
    (hNoEnter : (delta Q C D T F).NoEdgeEnters D)
    (hdisjoint : Disjoint D
      ((delta Q C D T F).roof (C \ D)))
    (hquotient :
      ((delta Q C D T F).quotient (C \ D)).IsUnhindered) :
    (delta Q C D T F).IsUnhindered :=
  isUnhindered_of_quotient (delta Q C D T F)
    hNoEnter hdisjoint hquotient

/-- The complete normalized unhinderedness argument of Assertion 9.10.
Unhinderedness of the ambient quotient passes to its roof restriction; the
exact quotient identity transports it to `normalizedDelta / (C \ D)`; and
Corollary 3.6 reflects it back to `normalizedDelta`. -/
theorem normalizedDelta_isUnhindered_of_geometry
    (Q : DWeb V) {C D T : Set V} (F : Set Q.DPath)
    (hDC : D ⊆ C)
    (htrim : IsTrimmedSeparator (normalizedDelta Q C D T F) C)
    (hcarrier :
      carrier Q C T F \
          (normalizedDelta Q C D T F).strictRoof (C \ D) =
        Q.roof T \ Q.strictRoof C)
    (hsource : (Q.quotient C).source = C)
    (hCroof : C ⊆ Q.roof T)
    (hQ : (Q.quotient C).IsUnhindered) :
    (normalizedDelta Q C D T F).IsUnhindered := by
  let Delta := normalizedDelta Q C D T F
  have hNoEnter : Delta.NoEdgeEnters Delta.source := by
    intro x y hxy hy
    exact ((delta Q C D T F).normalized_isNormalized hxy).1 hy
  have hdisjoint : Disjoint Delta.source (Delta.roof (C \ D)) := by
    simpa only [Delta, normalizedDelta_source] using
      (disjoint_subset_roof_sdiff_of_trimmed Delta htrim hDC)
  have hquotient : (Delta.quotient (C \ D)).IsUnhindered := by
    rw [show Delta.quotient (C \ D) =
        normalizedRoofQuotientWeb Q C T by
      exact normalizedQuotient_eq_normalizedRoofQuotientWeb
        Q F hDC htrim hcarrier]
    exact normalizedRoofQuotientWeb_isUnhindered
      Q hsource hCroof hQ
  exact isUnhindered_of_quotient Delta hNoEnter hdisjoint hquotient

/-- Ambient-data form of the preceding theorem; trimmedness of `C` inside
`normalizedDelta` is reconstructed from the ambient trimmed stop-over. -/
theorem normalizedDelta_isUnhindered_of_ambientGeometry
    (Q : DWeb V) {C D T : Set V} (F : Set Q.DPath)
    (hDC : D ⊆ C)
    (hCtrim : IsTrimmedSeparator Q C)
    (hcarrier :
      carrier Q C T F \
          (normalizedDelta Q C D T F).strictRoof (C \ D) =
        Q.roof T \ Q.strictRoof C)
    (hsource : (Q.quotient C).source = C)
    (hCroof : C ⊆ Q.roof T)
    (hQ : (Q.quotient C).IsUnhindered) :
    (normalizedDelta Q C D T F).IsUnhindered := by
  apply normalizedDelta_isUnhindered_of_geometry Q F hDC
  · exact normalizedDelta_isTrimmedSeparator Q F hDC hCtrim hCroof
  · exact hcarrier
  · exact hsource
  · exact hCroof
  · exact hQ

/-- Ambient-data form with the exact remaining suffix chronology exposed.
All annular quotient geometry is discharged internally. -/
theorem normalizedDelta_isUnhindered_of_suffixStrictRoof
    (Q : DWeb V) {C D T : Set V} (F : Set Q.DPath)
    (hDC : D ⊆ C)
    (hCtrim : IsTrimmedSeparator Q C)
    (hFroof : Q.vertexSet F ⊆ Q.roof T)
    (hsuffix : Q.vertexSet F ∩ Q.strictRoof C ⊆
      (normalizedDelta Q C D T F).strictRoof (C \ D))
    (hsource : (Q.quotient C).source = C)
    (hCroof : C ⊆ Q.roof T)
    (hQ : (Q.quotient C).IsUnhindered) :
    (normalizedDelta Q C D T F).IsUnhindered := by
  apply normalizedDelta_isUnhindered_of_ambientGeometry
    Q F hDC hCtrim
  · exact retainedCarrier_eq_of_suffix_strictRoof
      Q F hDC hFroof hsuffix
  · exact hsource
  · exact hCroof
  · exact hQ

/-- The lower-cardinal extension clause in the normalized restricted web.
The complementary linkage is accepted already retyped in
`normalizedDelta`; `StarCompatible` supplies that retyping in the stage
construction. -/
theorem exists_normalizedDeltaLinkage_of_lower
    {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (Q : DWeb V) {C D T E : Set V} {F : Set Q.DPath}
    (hDC : D ⊆ C)
    (htrim : IsTrimmedSeparator (normalizedDelta Q C D T F) C)
    (hcarrier :
      carrier Q C T F \
          (normalizedDelta Q C D T F).strictRoof (C \ D) =
        Q.roof T \ Q.strictRoof C)
    (hsource : (Q.quotient C).source = C)
    (hCroof : C ⊆ Q.roof T)
    (hQ : (Q.quotient C).IsUnhindered)
    (hEsub : E ⊆ D) (hE : #E < kappa)
    (Fdelta : Set (normalizedDelta Q C D T F).DPath)
    (hFdelta : IsLinkageBetween (normalizedDelta Q C D T F)
      (D \ E) T Fdelta) :
    ∃ R : Set (normalizedDelta Q C D T F).DPath,
      IsLinkageBetween (normalizedDelta Q C D T F) D T R := by
  let Delta := normalizedDelta Q C D T F
  have hDelta : Delta.IsUnhindered :=
    normalizedDelta_isUnhindered_of_geometry
      Q F hDC htrim hcarrier hsource hCroof hQ
  have hstep : CardinalInductionAt Delta #E :=
    hlower #E hE Delta hDelta
  have hcomplement : IsLinkageBetween Delta
      (Delta.source \ E) Delta.target Fdelta := by
    simpa only [Delta, normalizedDelta_source, normalizedDelta_target] using
      hFdelta
  obtain ⟨R, hR⟩ :=
    hstep.extension E
      (by simpa only [Delta, normalizedDelta_source] using hEsub)
      rfl ⟨Fdelta, hcomplement⟩
  exact ⟨R, by
    simpa only [Delta, normalizedDelta_source, normalizedDelta_target] using
      hR⟩

/-- Lower-cardinal extension from the ambient stop-over data, exposing only
the suffix portion of the strict-roof calculation. -/
theorem exists_normalizedDeltaLinkage_of_suffixStrictRoof_lower
    {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (Q : DWeb V) {C D T E : Set V} {F : Set Q.DPath}
    (hDC : D ⊆ C)
    (hCtrim : IsTrimmedSeparator Q C)
    (hFroof : Q.vertexSet F ⊆ Q.roof T)
    (hsuffix : Q.vertexSet F ∩ Q.strictRoof C ⊆
      (normalizedDelta Q C D T F).strictRoof (C \ D))
    (hsource : (Q.quotient C).source = C)
    (hCroof : C ⊆ Q.roof T)
    (hQ : (Q.quotient C).IsUnhindered)
    (hEsub : E ⊆ D) (hE : #E < kappa)
    (Fdelta : Set (normalizedDelta Q C D T F).DPath)
    (hFdelta : IsLinkageBetween (normalizedDelta Q C D T F)
      (D \ E) T Fdelta) :
    ∃ R : Set (normalizedDelta Q C D T F).DPath,
      IsLinkageBetween (normalizedDelta Q C D T F) D T R := by
  apply exists_normalizedDeltaLinkage_of_lower
    hlower Q hDC
    (normalizedDelta_isTrimmedSeparator Q F hDC hCtrim hCroof)
    (retainedCarrier_eq_of_suffix_strictRoof Q F hDC hFroof hsuffix)
    hsource hCroof hQ hEsub hE Fdelta hFdelta

/-- The exact lower-cardinal extension-clause input produced by Assertion
9.10.  The complement family is the old-ladder suffix linkage `F`, retyped
inside the induced `Delta`; quotient reflection proves that `Delta` is
unhindered, after which the lower extension clause fills the exceptional
source set `E`. -/
theorem exists_deltaLinkage_of_lower
    {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (Q : DWeb V) {C D T E : Set V} {F : Set Q.DPath}
    (hNoEnter : (delta Q C D T F).NoEdgeEnters D)
    (hdisjoint : Disjoint D
      ((delta Q C D T F).roof (C \ D)))
    (hquotient :
      ((delta Q C D T F).quotient (C \ D)).IsUnhindered)
    (hEsub : E ⊆ D) (hE : #E < kappa)
    (hF : IsLinkageBetween Q (D \ E) T F) :
    ∃ R : Set (delta Q C D T F).DPath,
      IsLinkageBetween (delta Q C D T F) D T R := by
  let Delta := delta Q C D T F
  have hDelta : Delta.IsUnhindered :=
    delta_isUnhindered_of_quotient_disjoint Q F
      hNoEnter hdisjoint hquotient
  have hcomplement : IsLinkageBetween Delta
      (Delta.source \ E) Delta.target (restrictedFamily Q C D T F) := by
    simpa only [Delta, delta_source, delta_target] using
      (restrictedFamily_isLinkageBetween
        (Q := Q) (C := C) (D := D) (T := T) hF)
  have hstep : CardinalInductionAt Delta #E :=
    hlower #E hE Delta hDelta
  obtain ⟨R, hR⟩ :=
    hstep.extension E (by simpa only [Delta, delta_source] using hEsub)
      rfl ⟨restrictedFamily Q C D T F, hcomplement⟩
  exact ⟨R, by simpa only [Delta, delta_source, delta_target] using hR⟩

end SliceRestrictedDelta
end CardinalInduction
end Erdos599
