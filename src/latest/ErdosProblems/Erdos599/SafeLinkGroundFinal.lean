/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SafeLinkGround
import ErdosProblems.Erdos599.SafeLinkBridge

/-!
# The completed countable ground-wave construction

The finite states in `SafeLinkGround` live in successively more-deleted
webs.  This file supplies the missing coherence argument.  We first lift
their families to the fixed web obtained by deleting only the root.  The
lifted families form a forward-extension chain, so a vertex which is on a
stage wave stays on every later stage wave.  Consequently the one-pass
enumeration is fair: every member of the countable closure is eventually
deleted or remains permanently on the wave.

We then restrict every stage to the union of all finite deletion sets.  The
resulting waves all live in one web and still form a chain, whose concrete
chain upper bound is the required ground wave.
-/

namespace Erdos599
namespace SafeLinkGroundFinal

open Set DirectedPath

universe u

variable {V : Type u}

namespace DirectedPath

namespace Walk

/-- Restricting a walk along support-local edge proofs and lifting it back
along the original edge inclusion leaves the walk unchanged. -/
theorem lift_restrictGraphOnSupport {D E : Digraph V} {a b : V}
    (p : Walk D a b)
    (h : ∀ {x y : V}, D.Adj x y → x ∈ p.support → y ∈ p.support →
      E.Adj x y)
    (hED : ∀ {x y : V}, E.Adj x y → D.Adj x y) :
    (p.restrictGraphOnSupport h).lift hED = p := by
  induction p with
  | nil => rfl
  | @cons x y z e p ih =>
      simp only [Walk.restrictGraphOnSupport, Walk.lift]
      congr
      apply ih
      intro u v huv hu hv
      apply h huv
      · simp only [Walk.support_cons, List.mem_cons]
        exact Or.inr hu
      · simp only [Walk.support_cons, List.mem_cons]
        exact Or.inr hv

/-- Lifting a walk along two inclusions is the same as lifting along their
composite. -/
theorem lift_lift {D E F : Digraph V} {a b : V} (p : Walk D a b)
    (hDE : ∀ {x y}, D.Adj x y → E.Adj x y)
    (hEF : ∀ {x y}, E.Adj x y → F.Adj x y)
    (hDF : ∀ {x y}, D.Adj x y → F.Adj x y) :
    (p.lift hDE).lift hEF = p.lift hDF := by
  induction p with
  | nil => rfl
  | cons e p ih =>
      simp only [Walk.lift]
      congr

end Walk

namespace FinitePath

/-- Restricting a finite path and lifting back leaves it unchanged. -/
theorem lift_restrictGraphOnSupport {D E : Digraph V}
    (p : FinitePath D)
    (h : ∀ {x y : V}, D.Adj x y → x ∈ p.support → y ∈ p.support →
      E.Adj x y)
    (hED : ∀ {x y : V}, E.Adj x y → D.Adj x y) :
    (p.restrictGraphOnSupport h).lift hED = p := by
  cases p with
  | mk start finish walk isPath =>
      rw [FinitePath.mk.injEq]
      exact ⟨rfl, rfl, heq_of_eq
        (SafeLinkGroundFinal.DirectedPath.Walk.lift_restrictGraphOnSupport
          walk (fun e hx hy ↦ h e hx hy) hED)⟩

end FinitePath

namespace Path

/-- Lifting both paths along a graph inclusion preserves forward extension. -/
theorem extends_lift {D E : Digraph V}
    (hDE : ∀ {x y}, D.Adj x y → E.Adj x y) {p q : Path D}
    (hpq : DirectedPath.Path.Extends p q) :
    DirectedPath.Path.Extends (p.lift hDE) (q.lift hDE) := by
  rcases p with p | p <;> rcases q with q | q
  · change p.walk.support <+: q.walk.support at hpq
    change (p.walk.lift hDE).support <+: (q.walk.lift hDE).support
    simpa only [Walk.support_lift] using hpq
  · change ∀ n (hn : n < p.walk.support.length),
      p.walk.support[n] = q n at hpq
    change ∀ n (hn : n < (p.walk.lift hDE).support.length),
      (p.walk.lift hDE).support[n] = (q.lift hDE) n
    simpa only [Walk.support_lift, Ray.lift] using hpq
  · exact False.elim hpq
  · change p.lift hDE = q.lift hDE
    exact congrArg (Ray.lift hDE) hpq

/-- Restricting a path and lifting it back leaves it unchanged. -/
theorem lift_restrictGraphOnSupport {D E : Digraph V} (p : Path D)
    (h : ∀ {x y : V}, D.Adj x y → x ∈ p.support → y ∈ p.support →
      E.Adj x y)
    (hED : ∀ {x y : V}, E.Adj x y → D.Adj x y) :
    (p.restrictGraphOnSupport h).lift hED = p := by
  rcases p with p | r
  · exact congrArg Sum.inl
      (SafeLinkGroundFinal.DirectedPath.FinitePath.lift_restrictGraphOnSupport
        p h hED)
  · apply congrArg Sum.inr
    apply Ray.ext
    rfl

/-- Lifting a path along two inclusions is the same as lifting along their
composite. -/
theorem lift_lift {D E F : Digraph V} (p : Path D)
    (hDE : ∀ {x y}, D.Adj x y → E.Adj x y)
    (hEF : ∀ {x y}, E.Adj x y → F.Adj x y)
    (hDF : ∀ {x y}, D.Adj x y → F.Adj x y) :
    (p.lift hDE).lift hEF = p.lift hDF := by
  rcases p with p | r
  · apply congrArg Sum.inl
    cases p with
    | mk start finish walk isPath =>
      rw [FinitePath.mk.injEq]
      exact ⟨rfl, rfl, heq_of_eq
        (SafeLinkGroundFinal.DirectedPath.Walk.lift_lift
          walk hDE hEF hDF)⟩
  · apply congrArg Sum.inr
    apply Ray.ext
    rfl

/-- Casting a path along a graph equality before lifting has the same
underlying path as lifting directly. -/
theorem lift_cast {D E F : Digraph V} (h : D = E) (p : Path D)
    (hEF : ∀ {x y}, E.Adj x y → F.Adj x y)
    (hDF : ∀ {x y}, D.Adj x y → F.Adj x y) :
    (cast (congrArg Path h) p).lift hEF = p.lift hDF := by
  subst E
  rfl

/-- Restricting both sides of a forward-extension relation to the same
graph preserves the relation. -/
theorem extends_restrictGraphOnSupport {D E : Digraph V} {p q : Path D}
    (hpq : Path.Extends p q)
    (hp : ∀ {x y : V}, D.Adj x y → x ∈ p.support → y ∈ p.support →
      E.Adj x y)
    (hq : ∀ {x y : V}, D.Adj x y → x ∈ q.support → y ∈ q.support →
      E.Adj x y) :
    Path.Extends (p.restrictGraphOnSupport hp)
      (q.restrictGraphOnSupport hq) := by
  rcases p with p | p <;> rcases q with q | q
  · change p.walk.support <+: q.walk.support at hpq
    change (p.walk.restrictGraphOnSupport _).support <+:
      (q.walk.restrictGraphOnSupport _).support
    simpa only [Walk.support_restrictGraphOnSupport] using hpq
  · change ∀ n (hn : n < p.walk.support.length), p.walk.support[n] = q n
      at hpq
    change ∀ n (hn : n < (p.walk.restrictGraphOnSupport _).support.length),
      (p.walk.restrictGraphOnSupport _).support[n] =
        (q.restrictGraphOnSupport _) n
    simpa only [Walk.support_restrictGraphOnSupport,
      Ray.restrictGraphOnSupport] using hpq
  · exact False.elim hpq
  · change p.restrictGraphOnSupport hp = q.restrictGraphOnSupport hq
    subst q
    apply Ray.ext
    rfl

end Path
end DirectedPath

namespace DWeb

variable (G : DWeb V)

/-- Restricting an avoiding path and immediately forgetting the restriction
recovers the original path. -/
@[simp]
theorem liftDeletePath_restrictDeletePath (X : Set V) (p : G.DPath)
    (hretain : p.support ⊆ Xᶜ) :
    G.liftDeletePath X (G.restrictDeletePath X p hretain) = p := by
  unfold DWeb.liftDeletePath DWeb.restrictDeletePath
  exact @SafeLinkGroundFinal.DirectedPath.Path.lift_restrictGraphOnSupport
    V G.graph (G.delete X).graph p
    (fun e hx hy ↦ ⟨e, hretain hx, hretain hy⟩)
    (fun e ↦ G.delete_adj_imp e)

/-- The family version of `liftDeletePath_restrictDeletePath`. -/
@[simp]
theorem liftDeleteFamily_restrictDeleteFamily (X : Set V)
    (W : Set G.DPath) (havoid : Disjoint (G.vertexSet W) X) :
    G.liftDeleteFamily X (G.restrictDeleteFamily X W havoid) = W := by
  ext p
  constructor
  · rintro ⟨q, ⟨w, _hw, rfl⟩, rfl⟩
    change G.liftDeletePath X (G.restrictDeletePath X w.1 _) ∈ W
    rw [liftDeletePath_restrictDeletePath G X w.1 _]
    exact w.2
  · intro hp
    let w : W := ⟨p, hp⟩
    refine ⟨G.restrictDeleteMember X W havoid w,
      ⟨w, Set.mem_univ w, rfl⟩, ?_⟩
    change G.liftDeletePath X (G.restrictDeletePath X p _) = p
    rw [liftDeletePath_restrictDeletePath G X p _]

/-- Lifting two families along the same deletion preserves their
forward-extension relation. -/
theorem forwardExtension_liftDeleteFamily (X : Set V)
    {U W : Set (G.delete X).DPath}
    (hUW : (G.delete X).ForwardExtension U W) :
    G.ForwardExtension (G.liftDeleteFamily X U)
      (G.liftDeleteFamily X W) := by
  constructor
  · rintro _ ⟨p, hp, rfl⟩
    obtain ⟨q, hq, hpq⟩ := hUW.1 p hp
    exact ⟨G.liftDeletePath X q, ⟨q, hq, rfl⟩,
      DirectedPath.Path.extends_lift _ hpq⟩
  · rintro _ ⟨q, hq, rfl⟩
    obtain ⟨p, hp, hpq⟩ := hUW.2 q hq
    exact ⟨G.liftDeletePath X p, ⟨p, hp, rfl⟩,
      DirectedPath.Path.extends_lift _ hpq⟩

/-- Restricting two avoiding families to the same deletion preserves
forward extension. -/
theorem forwardExtension_restrictDeleteFamily (X : Set V)
    {U W : Set G.DPath}
    (hUavoid : Disjoint (G.vertexSet U) X)
    (hWavoid : Disjoint (G.vertexSet W) X)
    (hUW : G.ForwardExtension U W) :
    (G.delete X).ForwardExtension
      (G.restrictDeleteFamily X U hUavoid)
      (G.restrictDeleteFamily X W hWavoid) := by
  constructor
  · rintro _ ⟨p, _hp, rfl⟩
    obtain ⟨q, hqW, hpq⟩ := hUW.1 p.1 p.2
    let qW : W := ⟨q, hqW⟩
    refine ⟨G.restrictDeleteMember X W hWavoid qW,
      ⟨qW, Set.mem_univ qW, rfl⟩, ?_⟩
    exact @SafeLinkGroundFinal.DirectedPath.Path.extends_restrictGraphOnSupport
      V G.graph (G.delete X).graph p.1 q hpq
      (fun e hu hv ↦ ⟨e,
        fun hx ↦ Set.disjoint_left.1 hUavoid ⟨p.1, p.2, hu⟩ hx,
        fun hx ↦ Set.disjoint_left.1 hUavoid ⟨p.1, p.2, hv⟩ hx⟩)
      (fun e hu hv ↦ ⟨e,
        fun hx ↦ Set.disjoint_left.1 hWavoid ⟨q, hqW, hu⟩ hx,
        fun hx ↦ Set.disjoint_left.1 hWavoid ⟨q, hqW, hv⟩ hx⟩)
  · rintro _ ⟨q, _hq, rfl⟩
    obtain ⟨p, hpU, hpq⟩ := hUW.2 q.1 q.2
    let pU : U := ⟨p, hpU⟩
    refine ⟨G.restrictDeleteMember X U hUavoid pU,
      ⟨pU, Set.mem_univ pU, rfl⟩, ?_⟩
    exact @SafeLinkGroundFinal.DirectedPath.Path.extends_restrictGraphOnSupport
      V G.graph (G.delete X).graph p q.1 hpq
      (fun e hu hv ↦ ⟨e,
        fun hx ↦ Set.disjoint_left.1 hUavoid ⟨p, hpU, hu⟩ hx,
        fun hx ↦ Set.disjoint_left.1 hUavoid ⟨p, hpU, hv⟩ hx⟩)
      (fun e hu hv ↦ ⟨e,
        fun hx ↦ Set.disjoint_left.1 hWavoid ⟨q.1, q.2, hu⟩ hx,
        fun hx ↦ Set.disjoint_left.1 hWavoid ⟨q.1, q.2, hv⟩ hx⟩)

/-- Forward extension can only enlarge the union of path supports. -/
theorem vertexSet_subset_of_forwardExtension {U W : Set G.DPath}
    (hUW : G.ForwardExtension U W) :
    G.vertexSet U ⊆ G.vertexSet W := by
  rintro x ⟨p, hpU, hxp⟩
  obtain ⟨q, hqW, hpq⟩ := hUW.1 p hpU
  exact ⟨q, hqW, G.support_mono_of_extends hpq hxp⟩

/-- Lifting a deletion family changes no support vertex. -/
@[simp]
theorem vertexSet_liftDeleteFamily (X : Set V)
    (W : Set (G.delete X).DPath) :
    G.vertexSet (G.liftDeleteFamily X W) = (G.delete X).vertexSet W := by
  ext x
  constructor
  · rintro ⟨p, ⟨q, hqW, rfl⟩, hxp⟩
    exact ⟨q, hqW, by simpa using hxp⟩
  · rintro ⟨q, hqW, hxq⟩
    exact ⟨G.liftDeletePath X q, ⟨q, hqW, rfl⟩, by simpa using hxq⟩

/-- Restricting an avoiding family changes no support vertex. -/
@[simp]
theorem vertexSet_restrictDeleteFamily (X : Set V) (W : Set G.DPath)
    (havoid : Disjoint (G.vertexSet W) X) :
    (G.delete X).vertexSet (G.restrictDeleteFamily X W havoid) =
      G.vertexSet W := by
  ext x
  constructor
  · rintro ⟨q, ⟨p, _hp, rfl⟩, hxq⟩
    exact ⟨p.1, p.2, by simpa using hxq⟩
  · rintro ⟨p, hpW, hxp⟩
    let pW : W := ⟨p, hpW⟩
    exact ⟨G.restrictDeleteMember X W havoid pW,
      ⟨pW, Set.mem_univ pW, rfl⟩, by simpa using hxp⟩

/-- Transporting a path along an equality of webs is the same dependent
cast as transporting along the induced equality of path types. -/
theorem castWebPath_eq_castPath {H K : DWeb V} (h : H = K)
    (p : H.DPath) :
    h ▸ p = cast (congrArg (fun L : DWeb V ↦ L.DPath) h) p := by
  subst K
  rfl

/-- Membership in a path family is invariant under transport along a web
equality. -/
theorem mem_castWebFamily {H K : DWeb V} (h : H = K)
    (W : Set H.DPath) (p : H.DPath) :
    (h ▸ p) ∈ (h ▸ W) ↔ p ∈ W := by
  subst K
  rfl

/-- A member of a transported family has an untransported preimage. -/
theorem exists_preimage_castWebFamily {H K : DWeb V} (h : H = K)
    (W : Set H.DPath) {p : K.DPath} (hp : p ∈ h ▸ W) :
    ∃ q ∈ W, p = h ▸ q := by
  subst K
  exact ⟨p, hp, rfl⟩

/-- The family underlying a transported wave is the transported underlying
family. -/
theorem val_castWebWave {H K : DWeb V} (h : H = K) (W : H.Wave) :
    (h ▸ W).1 = h ▸ W.1 := by
  subst K
  rfl

/-- Lifting through two successive deletions, including the web cast which
identifies the iterated deletion with deletion of the union, is the same as
lifting successively. -/
theorem liftDeletePath_cast_delete_singleton (R : Set V) (x : V)
    (h : (G.delete R).delete {x} = G.delete (insert x R))
    (p : ((G.delete R).delete {x}).DPath) :
    G.liftDeletePath (insert x R) (h ▸ p) =
      G.liftDeletePath R ((G.delete R).liftDeletePath {x} p) := by
  unfold DWeb.liftDeletePath
  rw [castWebPath_eq_castPath h p]
  let hDF : ∀ {u v}, ((G.delete R).delete {x}).graph.Adj u v →
      G.graph.Adj u v := fun e ↦ e.1.1
  let hDE : ∀ {u v}, ((G.delete R).delete {x}).graph.Adj u v →
      (G.delete R).graph.Adj u v := fun e ↦ e.1
  let hEF : ∀ {u v}, (G.delete R).graph.Adj u v → G.graph.Adj u v :=
    fun e ↦ e.1
  calc
    _ = p.lift hDF := @SafeLinkGroundFinal.DirectedPath.Path.lift_cast V
      ((G.delete R).delete {x}).graph (G.delete (insert x R)).graph G.graph
      (congrArg DWeb.graph h) p (fun e ↦ e.1) hDF
    _ = (p.lift hDE).lift hEF :=
      (SafeLinkGroundFinal.DirectedPath.Path.lift_lift
        p hDE hEF hDF).symm

/-- The direct ambient lift of the restricted family used in one ground
step is exactly the old ambient family. -/
theorem liftDeleteFamily_cast_restrict_singleton (R : Set V) (x : V)
    (W : Set (G.delete R).DPath)
    (hAvoid : Disjoint ((G.delete R).vertexSet W) {x}) :
    G.liftDeleteFamily (insert x R)
      ((G.delete_delete_singleton R x) ▸
        ((G.delete R).restrictDeleteFamily {x} W hAvoid)) =
      G.liftDeleteFamily R W := by
  let h := G.delete_delete_singleton R x
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨q₀, hq₀, rfl⟩ := exists_preimage_castWebFamily h _ hq
    obtain ⟨w, _hw, rfl⟩ := hq₀
    change G.liftDeletePath (insert x R)
      (h ▸ ((G.delete R).restrictDeleteMember {x} W hAvoid w)) ∈ _
    rw [liftDeletePath_cast_delete_singleton G R x h]
    change G.liftDeletePath R
      ((G.delete R).liftDeletePath {x}
        ((G.delete R).restrictDeletePath {x} w.1 _)) ∈ _
    rw [liftDeletePath_restrictDeletePath (G.delete R) {x} w.1]
    exact ⟨w.1, w.2, rfl⟩
  · rintro ⟨p₀, hp₀, rfl⟩
    let w : W := ⟨p₀, hp₀⟩
    let q₀ := (G.delete R).restrictDeleteMember {x} W hAvoid w
    let q : (G.delete (insert x R)).DPath := h ▸ q₀
    refine ⟨q, ?_, ?_⟩
    · apply (mem_castWebFamily h _ q₀).2
      exact ⟨w, Set.mem_univ w, rfl⟩
    · dsimp only [q]
      rw [liftDeletePath_cast_delete_singleton G R x h]
      change G.liftDeletePath R
        ((G.delete R).liftDeletePath {x}
          ((G.delete R).restrictDeletePath {x} p₀ _)) = _
      rw [liftDeletePath_restrictDeletePath (G.delete R) {x} p₀]

/-- Regard a finite ground state as a path family in the fixed web with
only the distinguished root deleted. -/
def GroundState.ambientFamily {a : V} {X : Set V}
    (s : SafeLinkGround.DWeb.GroundState G a X) :
    Set (G.delete {a}).DPath :=
  (G.delete {a}).liftDeleteFamily s.removed s.wave.1

/-- Adding one point and maximizing in the enlarged deletion forward-
extends the old family after both families are lifted to the fixed
root-deleted web. -/
theorem GroundState.ambientFamily_forward_add
    {a : V} {X : Set V}
    (s : SafeLinkGround.DWeb.GroundState G a X)
    (x : V) (hxX : x ∈ X)
    (hxWave : x ∉ ((G.delete {a}).delete s.removed).vertexSet s.wave.1) :
    (G.delete {a}).ForwardExtension (GroundState.ambientFamily G s)
      (GroundState.ambientFamily G (s.add x hxX hxWave)) := by
  classical
  let H := (G.delete {a}).delete s.removed
  have hAvoid : Disjoint (H.vertexSet s.wave.1) ({x} : Set V) := by
    rw [Set.disjoint_singleton_right]
    exact hxWave
  let restricted : (H.delete {x}).Wave :=
    ⟨H.restrictDeleteFamily {x} s.wave.1 hAvoid,
      DWeb.IsWave.restrictDeleteFamily H s.wave.2 hAvoid⟩
  have heq : H.delete {x} =
      (G.delete {a}).delete (insert x s.removed) := by
    simpa only [H] using
      (G.delete {a}).delete_delete_singleton s.removed x
  let restricted' : ((G.delete {a}).delete (insert x s.removed)).Wave :=
    heq ▸ restricted
  let target := (G.delete {a}).delete (insert x s.removed)
  let M : target.Wave := Classical.choose
    (target.exists_maximal_wave_extending restricted')
  have hMspec : restricted' ≤ M ∧ IsMax M :=
    Classical.choose_spec (target.exists_maximal_wave_extending restricted')
  have hforward := forwardExtension_liftDeleteFamily (G.delete {a})
    (insert x s.removed) hMspec.1
  have hrestricted :
      (G.delete {a}).liftDeleteFamily (insert x s.removed) restricted'.1 =
        GroundState.ambientFamily G s := by
    rw [show restricted'.1 = heq ▸ restricted.1 by
      exact val_castWebWave heq restricted]
    exact liftDeleteFamily_cast_restrict_singleton (G.delete {a})
      s.removed x s.wave.1 hAvoid
  rw [hrestricted] at hforward
  change (G.delete {a}).ForwardExtension (GroundState.ambientFamily G s)
    ((G.delete {a}).liftDeleteFamily (insert x s.removed) M.1)
  exact hforward

/-- One recursion step forward-extends the family after both stages are
viewed in the fixed root-deleted web. -/
theorem GroundState.ambientFamily_forward_next
    {a : V} {X : Set V}
    (s : SafeLinkGround.DWeb.GroundState G a X) (x : V) :
    (G.delete {a}).ForwardExtension (GroundState.ambientFamily G s)
      (GroundState.ambientFamily G (s.next x)) := by
  classical
  unfold SafeLinkGround.DWeb.GroundState.next
  split
  · rename_i h
    exact GroundState.ambientFamily_forward_add G s x h.1 h.2.2
  · exact (G.delete {a}).forwardExtension_refl
      (GroundState.ambientFamily G s)

/-! ## Passage to the common final deletion -/

/-- Restricting the lift of a wave from a smaller deletion to a larger
deletion again gives a wave. -/
theorem IsWave.restrict_liftDeleteFamily_of_subset
    {S R : Set V} {W : Set (G.delete S).DPath}
    (hW : (G.delete S).IsWave W) (hSR : S ⊆ R)
    (havoid : Disjoint (G.vertexSet (G.liftDeleteFamily S W)) R) :
    (G.delete R).IsWave
      (G.restrictDeleteFamily R (G.liftDeleteFamily S W) havoid) := by
  let L := G.liftDeleteFamily S W
  refine ⟨DWeb.IsWarp.restrictDeleteFamily G hW.1.liftDeleteFamily havoid,
    ?_, ?_⟩
  · rw [G.initialSet_restrictDeleteFamily,
      G.initialSet_liftDeleteFamily]
    intro x hx
    refine ⟨hW.2.1 hx |>.1, ?_⟩
    obtain ⟨p, hpW, rfl⟩ := hx
    intro hxR
    apply Set.disjoint_left.1 havoid
      ⟨G.liftDeletePath S p, ⟨p, hpW, rfl⟩,
        DirectedPath.Path.initial_mem_support _⟩
    simpa using hxR
  · intro x hx p hp
    let q : DirectedPath.FinitePath (G.delete S).graph :=
      @DirectedPath.FinitePath.lift V (G.delete R).graph
        (G.delete S).graph (fun {_ _} e ↦
          ⟨e.1, fun huS ↦ e.2.1 (hSR huS),
            fun hvS ↦ e.2.2 (hSR hvS)⟩) p
    have hq : (G.delete S).IsTargetPathFrom x q := by
      exact ⟨hp.1, ⟨hp.2.1, fun hzS ↦ hp.2.2 (hSR hzS)⟩⟩
    have hxS : x ∈ (G.delete S).source :=
      ⟨hx.1, fun hxS ↦ hx.2 (hSR hxS)⟩
    obtain ⟨z, hzp, hzTerm⟩ := hW.2.2 hxS q hq
    refine ⟨z, ?_, ?_⟩
    · have hsupp : q.support = p.support := by
        dsimp only [q]
        exact _root_.Erdos599.DirectedPath.FinitePath.support_lift _ p
      rw [hsupp] at hzp
      exact hzp
    · rw [G.terminalFrontier_restrictDeleteFamily,
        G.terminalFrontier_liftDeleteFamily]
      exact hzTerm

/-- The set of all points deleted during the ground recursion. -/
def groundRemoved (a : V) (X : Set V) (e : ℕ → V) : Set V :=
  ⋃ n, (SafeLinkGround.DWeb.groundState G a X e n).removed

theorem groundState_removed_subset_groundRemoved
    {a : V} (X : Set V) (e : ℕ → V) (n : ℕ) :
    (SafeLinkGround.DWeb.groundState G a X e n).removed ⊆
      groundRemoved G a X e := by
  intro x hx
  exact Set.mem_iUnion_of_mem n hx

theorem groundRemoved_subset {a : V} (X : Set V) (e : ℕ → V) :
    groundRemoved G a X e ⊆ X := by
  intro x hx
  obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hx
  exact (SafeLinkGround.DWeb.groundState G a X e n).removed_subset hxn

theorem groundRemoved_countable {a : V} (X : Set V) (e : ℕ → V) :
    (groundRemoved G a X e).Countable := by
  exact Set.countable_iUnion fun n ↦
    (SafeLinkGround.DWeb.groundState G a X e n).removed_finite.countable

/-- Ambient stage families are monotone in the forward-extension order. -/
theorem groundState_ambientFamily_forward {a : V} (X : Set V)
    (e : ℕ → V) {n m : ℕ} (hnm : n ≤ m) :
    (G.delete {a}).ForwardExtension
      (GroundState.ambientFamily G
        (SafeLinkGround.DWeb.groundState G a X e n))
      (GroundState.ambientFamily G
        (SafeLinkGround.DWeb.groundState G a X e m)) := by
  induction m, hnm using Nat.le_induction with
  | base => exact (G.delete {a}).forwardExtension_refl _
  | succ m hnm ih =>
      apply (G.delete {a}).forwardExtension_trans ih
      rw [SafeLinkGround.DWeb.groundState_succ]
      exact GroundState.ambientFamily_forward_next G _ _

/-- Every ambient stage family avoids the union of all deleted points. -/
theorem groundState_ambientFamily_disjoint_groundRemoved
    {a : V} (X : Set V) (e : ℕ → V) (n : ℕ) :
    Disjoint ((G.delete {a}).vertexSet
      (GroundState.ambientFamily G
        (SafeLinkGround.DWeb.groundState G a X e n)))
      (groundRemoved G a X e) := by
  rw [Set.disjoint_left]
  intro x hxFamily hxR
  obtain ⟨m, hxm⟩ := Set.mem_iUnion.mp hxR
  rcases le_total m n with hmn | hnm
  · have hxm' : x ∈
        (SafeLinkGround.DWeb.groundState G a X e n).removed :=
      SafeLinkGround.DWeb.groundState_removed_monotone G a X e hmn hxm
    exact Set.disjoint_left.1
      ((G.delete {a}).vertexSet_liftDeleteFamily_disjoint
        (SafeLinkGround.DWeb.groundState G a X e n).wave.2.2.1)
      hxFamily hxm'
  · have hxLater : x ∈ (G.delete {a}).vertexSet
        (GroundState.ambientFamily G
          (SafeLinkGround.DWeb.groundState G a X e m)) :=
      vertexSet_subset_of_forwardExtension (G.delete {a})
        (groundState_ambientFamily_forward G X e hnm) hxFamily
    exact Set.disjoint_left.1
      ((G.delete {a}).vertexSet_liftDeleteFamily_disjoint
        (SafeLinkGround.DWeb.groundState G a X e m).wave.2.2.1)
      hxLater hxm

/-- The `n`th wave, transported to the common final deletion. -/
noncomputable def groundStageWave (a : V) (X : Set V) (e : ℕ → V)
    (n : ℕ) : ((G.delete {a}).delete (groundRemoved G a X e)).Wave := by
  let s := SafeLinkGround.DWeb.groundState G a X e n
  let H := G.delete {a}
  let A := GroundState.ambientFamily G s
  have havoid : Disjoint (H.vertexSet A) (groundRemoved G a X e) :=
    groundState_ambientFamily_disjoint_groundRemoved G X e n
  refine ⟨H.restrictDeleteFamily (groundRemoved G a X e) A havoid, ?_⟩
  exact IsWave.restrict_liftDeleteFamily_of_subset H s.wave.2
    (groundState_removed_subset_groundRemoved G X e n) havoid

@[simp]
theorem groundStageWave_val (a : V) (X : Set V) (e : ℕ → V)
    (n : ℕ) :
    (groundStageWave G a X e n).1 =
      let s := SafeLinkGround.DWeb.groundState G a X e n
      let H := G.delete {a}
      let A := GroundState.ambientFamily G s
      H.restrictDeleteFamily (groundRemoved G a X e) A
        (groundState_ambientFamily_disjoint_groundRemoved G X e n) :=
  rfl

/-- The common-deletion stage waves inherit the ambient forward-extension
chain. -/
theorem groundStageWave_forward {a : V} (X : Set V) (e : ℕ → V)
    {n m : ℕ} (hnm : n ≤ m) :
    ((G.delete {a}).delete (groundRemoved G a X e)).ForwardExtension
      (groundStageWave G a X e n).1 (groundStageWave G a X e m).1 := by
  let H := G.delete {a}
  let sn := SafeLinkGround.DWeb.groundState G a X e n
  let sm := SafeLinkGround.DWeb.groundState G a X e m
  let An := GroundState.ambientFamily G sn
  let Am := GroundState.ambientFamily G sm
  have hnAvoid : Disjoint (H.vertexSet An) (groundRemoved G a X e) :=
    groundState_ambientFamily_disjoint_groundRemoved G X e n
  have hmAvoid : Disjoint (H.vertexSet Am) (groundRemoved G a X e) :=
    groundState_ambientFamily_disjoint_groundRemoved G X e m
  have hforward : H.ForwardExtension An Am :=
    groundState_ambientFamily_forward G X e hnm
  change (H.delete (groundRemoved G a X e)).ForwardExtension
    (H.restrictDeleteFamily (groundRemoved G a X e) An hnAvoid)
    (H.restrictDeleteFamily (groundRemoved G a X e) Am hmAvoid)
  exact forwardExtension_restrictDeleteFamily H _ hnAvoid hmAvoid hforward

theorem groundStageWave_range_isChain {a : V} (X : Set V) (e : ℕ → V) :
    IsChain (· ≤ ·) (Set.range (groundStageWave G a X e)) := by
  rintro U ⟨n, rfl⟩ W ⟨m, rfl⟩ _hne
  rcases le_total n m with hnm | hmn
  · exact Or.inl (groundStageWave_forward G X e hnm)
  · exact Or.inr (groundStageWave_forward G X e hmn)

theorem groundStageWave_range_nonempty {a : V} (X : Set V)
    (e : ℕ → V) :
    (Set.range (groundStageWave G a X e)).Nonempty :=
  ⟨groundStageWave G a X e 0, ⟨0, rfl⟩⟩

/-- The final ground wave is the direct limit of the common-deletion stage
chain. -/
noncomputable def groundWave (a : V) (X : Set V) (e : ℕ → V) :
    ((G.delete {a}).delete (groundRemoved G a X e)).Wave :=
  let H := (G.delete {a}).delete (groundRemoved G a X e)
  H.waveChainUpperWave (Set.range (groundStageWave G a X e))
    (groundStageWave_range_nonempty G X e)
    (groundStageWave_range_isChain G X e)

/-- Every stage forward-extends to the final ground wave. -/
theorem groundStageWave_forward_groundWave {a : V} (X : Set V)
    (e : ℕ → V) (n : ℕ) :
    ((G.delete {a}).delete (groundRemoved G a X e)).ForwardExtension
      (groundStageWave G a X e n).1 (groundWave G a X e).1 := by
  let H := (G.delete {a}).delete (groundRemoved G a X e)
  exact H.forwardExtension_waveChainUpper
    (Set.range (groundStageWave G a X e))
    (groundStageWave_range_nonempty G X e)
    (groundStageWave_range_isChain G X e)
    (Set.mem_range_self n)

/-- A common-deletion stage has exactly the same terminal frontier as the
original finite-deletion stage. -/
theorem terminalFrontier_groundStageWave {a : V} (X : Set V)
    (e : ℕ → V) (n : ℕ) :
    ((G.delete {a}).delete (groundRemoved G a X e)).terminalFrontier
        (groundStageWave G a X e n).1 =
      ((G.delete {a}).delete
        (SafeLinkGround.DWeb.groundState G a X e n).removed).terminalFrontier
          (SafeLinkGround.DWeb.groundState G a X e n).wave.1 := by
  change ((G.delete {a}).delete (groundRemoved G a X e)).terminalFrontier
    ((G.delete {a}).restrictDeleteFamily (groundRemoved G a X e)
      (GroundState.ambientFamily G
        (SafeLinkGround.DWeb.groundState G a X e n)) _) = _
  rw [(G.delete {a}).terminalFrontier_restrictDeleteFamily,
    show GroundState.ambientFamily G
      (SafeLinkGround.DWeb.groundState G a X e n) =
        (G.delete {a}).liftDeleteFamily
          (SafeLinkGround.DWeb.groundState G a X e n).removed
          (SafeLinkGround.DWeb.groundState G a X e n).wave.1 from rfl,
    (G.delete {a}).terminalFrontier_liftDeleteFamily]

/-- A common-deletion stage has exactly the same vertex set as the
original finite-deletion stage. -/
theorem vertexSet_groundStageWave {a : V} (X : Set V)
    (e : ℕ → V) (n : ℕ) :
    ((G.delete {a}).delete (groundRemoved G a X e)).vertexSet
        (groundStageWave G a X e n).1 =
      ((G.delete {a}).delete
        (SafeLinkGround.DWeb.groundState G a X e n).removed).vertexSet
          (SafeLinkGround.DWeb.groundState G a X e n).wave.1 := by
  change ((G.delete {a}).delete (groundRemoved G a X e)).vertexSet
    ((G.delete {a}).restrictDeleteFamily (groundRemoved G a X e)
      (GroundState.ambientFamily G
        (SafeLinkGround.DWeb.groundState G a X e n)) _) = _
  rw [vertexSet_restrictDeleteFamily (G.delete {a}),
    show GroundState.ambientFamily G
      (SafeLinkGround.DWeb.groundState G a X e n) =
        (G.delete {a}).liftDeleteFamily
          (SafeLinkGround.DWeb.groundState G a X e n).removed
          (SafeLinkGround.DWeb.groundState G a X e n).wave.1 from rfl,
    vertexSet_liftDeleteFamily (G.delete {a})]

/-- Assertion 6.5 survives the direct limit. -/
theorem groundWave_terminal_disjoint_tree
    {a : V} {T X : Set V} (hT : G.IsTreeSet a T)
    (hXT : X ⊆ T \ {a}) (e : ℕ → V) :
    Disjoint T (((G.delete {a}).delete (groundRemoved G a X e)).terminalFrontier
      (groundWave G a X e).1) := by
  let H := (G.delete {a}).delete (groundRemoved G a X e)
  let c := Set.range (groundStageWave G a X e)
  have hcne : c.Nonempty := groundStageWave_range_nonempty G X e
  have hc : IsChain (· ≤ ·) c := groundStageWave_range_isChain G X e
  rw [Set.disjoint_left]
  intro x hxT hxFinal
  have hxStages : x ∈ ⋃ U : c, H.terminalFrontier U.1.1 :=
    SafeLinkGround.DWeb.terminalFrontier_waveChainUpper_subset_iUnion
      H c hcne hc (by
        simpa only [groundWave, H, DWeb.waveChainUpperWave] using hxFinal)
  simp only [Set.mem_iUnion] at hxStages
  obtain ⟨U, hxU⟩ := hxStages
  obtain ⟨n, hn⟩ := U.2
  rw [← hn] at hxU
  rw [terminalFrontier_groundStageWave G X e n] at hxU
  exact Set.disjoint_left.1
    (SafeLinkGround.DWeb.groundState_terminal_disjoint_tree
      G hT hXT e n) hxT hxU

/-- Assertion 6.6 survives the direct limit. -/
theorem groundWave_vertexSet_disjoint_nonBounded
    (hG : G.IsNormalized) {a : V} (ha : a ∈ G.source)
    {T X : Set V} (hT : G.IsTreeSet a T) (hXT : X ⊆ T \ {a})
    (e : ℕ → V) :
    Disjoint (((G.delete {a}).delete (groundRemoved G a X e)).vertexSet
      (groundWave G a X e).1)
      (SafeLink.nonBoundedTreeVertices G a T) := by
  let H := (G.delete {a}).delete (groundRemoved G a X e)
  let c := Set.range (groundStageWave G a X e)
  have hcne : c.Nonempty := groundStageWave_range_nonempty G X e
  have hc : IsChain (· ≤ ·) c := groundStageWave_range_isChain G X e
  rw [Set.disjoint_left]
  intro x hxFinal hxQ
  have hxStages : x ∈ ⋃ U : c, H.vertexSet U.1.1 :=
    H.vertexSet_waveChainUpper_subset_iUnion c hcne hc (by
      simpa only [groundWave, H, DWeb.waveChainUpperWave] using hxFinal)
  simp only [Set.mem_iUnion] at hxStages
  obtain ⟨U, hxU⟩ := hxStages
  obtain ⟨n, hn⟩ := U.2
  rw [← hn] at hxU
  rw [vertexSet_groundStageWave G X e n] at hxU
  exact Set.disjoint_left.1
    (SafeLinkGround.DWeb.groundState_vertexSet_disjoint_nonBounded
      G hG ha hT hXT e n) hxU hxQ

/-- The one-pass enumeration is fair because vertices already on a stage
wave persist along the ambient forward-extension chain. -/
theorem groundCovered
    {a : V} {X : Set V} {e : ℕ → V} (henum : X ⊆ Set.range e) :
    X ⊆ groundRemoved G a X e ∪
      ((G.delete {a}).delete (groundRemoved G a X e)).vertexSet
        (groundWave G a X e).1 := by
  intro x hxX
  obtain ⟨n, hxn | hxn⟩ :=
    SafeLinkGround.DWeb.eventually_removed_or_mem_stageWave
      G a henum hxX
  · exact Or.inl (groundState_removed_subset_groundRemoved G X e n hxn)
  · apply Or.inr
    have hxStage : x ∈ ((G.delete {a}).delete
        (groundRemoved G a X e)).vertexSet (groundStageWave G a X e n).1 := by
      rw [vertexSet_groundStageWave G X e n]
      exact hxn
    exact vertexSet_subset_of_forwardExtension
      ((G.delete {a}).delete (groundRemoved G a X e))
      (groundStageWave_forward_groundWave G X e n) hxStage

/-- The alternative “already deleted or currently on the wave” persists
to every later finite stage. -/
theorem groundState_removed_or_mem_stageWave_mono
    {a : V} (X : Set V) (e : ℕ → V) {n m : ℕ} (hnm : n ≤ m)
    {x : V}
    (hx : x ∈ (SafeLinkGround.DWeb.groundState G a X e n).removed ∨
      x ∈ ((G.delete {a}).delete
        (SafeLinkGround.DWeb.groundState G a X e n).removed).vertexSet
          (SafeLinkGround.DWeb.groundState G a X e n).wave.1) :
    x ∈ (SafeLinkGround.DWeb.groundState G a X e m).removed ∨
      x ∈ ((G.delete {a}).delete
        (SafeLinkGround.DWeb.groundState G a X e m).removed).vertexSet
          (SafeLinkGround.DWeb.groundState G a X e m).wave.1 := by
  rcases hx with hxR | hxW
  · exact Or.inl
      (SafeLinkGround.DWeb.groundState_removed_monotone G a X e hnm hxR)
  · apply Or.inr
    have hxAmbientN : x ∈ (G.delete {a}).vertexSet
        (GroundState.ambientFamily G
          (SafeLinkGround.DWeb.groundState G a X e n)) := by
      change x ∈ (G.delete {a}).vertexSet
        ((G.delete {a}).liftDeleteFamily
          (SafeLinkGround.DWeb.groundState G a X e n).removed
          (SafeLinkGround.DWeb.groundState G a X e n).wave.1)
      rw [vertexSet_liftDeleteFamily (G.delete {a})]
      exact hxW
    have hxAmbientM : x ∈ (G.delete {a}).vertexSet
        (GroundState.ambientFamily G
          (SafeLinkGround.DWeb.groundState G a X e m)) :=
      vertexSet_subset_of_forwardExtension (G.delete {a})
        (groundState_ambientFamily_forward G X e hnm) hxAmbientN
    change x ∈ (G.delete {a}).vertexSet
      ((G.delete {a}).liftDeleteFamily
        (SafeLinkGround.DWeb.groundState G a X e m).removed
        (SafeLinkGround.DWeb.groundState G a X e m).wave.1) at hxAmbientM
    rw [vertexSet_liftDeleteFamily (G.delete {a})] at hxAmbientM
    exact hxAmbientM

/-- A finite subset of the countable commitment set is simultaneously
settled at one finite stage. -/
theorem exists_stage_removed_or_mem_for_finite
    {a : V} {X : Set V} {e : ℕ → V} (henum : X ⊆ Set.range e)
    {F : Set V} (hF : F.Finite) (hFX : F ⊆ X) :
    ∃ n, ∀ x ∈ F,
      x ∈ (SafeLinkGround.DWeb.groundState G a X e n).removed ∨
        x ∈ ((G.delete {a}).delete
          (SafeLinkGround.DWeb.groundState G a X e n).removed).vertexSet
            (SafeLinkGround.DWeb.groundState G a X e n).wave.1 := by
  induction F, hF using Set.Finite.induction_on with
  | empty =>
      exact ⟨0, by simp⟩
  | @insert x F hxF hF ih =>
      have hxX : x ∈ X := hFX (Set.mem_insert x F)
      obtain ⟨nx, hxStage⟩ :=
        SafeLinkGround.DWeb.eventually_removed_or_mem_stageWave
          G a henum hxX
      have hFX' : F ⊆ X := fun z hz ↦ hFX (Set.mem_insert_of_mem x hz)
      obtain ⟨nF, hFStage⟩ := ih hFX'
      refine ⟨max nx nF, ?_⟩
      intro z hz
      rcases hz with rfl | hzF
      · exact groundState_removed_or_mem_stageWave_mono G X e
          (Nat.le_max_left nx nF) hxStage
      · exact groundState_removed_or_mem_stageWave_mono G X e
          (Nat.le_max_right nx nF) (hFStage z hzF)

/-- Finite capture in the form used by Assertion 6.8: every undeleted
point of `F` lies on the selected finite-stage wave. -/
theorem exists_stage_finite_capture
    {a : V} {X : Set V} {e : ℕ → V} (henum : X ⊆ Set.range e)
    {F : Set V} (hF : F.Finite) (hFX : F ⊆ X) :
    ∃ n, F \ (SafeLinkGround.DWeb.groundState G a X e n).removed ⊆
      ((G.delete {a}).delete
        (SafeLinkGround.DWeb.groundState G a X e n).removed).vertexSet
          (SafeLinkGround.DWeb.groundState G a X e n).wave.1 := by
  obtain ⟨n, hn⟩ :=
    exists_stage_removed_or_mem_for_finite G henum hF hFX
  refine ⟨n, ?_⟩
  intro x hx
  rcases hn x hx.1 with hxR | hxW
  · exact (hx.2 hxR).elim
  · exact hxW

/-- Restoring the additional future deletions only enlarges the roof of a
finite-stage terminal frontier. -/
theorem groundState_roof_subset_groundStageWave_roof
    {a : V} (X : Set V) (e : ℕ → V) (n : ℕ) :
    ((G.delete {a}).delete
      (SafeLinkGround.DWeb.groundState G a X e n).removed).roof
        (((G.delete {a}).delete
          (SafeLinkGround.DWeb.groundState G a X e n).removed).terminalFrontier
            (SafeLinkGround.DWeb.groundState G a X e n).wave.1) ⊆
      ((G.delete {a}).delete (groundRemoved G a X e)).roof
        (((G.delete {a}).delete (groundRemoved G a X e)).terminalFrontier
          (groundStageWave G a X e n).1) := by
  let H := G.delete {a}
  let S := (SafeLinkGround.DWeb.groundState G a X e n).removed
  let R := groundRemoved G a X e
  have hSR : S ⊆ R := groundState_removed_subset_groundRemoved G X e n
  have heq : (H.delete S).delete (R \ S) = H.delete R := by
    rw [H.delete_delete]
    congr 1
    calc
      S ∪ R \ S = S ∪ R := Set.union_diff_self
      _ = R := Set.union_eq_right.mpr hSR
  intro x hx
  have hx' := DWeb.roof_subset_delete_roof (H.delete S)
    ((H.delete S).terminalFrontier
      (SafeLinkGround.DWeb.groundState G a X e n).wave.1)
    (R \ S) hx
  rw [heq] at hx'
  rw [terminalFrontier_groundStageWave G X e n]
  exact hx'

/-- Every roof obtained at a finite ground stage persists to the final
ground wave. -/
theorem groundState_roof_subset_groundWave_roof
    {a : V} (X : Set V) (e : ℕ → V) (n : ℕ) :
    ((G.delete {a}).delete
      (SafeLinkGround.DWeb.groundState G a X e n).removed).roof
        (((G.delete {a}).delete
          (SafeLinkGround.DWeb.groundState G a X e n).removed).terminalFrontier
            (SafeLinkGround.DWeb.groundState G a X e n).wave.1) ⊆
      ((G.delete {a}).delete (groundRemoved G a X e)).roof
        (((G.delete {a}).delete (groundRemoved G a X e)).terminalFrontier
          (groundWave G a X e).1) := by
  exact (groundState_roof_subset_groundStageWave_roof G X e n).trans
    (((G.delete {a}).delete (groundRemoved G a X e)).roofLE_of_forwardExtension
      (groundWave G a X e).2
      (groundStageWave_forward_groundWave G X e n))

/-- Packaged final form of the countable bring-down construction. -/
theorem exists_groundWave
    (hG : G.IsNormalized) {a : V} (ha : a ∈ G.source)
    {T X : Set V} (hT : G.IsTreeSet a T) (hXcount : X.Countable)
    (hXT : X ⊆ T \ {a}) :
    ∃ (e : ℕ → V) (R : Set V)
      (ground : ((G.delete {a}).delete R).Wave),
      R.Countable ∧ R ⊆ X ∧
        Disjoint T (((G.delete {a}).delete R).terminalFrontier ground.1) ∧
        Disjoint (((G.delete {a}).delete R).vertexSet ground.1)
          (SafeLink.nonBoundedTreeVertices G a T) ∧
        X ⊆ R ∪ ((G.delete {a}).delete R).vertexSet ground.1 := by
  let : Nonempty V := ⟨a⟩
  obtain ⟨e, henum⟩ := Set.countable_iff_exists_subset_range.mp hXcount
  refine ⟨e, groundRemoved G a X e, groundWave G a X e,
    groundRemoved_countable G X e, groundRemoved_subset G X e,
    groundWave_terminal_disjoint_tree G hT hXT e,
    groundWave_vertexSet_disjoint_nonBounded G hG ha hT hXT e,
    groundCovered G henum⟩

end DWeb

end SafeLinkGroundFinal
end Erdos599
