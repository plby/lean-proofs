/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Alternating

/-!
# Finite components of a locally functional directed relation

This file supplies the graph-theoretic component decomposition used by the
switching arguments in Section 4.  A directed relation with at most one edge
entering and leaving every vertex is, on each finite weak component, either a
finite directed path or a directed cycle.  Singleton components are retained
separately, since an edge relation alone cannot record them.
-/

namespace Erdos599
namespace Alternating
namespace RelationComponents

open Set DirectedPath

universe u

variable {V : Type u} {D : Digraph V}

/-- The symmetric relation underlying a directed edge set. -/
def WeakRel (E : Set (V × V)) (x y : V) : Prop :=
  (x, y) ∈ E ∨ (y, x) ∈ E

theorem weakRel_symm {E : Set (V × V)} {x y : V} :
    WeakRel E x y → WeakRel E y x := by
  intro h
  exact h.symm

private theorem reflTransGen_symm_of_symm
    {r : V → V → Prop} (hr : ∀ {x y}, r x y → r y x)
    {x y : V} (h : Relation.ReflTransGen r x y) :
    Relation.ReflTransGen r y x := by
  induction h with
  | refl => exact .refl
  | tail hxy hyz ih =>
      exact (Relation.ReflTransGen.single (hr hyz)).trans ih

/-- Weak connectivity is an equivalence relation. -/
def weakSetoid (E : Set (V × V)) : Setoid V where
  r x y := Relation.ReflTransGen (WeakRel E) x y
  iseqv := {
    refl := fun _ ↦ .refl
    symm := fun h ↦ reflTransGen_symm_of_symm
      (fun {_ _} hxy ↦ weakRel_symm hxy) h
    trans := fun hxy hyz ↦ hxy.trans hyz }

/-- The type of weak components of `E`. -/
abbrev Component (E : Set (V × V)) := Quotient (weakSetoid E)

/-- The weak component containing `x`. -/
def componentMk (E : Set (V × V)) (x : V) : Component E :=
  Quotient.mk (weakSetoid E) x

/-- The vertex support of a weak component. -/
def componentSupport (E : Set (V × V)) (c : Component E) : Set V :=
  {x | componentMk E x = c}

@[simp]
theorem mem_componentSupport_iff {E : Set (V × V)}
    {c : Component E} {x : V} :
    x ∈ componentSupport E c ↔ componentMk E x = c :=
  Iff.rfl

theorem componentMk_mem (E : Set (V × V)) (x : V) :
    x ∈ componentSupport E (componentMk E x) :=
  rfl

theorem componentSupport_nonempty (E : Set (V × V)) (c : Component E) :
    (componentSupport E c).Nonempty := by
  refine Quotient.inductionOn c ?_
  intro x
  change (componentSupport E (componentMk E x)).Nonempty
  exact ⟨x, componentMk_mem E x⟩

theorem componentMk_eq_of_weakRel {E : Set (V × V)} {x y : V}
    (h : WeakRel E x y) : componentMk E x = componentMk E y := by
  exact Quotient.sound (Relation.ReflTransGen.single h)

theorem mem_componentSupport_congr_weakRel {E : Set (V × V)}
    {c : Component E} {x y : V} (h : WeakRel E x y) :
    x ∈ componentSupport E c ↔ y ∈ componentSupport E c := by
  change componentMk E x = c ↔ componentMk E y = c
  rw [componentMk_eq_of_weakRel h]

theorem componentSupport_disjoint {E : Set (V × V)}
    {c d : Component E} (hcd : c ≠ d) :
    Disjoint (componentSupport E c) (componentSupport E d) := by
  rw [Set.disjoint_left]
  intro x hxc hxd
  apply hcd
  exact hxc.symm.trans hxd

/-- A finite directed path lies inside the indicated weak component and
uses only edges of `E`. -/
def IsComponentPath (E : Set (V × V)) (c : Component E)
    (p : FinitePath D) : Prop :=
  p.edgeSet ⊆ E ∧ p.support ⊆ componentSupport E c

private theorem Walk.support_length_eq_length_add_one {a b : V}
    (p : Walk D a b) : p.support.length = p.length + 1 := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem finitePath_support_length_le_ncard
    {E : Set (V × V)} {c : Component E}
    (hc : (componentSupport E c).Finite) {p : FinitePath D}
    (hp : IsComponentPath E c p) :
    p.walk.support.length ≤ hc.toFinset.card := by
  classical
  rw [← List.toFinset_card_of_nodup p.isPath]
  apply Finset.card_le_card
  intro x hx
  simp only [List.mem_toFinset] at hx
  simp only [Set.Finite.mem_toFinset]
  exact hp.2 hx

private theorem exists_longest_componentPath
    {E : Set (V × V)} (c : Component E)
    (hc : (componentSupport E c).Finite) :
    ∃ p : FinitePath D, IsComponentPath E c p ∧
      ∀ q : FinitePath D, IsComponentPath E c q →
        q.walk.support.length ≤ p.walk.support.length := by
  classical
  obtain ⟨x, hxc⟩ := componentSupport_nonempty E c
  let p₀ := FinitePath.trivial D x
  have hp₀ : IsComponentPath E c p₀ := by
    constructor
    · simp [p₀, FinitePath.edgeSet, Walk.edgeSet]
    · simpa [p₀] using hxc
  let P : ℕ → Prop := fun n ↦
    ∃ p : FinitePath D, IsComponentPath E c p ∧
      p.walk.support.length = n
  let m := Nat.findGreatest P hc.toFinset.card
  have hp₀bound := finitePath_support_length_le_ncard hc hp₀
  have hp₀P : P p₀.walk.support.length := ⟨p₀, hp₀, rfl⟩
  have hmP : P m := Nat.findGreatest_spec hp₀bound hp₀P
  obtain ⟨p, hp, hplen⟩ := hmP
  refine ⟨p, hp, ?_⟩
  intro q hq
  rw [hplen]
  exact Nat.le_findGreatest (finitePath_support_length_le_ncard hc hq)
    ⟨q, hq, rfl⟩

theorem walkExistsIncomingRC
    {a b x : V} (p : Walk D a b) (hx : x ∈ p.support) (hxa : x ≠ a) :
    ∃ y, (y, x) ∈ p.edgeSet := by
  induction p with
  | nil => exact False.elim (hxa (by simpa using hx))
  | @cons a c b e p ih =>
      simp only [Walk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact False.elim (hxa rfl)
      · by_cases hxc : x = c
        · subst x
          exact ⟨a, by simp⟩
        · obtain ⟨y, hy⟩ := ih hx hxc
          exact ⟨y, by simp [hy]⟩

theorem walkExistsOutgoingRC
    {a b x : V} (p : Walk D a b) (hx : x ∈ p.support) (hxb : x ≠ b) :
    ∃ y, (x, y) ∈ p.edgeSet := by
  induction p with
  | nil => exact False.elim (hxb (by simpa using hx))
  | @cons a c b e p ih =>
      simp only [Walk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨c, by simp⟩
      · obtain ⟨y, hy⟩ := ih hx hxb
        exact ⟨y, by simp [hy]⟩

theorem finitePathExistsIncomingRC
    (p : FinitePath D) {x : V} (hx : x ∈ p.support) (hxa : x ≠ p.start) :
    ∃ y, (y, x) ∈ p.edgeSet :=
  walkExistsIncomingRC p.walk hx hxa

theorem finitePathExistsOutgoingRC
    (p : FinitePath D) {x : V} (hx : x ∈ p.support) (hxb : x ≠ p.finish) :
    ∃ y, (x, y) ∈ p.edgeSet :=
  walkExistsOutgoingRC p.walk hx hxb

def appendFreshRC (p : FinitePath D) {y : V}
    (hpy : D.Adj p.finish y) (hy : y ∉ p.support) : FinitePath D where
  start := p.start
  finish := y
  walk := p.walk.concat hpy
  isPath := by
    rw [Walk.isPath_iff, Walk.support_concat]
    rw [List.nodup_append']
    refine ⟨p.isPath, by simp, ?_⟩
    rw [List.disjoint_left]
    intro z hz hz'
    have hzy : z = y := by simpa using hz'
    exact hy (hzy ▸ hz)

def prependFreshRC (p : FinitePath D) {y : V}
    (hyp : D.Adj y p.start) (hy : y ∉ p.support) : FinitePath D where
  start := y
  finish := p.finish
  walk := .cons hyp p.walk
  isPath := by
    rw [Walk.isPath_iff, Walk.support_cons]
    simpa using List.nodup_cons.mpr ⟨hy, p.isPath⟩

@[simp]
theorem support_appendFreshRC (p : FinitePath D) {y : V}
    (hpy : D.Adj p.finish y) (hy : y ∉ p.support) :
    (appendFreshRC p hpy hy).support = insert y p.support := by
  ext x
  simp only [appendFreshRC, FinitePath.support, Walk.support_concat,
    List.mem_append, List.mem_singleton, Set.mem_insert_iff]
  change (x ∈ p.walk.support ∨ x = y) ↔ x = y ∨ x ∈ p.walk.support
  exact or_comm

@[simp]
theorem support_prependFreshRC (p : FinitePath D) {y : V}
    (hyp : D.Adj y p.start) (hy : y ∉ p.support) :
    (prependFreshRC p hyp hy).support = insert y p.support := by
  ext x
  simp [prependFreshRC, FinitePath.support]

@[simp]
theorem walkEdgeSetAppendRC {a b c : V} (p : Walk D a b)
    (q : Walk D b c) :
    (p.append q).edgeSet = p.edgeSet ∪ q.edgeSet := by
  induction p with
  | nil => simp [Walk.edgeSet]
  | cons e p ih =>
      ext z
      simp only [Walk.append, Walk.edgeSet_cons, ih, Set.mem_union,
        Set.mem_singleton_iff]
      tauto

@[simp]
theorem walkEdgeSetConcatRC {a b c : V} (w : Walk D a b)
    (h : D.Adj b c) :
    (w.concat h).edgeSet = w.edgeSet ∪ {(b, c)} := by
  simp [Walk.concat, walkEdgeSetAppendRC, Walk.edgeSet]

@[simp]
theorem edgeSet_appendFreshRC (p : FinitePath D) {y : V}
    (hpy : D.Adj p.finish y) (hy : y ∉ p.support) :
    (appendFreshRC p hpy hy).edgeSet = p.edgeSet ∪ {(p.finish, y)} := by
  exact walkEdgeSetConcatRC p.walk hpy

@[simp]
theorem edgeSet_prependFreshRC (p : FinitePath D) {y : V}
    (hyp : D.Adj y p.start) (hy : y ∉ p.support) :
    (prependFreshRC p hyp hy).edgeSet = {(y, p.start)} ∪ p.edgeSet :=
  rfl

@[simp]
theorem support_length_appendFreshRC (p : FinitePath D)
    {y : V} (hpy : D.Adj p.finish y) (hy : y ∉ p.support) :
    (appendFreshRC p hpy hy).walk.support.length = p.walk.support.length + 1 := by
  simp [appendFreshRC]

@[simp]
theorem support_length_prependFreshRC (p : FinitePath D)
    {y : V} (hyp : D.Adj y p.start) (hy : y ∉ p.support) :
    (prependFreshRC p hyp hy).walk.support.length = p.walk.support.length + 1 := by
  simp [prependFreshRC]

/-! ## Closing a path into a directed cycle -/

theorem walkMemEdgeSetIffGetElem {a b s t : V} (w : Walk D a b) :
    (s, t) ∈ w.edgeSet ↔
      ∃ n : ℕ, ∃ hn : n + 1 < w.support.length,
        w.support[n] = s ∧ w.support[n + 1] = t := by
  induction w with
  | nil => simp [Walk.edgeSet]
  | @cons a c b h q ih =>
      constructor
      · intro he
        simp only [Walk.edgeSet_cons, Set.mem_union,
          Set.mem_singleton_iff] at he
        rcases he with he | he
        · have hac : s = a ∧ t = c := by
            exact ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩
          obtain ⟨rfl, rfl⟩ := hac
          have hqpos : 0 < q.support.length :=
            List.length_pos_iff.mpr q.support_ne_nil
          refine ⟨0, by simpa using hqpos, ?_, ?_⟩
          · rfl
          · have h0 : q.support[0] = t :=
              (List.getElem_zero hqpos).trans q.head_support
            exact h0
        · rcases ih.mp he with ⟨n, hn, hns, hnt⟩
          refine ⟨n + 1, by
            simp only [Walk.support_cons, List.length_cons]
            omega, ?_, ?_⟩
          · simpa using hns
          · simpa [Nat.add_assoc] using hnt
      · rintro ⟨n, hn, hns, hnt⟩
        cases n with
        | zero =>
            left
            have hqpos : 0 < q.support.length := by simpa using hn
            have hct : c = t := by
              calc c = q.support[0] :=
                    ((List.getElem_zero hqpos).trans q.head_support).symm
                _ = t := by simpa using hnt
            have has : a = s := by simpa using hns
            exact Prod.ext has.symm hct.symm
        | succ n =>
            right
            apply ih.mpr
            refine ⟨n, by
              simp only [Walk.support_cons, List.length_cons] at hn
              omega, ?_, ?_⟩
            · simpa [Nat.add_assoc] using hns
            · simpa [Nat.add_assoc] using hnt

/-- Close the ordered support of a finite path cyclically. -/
def cycleOfPath (p : FinitePath D) : DirectedCycle V where
  length := p.walk.support.length
  positive := p.support_length_pos
  vertex i := p.walk.support[i]
  injective := by
    intro i j hij
    apply Fin.ext
    exact p.isPath.getElem_inj_iff.mp hij

theorem cycleOfPath_support (p : FinitePath D) :
    (cycleOfPath p).support = p.support := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    change p.walk.support[i] ∈ p.walk.support
    exact List.getElem_mem _
  · intro hx
    change x ∈ p.walk.support at hx
    rcases List.mem_iff_getElem.mp hx with ⟨n, hn, hnx⟩
    exact ⟨⟨n, hn⟩, hnx⟩

theorem cycleOfPath_next_of_lt (p : FinitePath D)
    (i : Fin (cycleOfPath p).length)
    (hi : i.1 + 1 < p.walk.support.length) :
    (cycleOfPath p).next i = ⟨i.1 + 1, hi⟩ := by
  apply Fin.ext
  simp [DirectedCycle.next, cycleOfPath, Nat.mod_eq_of_lt hi]

theorem cycleOfPath_next_of_not_lt (p : FinitePath D)
    (i : Fin (cycleOfPath p).length)
    (hi : ¬ i.1 + 1 < p.walk.support.length) :
    (cycleOfPath p).next i = ⟨0, p.support_length_pos⟩ := by
  apply Fin.ext
  have hii : i.1 < p.walk.support.length := by
    simpa [cycleOfPath] using i.isLt
  have hilast : i.1 + 1 = p.walk.support.length := by omega
  simp [DirectedCycle.next, cycleOfPath, hilast, Nat.mod_self]

theorem getElem_last_support_eq_finish (p : FinitePath D)
    (i : ℕ) (hi : i < p.walk.support.length)
    (hilast : ¬ i + 1 < p.walk.support.length) :
    p.walk.support[i] = p.finish := by
  have hieq : i + 1 = p.walk.support.length := by omega
  have hiidx : i = p.walk.support.length - 1 := by omega
  have hlast : p.walk.support.getLast p.walk.support_ne_nil = p.finish :=
    p.walk.getLast_support
  subst i
  exact (List.getLast_eq_getElem p.walk.support_ne_nil).symm.trans hlast

theorem cycleOfPath_edgeSet (p : FinitePath D) :
    (cycleOfPath p).EdgeSet = p.edgeSet ∪ {(p.finish, p.start)} := by
  ext e
  constructor
  · rintro ⟨i, rfl⟩
    by_cases hi : i.1 + 1 < p.walk.support.length
    · left
      rw [cycleOfPath_next_of_lt p i hi]
      apply (walkMemEdgeSetIffGetElem p.walk).mpr
      exact ⟨i.1, hi, rfl, rfl⟩
    · right
      rw [cycleOfPath_next_of_not_lt p i hi]
      apply Set.mem_singleton_iff.mpr
      apply Prod.ext
      · exact getElem_last_support_eq_finish p i.1
          (by simpa [cycleOfPath] using i.2) hi
      · simpa [cycleOfPath] using p.support_getElem_zero
  · intro he
    rcases he with he | he
    · rcases (walkMemEdgeSetIffGetElem p.walk).mp he with
        ⟨n, hn, hns, hnt⟩
      have hn' : n < (cycleOfPath p).length := by
        simp only [cycleOfPath]
        omega
      let i : Fin (cycleOfPath p).length := ⟨n, hn'⟩
      refine ⟨i, ?_⟩
      rw [cycleOfPath_next_of_lt p i hn]
      exact Prod.ext hns.symm hnt.symm
    · have heq : e = (p.finish, p.start) := Set.mem_singleton_iff.mp he
      subst e
      let n := p.walk.support.length - 1
      have hn : n < p.walk.support.length := by
        dsimp [n]
        have := p.support_length_pos
        omega
      have hn' : n < (cycleOfPath p).length := by
        simpa [cycleOfPath] using hn
      let i : Fin (cycleOfPath p).length := ⟨n, hn'⟩
      refine ⟨i, ?_⟩
      have hnot : ¬ i.1 + 1 < p.walk.support.length := by
        dsimp [i, n]
        omega
      rw [cycleOfPath_next_of_not_lt p i hnot]
      apply Prod.ext
      · exact (getElem_last_support_eq_finish p i.1
          (by simpa [cycleOfPath] using i.2) hnot).symm
      · simpa [cycleOfPath] using p.support_getElem_zero

/-- A longest path in a finite weak component contains every vertex of that
component. -/
private theorem longest_componentPath_support_eq
    {E : Set (V × V)} {c : Component E}
    (hE : E ⊆ {e | D.Adj e.1 e.2})
    (hout : ∀ {x y z}, (x, y) ∈ E → (x, z) ∈ E → y = z)
    (hin : ∀ {x y z}, (x, z) ∈ E → (y, z) ∈ E → x = y)
    {p : FinitePath D} (hp : IsComponentPath E c p)
    (hmax : ∀ q : FinitePath D, IsComponentPath E c q →
      q.walk.support.length ≤ p.walk.support.length) :
    p.support = componentSupport E c := by
  apply Set.Subset.antisymm hp.2
  have hclosed : ∀ {x y : V}, x ∈ p.support → WeakRel E x y →
      y ∈ p.support := by
    intro x y hxp hxy
    by_contra hyp
    rcases hxy with hxy | hyx
    · by_cases hxfinish : x = p.finish
      · subst x
        let q := appendFreshRC p (hE hxy) hyp
        have hq : IsComponentPath E c q := by
          constructor
          · rw [edgeSet_appendFreshRC]
            exact Set.union_subset hp.1 (Set.singleton_subset_iff.mpr hxy)
          · rw [support_appendFreshRC]
            exact Set.insert_subset
              ((mem_componentSupport_congr_weakRel (Or.inl hxy)).mp
                (hp.2 p.finish_mem_support)) hp.2
        have := hmax q hq
        simp [q] at this
      · obtain ⟨z, hxz⟩ :=
          finitePathExistsOutgoingRC p hxp hxfinish
        have hxzE := hp.1 hxz
        have hyz : y = z := hout hxy hxzE
        exact hyp (hyz ▸ p.edgeSet_subset_support_prod hxz |>.2)
    · by_cases hxstart : x = p.start
      · subst x
        let q := prependFreshRC p (hE hyx) hyp
        have hq : IsComponentPath E c q := by
          constructor
          · rw [edgeSet_prependFreshRC]
            exact Set.union_subset (Set.singleton_subset_iff.mpr hyx) hp.1
          · rw [support_prependFreshRC]
            exact Set.insert_subset
              ((mem_componentSupport_congr_weakRel (Or.inr hyx)).mp
                (hp.2 p.start_mem_support)) hp.2
        have := hmax q hq
        simp [q] at this
      · obtain ⟨z, hzx⟩ :=
          finitePathExistsIncomingRC p hxp hxstart
        have hzxE := hp.1 hzx
        have hyz : y = z := hin hyx hzxE
        exact hyp (hyz ▸ p.edgeSet_subset_support_prod hzx |>.1)
  intro y hyc
  have hpstart : componentMk E p.start = c := hp.2 p.start_mem_support
  have hyreach : Relation.ReflTransGen (WeakRel E) p.start y := by
    have : componentMk E p.start = componentMk E y :=
      hpstart.trans hyc.symm
    exact @Quotient.exact V (weakSetoid E) p.start y this
  have hprop : ∀ {z : V},
      Relation.ReflTransGen (WeakRel E) p.start z → z ∈ p.support := by
    intro z hz
    induction hz with
    | refl => exact p.start_mem_support
    | tail hxy hyz ih => exact hclosed ih hyz
  exact hprop hyreach

/-- On a longest component path, every component edge is a path edge except
possibly the closing edge from its finish to its start. -/
private theorem component_edges_eq_path_or_close
    {E : Set (V × V)} {c : Component E}
    (hout : ∀ {x y z}, (x, y) ∈ E → (x, z) ∈ E → y = z)
    (hin : ∀ {x y z}, (x, z) ∈ E → (y, z) ∈ E → x = y)
    {p : FinitePath D} (hpE : p.edgeSet ⊆ E)
    (hsupport : p.support = componentSupport E c) :
    {e ∈ E | e.1 ∈ componentSupport E c} =
      p.edgeSet ∪ ({(p.finish, p.start)} ∩ E) := by
  apply Set.Subset.antisymm
  · rintro ⟨x, y⟩ ⟨hxy, hxc⟩
    have hxp : x ∈ p.support := by simpa [hsupport] using hxc
    have hyc : y ∈ componentSupport E c :=
      (mem_componentSupport_congr_weakRel (Or.inl hxy)).mp hxc
    have hyp : y ∈ p.support := by simpa [hsupport] using hyc
    by_cases hxfinish : x = p.finish
    · by_cases hystart : y = p.start
      · right
        simpa [hxfinish, hystart] using hxy
      · obtain ⟨z, hzy⟩ :=
          finitePathExistsIncomingRC p hyp hystart
        have hzyE := hpE hzy
        have hxz : x = z := hin hxy hzyE
        left
        simpa [hxz] using hzy
    · obtain ⟨z, hxz⟩ :=
        finitePathExistsOutgoingRC p hxp hxfinish
      have hxzE := hpE hxz
      have hyz : y = z := hout hxy hxzE
      left
      simpa [hyz] using hxz
  · rintro e (he | he)
    · exact ⟨hpE he, by simpa [hsupport] using
        (p.edgeSet_subset_support_prod he).1⟩
    · rcases he with ⟨rfl, hclose⟩
      exact ⟨hclose, by simpa [hsupport] using p.finish_mem_support⟩

/-! ## A canonical component decomposition -/

noncomputable def componentPath (E : Set (V × V)) (c : Component E)
    (hc : (componentSupport E c).Finite) : FinitePath D :=
  Classical.choose (exists_longest_componentPath (D := D) c hc)

theorem componentPath_spec (E : Set (V × V)) (c : Component E)
    (hc : (componentSupport E c).Finite) :
    IsComponentPath E c (componentPath (D := D) E c hc) ∧
      ∀ q : FinitePath D, IsComponentPath E c q →
        q.walk.support.length ≤
          (componentPath (D := D) E c hc).walk.support.length :=
  Classical.choose_spec (exists_longest_componentPath (D := D) c hc)

theorem componentPath_support_eq (E : Set (V × V))
    (hE : E ⊆ {e | D.Adj e.1 e.2})
    (hout : ∀ {x y z}, (x, y) ∈ E → (x, z) ∈ E → y = z)
    (hin : ∀ {x y z}, (x, z) ∈ E → (y, z) ∈ E → x = y)
    (c : Component E) (hc : (componentSupport E c).Finite) :
    (componentPath (D := D) E c hc).support = componentSupport E c := by
  exact longest_componentPath_support_eq hE hout hin
    (componentPath_spec (D := D) E c hc).1
    (componentPath_spec (D := D) E c hc).2

theorem componentPath_edges_eq_path_or_close (E : Set (V × V))
    (hout : ∀ {x y z}, (x, y) ∈ E → (x, z) ∈ E → y = z)
    (hin : ∀ {x y z}, (x, z) ∈ E → (y, z) ∈ E → x = y)
    (c : Component E) (hc : (componentSupport E c).Finite)
    (hsupport : (componentPath (D := D) E c hc).support =
      componentSupport E c) :
    {e ∈ E | e.1 ∈ componentSupport E c} =
      (componentPath (D := D) E c hc).edgeSet ∪
        ({((componentPath (D := D) E c hc).finish,
          (componentPath (D := D) E c hc).start)} ∩ E) :=
  component_edges_eq_path_or_close hout hin
    (componentPath_spec (D := D) E c hc).1.1 hsupport

/-- The selected path closes to a directed cycle. -/
def IsCycleComponent (E : Set (V × V)) (c : Component E)
    (hc : (componentSupport E c).Finite) : Prop :=
  ((componentPath (D := D) E c hc).finish,
    (componentPath (D := D) E c hc).start) ∈ E

/-- Exact edge coverage in a noncyclic component.  Its selected longest path
contains every edge of the component. -/
theorem componentEdges_eq_componentPath_of_not_cycle
    (E : Set (V × V))
    (hE : E ⊆ {e | D.Adj e.1 e.2})
    (hout : ∀ {x y z}, (x, y) ∈ E → (x, z) ∈ E → y = z)
    (hin : ∀ {x y z}, (x, z) ∈ E → (y, z) ∈ E → x = y)
    (c : Component E) (hc : (componentSupport E c).Finite)
    (hnocycle : ¬ IsCycleComponent (D := D) E c hc) :
    {e ∈ E | e.1 ∈ componentSupport E c} =
      (componentPath (D := D) E c hc).edgeSet := by
  let p := componentPath (D := D) E c hc
  have hsupport : p.support = componentSupport E c :=
    componentPath_support_eq E hE hout hin c hc
  have hEq := componentPath_edges_eq_path_or_close E hout hin c hc hsupport
  have hnoclose : (p.finish, p.start) ∉ E := by
    simpa [IsCycleComponent, p] using hnocycle
  have hnone : ({(p.finish, p.start)} ∩ E : Set (V × V)) = ∅ := by
    ext z
    simp [hnoclose]
  simpa [p, hnone] using hEq

/-- Exact edge coverage in a cyclic component.  Closing the selected longest
path gives precisely every edge of the component. -/
theorem componentEdges_eq_cycleOfPath_of_cycle
    (E : Set (V × V))
    (hE : E ⊆ {e | D.Adj e.1 e.2})
    (hout : ∀ {x y z}, (x, y) ∈ E → (x, z) ∈ E → y = z)
    (hin : ∀ {x y z}, (x, z) ∈ E → (y, z) ∈ E → x = y)
    (c : Component E) (hc : (componentSupport E c).Finite)
    (hcycle : IsCycleComponent (D := D) E c hc) :
    {e ∈ E | e.1 ∈ componentSupport E c} =
      (cycleOfPath (componentPath (D := D) E c hc)).EdgeSet := by
  let p := componentPath (D := D) E c hc
  have hsupport : p.support = componentSupport E c :=
    componentPath_support_eq E hE hout hin c hc
  have hEq := componentPath_edges_eq_path_or_close E hout hin c hc hsupport
  have hclose : (p.finish, p.start) ∈ E := by
    simpa [IsCycleComponent, p] using hcycle
  have hone : ({(p.finish, p.start)} ∩ E : Set (V × V)) =
      {(p.finish, p.start)} := by
    ext z
    simp [hclose]
  rw [hone] at hEq
  exact hEq.trans (cycleOfPath_edgeSet p).symm

/-- A component is active when it contains an edge of the relation. -/
def ActiveComponent (E : Set (V × V)) (c : Component E) : Prop :=
  ∃ e ∈ E, e.1 ∈ componentSupport E c

theorem componentSupport_componentMk (E : Set (V × V)) (root : V) :
    componentSupport E (componentMk E root) =
      {x | Relation.ReflTransGen (WeakRel E) root x} := by
  ext x
  change componentMk E x = componentMk E root ↔ _
  constructor
  · intro h
    exact reflTransGen_symm_of_symm
      (fun {_ _} hxy ↦ weakRel_symm hxy)
      (@Quotient.exact V (weakSetoid E) x root h)
  · intro h
    exact Quotient.sound (reflTransGen_symm_of_symm
      (fun {_ _} hxy ↦ weakRel_symm hxy) h)

/-- Root-indexed finiteness is equivalent to finiteness of every quotient
component support. -/
theorem finite_componentSupports_of_roots {E : Set (V × V)}
    (hfinite : ∀ root : V,
      {x | Relation.ReflTransGen (WeakRel E) root x}.Finite) :
    ∀ c : Component E, (componentSupport E c).Finite := by
  intro c
  refine Quotient.inductionOn c ?_
  intro root
  change (componentSupport E (componentMk E root)).Finite
  rw [componentSupport_componentMk]
  exact hfinite root

/-- A vertex with no incident edge forms a singleton weak component. -/
theorem weaklyConnected_eq_of_not_incident {E : Set (V × V)} {x y : V}
    (hno : ∀ z, (x, z) ∉ E ∧ (z, x) ∉ E)
    (hxy : Relation.ReflTransGen (WeakRel E) x y) : y = x := by
  rcases hxy.cases_head with h | ⟨z, hxz, _⟩
  · exact h.symm
  · rcases hxz with hxz | hzx
    · exact False.elim ((hno z).1 hxz)
    · exact False.elim ((hno z).2 hzx)

theorem isolated_not_mem_active {E : Set (V × V)}
    {I : Set V} (hI : ∀ x ∈ I, ∀ y, (x, y) ∉ E ∧ (y, x) ∉ E)
    {x : V} (hxI : x ∈ I) {c : Component E}
    (hxc : x ∈ componentSupport E c) : ¬ ActiveComponent E c := by
  rintro ⟨⟨u, v⟩, huv, huc⟩
  have hcomp : componentMk E x = componentMk E u := hxc.trans huc.symm
  have hreach : Relation.ReflTransGen (WeakRel E) x u :=
    @Quotient.exact V (weakSetoid E) x u hcomp
  have hux : u = x := weaklyConnected_eq_of_not_incident (hI x hxI) hreach
  subst u
  exact (hI x hxI v).1 huv

noncomputable def activePathComponents (G : DWeb V) (E : Set (V × V))
    (hfinite : ∀ c : Component E, (componentSupport E c).Finite) :
    Set G.DPath :=
  {q | ∃ c : Component E, ActiveComponent E c ∧
    ¬ IsCycleComponent (D := G.graph) E c (hfinite c) ∧
    q = .inl (componentPath (D := G.graph) E c (hfinite c))}

def isolatedPathComponents (G : DWeb V) (I : Set V) : Set G.DPath :=
  G.trivialPath '' I

noncomputable def pathComponents (G : DWeb V) (E : Set (V × V))
    (I : Set V)
    (hfinite : ∀ c : Component E, (componentSupport E c).Finite) :
    Set G.DPath :=
  activePathComponents G E hfinite ∪ isolatedPathComponents G I

noncomputable def cycleComponents (G : DWeb V) (E : Set (V × V))
    (hfinite : ∀ c : Component E, (componentSupport E c).Finite) :
    Set (DirectedCycle V) :=
  {C | ∃ c : Component E, ActiveComponent E c ∧
    IsCycleComponent (D := G.graph) E c (hfinite c) ∧
    C = cycleOfPath (componentPath (D := G.graph) E c (hfinite c))}

theorem activePathComponents_isWarp (G : DWeb V) (E : Set (V × V))
    (hE : E ⊆ {e | G.graph.Adj e.1 e.2})
    (hout : ∀ {x y z}, (x, y) ∈ E → (x, z) ∈ E → y = z)
    (hin : ∀ {x y z}, (x, z) ∈ E → (y, z) ∈ E → x = y)
    (hfinite : ∀ c : Component E, (componentSupport E c).Finite) :
    G.IsWarp (activePathComponents G E hfinite) := by
  intro p hp q hq hpq
  rcases hp with ⟨c, hcactive, hcnocycle, rfl⟩
  rcases hq with ⟨d, hdactive, hdnocycle, rfl⟩
  have hcd : c ≠ d := by
    intro h
    subst d
    exact hpq rfl
  change Disjoint
    (componentPath (D := G.graph) E c (hfinite c)).support
    (componentPath (D := G.graph) E d (hfinite d)).support
  rw [componentPath_support_eq E hE hout hin c (hfinite c),
    componentPath_support_eq E hE hout hin d (hfinite d)]
  exact componentSupport_disjoint hcd

theorem isolatedPathComponents_isWarp (G : DWeb V) (I : Set V) :
    G.IsWarp (isolatedPathComponents G I) := by
  intro p hp q hq hpq
  rcases hp with ⟨x, hxI, rfl⟩
  rcases hq with ⟨y, hyI, rfl⟩
  have hxy : x ≠ y := by
    intro h
    subst y
    exact hpq rfl
  change Disjoint (G.trivialPath x).support (G.trivialPath y).support
  rw [G.support_trivialPath, G.support_trivialPath]
  exact Set.disjoint_singleton.2 hxy

theorem activePathComponents_disjoint_isolated
    (G : DWeb V) (E : Set (V × V)) (I : Set V)
    (hE : E ⊆ {e | G.graph.Adj e.1 e.2})
    (hout : ∀ {x y z}, (x, y) ∈ E → (x, z) ∈ E → y = z)
    (hin : ∀ {x y z}, (x, z) ∈ E → (y, z) ∈ E → x = y)
    (hfinite : ∀ c : Component E, (componentSupport E c).Finite)
    (hI : ∀ x ∈ I, ∀ y, (x, y) ∉ E ∧ (y, x) ∉ E) :
    ∀ p ∈ activePathComponents G E hfinite,
      ∀ q ∈ isolatedPathComponents G I,
        Disjoint p.support q.support := by
  intro p hp q hq
  rcases hp with ⟨c, hcactive, hcnocycle, rfl⟩
  rcases hq with ⟨x, hxI, rfl⟩
  change Disjoint
    (componentPath (D := G.graph) E c (hfinite c)).support
    (G.trivialPath x).support
  rw [componentPath_support_eq E hE hout hin c (hfinite c),
    G.support_trivialPath]
  rw [Set.disjoint_singleton_right]
  intro hxc
  exact isolated_not_mem_active hI hxI hxc hcactive

theorem pathComponents_isWarp
    (G : DWeb V) (E : Set (V × V)) (I : Set V)
    (hE : E ⊆ {e | G.graph.Adj e.1 e.2})
    (hout : ∀ {x y z}, (x, y) ∈ E → (x, z) ∈ E → y = z)
    (hin : ∀ {x y z}, (x, z) ∈ E → (y, z) ∈ E → x = y)
    (hfinite : ∀ c : Component E, (componentSupport E c).Finite)
    (hI : ∀ x ∈ I, ∀ y, (x, y) ∉ E ∧ (y, x) ∉ E) :
    G.IsWarp (pathComponents G E I hfinite) := by
  intro p hp q hq hpq
  rcases hp with hp | hp <;> rcases hq with hq | hq
  · exact activePathComponents_isWarp G E hE hout hin hfinite hp hq hpq
  · exact activePathComponents_disjoint_isolated G E I hE hout hin
      hfinite hI p hp q hq
  · exact (activePathComponents_disjoint_isolated G E I hE hout hin
      hfinite hI q hq p hp).symm
  · exact isolatedPathComponents_isWarp G I hp hq hpq

theorem pathComponents_finiteCharacter
    (G : DWeb V) (E : Set (V × V)) (I : Set V)
    (hfinite : ∀ c : Component E, (componentSupport E c).Finite) :
    G.HasFiniteCharacter (pathComponents G E I hfinite) := by
  intro p hp
  rcases hp with hp | hp
  · rcases hp with ⟨c, _, _, rfl⟩
    exact ⟨componentPath E c (hfinite c), rfl⟩
  · rcases hp with ⟨x, hxI, rfl⟩
    exact ⟨FinitePath.trivial G.graph x, rfl⟩

theorem cycleComponents_in_graph
    (G : DWeb V) (E : Set (V × V))
    (hE : E ⊆ {e | G.graph.Adj e.1 e.2})
    (hfinite : ∀ c : Component E, (componentSupport E c).Finite) :
    ∀ C ∈ cycleComponents G E hfinite,
      C.EdgeSet ⊆ {e | G.graph.Adj e.1 e.2} := by
  intro C hC
  rcases hC with ⟨c, hcactive, hclose, rfl⟩
  rw [cycleOfPath_edgeSet]
  apply Set.union_subset
  · exact (componentPath_spec E c (hfinite c)).1.1.trans hE
  · exact (Set.singleton_subset_iff.mpr hclose).trans hE

theorem cycleComponents_pairwise
    (G : DWeb V) (E : Set (V × V))
    (hE : E ⊆ {e | G.graph.Adj e.1 e.2})
    (hout : ∀ {x y z}, (x, y) ∈ E → (x, z) ∈ E → y = z)
    (hin : ∀ {x y z}, (x, z) ∈ E → (y, z) ∈ E → x = y)
    (hfinite : ∀ c : Component E, (componentSupport E c).Finite) :
    (cycleComponents G E hfinite).PairwiseDisjoint DirectedCycle.support := by
  intro C hC K hK hCK
  rcases hC with ⟨c, hcactive, hclose, rfl⟩
  rcases hK with ⟨d, hdactive, hdclose, rfl⟩
  have hcd : c ≠ d := by
    intro h
    subst d
    exact hCK rfl
  change Disjoint
    (cycleOfPath (componentPath (D := G.graph) E c (hfinite c))).support
    (cycleOfPath (componentPath (D := G.graph) E d (hfinite d))).support
  rw [cycleOfPath_support, cycleOfPath_support,
    componentPath_support_eq E hE hout hin c (hfinite c),
    componentPath_support_eq E hE hout hin d (hfinite d)]
  exact componentSupport_disjoint hcd

theorem pathComponents_cycles_disjoint
    (G : DWeb V) (E : Set (V × V)) (I : Set V)
    (hE : E ⊆ {e | G.graph.Adj e.1 e.2})
    (hout : ∀ {x y z}, (x, y) ∈ E → (x, z) ∈ E → y = z)
    (hin : ∀ {x y z}, (x, z) ∈ E → (y, z) ∈ E → x = y)
    (hfinite : ∀ c : Component E, (componentSupport E c).Finite)
    (hI : ∀ x ∈ I, ∀ y, (x, y) ∉ E ∧ (y, x) ∉ E) :
    ∀ p ∈ pathComponents G E I hfinite,
      ∀ C ∈ cycleComponents G E hfinite,
        Disjoint p.support C.support := by
  intro p hp C hC
  rcases hC with ⟨d, hdactive, hdclose, rfl⟩
  rcases hp with hp | hp
  · rcases hp with ⟨c, hcactive, hcnoclose, rfl⟩
    have hcd : c ≠ d := by
      intro h
      subst d
      exact hcnoclose hdclose
    change Disjoint
      (componentPath (D := G.graph) E c (hfinite c)).support
      (cycleOfPath (componentPath (D := G.graph) E d (hfinite d))).support
    rw [cycleOfPath_support,
      componentPath_support_eq E hE hout hin c (hfinite c),
      componentPath_support_eq E hE hout hin d (hfinite d)]
    exact componentSupport_disjoint hcd
  · rcases hp with ⟨x, hxI, rfl⟩
    change Disjoint (G.trivialPath x).support
      (cycleOfPath (componentPath (D := G.graph) E d (hfinite d))).support
    rw [G.support_trivialPath, cycleOfPath_support,
      componentPath_support_eq E hE hout hin d (hfinite d),
      Set.disjoint_singleton_left]
    intro hxd
    exact isolated_not_mem_active hI hxI hxd hdactive

theorem familyEdges_pathComponents_subset
    (G : DWeb V) (E : Set (V × V)) (I : Set V)
    (hfinite : ∀ c : Component E, (componentSupport E c).Finite) :
    familyEdges (pathComponents G E I hfinite) ⊆ E := by
  intro e he
  simp only [familyEdges, Set.mem_iUnion] at he
  rcases he with ⟨p, hp, hep⟩
  rcases hp with hp | hp
  · rcases hp with ⟨c, hcactive, hcnoclose, rfl⟩
    exact (componentPath_spec E c (hfinite c)).1.1 hep
  · rcases hp with ⟨x, hxI, rfl⟩
    simpa [DWeb.trivialPath, Path.trivial, FinitePath.trivial,
      FinitePath.edgeSet, Walk.edgeSet] using hep

theorem cycleEdges_subset
    (G : DWeb V) (E : Set (V × V))
    (hfinite : ∀ c : Component E, (componentSupport E c).Finite) :
    (⋃ C ∈ cycleComponents G E hfinite, C.EdgeSet) ⊆ E := by
  intro e he
  simp only [Set.mem_iUnion] at he
  rcases he with ⟨C, hC, heC⟩
  rcases hC with ⟨c, hcactive, hclose, rfl⟩
  rw [cycleOfPath_edgeSet] at heC
  rcases heC with heC | heC
  · exact (componentPath_spec E c (hfinite c)).1.1 heC
  · exact Set.mem_singleton_iff.mp heC ▸ hclose

theorem edges_covered_by_components
    (G : DWeb V) (E : Set (V × V)) (I : Set V)
    (hE : E ⊆ {e | G.graph.Adj e.1 e.2})
    (hout : ∀ {x y z}, (x, y) ∈ E → (x, z) ∈ E → y = z)
    (hin : ∀ {x y z}, (x, z) ∈ E → (y, z) ∈ E → x = y)
    (hfinite : ∀ c : Component E, (componentSupport E c).Finite) :
    E ⊆ familyEdges (pathComponents G E I hfinite) ∪
      ⋃ C ∈ cycleComponents G E hfinite, C.EdgeSet := by
  intro e he
  let c : Component E := componentMk E e.1
  have hcactive : ActiveComponent E c :=
    ⟨e, he, componentMk_mem E e.1⟩
  let p := componentPath (D := G.graph) E c (hfinite c)
  have hecomp : e ∈ {e ∈ E | e.1 ∈ componentSupport E c} :=
    ⟨he, componentMk_mem E e.1⟩
  have hsupport : p.support = componentSupport E c :=
    componentPath_support_eq E hE hout hin c (hfinite c)
  by_cases hclose : IsCycleComponent (D := G.graph) E c (hfinite c)
  · right
    simp only [Set.mem_iUnion]
    refine ⟨cycleOfPath p, ⟨⟨c, hcactive, hclose, rfl⟩, ?_⟩⟩
    rw [cycleOfPath_edgeSet]
    have hmem := (componentPath_edges_eq_path_or_close E hout hin c
      (hfinite c) hsupport) ▸ hecomp
    rcases hmem with hmem | hmem
    · exact Or.inl hmem
    · exact Or.inr hmem.1
  · left
    simp only [familyEdges, Set.mem_iUnion]
    refine ⟨(.inl p : G.DPath), ⟨Or.inl ⟨c, hcactive, hclose, rfl⟩, ?_⟩⟩
    have hEq := componentPath_edges_eq_path_or_close E hout hin c
      (hfinite c) hsupport
    have hclose' : (p.finish, p.start) ∉ E := by
      simpa [IsCycleComponent, p] using hclose
    have hnone : ({(p.finish, p.start)} ∩ E : Set (V × V)) = ∅ := by
      ext z
      simp [hclose']
    rw [hnone, Set.union_empty] at hEq
    change e ∈ p.edgeSet
    rw [← hEq]
    exact hecomp

theorem isolatedVertices_pathComponents
    (G : DWeb V) (E : Set (V × V)) (I : Set V)
    (hE : E ⊆ {e | G.graph.Adj e.1 e.2})
    (hout : ∀ {x y z}, (x, y) ∈ E → (x, z) ∈ E → y = z)
    (hin : ∀ {x y z}, (x, z) ∈ E → (y, z) ∈ E → x = y)
    (hfinite : ∀ c : Component E, (componentSupport E c).Finite) :
    isolatedVertices (pathComponents G E I hfinite) = I := by
  ext v
  constructor
  · intro hv
    rcases hv with hv | hv
    · rcases hv with ⟨c, hcactive, hnoclose, heq⟩
      let p := componentPath (D := G.graph) E c (hfinite c)
      have hsupport : p.support = componentSupport E c :=
        componentPath_support_eq E hE hout hin c (hfinite c)
      have hEq := componentPath_edges_eq_path_or_close E hout hin c
        (hfinite c) hsupport
      have hnoclose' : (p.finish, p.start) ∉ E := by
        simpa [IsCycleComponent, p] using hnoclose
      have hnone : ({(p.finish, p.start)} ∩ E : Set (V × V)) = ∅ := by
        ext z
        simp [hnoclose']
      rw [hnone, Set.union_empty] at hEq
      obtain ⟨e, heE, hec⟩ := hcactive
      have hep : e ∈ p.edgeSet := by
        rw [← hEq]
        exact ⟨heE, hec⟩
      have hep' : e ∈ Path.edgeSet (.inl p : G.DPath) := hep
      have heq' : G.trivialPath v = (.inl p : G.DPath) := heq
      rw [← heq'] at hep'
      simpa [DWeb.trivialPath, Path.trivial, FinitePath.trivial,
        FinitePath.edgeSet, Walk.edgeSet] using hep'
    · rcases hv with ⟨x, hxI, heq⟩
      have hini := congrArg Path.initial heq
      have hvx : v = x := by
        simpa using hini.symm
      simpa [hvx] using hxI
  · intro hvI
    exact Or.inr ⟨v, hvI, rfl⟩

/-- The cyclowarp obtained by selecting one longest path in every active
finite weak component and closing exactly the cyclic ones. -/
noncomputable def cyclowarpOfFiniteComponents
    (G : DWeb V) (E : Set (V × V)) (I : Set V)
    (hE : E ⊆ {e | G.graph.Adj e.1 e.2})
    (hout : ∀ {x y z}, (x, y) ∈ E → (x, z) ∈ E → y = z)
    (hin : ∀ {x y z}, (x, z) ∈ E → (y, z) ∈ E → x = y)
    (hfinite : ∀ c : Component E, (componentSupport E c).Finite)
    (hI : ∀ x ∈ I, ∀ y, (x, y) ∉ E ∧ (y, x) ∉ E) :
    Cyclowarp G where
  paths := pathComponents G E I hfinite
  cycles := cycleComponents G E hfinite
  paths_isWarp := pathComponents_isWarp G E I hE hout hin hfinite hI
  cycles_in_graph := cycleComponents_in_graph G E hE hfinite
  cycles_disjoint := cycleComponents_pairwise G E hE hout hin hfinite
  paths_cycles_disjoint :=
    pathComponents_cycles_disjoint G E I hE hout hin hfinite hI

theorem cyclowarpOfFiniteComponents_edges
    (G : DWeb V) (E : Set (V × V)) (I : Set V)
    (hE : E ⊆ {e | G.graph.Adj e.1 e.2})
    (hout : ∀ {x y z}, (x, y) ∈ E → (x, z) ∈ E → y = z)
    (hin : ∀ {x y z}, (x, z) ∈ E → (y, z) ∈ E → x = y)
    (hfinite : ∀ c : Component E, (componentSupport E c).Finite)
    (hI : ∀ x ∈ I, ∀ y, (x, y) ∉ E ∧ (y, x) ∉ E) :
    (cyclowarpOfFiniteComponents G E I hE hout hin hfinite hI).edges = E := by
  apply Set.Subset.antisymm
  · exact Set.union_subset
      (familyEdges_pathComponents_subset G E I hfinite)
      (cycleEdges_subset G E hfinite)
  · exact edges_covered_by_components G E I hE hout hin hfinite

theorem cyclowarpOfFiniteComponents_isolated
    (G : DWeb V) (E : Set (V × V)) (I : Set V)
    (hE : E ⊆ {e | G.graph.Adj e.1 e.2})
    (hout : ∀ {x y z}, (x, y) ∈ E → (x, z) ∈ E → y = z)
    (hin : ∀ {x y z}, (x, z) ∈ E → (y, z) ∈ E → x = y)
    (hfinite : ∀ c : Component E, (componentSupport E c).Finite)
    (hI : ∀ x ∈ I, ∀ y, (x, y) ∉ E ∧ (y, x) ∉ E) :
    (cyclowarpOfFiniteComponents G E I hE hout hin hfinite hI).isolated = I :=
  isolatedVertices_pathComponents G E I hE hout hin hfinite

theorem cyclowarpOfFiniteComponents_finiteCharacter
    (G : DWeb V) (E : Set (V × V)) (I : Set V)
    (hE : E ⊆ {e | G.graph.Adj e.1 e.2})
    (hout : ∀ {x y z}, (x, y) ∈ E → (x, z) ∈ E → y = z)
    (hin : ∀ {x y z}, (x, z) ∈ E → (y, z) ∈ E → x = y)
    (hfinite : ∀ c : Component E, (componentSupport E c).Finite)
    (hI : ∀ x ∈ I, ∀ y, (x, y) ∉ E ∧ (y, x) ∉ E) :
    G.HasFiniteCharacter
      (cyclowarpOfFiniteComponents G E I hE hout hin hfinite hI).pathPart :=
  pathComponents_finiteCharacter G E I hfinite

/-- Quotient-component form of the finite locally-functional decomposition
theorem. -/
theorem exists_cyclowarp_of_finite_componentSupports
    (G : DWeb V) (E : Set (V × V)) (I : Set V)
    (hE : E ⊆ {e | G.graph.Adj e.1 e.2})
    (hout : ∀ {x y z}, (x, y) ∈ E → (x, z) ∈ E → y = z)
    (hin : ∀ {x y z}, (x, z) ∈ E → (y, z) ∈ E → x = y)
    (hfinite : ∀ c : Component E, (componentSupport E c).Finite)
    (hI : ∀ x ∈ I, ∀ y, (x, y) ∉ E ∧ (y, x) ∉ E) :
    ∃ C : Cyclowarp G, C.edges = E ∧ C.isolated = I ∧
      G.HasFiniteCharacter C.pathPart := by
  let C := cyclowarpOfFiniteComponents G E I hE hout hin hfinite hI
  exact ⟨C, cyclowarpOfFiniteComponents_edges G E I hE hout hin hfinite hI,
    cyclowarpOfFiniteComponents_isolated G E I hE hout hin hfinite hI,
    cyclowarpOfFiniteComponents_finiteCharacter G E I hE hout hin hfinite hI⟩

/-- Root-indexed form, convenient for applications whose affected weak
components are proved finite by a reachability argument. -/
theorem exists_cyclowarp_of_finite_components
    (G : DWeb V) (E : Set (V × V)) (I : Set V)
    (hE : E ⊆ {e | G.graph.Adj e.1 e.2})
    (hout : ∀ {x y z}, (x, y) ∈ E → (x, z) ∈ E → y = z)
    (hin : ∀ {x y z}, (x, z) ∈ E → (y, z) ∈ E → x = y)
    (hfinite : ∀ root : V,
      {x | Relation.ReflTransGen (WeakRel E) root x}.Finite)
    (hI : ∀ x ∈ I, ∀ y, (x, y) ∉ E ∧ (y, x) ∉ E) :
    ∃ C : Cyclowarp G, C.edges = E ∧ C.isolated = I ∧
      G.HasFiniteCharacter C.pathPart :=
  exists_cyclowarp_of_finite_componentSupports G E I hE hout hin
    (finite_componentSupports_of_roots hfinite) hI

end RelationComponents
end Alternating
end Erdos599
