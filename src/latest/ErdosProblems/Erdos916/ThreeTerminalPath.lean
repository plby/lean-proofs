import ErdosProblems.Erdos599.Countable
import ErdosProblems.Erdos916.Blocks

/-!
# A path through three prescribed vertices

This file proves the elementary ``three-point path theorem'' in the form used by the
false-twin reduction for Erdős Problem 916: in a finite vertex-two-connected simple graph,
three distinct prescribed vertices lie on a simple path, and the endpoints of the path can
be chosen among the prescribed vertices.

The proof uses the finite vertex-Menger theorem already available in `Erdos599`.  The third
terminal is split into two auxiliary sources, each adjacent to all of its old neighbours.
Deleting fewer than two vertices cannot separate those sources from the other two terminals:
after choosing a surviving source and target, vertex-two-connectivity supplies a route in the
old graph avoiding the possible deleted vertex.  Two disjoint auxiliary paths therefore give
two internally disjoint arms from the split terminal to the other two terminals.
-/

open Finset Set

attribute [local instance] Classical.propDecidable

namespace Erdos916

open SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## The finite two-path consequence of Erdős--Menger -/

/-- Two explicitly indexed, fully vertex-disjoint `A`–`B` paths. -/
structure TwoABLinkage {W : Type*} (H : SimpleGraph W) (A B : Set W) where
  left : Fin 2 → W
  right : Fin 2 → W
  path : ∀ i, H.Walk (left i) (right i)
  left_mem : ∀ i, left i ∈ A
  right_mem : ∀ i, right i ∈ B
  isPath : ∀ i, (path i).IsPath
  disjoint : Pairwise fun i j ↦
    Disjoint {v | v ∈ (path i).support} {v | v ∈ (path j).support}

/-- Finite vertex Menger, specialized to two paths. -/
theorem exists_twoABLinkage_of_separator_two_le {W : Type} [Finite W]
    (H : SimpleGraph W) (A B : Set W)
    (hsep : ∀ S, Erdos599.Countable.Separates H A B S → 2 ≤ S.ncard) :
    Nonempty (TwoABLinkage H A B) := by
  classical
  have hEM : Erdos599.Countable.HasErdosMengerPair H A B :=
    Erdos599.Countable.hasErdosMengerPair_of_safePathRemoval_of_countable
      Erdos599.Countable.safePathRemoval H A B (Set.toFinite A).countable
  rcases hEM with ⟨ι, left, right, path, S, hleft, hright, hpath,
    hdisjoint, hSsub, horth, hseparates⟩
  have hScard : 2 ≤ S.ncard := hsep S hseparates
  have hSfinite : S.Finite := Set.toFinite S
  let _ : Fintype S := hSfinite.fintype
  have hcard : 2 ≤ Fintype.card S := by
    simpa [Set.fintypeCard_eq_ncard] using hScard
  have htwo : Fintype.card (Fin 2) ≤ Fintype.card S := by simpa using hcard
  rcases Function.Embedding.nonempty_of_card_le htwo with ⟨pickS⟩
  choose pickI hpickI using fun i : Fin 2 ↦ hSsub (pickS i).property
  have hpickI_inj : Function.Injective pickI := by
    intro i j hij
    by_contra hne
    have hi : (pickS i : W) ∈ S ∧ (pickS i : W) ∈ (path (pickI i)).support :=
      ⟨(pickS i).property, hpickI i⟩
    have hj : (pickS j : W) ∈ S ∧ (pickS j : W) ∈ (path (pickI i)).support := by
      rw [hij]
      exact ⟨(pickS j).property, hpickI j⟩
    have hsEq : (pickS i : W) = pickS j := (horth (pickI i)).unique hi hj
    exact hne (pickS.injective (Subtype.ext hsEq))
  exact ⟨{
    left := fun i ↦ left (pickI i)
    right := fun i ↦ right (pickI i)
    path := fun i ↦ path (pickI i)
    left_mem := fun i ↦ hleft (pickI i)
    right_mem := fun i ↦ hright (pickI i)
    isPath := fun i ↦ hpath (pickI i)
    disjoint := fun i j hij ↦ hdisjoint (hpickI_inj.ne hij) }⟩

/-- The vertex type obtained by replacing `c` by two new source vertices. -/
abbrev SplitVertex (c : V) := Fin 2 ⊕ {v : V // v ≠ c}

/-- Replace `c` by two false twins, both with the old neighbourhood of `c`.  The old copy of
`c` is omitted. -/
def splitTerminalGraph (G : SimpleGraph V) (c : V) : SimpleGraph (SplitVertex c) where
  Adj x y :=
    match x, y with
    | .inl _, .inl _ => False
    | .inl _, .inr y => G.Adj c y.1
    | .inr x, .inl _ => G.Adj x.1 c
    | .inr x, .inr y => G.Adj x.1 y.1
  symm := ⟨by
    rintro (i | x) (j | y) <;> simp only
    · exact fun h ↦ h
    · exact G.adj_symm
    · exact G.adj_symm
    · exact G.adj_symm⟩
  loopless := ⟨by
    rintro (i | x) <;> simp only
    · exact id
    · exact G.loopless.irrefl x.1⟩

@[simp] theorem splitTerminalGraph_adj_source_old {c : V} {i : Fin 2}
    {x : {v : V // v ≠ c}} :
    (splitTerminalGraph G c).Adj (.inl i) (.inr x) ↔ G.Adj c x.1 :=
  Iff.rfl

@[simp] theorem splitTerminalGraph_adj_old_source {c : V} {i : Fin 2}
    {x : {v : V // v ≠ c}} :
    (splitTerminalGraph G c).Adj (.inr x) (.inl i) ↔ G.Adj x.1 c :=
  Iff.rfl

@[simp] theorem splitTerminalGraph_adj_old_old {c : V}
    {x y : {v : V // v ≠ c}} :
    (splitTerminalGraph G c).Adj (.inr x) (.inr y) ↔ G.Adj x.1 y.1 :=
  Iff.rfl

@[simp] theorem not_splitTerminalGraph_adj_source_source {c : V} {i j : Fin 2} :
    ¬(splitTerminalGraph G c).Adj (.inl i) (.inl j) :=
  id

/-- The inclusion of the surviving old vertices into the split graph. -/
def splitOldHom (G : SimpleGraph V) (c : V) :
    G.induce {v | v ≠ c} →g splitTerminalGraph G c where
  toFun x := .inr x
  map_rel' := by
    intro x y hxy
    exact hxy

@[simp] theorem splitOldHom_apply (G : SimpleGraph V) (c : V)
    (x : {v : V // v ≠ c}) : splitOldHom G c x = .inr x :=
  rfl

/-- Lift a walk all of whose vertices avoid `c` into the old-vertex part of the split graph. -/
def splitTail {c : V} :
    ∀ {x t : V} (p : G.Walk x t) (hout : ∀ y ∈ p.support, y ≠ c),
      (splitTerminalGraph G c).Walk (.inr ⟨x, hout x p.start_mem_support⟩)
        (.inr ⟨t, hout t p.end_mem_support⟩)
  | _, _, .nil, _ => .nil
  | _, _, .cons hxy q, hout =>
      .cons (by exact hxy) (splitTail q fun y hy ↦ hout y (by simp [hy]))

private theorem splitTail_cons_eq {c x y t : V} (hxy : G.Adj x y)
    (q : G.Walk y t) (hout : ∀ z ∈ (q.cons hxy).support, z ≠ c) :
    splitTail (q.cons hxy) hout =
      (splitTail q (fun z hz ↦ hout z (by simp [hz]))).cons
        (show (splitTerminalGraph G c).Adj
          (.inr ⟨x, hout x (by simp)⟩)
          (.inr ⟨y, hout y (by simp)⟩) from hxy) := by
  rfl

private theorem splitTail_support_cases {c x t : V} (p : G.Walk x t)
    (hout : ∀ y ∈ p.support, y ≠ c) {z : SplitVertex c}
    (hz : z ∈ (splitTail p hout).support) :
    ∃ y, ∃ hyc : y ≠ c, y ∈ p.support ∧ z = .inr ⟨y, hyc⟩ := by
  let rec go {x t : V} (p : G.Walk x t)
      (hout : ∀ y ∈ p.support, y ≠ c) {z : SplitVertex c}
      (hz : z ∈ (splitTail p hout).support) :
      ∃ y, ∃ hyc : y ≠ c, y ∈ p.support ∧ z = .inr ⟨y, hyc⟩ := by
    cases p with
    | nil =>
        refine ⟨x, hout x (by simp), by simp, ?_⟩
        simpa [splitTail] using hz
    | @cons x y t hxy q =>
        have hz' : z = .inr ⟨x, hout x (by simp)⟩ ∨
            z ∈ (splitTail q (fun w hw ↦ hout w (by simp [hw]))).support := by
          rw [splitTail_cons_eq hxy q hout, Walk.support_cons] at hz
          exact List.mem_cons.mp hz
        rcases hz' with rfl | hz'
        · exact ⟨x, hout x (by simp), by simp, rfl⟩
        · obtain ⟨w, hwc, hwq, rfl⟩ := go q _ hz'
          exact ⟨w, hwc, by simp [hwq], rfl⟩
  exact go p hout hz

private theorem splitTail_isPath {c x t : V} (p : G.Walk x t) (hp : p.IsPath)
    (hout : ∀ y ∈ p.support, y ≠ c) : (splitTail p hout).IsPath := by
  rw [Walk.isPath_def]
  induction p with
  | nil => simp [splitTail]
  | @cons x y t hxy q ih =>
      rw [splitTail_cons_eq hxy q hout, Walk.support_cons, List.nodup_cons]
      have hpN : (x :: q.support).Nodup := hp.support_nodup
      constructor
      · intro hx
        obtain ⟨w, hwc, hwq, hw⟩ := splitTail_support_cases q _ hx
        have hxw : x = w := by
          have := congrArg (fun z ↦ match z with
            | .inl _ => c
            | .inr z => z.1) hw
          simpa using this
        exact (List.nodup_cons.mp hpN).1 (hxw ▸ hwq)
      · exact ih (Walk.IsPath.mk' (List.nodup_cons.mp hpN).2) _

/-- Lift a nontrivial path starting at `c` to a path starting at either new source. -/
noncomputable def splitArm {c t : V} (i : Fin 2) (p : G.Walk c t)
    (hp : p.IsPath) (hct : c ≠ t) :
    (splitTerminalGraph G c).Walk (.inl i) (.inr ⟨t, Ne.symm hct⟩) := by
  cases p with
  | nil => exact False.elim (hct rfl)
  | @cons _ x _ hcx q =>
      have hqoutside : ∀ y ∈ q.support, y ≠ c := by
        intro y hy hyc
        subst y
        have hpN : (c :: q.support).Nodup := hp.support_nodup
        exact (List.nodup_cons.mp hpN).1 hy
      have hsource : (splitTerminalGraph G c).Adj (.inl i)
          (.inr ⟨x, hqoutside x q.start_mem_support⟩) := hcx
      exact (splitTail q hqoutside).cons hsource

private theorem splitArm_cons_eq {c x t : V} (i : Fin 2) (hcx : G.Adj c x)
    (q : G.Walk x t) (hp : (q.cons hcx).IsPath) (hct : c ≠ t) :
    splitArm i (q.cons hcx) hp hct =
      (splitTail q (fun y hy ↦ by
        have hpN : (c :: q.support).Nodup := hp.support_nodup
        exact fun hyc ↦ (List.nodup_cons.mp hpN).1 (hyc ▸ hy))).cons
        (show (splitTerminalGraph G c).Adj (.inl i)
          (.inr ⟨x, by
            have hpN : (c :: q.support).Nodup := hp.support_nodup
            exact fun hxc' ↦ (List.nodup_cons.mp hpN).1
              (hxc' ▸ q.start_mem_support)⟩) from hcx) := by
  rfl

private theorem splitArm_isPath {c t : V} (i : Fin 2) (p : G.Walk c t)
    (hp : p.IsPath) (hct : c ≠ t) :
    (splitArm i p hp hct).IsPath := by
  cases p with
  | nil => exact False.elim (hct rfl)
  | @cons _ x _ hcx q =>
      have hpN : (c :: q.support).Nodup := hp.support_nodup
      have hqPath : q.IsPath := Walk.IsPath.mk' (List.nodup_cons.mp hpN).2
      have hqoutside : ∀ y ∈ q.support, y ≠ c := by
        intro y hy hyc
        subst y
        exact (List.nodup_cons.mp hpN).1 hy
      have htailPath : (splitTail q hqoutside).IsPath := by
        exact splitTail_isPath q hqPath hqoutside
      have hsourceFresh : (.inl i : SplitVertex c) ∉
          (splitTail q hqoutside).support := by
        intro hs
        obtain ⟨z, hzc, -, hz⟩ := splitTail_support_cases q hqoutside hs
        simp at hz
      exact htailPath.cons hsourceFresh

private theorem splitArm_support_cases {c t : V} (i : Fin 2) (p : G.Walk c t)
    (hp : p.IsPath) (hct : c ≠ t) {z : SplitVertex c}
    (hz : z ∈ (splitArm i p hp hct).support) :
    z = .inl i ∨ ∃ x, ∃ hxc : x ≠ c, x ∈ p.support ∧ z = .inr ⟨x, hxc⟩ := by
  cases p with
  | nil => exact False.elim (hct rfl)
  | @cons _ x _ hcx q =>
      have hqoutside : ∀ y ∈ q.support, y ≠ c := by
        intro y hy hyc
        subst y
        exact (List.nodup_cons.mp hp.support_nodup).1 hy
      have hz' : z = .inl i ∨ z ∈ (splitTail q hqoutside).support := by
        rw [splitArm_cons_eq i hcx q hp hct, Walk.support_cons] at hz
        exact List.mem_cons.mp hz
      rcases hz' with hz' | hz'
      · exact Or.inl hz'
      · obtain ⟨y, hyc, hyq, rfl⟩ := splitTail_support_cases q hqoutside hz'
        exact Or.inr ⟨y, hyc, by simp [hyq], rfl⟩

/-- The two auxiliary source vertices. -/
def splitSources (c : V) : Set (SplitVertex c) := Set.range Sum.inl

/-- The two old target vertices corresponding to `a` and `b`. -/
def splitTargets {c : V} (a b : {v : V // v ≠ c}) : Set (SplitVertex c) :=
  {.inr a, .inr b}

@[simp] theorem mem_splitSources {c : V} {z : SplitVertex c} :
    z ∈ splitSources c ↔ ∃ i, z = .inl i := by
  simp [splitSources, eq_comm]

@[simp] theorem mem_splitTargets {c : V} {a b : {v : V // v ≠ c}}
    {z : SplitVertex c} :
    z ∈ splitTargets a b ↔ z = .inr a ∨ z = .inr b := by
  simp [splitTargets]

/-- No one-vertex set separates the split sources from two prescribed old targets. -/
private theorem split_separator_two_le
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hconn : G.Connected)
    (hdelete : ∀ v : V, (G.induce fun w : V ↦ w ≠ v).Connected)
    (S : Set (SplitVertex c))
    (hS : Erdos599.Countable.Separates (splitTerminalGraph G c) (splitSources c)
      (splitTargets ⟨a, hac⟩ ⟨b, hbc⟩) S) :
    2 ≤ S.ncard := by
  classical
  by_contra hnot
  have hlt : S.ncard < 2 := Nat.lt_of_not_ge hnot
  have hfinite : S.Finite := Set.toFinite S
  have hcases : S = ∅ ∨ ∃ s, S = {s} := by
    have hzero_or_one : S.ncard = 0 ∨ S.ncard = 1 := by omega
    rcases hzero_or_one with hzero | hone
    · exact Or.inl (Set.ncard_eq_zero hfinite |>.mp hzero)
    · exact Or.inr (Set.ncard_eq_one.mp hone)
  rcases hcases with rfl | ⟨s, rfl⟩
  · obtain ⟨p, hp⟩ := (hconn c a).exists_isPath
    let q := splitArm 0 p hp (Ne.symm hac)
    have hq : q.IsPath := splitArm_isPath 0 p hp (Ne.symm hac)
    rcases hS (.inl 0) ⟨0, rfl⟩ (.inr ⟨a, hac⟩) (by simp)
        q hq with ⟨z, -, hz⟩
    exact hz
  · cases s with
    | inl j =>
        let i : Fin 2 := 1 - j
        have hij : i ≠ j := by fin_cases j <;> decide
        obtain ⟨p, hp⟩ := (hconn c a).exists_isPath
        let q := splitArm i p hp (Ne.symm hac)
        have hq : q.IsPath := splitArm_isPath i p hp (Ne.symm hac)
        rcases hS (.inl i) ⟨i, rfl⟩ (.inr ⟨a, hac⟩) (by simp)
            q hq with ⟨z, hzq, hz⟩
        have hzj : z = .inl j := by simpa using hz
        rcases splitArm_support_cases i p hp (Ne.symm hac) hzq with hzi | ⟨x, hxc, -, hzx⟩
        · exact hij (Sum.inl.inj (hzi.symm.trans hzj))
        · have hne : (Sum.inr ⟨x, hxc⟩ : SplitVertex c) ≠ Sum.inl j := by simp
          exact hne (hzx.symm.trans hzj)
    | inr d =>
        by_cases hda : d.1 = a
        · let t : {v : V // v ≠ d.1} := ⟨b, fun h ↦ hab (h.trans hda).symm⟩
          let c' : {v : V // v ≠ d.1} := ⟨c, Ne.symm d.2⟩
          obtain ⟨p', hp'⟩ := ((hdelete d.1) c' t).exists_isPath
          let inc := SimpleGraph.Embedding.induce (G := G) (s := fun w : V ↦ w ≠ d.1)
          let p : G.Walk c b := p'.map inc.toHom
          have hp : p.IsPath := hp'.map inc.injective
          let q := splitArm 0 p hp (Ne.symm hbc)
          have hq : q.IsPath := splitArm_isPath 0 p hp (Ne.symm hbc)
          rcases hS (.inl 0) ⟨0, rfl⟩ (.inr ⟨b, hbc⟩) (by simp)
              q hq with ⟨z, hzq, hz⟩
          have hzd : z = .inr d := by simpa using hz
          rcases splitArm_support_cases 0 p hp (Ne.symm hbc) hzq with hzi |
              ⟨x, hxc, hxp, hzx⟩
          · have hne : (Sum.inl 0 : SplitVertex c) ≠ Sum.inr d := by simp
            exact hne (hzi.symm.trans hzd)
          · have hxd : x = d.1 := by
              have hs : (⟨x, hxc⟩ : {v : V // v ≠ c}) = d :=
                Sum.inr.inj (hzx.symm.trans hzd)
              exact congrArg Subtype.val hs
            have hxavoid : x ≠ d.1 := by
              change x ∈ (p'.map inc.toHom).support at hxp
              rw [Walk.support_map] at hxp
              obtain ⟨y, hy, hyx⟩ := List.mem_map.mp hxp
              have hyx' : y.1 = x := hyx
              exact fun hxd ↦ y.2 (hyx'.trans hxd)
            exact hxavoid hxd
        · let t : {v : V // v ≠ d.1} := ⟨a, Ne.symm hda⟩
          let c' : {v : V // v ≠ d.1} := ⟨c, Ne.symm d.2⟩
          obtain ⟨p', hp'⟩ := ((hdelete d.1) c' t).exists_isPath
          let inc := SimpleGraph.Embedding.induce (G := G) (s := fun w : V ↦ w ≠ d.1)
          let p : G.Walk c a := p'.map inc.toHom
          have hp : p.IsPath := hp'.map inc.injective
          let q := splitArm 0 p hp (Ne.symm hac)
          have hq : q.IsPath := splitArm_isPath 0 p hp (Ne.symm hac)
          rcases hS (.inl 0) ⟨0, rfl⟩ (.inr ⟨a, hac⟩) (by simp)
              q hq with ⟨z, hzq, hz⟩
          have hzd : z = .inr d := by simpa using hz
          rcases splitArm_support_cases 0 p hp (Ne.symm hac) hzq with hzi |
              ⟨x, hxc, hxp, hzx⟩
          · have hne : (Sum.inl 0 : SplitVertex c) ≠ Sum.inr d := by simp
            exact hne (hzi.symm.trans hzd)
          · have hxd : x = d.1 := by
              have hs : (⟨x, hxc⟩ : {v : V // v ≠ c}) = d :=
                Sum.inr.inj (hzx.symm.trans hzd)
              exact congrArg Subtype.val hs
            have hxavoid : x ≠ d.1 := by
              change x ∈ (p'.map inc.toHom).support at hxp
              rw [Walk.support_map] at hxp
              obtain ⟨y, hy, hyx⟩ := List.mem_map.mp hxp
              have hyx' : y.1 = x := hyx
              exact fun hxd ↦ y.2 (hyx'.trans hxd)
            exact hxavoid hxd

/-! ## Collapsing the two sources and extracting the rooted path -/

/-- Collapse both split sources back to `c`. -/
def collapseSplitHom (G : SimpleGraph V) (c : V) : splitTerminalGraph G c →g G where
  toFun z := match z with | .inl _ => c | .inr x => x.1
  map_rel' := by
    rintro (i | x) (j | y) h <;> simp only at h ⊢
    · exact h.elim
    · exact h
    · exact h
    · exact h

@[simp] theorem collapseSplitHom_source (G : SimpleGraph V) (c : V) (i : Fin 2) :
    collapseSplitHom G c (.inl i) = c := rfl

@[simp] theorem collapseSplitHom_old (G : SimpleGraph V) (c : V)
    (x : {v : V // v ≠ c}) : collapseSplitHom G c (.inr x) = x.1 := rfl

private theorem Walk.IsPath.append_of_inter_eq_endpoint {W : Type*}
    {H : SimpleGraph W} {a b c : W} {p : H.Walk a b} {q : H.Walk b c}
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

/-- Universe-zero core of the three-point path theorem. -/
private theorem exists_path_between_through_type0
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hconn : G.Connected)
    (hdelete : ∀ v : V, (G.induce fun w : V ↦ w ≠ v).Connected) :
    ∃ p : G.Walk a b, p.IsPath ∧ c ∈ p.support := by
  classical
  let H := splitTerminalGraph G c
  let A := splitSources c
  let B := splitTargets ⟨a, hac⟩ ⟨b, hbc⟩
  obtain ⟨L⟩ : Nonempty (TwoABLinkage H A B) :=
    exists_twoABLinkage_of_separator_two_le H A B
      (split_separator_two_le hab hac hbc hconn hdelete)
  choose src hsrc using fun i ↦ (mem_splitSources.mp (L.left_mem i))
  have hleft (i) : L.left i = .inl (src i) := hsrc i
  have hsrcInj : Function.Injective src := by
    intro i j hij
    by_contra hne
    have hd := L.disjoint hne
    have hi : L.left i ∈ (L.path i).support := (L.path i).start_mem_support
    have hj : L.left i ∈ (L.path j).support := by
      have hleftEq : L.left i = L.left j := by
        rw [hleft i, hleft j, hij]
      rw [hleftEq]
      exact (L.path j).start_mem_support
    exact Set.disjoint_left.mp hd hi hj
  have hsrcSurj : Function.Surjective src :=
    Fintype.bijective_iff_injective_and_card src |>.mpr ⟨hsrcInj, by simp⟩ |>.2
  have source_mem_only (i : Fin 2) (j : Fin 2)
      (hj : (.inl j : SplitVertex c) ∈ (L.path i).support) :
      (.inl j : SplitVertex c) = L.left i := by
    obtain ⟨k, hk⟩ := hsrcSurj j
    by_cases hki : k = i
    · subst k
      rw [hleft i, hk]
    · have hd := L.disjoint hki
      have hkpath : (.inl j : SplitVertex c) ∈ (L.path k).support := by
        have hinl : (.inl j : SplitVertex c) = L.left k := by
          rw [hleft k, hk]
        rw [hinl]
        exact (L.path k).start_mem_support
      exact False.elim (Set.disjoint_left.mp hd hkpath hj)
  let q (i : Fin 2) : G.Walk (collapseSplitHom G c (L.left i))
      (collapseSplitHom G c (L.right i)) := (L.path i).map (collapseSplitHom G c)
  have hqPath (i : Fin 2) : (q i).IsPath := by
    change ((L.path i).map (collapseSplitHom G c)).IsPath
    rw [Walk.isPath_def, Walk.support_map]
    apply L.isPath i |>.support_nodup.map_on
    intro x hx y hy hxy
    cases x with
    | inl ix =>
        cases y with
        | inl iy =>
            exact (source_mem_only i ix hx).trans (source_mem_only i iy hy).symm
        | inr y =>
            exfalso
            exact y.2 (by simpa using hxy.symm)
    | inr x =>
        cases y with
        | inl iy =>
            exfalso
            exact x.2 (by simpa using hxy)
        | inr y =>
            exact congrArg Sum.inr (Subtype.ext (by simpa using hxy))
  have q_inter (i j : Fin 2) (hij : i ≠ j) (x : V)
      (hxi : x ∈ (q i).support) (hxj : x ∈ (q j).support) : x = c := by
    change x ∈ ((L.path i).map (collapseSplitHom G c)).support at hxi
    change x ∈ ((L.path j).map (collapseSplitHom G c)).support at hxj
    rw [Walk.support_map] at hxi hxj
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hxi
    obtain ⟨v, hv, huv⟩ := List.mem_map.mp hxj
    cases u with
    | inl iu => rfl
    | inr u =>
        cases v with
        | inl iv => exact False.elim (u.2 (by simpa using huv.symm))
        | inr v =>
            have huv' : (Sum.inr u : SplitVertex c) = .inr v := by
              congr 1
              exact Subtype.ext (by simpa using huv.symm)
            have hu' : (Sum.inr u : SplitVertex c) ∈ (L.path j).support := by
              rw [huv']
              exact hv
            exact False.elim (Set.disjoint_left.mp (L.disjoint hij) hu hu')
  have hright_ne : L.right 0 ≠ L.right 1 := by
    intro h
    have hd := L.disjoint (by decide : (0 : Fin 2) ≠ 1)
    have hright0 : L.right 0 ∈ (L.path 1).support := by
      rw [h]
      exact (L.path 1).end_mem_support
    exact Set.disjoint_left.mp hd (L.path 0).end_mem_support
      hright0
  have hr0 := mem_splitTargets.mp (L.right_mem 0)
  have hr1 := mem_splitTargets.mp (L.right_mem 1)
  have hc0 : collapseSplitHom G c (L.left 0) = c := by rw [hleft]; simp
  have hc1 : collapseSplitHom G c (L.left 1) = c := by rw [hleft]; simp
  let q0 : G.Walk c (collapseSplitHom G c (L.right 0)) := (q 0).copy hc0 rfl
  let q1 : G.Walk c (collapseSplitHom G c (L.right 1)) := (q 1).copy hc1 rfl
  have hq0 : q0.IsPath := (Walk.isPath_copy _ _ _).mpr (hqPath 0)
  have hq1 : q1.IsPath := (Walk.isPath_copy _ _ _).mpr (hqPath 1)
  let r := q0.reverse.append q1
  have hrPath : r.IsPath := by
    apply Walk.IsPath.append_of_inter_eq_endpoint hq0.reverse hq1
    intro x hx0 hx1
    have hx0' : x ∈ (q 0).support := by
      simpa [q0, Walk.support_copy, Walk.support_reverse] using hx0
    have hx1' : x ∈ (q 1).support := by simpa [q1, Walk.support_copy] using hx1
    exact q_inter 0 1 (by decide) x hx0' hx1'
  have hcr : c ∈ r.support := by
    change c ∈ (q0.reverse.append q1).support
    rw [Walk.support_append]
    exact List.mem_append.mpr <| Or.inl <| by
      simpa [Walk.support_reverse] using q0.start_mem_support
  rcases hr0 with hr0a | hr0b
  · have hr1b : L.right 1 = .inr ⟨b, hbc⟩ := hr1.resolve_left fun h ↦ hright_ne (hr0a.trans h.symm)
    let p : G.Walk a b := r.copy (by simpa [r, q0, q, hr0a]) (by simpa [r, q1, q, hr1b])
    exact ⟨p, (Walk.isPath_copy _ _ _).mpr hrPath, by simpa [p, Walk.support_copy] using hcr⟩
  · have hr1a : L.right 1 = .inr ⟨a, hac⟩ := hr1.resolve_right fun h ↦ hright_ne (hr0b.trans h.symm)
    let p : G.Walk a b := r.reverse.copy
      (by simpa [r, q1, q, hr1a]) (by simpa [r, q0, q, hr0b])
    exact ⟨p, (Walk.isPath_copy _ _ _).mpr hrPath.reverse,
      by simpa [p, Walk.support_copy, Walk.support_reverse] using hcr⟩

/-- In a finite vertex-two-connected graph, there is an `a`–`b` path through `c`.

The Menger theorem used above is stated in universe zero.  For a finite type in an arbitrary
universe, relabel the graph by `Fin (Fintype.card V)`, apply the universe-zero result, and
transport the resulting path back across the graph isomorphism. -/
theorem exists_path_between_through
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hconn : G.Connected)
    (hdelete : ∀ v : V, (G.induce fun w : V ↦ w ≠ v).Connected) :
    ∃ p : G.Walk a b, p.IsPath ∧ c ∈ p.support := by
  classical
  let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  let H : SimpleGraph (Fin (Fintype.card V)) := G.map e
  let φ : G ≃g H := SimpleGraph.Iso.map e G
  have heBij (x : Fin (Fintype.card V)) :
      Set.BijOn e {w : V | w ≠ e.symm x} {y : Fin (Fintype.card V) | y ≠ x} := by
    refine ⟨?_, e.injective.injOn, ?_⟩
    · intro w hw
      change e w ≠ x
      intro hewx
      exact hw (by simpa using congrArg e.symm hewx)
    · intro y hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      exact e.symm.injective.ne hy
  have hconnH : H.Connected := (SimpleGraph.Iso.connected_iff φ).mp hconn
  have hdeleteH (x : Fin (Fintype.card V)) :
      (H.induce fun y : Fin (Fintype.card V) ↦ y ≠ x).Connected := by
    let φx := φ.induce (heBij x)
    exact (SimpleGraph.Iso.connected_iff φx).mp (hdelete (e.symm x))
  obtain ⟨q, hq, hcq⟩ := exists_path_between_through_type0
    (G := H) (e.injective.ne hab) (e.injective.ne hac) (e.injective.ne hbc)
      hconnH hdeleteH
  let r := q.map φ.symm.toHom
  have hra : φ.symm (e a) = a := by
    change e.symm (e a) = a
    exact e.symm_apply_apply a
  have hrb : φ.symm (e b) = b := by
    change e.symm (e b) = b
    exact e.symm_apply_apply b
  let p : G.Walk a b := r.copy hra hrb
  have hrPath : r.IsPath := hq.map φ.symm.injective
  have hcr : c ∈ r.support := by
    change c ∈ (q.map φ.symm.toHom).support
    rw [Walk.support_map]
    refine List.mem_map.mpr ⟨e c, hcq, ?_⟩
    change e.symm (e c) = c
    exact e.symm_apply_apply c
  exact ⟨p, (Walk.isPath_copy _ _ _).mpr hrPath,
    by simpa [p, Walk.support_copy] using hcr⟩

/-- Rooted form: a path starting at `r`, passing through `a`, and ending at `b`. -/
theorem exists_rooted_three_path
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {r a b : V} (hra : r ≠ a) (hrb : r ≠ b) (hab : a ≠ b)
    (hconn : G.Connected)
    (hdelete : ∀ v : V, (G.induce fun w : V ↦ w ≠ v).Connected) :
    ∃ p : G.Walk r b, p.IsPath ∧ a ∈ p.support := by
  exact exists_path_between_through hrb hra (Ne.symm hab) hconn hdelete

end Erdos916
