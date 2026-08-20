/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Lifting linkages through a single safe edge contraction.

This is the elementary contraction step used in the terminal-aware
Thomas--Wollan minimal-counterexample argument.
-/

import ErdosProblems.Erdos717.DenseMinor

open Function Set
open SimpleGraph

namespace Erdos717
namespace ContractLinkage

universe u v

variable {V : Type u}

open DenseMinor

/-- A walk in `G` replacing one edge of the contracted graph, together with
the support control needed below. -/
lemma exists_liftContractAdj (G : SimpleGraph V) {a b : V} (hab : G.Adj a b)
    {x y : {z : V // z ≠ b}} (h : (contractAt G a b).Adj x y) :
    ∃ p : G.Walk (x : V) (y : V), ∀ z ∈ p.support,
      (z = b ∧ (x = ⟨a, hab.ne⟩ ∨ y = ⟨a, hab.ne⟩)) ∨
        z = (x : V) ∨ z = (y : V) := by
  rcases h.2 with hxy | hxy | hxy
  · refine ⟨hxy.toWalk, ?_⟩
    intro z hz
    simp only [Adj.toWalk, Walk.support_cons, Walk.support_nil,
      List.mem_cons] at hz
    rcases hz with hx | hy | hfalse
    · exact Or.inr (Or.inl hx)
    · exact Or.inr (Or.inr hy)
    · contradiction
  · rcases hxy with ⟨hx, hby⟩
    have hx' : x = ⟨a, hab.ne⟩ := Subtype.ext hx
    subst x
    refine ⟨hab.toWalk.concat hby, ?_⟩
    intro z hz
    simp only [Adj.toWalk, Walk.support_concat, Walk.support_cons,
      Walk.support_nil, List.mem_append, List.mem_cons,
      List.mem_singleton] at hz
    rcases hz with ((rfl | rfl | hfalse) | rfl | hfalse)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl ⟨rfl, Or.inl rfl⟩
    · contradiction
    · exact Or.inr (Or.inr rfl)
    · contradiction
  · rcases hxy with ⟨hy, hbx⟩
    have hy' : y = ⟨a, hab.ne⟩ := Subtype.ext hy
    subst y
    refine ⟨hbx.symm.toWalk.concat hab.symm, ?_⟩
    intro z hz
    simp only [Adj.toWalk, Walk.support_concat, Walk.support_cons,
      Walk.support_nil, List.mem_append, List.mem_cons,
      List.mem_singleton] at hz
    rcases hz with ((rfl | rfl | hfalse) | rfl | hfalse)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl ⟨rfl, Or.inr rfl⟩
    · contradiction
    · exact Or.inr (Or.inr rfl)
    · contradiction

noncomputable def liftContractAdj (G : SimpleGraph V) {a b : V}
    (hab : G.Adj a b) {x y : {z : V // z ≠ b}}
    (h : (contractAt G a b).Adj x y) : G.Walk (x : V) (y : V) :=
  Classical.choose (exists_liftContractAdj G hab h)

/-- Replace each contracted edge of a walk by its one- or two-edge lift. -/
noncomputable def liftContractWalk (G : SimpleGraph V) {a b : V} (hab : G.Adj a b) :
    {x y : {z : V // z ≠ b}} →
      (contractAt G a b).Walk x y → G.Walk (x : V) (y : V)
  | _, _, .nil => .nil
  | _, _, .cons h p =>
      (liftContractAdj G hab h).append (liftContractWalk G hab p)

lemma support_liftContractAdj {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b) {x y : {z : V // z ≠ b}}
    (h : (contractAt G a b).Adj x y) {z : V}
    (hz : z ∈ (liftContractAdj G hab h).support) :
    (z = b ∧ (x = ⟨a, hab.ne⟩ ∨ y = ⟨a, hab.ne⟩)) ∨
      z = (x : V) ∨ z = (y : V) := by
  exact Classical.choose_spec (exists_liftContractAdj G hab h) z hz

/-- Every lifted vertex is either the deleted endpoint `b` (in which case
the contracted walk visits `a`) or the image of a vertex of the contracted
walk. -/
lemma support_liftContractWalk {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b) {x y : {z : V // z ≠ b}}
    (p : (contractAt G a b).Walk x y) {z : V}
    (hz : z ∈ (liftContractWalk G hab p).support) :
    (z = b ∧ (⟨a, hab.ne⟩ : {z : V // z ≠ b}) ∈ p.support) ∨
      ∃ w ∈ p.support, (w : V) = z := by
  induction p with
  | nil =>
      simp only [liftContractWalk, Walk.support_nil, List.mem_singleton] at hz
      exact Or.inr ⟨_, by simp, hz.symm⟩
  | @cons x q y h pq ih =>
      rw [liftContractWalk, Walk.mem_support_append_iff] at hz
      rcases hz with hz | hz
      · rcases support_liftContractAdj hab h hz with hb | hx | hq
        · exact Or.inl ⟨hb.1, by
            simp only [Walk.support_cons, List.mem_cons]
            exact hb.2.elim (fun ha => Or.inl ha.symm) (fun ha => Or.inr (by
              rw [← ha]
              exact pq.start_mem_support))⟩
        · exact Or.inr ⟨x, by simp, hx.symm⟩
        · exact Or.inr ⟨q, by simp, hq.symm⟩
      · rcases ih hz with hb | hw
        · exact Or.inl ⟨hb.1, by
            simp only [Walk.support_cons, List.mem_cons]
            exact Or.inr hb.2⟩
        · rcases hw with ⟨w, hwp, hwz⟩
          exact Or.inr ⟨w, by
            simp only [Walk.support_cons, List.mem_cons]
            exact Or.inr hwp, hwz⟩

/-- The contracted terminal embedding, defined when the deleted endpoint is
not a terminal. -/
def contractTerminal {ι : Type v} {G : SimpleGraph V} {a b : V}
    (terminal : Sum ι ι ↪ V) (hb : b ∉ Set.range terminal) :
    Sum ι ι ↪ {z : V // z ≠ b} where
  toFun z := ⟨terminal z, fun h => hb ⟨z, h⟩⟩
  inj' := by
    intro x y h
    exact terminal.injective (congrArg Subtype.val h)

@[simp] lemma contractTerminal_coe {ι : Type v} {G : SimpleGraph V}
    {a b : V} (terminal : Sum ι ι ↪ V)
    (hb : b ∉ Set.range terminal) (z : Sum ι ι) :
    ((contractTerminal (G := G) (a := a) terminal hb z :
      {z : V // z ≠ b}) : V) = terminal z := rfl

/-- A linkage for the contracted terminal problem lifts to the original
graph.  Loop erasure is applied separately to each lifted walk; its support
only shrinks. -/
noncomputable def Erdos718.PairLinkage.liftContract {ι : Type v} [Fintype ι]
    [DecidableEq V]
    {G : SimpleGraph V} {a b : V} (hab : G.Adj a b)
    (terminal : Sum ι ι ↪ V) (hb : b ∉ Set.range terminal)
    (L : Erdos718.PairLinkage (contractAt G a b)
      (Set.range (contractTerminal (G := G) (a := a) terminal hb))
      (contractTerminal (G := G) (a := a) terminal hb)) :
    Erdos718.PairLinkage G (Set.range terminal) terminal where
  path i := ((liftContractWalk G hab (L.path i)).toPath :
      G.Walk _ _).copy
        (contractTerminal_coe (G := G) (a := a) terminal hb (.inl i))
        (contractTerminal_coe (G := G) (a := a) terminal hb (.inr i))
  isPath i := by
    simpa only [Walk.isPath_copy] using
      (liftContractWalk G hab (L.path i)).toPath.isPath
  avoids i := by
    rw [Set.disjoint_left]
    intro z hz hterminal
    have hzsupport : z ∈ (liftContractWalk G hab (L.path i)).support :=
      Walk.support_toPath_subset_support _ hz.1
    rcases support_liftContractWalk hab (L.path i) hzsupport with hbcase | hw
    · apply hb
      rwa [← hbcase.1]
    · obtain ⟨w, hwp, hwz⟩ := hw
      have hwstart : w ≠ contractTerminal (G := G) (a := a) terminal hb (.inl i) := by
        intro h
        apply hz.2.1
        rw [← hwz, h]
        rfl
      have hwend : w ≠ contractTerminal (G := G) (a := a) terminal hb (.inr i) := by
        intro h
        apply hz.2.2
        rw [← hwz, h]
        rfl
      have hwinterior : w ∈ Erdos718.walkInteriorSet (L.path i) :=
        ⟨hwp, hwstart, hwend⟩
      have hwterminal : w ∈ Set.range
          (contractTerminal (G := G) (a := a) terminal hb) := by
        obtain ⟨t, htz⟩ := hterminal
        exact ⟨t, Subtype.ext (by simpa [htz] using hwz.symm)⟩
      exact (Set.disjoint_left.mp (L.avoids i)) hwinterior hwterminal
  disjoint i j hij := by
    dsimp only
    rw [Set.disjoint_left]
    intro z hzi hzj
    rw [Walk.support_copy] at hzi hzj
    have hzi' : z ∈ (liftContractWalk G hab (L.path i)).support :=
      Walk.support_toPath_subset_support _ hzi
    have hzj' : z ∈ (liftContractWalk G hab (L.path j)).support :=
      Walk.support_toPath_subset_support _ hzj
    rcases support_liftContractWalk hab (L.path i) hzi' with hbi | hwi
    · rcases support_liftContractWalk hab (L.path j) hzj' with hbj | hwj
      · exact (Set.disjoint_left.mp (L.disjoint hij)) hbi.2 hbj.2
      · obtain ⟨w, _hwj, hwz⟩ := hwj
        exact w.2 (hwz.trans hbi.1)
    · rcases support_liftContractWalk hab (L.path j) hzj' with hbj | hwj
      · obtain ⟨w, _hwi, hwz⟩ := hwi
        exact w.2 (hwz.trans hbj.1)
      · obtain ⟨wi, hwi, hwiz⟩ := hwi
        obtain ⟨wj, hwj, hwjz⟩ := hwj
        have hwij : wi = wj := Subtype.ext (hwiz.trans hwjz.symm)
        subst wj
        exact (Set.disjoint_left.mp (L.disjoint hij)) hwi hwj

theorem nonempty_pairLinkage_of_contract {ι : Type v} [Fintype ι]
    [DecidableEq V]
    {G : SimpleGraph V} {a b : V} (hab : G.Adj a b)
    (terminal : Sum ι ι ↪ V) (hb : b ∉ Set.range terminal)
    (h : Nonempty (Erdos718.PairLinkage (contractAt G a b)
      (Set.range (contractTerminal (G := G) (a := a) terminal hb))
      (contractTerminal (G := G) (a := a) terminal hb))) :
    Nonempty (Erdos718.PairLinkage G (Set.range terminal) terminal) :=
  h.map fun L => Erdos718.PairLinkage.liftContract hab terminal hb L

/-- The image of a vertex set in the contracted vertex type, when the
deleted endpoint is outside that set. -/
def contractSet {b : V} (X : Set V) : Set {z : V // z ≠ b} :=
  {z | (z : V) ∈ X}

/-- Lifting through a safe contraction while retaining an arbitrary
forbidden set containing the terminals. -/
noncomputable def Erdos718.PairLinkage.liftContractOfSubset
    {ι : Type v} [Fintype ι] [DecidableEq V]
    {G : SimpleGraph V} {a b : V} (hab : G.Adj a b)
    {X : Set V} (terminal : Sum ι ι ↪ V)
    (hterminal : Set.range terminal ⊆ X) (hb : b ∉ X)
    (L : Erdos718.PairLinkage (contractAt G a b) (contractSet X)
      (contractTerminal (G := G) (a := a) terminal
        (fun hbRange => hb (hterminal hbRange)))) :
    Erdos718.PairLinkage G X terminal where
  path i := ((liftContractWalk G hab (L.path i)).toPath :
      G.Walk _ _).copy
        (contractTerminal_coe (G := G) (a := a) terminal
          (fun hbRange => hb (hterminal hbRange)) (.inl i))
        (contractTerminal_coe (G := G) (a := a) terminal
          (fun hbRange => hb (hterminal hbRange)) (.inr i))
  isPath i := by
    simpa only [Walk.isPath_copy] using
      (liftContractWalk G hab (L.path i)).toPath.isPath
  avoids i := by
    rw [Set.disjoint_left]
    intro z hz hzX
    have hzsupport : z ∈ (liftContractWalk G hab (L.path i)).support :=
      Walk.support_toPath_subset_support _ hz.1
    rcases support_liftContractWalk hab (L.path i) hzsupport with hbcase | hw
    · exact hb (hbcase.1 ▸ hzX)
    · obtain ⟨w, hwp, hwz⟩ := hw
      have hwstart : w ≠ contractTerminal (G := G) (a := a) terminal
          (fun hbRange => hb (hterminal hbRange)) (.inl i) := by
        intro h
        apply hz.2.1
        rw [← hwz, h]
        rfl
      have hwend : w ≠ contractTerminal (G := G) (a := a) terminal
          (fun hbRange => hb (hterminal hbRange)) (.inr i) := by
        intro h
        apply hz.2.2
        rw [← hwz, h]
        rfl
      have hwinterior : w ∈ Erdos718.walkInteriorSet (L.path i) :=
        ⟨hwp, hwstart, hwend⟩
      have hwX : w ∈ contractSet X := by
        change (w : V) ∈ X
        rwa [hwz]
      exact (Set.disjoint_left.mp (L.avoids i)) hwinterior hwX
  disjoint i j hij := by
    dsimp only
    rw [Set.disjoint_left]
    intro z hzi hzj
    rw [Walk.support_copy] at hzi hzj
    have hzi' : z ∈ (liftContractWalk G hab (L.path i)).support :=
      Walk.support_toPath_subset_support _ hzi
    have hzj' : z ∈ (liftContractWalk G hab (L.path j)).support :=
      Walk.support_toPath_subset_support _ hzj
    rcases support_liftContractWalk hab (L.path i) hzi' with hbi | hwi
    · rcases support_liftContractWalk hab (L.path j) hzj' with hbj | hwj
      · exact (Set.disjoint_left.mp (L.disjoint hij)) hbi.2 hbj.2
      · obtain ⟨w, _hwj, hwz⟩ := hwj
        exact w.2 (hwz.trans hbi.1)
    · rcases support_liftContractWalk hab (L.path j) hzj' with hbj | hwj
      · obtain ⟨w, _hwi, hwz⟩ := hwi
        exact w.2 (hwz.trans hbj.1)
      · obtain ⟨wi, hwi, hwiz⟩ := hwi
        obtain ⟨wj, hwj, hwjz⟩ := hwj
        have hwij : wi = wj := Subtype.ext (hwiz.trans hwjz.symm)
        subst wj
        exact (Set.disjoint_left.mp (L.disjoint hij)) hwi hwj

theorem nonempty_pairLinkage_of_contract_of_subset
    {ι : Type v} [Fintype ι] [DecidableEq V]
    {G : SimpleGraph V} {a b : V} (hab : G.Adj a b)
    {X : Set V} (terminal : Sum ι ι ↪ V)
    (hterminal : Set.range terminal ⊆ X) (hb : b ∉ X)
    (h : Nonempty (Erdos718.PairLinkage (contractAt G a b)
      (contractSet X)
      (contractTerminal (G := G) (a := a) terminal
        (fun hbRange => hb (hterminal hbRange))))) :
    Nonempty (Erdos718.PairLinkage G X terminal) :=
  h.map fun L =>
    Erdos717.ContractLinkage.Erdos718.PairLinkage.liftContractOfSubset
      hab terminal hterminal hb L

end ContractLinkage
end Erdos717
