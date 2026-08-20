/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Expanding linkages from a completed separation torso. -/

import ErdosProblems.Erdos717.TorsoLinkage

open Function Set
open SimpleGraph

namespace Erdos717
namespace ThomasWollanMassed

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The inclusion of the graph induced by the right side of a separation. -/
def induceRightToGraph {G : SimpleGraph V} (s : Erdos718.Separation G) :
    G.induce (s.right : Set V) →g G where
  toFun := Subtype.val
  map_rel' := fun {_ _} h => h

/-- Expand the final `d` edges of one path in a left-torso linkage.  An
ordinary torso edge is an edge of `G`; a virtual edge in the completed
separator is replaced by the corresponding path in the linked right side. -/
noncomputable def expandTorsoPathAux
    {J : Type} [Fintype J] {G : SimpleGraph V}
    (s : Erdos718.Separation G)
    {X : Set (s.left : Set V)}
    {terminal : Sum J J ↪ (s.left : Set V)}
    (L : Erdos718.PairLinkage (leftTorso s) X terminal)
    (hnoTriple : HasNoSeparatorTriple s L)
    (M : Erdos718.PairLinkage (G.induce (s.right : Set V))
      (rightSeparator s : Set (s.right : Set V))
      (separatorEdgeTerminal s L hnoTriple))
    (i : J) : ∀ d n : ℕ, n + d = (L.path i).length →
      G.Walk ((L.path i).getVert n : V)
        ((L.path i).getVert (L.path i).length : V)
  | 0, n, hnd => by
      have hn : n = (L.path i).length := by omega
      exact Walk.nil.copy rfl (congrArg (fun m =>
        ((L.path i).getVert m : V)) hn)
  | d + 1, n, hnd => by
      have hnlt : n < (L.path i).length := by omega
      have hnext : n + 1 + d = (L.path i).length := by omega
      by_cases hs :
          ((L.path i).getVert n : V) ∈ s.separator ∧
            ((L.path i).getVert (n + 1) : V) ∈ s.separator
      · let o : SeparatorEdgeOccurrence s L :=
          ⟨⟨i, ⟨n, hnlt⟩⟩, hs⟩
        let q := (M.path o).map (induceRightToGraph s)
        have hqStart :
            (separatorEdgeTerminal s L hnoTriple (.inl o) : V) =
              ((L.path i).getVert n : V) := by rfl
        have hqEnd :
            (separatorEdgeTerminal s L hnoTriple (.inr o) : V) =
              ((L.path i).getVert (n + 1) : V) := by rfl
        let q' : G.Walk ((L.path i).getVert n : V)
            ((L.path i).getVert (n + 1) : V) := q.copy hqStart hqEnd
        exact q'.append (expandTorsoPathAux s L hnoTriple M i d (n + 1) hnext)
      · have htorso := (L.path i).adj_getVert_succ hnlt
        have hG : G.Adj ((L.path i).getVert n : V)
            ((L.path i).getVert (n + 1) : V) :=
          (leftTorso_adj_iff.mp htorso).resolve_right fun hsep =>
            hs ⟨hsep.1, hsep.2.1⟩
        exact (expandTorsoPathAux s L hnoTriple M i d (n + 1) hnext).cons hG

/-- Expand a whole torso path to a walk in the original graph. -/
noncomputable def expandTorsoPath
    {J : Type} [Fintype J] {G : SimpleGraph V}
    (s : Erdos718.Separation G)
    {X : Set (s.left : Set V)}
    {terminal : Sum J J ↪ (s.left : Set V)}
    (L : Erdos718.PairLinkage (leftTorso s) X terminal)
    (hnoTriple : HasNoSeparatorTriple s L)
    (M : Erdos718.PairLinkage (G.induce (s.right : Set V))
      (rightSeparator s : Set (s.right : Set V))
      (separatorEdgeTerminal s L hnoTriple))
    (i : J) : G.Walk (terminal (.inl i) : V) (terminal (.inr i) : V) := by
  exact (expandTorsoPathAux s L hnoTriple M i
    (L.path i).length 0 (by omega)).copy
    (by simpa using congrArg Subtype.val (L.path i).getVert_zero)
    (by simpa using congrArg Subtype.val (L.path i).getVert_length)

/-- Vertices that are permitted to occur while expanding path `i`: either
an original vertex of the torso path, or a vertex of a right-side path used
to replace a virtual edge of that same torso path. -/
def TorsoExpansionAllowed
    {J : Type} [Fintype J] {G : SimpleGraph V}
    (s : Erdos718.Separation G)
    {X : Set (s.left : Set V)}
    {terminal : Sum J J ↪ (s.left : Set V)}
    (L : Erdos718.PairLinkage (leftTorso s) X terminal)
    (hnoTriple : HasNoSeparatorTriple s L)
    (M : Erdos718.PairLinkage (G.induce (s.right : Set V))
      (rightSeparator s : Set (s.right : Set V))
      (separatorEdgeTerminal s L hnoTriple))
    (i : J) (x : V) : Prop :=
  (∃ y ∈ (L.path i).support, (y : V) = x) ∨
    ∃ o : SeparatorEdgeOccurrence s L,
      o.1.1 = i ∧
        x ∈ ((M.path o).map (induceRightToGraph s)).support

theorem mem_support_expandTorsoPathAux_allowed
    {J : Type} [Fintype J] {G : SimpleGraph V}
    (s : Erdos718.Separation G)
    {X : Set (s.left : Set V)}
    {terminal : Sum J J ↪ (s.left : Set V)}
    (L : Erdos718.PairLinkage (leftTorso s) X terminal)
    (hnoTriple : HasNoSeparatorTriple s L)
    (M : Erdos718.PairLinkage (G.induce (s.right : Set V))
      (rightSeparator s : Set (s.right : Set V))
      (separatorEdgeTerminal s L hnoTriple))
    (i : J) (d n : ℕ) (hnd : n + d = (L.path i).length)
    {x : V}
    (hx : x ∈ (expandTorsoPathAux s L hnoTriple M i d n hnd).support) :
    TorsoExpansionAllowed s L hnoTriple M i x := by
  induction d generalizing n with
  | zero =>
      simp only [expandTorsoPathAux, Walk.support_copy,
        Walk.support_nil, List.mem_singleton] at hx
      left
      refine ⟨(L.path i).getVert n,
        (L.path i).getVert_mem_support n, ?_⟩
      exact hx.symm
  | succ d ih =>
      have hnlt : n < (L.path i).length := by omega
      have hnext : n + 1 + d = (L.path i).length := by omega
      by_cases hs :
          ((L.path i).getVert n : V) ∈ s.separator ∧
            ((L.path i).getVert (n + 1) : V) ∈ s.separator
      · let o : SeparatorEdgeOccurrence s L :=
          ⟨⟨i, ⟨n, hnlt⟩⟩, hs⟩
        let q := (M.path o).map (induceRightToGraph s)
        let q' : G.Walk ((L.path i).getVert n : V)
            ((L.path i).getVert (n + 1) : V) := q.copy rfl rfl
        have hx' : x ∈ q'.support ∨
            x ∈ (expandTorsoPathAux s L hnoTriple M i d (n + 1) hnext).support := by
          simp [expandTorsoPathAux, hs, Walk.support_append] at hx
          exact hx.imp_right List.mem_of_mem_tail
        rcases hx' with hxq | hxrest
        · right
          refine ⟨o, rfl, ?_⟩
          have hsupport : q'.support = q.support := by
            exact Walk.support_copy q rfl rfl
          rw [hsupport] at hxq
          exact hxq
        · exact ih (n + 1) hnext hxrest
      · have hx' : x = ((L.path i).getVert n : V) ∨
            x ∈ (expandTorsoPathAux s L hnoTriple M i d (n + 1) hnext).support := by
          simpa [expandTorsoPathAux, hs] using hx
        rcases hx' with rfl | hxrest
        · left
          exact ⟨(L.path i).getVert n,
            (L.path i).getVert_mem_support n, rfl⟩
        · exact ih (n + 1) hnext hxrest

theorem mem_support_expandTorsoPath_allowed
    {J : Type} [Fintype J] {G : SimpleGraph V}
    (s : Erdos718.Separation G)
    {X : Set (s.left : Set V)}
    {terminal : Sum J J ↪ (s.left : Set V)}
    (L : Erdos718.PairLinkage (leftTorso s) X terminal)
    (hnoTriple : HasNoSeparatorTriple s L)
    (M : Erdos718.PairLinkage (G.induce (s.right : Set V))
      (rightSeparator s : Set (s.right : Set V))
      (separatorEdgeTerminal s L hnoTriple))
    (i : J) {x : V} (hx : x ∈ (expandTorsoPath s L hnoTriple M i).support) :
    TorsoExpansionAllowed s L hnoTriple M i x := by
  apply mem_support_expandTorsoPathAux_allowed s L hnoTriple M i
    (L.path i).length 0 (by omega)
  simpa only [expandTorsoPath, Walk.support_copy] using hx

lemma mem_right_of_mem_central_support
    {J : Type} [Fintype J] {G : SimpleGraph V}
    (s : Erdos718.Separation G)
    {X : Set (s.left : Set V)}
    {terminal : Sum J J ↪ (s.left : Set V)}
    (L : Erdos718.PairLinkage (leftTorso s) X terminal)
    (hnoTriple : HasNoSeparatorTriple s L)
    (M : Erdos718.PairLinkage (G.induce (s.right : Set V))
      (rightSeparator s : Set (s.right : Set V))
      (separatorEdgeTerminal s L hnoTriple))
    (o : SeparatorEdgeOccurrence s L) {x : V}
    (hx : x ∈ ((M.path o).map (induceRightToGraph s)).support) :
    x ∈ s.right := by
  rw [Walk.support_map] at hx
  obtain ⟨z, _hz, hzx⟩ := List.mem_map.mp hx
  change (z : V) = x at hzx
  exact hzx ▸ z.property

/-- A right-side replacement path meets the separator only at its two
prescribed endpoints. -/
lemma central_support_eq_virtual_endpoint_of_mem_separator
    {J : Type} [Fintype J] {G : SimpleGraph V}
    (s : Erdos718.Separation G)
    {X : Set (s.left : Set V)}
    {terminal : Sum J J ↪ (s.left : Set V)}
    (L : Erdos718.PairLinkage (leftTorso s) X terminal)
    (hnoTriple : HasNoSeparatorTriple s L)
    (M : Erdos718.PairLinkage (G.induce (s.right : Set V))
      (rightSeparator s : Set (s.right : Set V))
      (separatorEdgeTerminal s L hnoTriple))
    (o : SeparatorEdgeOccurrence s L) {x : V}
    (hx : x ∈ ((M.path o).map (induceRightToGraph s)).support)
    (hxsep : x ∈ s.separator) :
    x = ((L.path o.1.1).getVert o.1.2 : V) ∨
      x = ((L.path o.1.1).getVert (o.1.2 + 1) : V) := by
  rw [Walk.support_map] at hx
  obtain ⟨z, hz, hzx⟩ := List.mem_map.mp hx
  change (z : V) = x at hzx
  have hzsep : (z : V) ∈ s.separator := by simpa only [hzx] using hxsep
  have hzrightSep : z ∈ (rightSeparator s : Set (s.right : Set V)) := by
    change z ∈ rightSeparator s
    exact (mem_rightSeparator s z).2 hzsep
  by_cases hstart : z = separatorEdgeTerminal s L hnoTriple (.inl o)
  · left
    calc
      x = (z : V) := hzx.symm
      _ = (separatorEdgeTerminal s L hnoTriple (.inl o) : V) :=
        congrArg Subtype.val hstart
      _ = ((L.path o.1.1).getVert o.1.2 : V) := by rfl
  by_cases hend : z = separatorEdgeTerminal s L hnoTriple (.inr o)
  · right
    calc
      x = (z : V) := hzx.symm
      _ = (separatorEdgeTerminal s L hnoTriple (.inr o) : V) :=
        congrArg Subtype.val hend
      _ = ((L.path o.1.1).getVert (o.1.2 + 1) : V) := by rfl
  · have hinterior : z ∈ Erdos718.walkInteriorSet (M.path o) :=
      ⟨hz, hstart, hend⟩
    exact (Set.disjoint_left.mp (M.avoids o) hinterior hzrightSep).elim

theorem torsoExpansionAllowed_disjoint
    {J : Type} [Fintype J] {G : SimpleGraph V}
    (s : Erdos718.Separation G)
    {X : Set (s.left : Set V)}
    {terminal : Sum J J ↪ (s.left : Set V)}
    (L : Erdos718.PairLinkage (leftTorso s) X terminal)
    (hnoTriple : HasNoSeparatorTriple s L)
    (M : Erdos718.PairLinkage (G.induce (s.right : Set V))
      (rightSeparator s : Set (s.right : Set V))
      (separatorEdgeTerminal s L hnoTriple))
    {i j : J} (hij : i ≠ j) {x : V}
    (hxi : TorsoExpansionAllowed s L hnoTriple M i x)
    (hxj : TorsoExpansionAllowed s L hnoTriple M j x) : False := by
  rcases hxi with ⟨yi, hyi, hyix⟩ | ⟨oi, hoi, hxi⟩ <;>
    rcases hxj with ⟨yj, hyj, hyjx⟩ | ⟨oj, hoj, hxj⟩
  · have hyy : yi = yj := Subtype.ext (hyix.trans hyjx.symm)
    exact (Set.disjoint_left.mp (L.disjoint hij) hyi (hyy ▸ hyj)).elim
  · have hxright := mem_right_of_mem_central_support s L hnoTriple M oj hxj
    have hxleft : x ∈ (s.left : Set V) := by
      rw [← hyix]
      exact yi.property
    have hxsep : x ∈ (s.separator : Set V) := by
      change x ∈ s.separator
      rw [Erdos718.Separation.separator, Finset.mem_inter]
      exact ⟨hxleft, hxright⟩
    rcases central_support_eq_virtual_endpoint_of_mem_separator
      s L hnoTriple M oj hxj hxsep with hx0 | hx1
    · have hyend : yi = (L.path j).getVert oj.1.2 := by
        apply Subtype.ext
        have hget := congrArg (fun r =>
          ((L.path r).getVert (oj.1.2 : ℕ) : V)) hoj
        exact hyix.trans (hx0.trans hget)
      exact (Set.disjoint_left.mp (L.disjoint hij) hyi
        (hyend ▸ (L.path j).getVert_mem_support oj.1.2)).elim
    · have hyend : yi = (L.path j).getVert (oj.1.2 + 1) := by
        apply Subtype.ext
        have hget := congrArg (fun r =>
          ((L.path r).getVert ((oj.1.2 : ℕ) + 1) : V)) hoj
        exact hyix.trans (hx1.trans hget)
      exact (Set.disjoint_left.mp (L.disjoint hij) hyi
        (hyend ▸ (L.path j).getVert_mem_support (oj.1.2 + 1))).elim
  · have hxright := mem_right_of_mem_central_support s L hnoTriple M oi hxi
    have hxleft : x ∈ (s.left : Set V) := by
      rw [← hyjx]
      exact yj.property
    have hxsep : x ∈ (s.separator : Set V) := by
      change x ∈ s.separator
      rw [Erdos718.Separation.separator, Finset.mem_inter]
      exact ⟨hxleft, hxright⟩
    rcases central_support_eq_virtual_endpoint_of_mem_separator
      s L hnoTriple M oi hxi hxsep with hx0 | hx1
    · have hyend : (L.path i).getVert oi.1.2 = yj := by
        apply Subtype.ext
        have hget := congrArg (fun r =>
          ((L.path r).getVert (oi.1.2 : ℕ) : V)) hoi
        exact hget.symm.trans (hx0.symm.trans hyjx.symm)
      exact (Set.disjoint_left.mp (L.disjoint hij)
        ((L.path i).getVert_mem_support oi.1.2)
        (hyend ▸ hyj)).elim
    · have hyend : (L.path i).getVert (oi.1.2 + 1) = yj := by
        apply Subtype.ext
        have hget := congrArg (fun r =>
          ((L.path r).getVert ((oi.1.2 : ℕ) + 1) : V)) hoi
        exact hget.symm.trans (hx1.symm.trans hyjx.symm)
      exact (Set.disjoint_left.mp (L.disjoint hij)
        ((L.path i).getVert_mem_support (oi.1.2 + 1))
        (hyend ▸ hyj)).elim
  · have hoine : oi ≠ oj := by
      intro h
      apply hij
      rw [← hoi, ← hoj, h]
    have hd : Disjoint {v | v ∈ (M.path oi).support}
        {v | v ∈ (M.path oj).support} := M.disjoint hoine
    rw [Set.disjoint_left] at hd
    rw [Walk.support_map] at hxi hxj
    obtain ⟨zi, hzi, hzix⟩ := List.mem_map.mp hxi
    obtain ⟨zj, hzj, hzjx⟩ := List.mem_map.mp hxj
    have hzz : zi = zj := by
      apply Subtype.ext
      change (zi : V) = (zj : V)
      change (zi : V) = x at hzix
      change (zj : V) = x at hzjx
      exact hzix.trans hzjx.symm
    exact (hd hzi (hzz ▸ hzj)).elim

/-- Regard terminals in the left side of a separation as terminals of the
ambient graph. -/
def leftTerminalToGraph
    {J : Type} {G : SimpleGraph V} (s : Erdos718.Separation G)
    (terminal : Sum J J ↪ (s.left : Set V)) : Sum J J ↪ V :=
  terminal.trans (Function.Embedding.subtype _)

@[simp] lemma leftTerminalToGraph_apply
    {J : Type} {G : SimpleGraph V} (s : Erdos718.Separation G)
    (terminal : Sum J J ↪ (s.left : Set V)) (z : Sum J J) :
    leftTerminalToGraph s terminal z = (terminal z : V) := rfl

/-- Regard a set of vertices of the left side as a set of vertices of the
ambient graph. -/
def liftLeftSet {G : SimpleGraph V} (s : Erdos718.Separation G)
    (X : Set (s.left : Set V)) : Set V :=
  {x | ∃ y ∈ X, (y : V) = x}

/-- Expand one fixed torso linkage, using one fixed linkage of all its
virtual separator edges through the right side. -/
noncomputable def Erdos718.PairLinkage.expandLeftTorso
    {J : Type} [Fintype J] {G : SimpleGraph V}
    (s : Erdos718.Separation G)
    {X : Set (s.left : Set V)}
    {terminal : Sum J J ↪ (s.left : Set V)}
    (L : Erdos718.PairLinkage (leftTorso s) X terminal)
    (hnoTriple : HasNoSeparatorTriple s L)
    (M : Erdos718.PairLinkage (G.induce (s.right : Set V))
      (rightSeparator s : Set (s.right : Set V))
      (separatorEdgeTerminal s L hnoTriple)) :
    Erdos718.PairLinkage G (liftLeftSet s X)
      (leftTerminalToGraph s terminal) := by
  classical
  let q (i : J) := expandTorsoPath s L hnoTriple M i
  let p (i : J) : G.Walk
      (leftTerminalToGraph s terminal (.inl i))
      (leftTerminalToGraph s terminal (.inr i)) :=
    ((q i).toPath : G.Walk (terminal (.inl i) : V)
      (terminal (.inr i) : V)).copy
        (leftTerminalToGraph_apply s terminal (.inl i)).symm
        (leftTerminalToGraph_apply s terminal (.inr i)).symm
  refine {
    path := p
    isPath := fun i => by
      change (p i).IsPath
      dsimp only [p]
      rw [Walk.isPath_copy]
      exact (q i).toPath.property
    avoids := ?_
    disjoint := ?_
  }
  · intro i
    rw [Set.disjoint_left]
    intro x hx hxterminal
    have hxsuppQ : x ∈ (q i).support :=
      (q i).support_toPath_subset_support (by
        simpa only [p, Walk.support_copy] using hx.1)
    have hxallowed := mem_support_expandTorsoPath_allowed
      s L hnoTriple M i (by simpa only [q] using hxsuppQ)
    obtain ⟨yX, hyXX, hyXx⟩ := hxterminal
    have hxstart : x ≠ (terminal (.inl i) : V) := by
      simpa only [leftTerminalToGraph_apply] using hx.2.1
    have hxend : x ≠ (terminal (.inr i) : V) := by
      simpa only [leftTerminalToGraph_apply] using hx.2.2
    have original_contra (y : (s.left : Set V))
        (hysupp : y ∈ (L.path i).support) (hyx : (y : V) = x) : False := by
      have hyinterior : y ∈ Erdos718.walkInteriorSet (L.path i) := by
        refine ⟨hysupp, ?_, ?_⟩
        · intro hy
          subst y
          exact hxstart hyx.symm
        · intro hy
          subst y
          exact hxend hyx.symm
      have hyX : y ∈ X := by
        have hyyX : y = yX := Subtype.ext (hyx.trans hyXx.symm)
        exact hyyX ▸ hyXX
      exact (Set.disjoint_left.mp (L.avoids i) hyinterior hyX).elim
    rcases hxallowed with ⟨y, hysupp, hyx⟩ | ⟨o, hoi, hxo⟩
    · exact original_contra y hysupp hyx
    · have hxright := mem_right_of_mem_central_support
        s L hnoTriple M o hxo
      have hxleft : x ∈ (s.left : Set V) := by
        rw [← hyXx]
        exact yX.property
      have hxsep : x ∈ (s.separator : Set V) := by
        change x ∈ s.separator
        rw [Erdos718.Separation.separator, Finset.mem_inter]
        exact ⟨hxleft, hxright⟩
      rcases central_support_eq_virtual_endpoint_of_mem_separator
        s L hnoTriple M o hxo hxsep with hx0 | hx1
      · have hget := congrArg (fun r =>
          ((L.path r).getVert (o.1.2 : ℕ) : V)) hoi
        apply original_contra ((L.path i).getVert o.1.2)
          ((L.path i).getVert_mem_support o.1.2)
        exact hget.symm.trans hx0.symm
      · have hget := congrArg (fun r =>
          ((L.path r).getVert ((o.1.2 : ℕ) + 1) : V)) hoi
        apply original_contra ((L.path i).getVert (o.1.2 + 1))
          ((L.path i).getVert_mem_support (o.1.2 + 1))
        exact hget.symm.trans hx1.symm
  · intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    change x ∈ (p i).support at hxi
    change x ∈ (p j).support at hxj
    have hxiQ : x ∈ (q i).support :=
      (q i).support_toPath_subset_support
        (by simpa only [p, Walk.support_copy] using hxi)
    have hxjQ : x ∈ (q j).support :=
      (q j).support_toPath_subset_support
        (by simpa only [p, Walk.support_copy] using hxj)
    exact torsoExpansionAllowed_disjoint s L hnoTriple M hij
      (mem_support_expandTorsoPath_allowed s L hnoTriple M i
        (by simpa only [q] using hxiQ))
      (mem_support_expandTorsoPath_allowed s L hnoTriple M j
        (by simpa only [q] using hxjQ))

lemma Erdos718.PairLinkage.support_expandLeftTorso_allowed
    {J : Type} [Fintype J] {G : SimpleGraph V}
    (s : Erdos718.Separation G)
    {X : Set (s.left : Set V)}
    {terminal : Sum J J ↪ (s.left : Set V)}
    (L : Erdos718.PairLinkage (leftTorso s) X terminal)
    (hnoTriple : HasNoSeparatorTriple s L)
    (M : Erdos718.PairLinkage (G.induce (s.right : Set V))
      (rightSeparator s : Set (s.right : Set V))
      (separatorEdgeTerminal s L hnoTriple))
    (i : J) {x : V}
    (hx : x ∈ ((Erdos718.PairLinkage.expandLeftTorso
      s L hnoTriple M).path i).support) :
    TorsoExpansionAllowed s L hnoTriple M i x := by
  let q := expandTorsoPath s L hnoTriple M i
  have hxq : x ∈ q.support :=
    q.support_toPath_subset_support (by
      simpa only [Erdos718.PairLinkage.expandLeftTorso,
        Walk.support_copy] using hx)
  exact mem_support_expandTorsoPath_allowed s L hnoTriple M i hxq

/-- A linkage in the completed left torso can be expanded through a linked
right separator to a linkage in the original graph.  This is the precise
linkage-transfer statement used in the separation argument. -/
theorem nonempty_pairLinkage_of_leftTorso_of_linked_right
    {J : Type} [Fintype J] {G : SimpleGraph V}
    (s : Erdos718.Separation G)
    (X : Set (s.left : Set V))
    (terminal : Sum J J ↪ (s.left : Set V))
    (hleft : Nonempty (Erdos718.PairLinkage (leftTorso s)
      X terminal))
    (hright : Erdos718.IsLinkedSet (G.induce (s.right : Set V))
      (rightSeparator s : Set (s.right : Set V))) :
    Nonempty (Erdos718.PairLinkage G
      (liftLeftSet s X)
      (leftTerminalToGraph s terminal)) := by
  classical
  obtain ⟨L, hminimal⟩ := exists_minimal_pairLinkageTotalLength hleft
  have hnoTriple : HasNoSeparatorTriple s L :=
    hasNoSeparatorTriple_of_minimal s L hminimal
  have hterminalSep : Set.range (separatorEdgeTerminal s L hnoTriple) ⊆
      (rightSeparator s : Set (s.right : Set V)) := by
    rintro z ⟨q, rfl⟩
    change separatorEdgeTerminal s L hnoTriple q ∈ rightSeparator s
    rw [mem_rightSeparator]
    cases q with
    | inl o => exact o.2.1
    | inr o => exact o.2.2
  obtain ⟨M⟩ := hright (SeparatorEdgeOccurrence s L)
    (separatorEdgeTerminal s L hnoTriple) hterminalSep
  let q (i : J) := expandTorsoPath s L hnoTriple M i
  let p (i : J) : G.Walk
      (leftTerminalToGraph s terminal (.inl i))
      (leftTerminalToGraph s terminal (.inr i)) :=
    ((q i).toPath : G.Walk (terminal (.inl i) : V)
      (terminal (.inr i) : V)).copy
        (leftTerminalToGraph_apply s terminal (.inl i)).symm
        (leftTerminalToGraph_apply s terminal (.inr i)).symm
  refine ⟨{
    path := p
    isPath := fun i => by
      change (p i).IsPath
      dsimp only [p]
      rw [Walk.isPath_copy]
      exact (q i).toPath.property
    avoids := ?_
    disjoint := ?_
  }⟩
  · intro i
    rw [Set.disjoint_left]
    intro x hx hxterminal
    have hxsuppQ : x ∈ (q i).support :=
      (q i).support_toPath_subset_support (by
        simpa only [p, Walk.support_copy] using hx.1)
    have hxallowed := mem_support_expandTorsoPath_allowed
      s L hnoTriple M i (by simpa only [q] using hxsuppQ)
    obtain ⟨yX, hyXX, hyXx⟩ := hxterminal
    have hxstart : x ≠ (terminal (.inl i) : V) := by
      simpa only [leftTerminalToGraph_apply] using hx.2.1
    have hxend : x ≠ (terminal (.inr i) : V) := by
      simpa only [leftTerminalToGraph_apply] using hx.2.2
    have original_contra (y : (s.left : Set V))
        (hysupp : y ∈ (L.path i).support) (hyx : (y : V) = x) : False := by
      have hyinterior : y ∈ Erdos718.walkInteriorSet (L.path i) := by
        refine ⟨hysupp, ?_, ?_⟩
        · intro hy
          subst y
          exact hxstart hyx.symm
        · intro hy
          subst y
          exact hxend hyx.symm
      have hyX : y ∈ X := by
        have hyyX : y = yX := Subtype.ext (hyx.trans hyXx.symm)
        exact hyyX ▸ hyXX
      exact (Set.disjoint_left.mp (L.avoids i) hyinterior hyX).elim
    rcases hxallowed with ⟨y, hysupp, hyx⟩ | ⟨o, hoi, hxo⟩
    · exact original_contra y hysupp hyx
    · have hxright := mem_right_of_mem_central_support
        s L hnoTriple M o hxo
      have hxleft : x ∈ (s.left : Set V) := by
        rw [← hyXx]
        exact yX.property
      have hxsep : x ∈ (s.separator : Set V) := by
        change x ∈ s.separator
        rw [Erdos718.Separation.separator, Finset.mem_inter]
        exact ⟨hxleft, hxright⟩
      rcases central_support_eq_virtual_endpoint_of_mem_separator
        s L hnoTriple M o hxo hxsep with hx0 | hx1
      · have hget := congrArg (fun r =>
          ((L.path r).getVert (o.1.2 : ℕ) : V)) hoi
        apply original_contra ((L.path i).getVert o.1.2)
          ((L.path i).getVert_mem_support o.1.2)
        exact hget.symm.trans hx0.symm
      · have hget := congrArg (fun r =>
          ((L.path r).getVert ((o.1.2 : ℕ) + 1) : V)) hoi
        apply original_contra ((L.path i).getVert (o.1.2 + 1))
          ((L.path i).getVert_mem_support (o.1.2 + 1))
        exact hget.symm.trans hx1.symm
  · intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    change x ∈ (p i).support at hxi
    change x ∈ (p j).support at hxj
    have hxiQ : x ∈ (q i).support :=
      (q i).support_toPath_subset_support
        (by simpa only [p, Walk.support_copy] using hxi)
    have hxjQ : x ∈ (q j).support :=
      (q j).support_toPath_subset_support
        (by simpa only [p, Walk.support_copy] using hxj)
    exact torsoExpansionAllowed_disjoint s L hnoTriple M hij
      (mem_support_expandTorsoPath_allowed s L hnoTriple M i
        (by simpa only [q] using hxiQ))
      (mem_support_expandTorsoPath_allowed s L hnoTriple M j
        (by simpa only [q] using hxjQ))

end ThomasWollanMassed
end Erdos717
