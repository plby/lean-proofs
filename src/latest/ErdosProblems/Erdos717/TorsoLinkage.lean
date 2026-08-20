/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Linkage transfer across a finite separation after completing its boundary. -/

import ErdosProblems.Erdos717.GlueLinkage

open Function Set
open SimpleGraph

namespace Erdos717
namespace ThomasWollanMassed

universe u w

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The left torso of a separation: induce on the left side and complete the
separator to a clique. -/
def leftTorso {G : SimpleGraph V} (s : Erdos718.Separation G) :
    SimpleGraph (s.left : Set V) where
  Adj x y := G.Adj (x : V) (y : V) ∨
    ((x : V) ∈ s.separator ∧ (y : V) ∈ s.separator ∧ x ≠ y)
  symm.symm _ _ := Or.imp G.adj_symm fun h => ⟨h.2.1, h.1, h.2.2.symm⟩

instance leftTorso.instDecidableRel {G : SimpleGraph V}
    [DecidableRel G.Adj] (s : Erdos718.Separation G) :
    DecidableRel (leftTorso s).Adj := inferInstanceAs <|
  DecidableRel fun x y : (s.left : Set V) =>
    G.Adj (x : V) (y : V) ∨
      ((x : V) ∈ s.separator ∧ (y : V) ∈ s.separator ∧ x ≠ y)

lemma leftTorso_adj_iff {G : SimpleGraph V} {s : Erdos718.Separation G}
    {x y : (s.left : Set V)} :
    (leftTorso s).Adj x y ↔ G.Adj (x : V) (y : V) ∨
      ((x : V) ∈ s.separator ∧ (y : V) ∈ s.separator ∧ x ≠ y) :=
  Iff.rfl

/-- The induced left graph embeds in its torso. -/
def induceLeftToTorso {G : SimpleGraph V} (s : Erdos718.Separation G) :
    G.induce (s.left : Set V) →g leftTorso s where
  toFun := id
  map_rel' := fun {_ _} h => Or.inl h

/-! ### Minimal-length prescribed linkages -/

variable {W : Type w} {J : Type} [Fintype J] {G : SimpleGraph W}
  {X : Set W} {terminal : Sum J J ↪ W}

def pairLinkageTotalLength (L : Erdos718.PairLinkage G X terminal) : ℕ :=
  ∑ i, (L.path i).length

/-- Replace one path by a path supported on the old one. -/
noncomputable def pairLinkageReplaceSubset
    (L : Erdos718.PairLinkage G X terminal)
    (i : J) (q : G.Walk (terminal (.inl i)) (terminal (.inr i)))
    (hq : q.IsPath)
    (hsub : ∀ x, x ∈ q.support → x ∈ (L.path i).support) :
    Erdos718.PairLinkage G X terminal := by
  classical
  let newPath (j : J) :
      G.Walk (terminal (.inl j)) (terminal (.inr j)) :=
    if hji : j = i then
      q.copy
        (congrArg (fun x : J => terminal (.inl x)) hji.symm)
        (congrArg (fun x : J => terminal (.inr x)) hji.symm)
    else L.path j
  refine {
    path := newPath
    isPath := ?_
    avoids := ?_
    disjoint := ?_
  }
  · intro j
    by_cases hji : j = i
    · simp only [newPath, hji, ↓reduceDIte]
      simpa only [Walk.isPath_copy] using hq
    · simp only [newPath, hji, ↓reduceDIte]
      exact L.isPath j
  · intro j
    by_cases hji : j = i
    · simp only [newPath, hji, ↓reduceDIte,
        Erdos718.walkInteriorSet, Walk.support_copy]
      rw [Set.disjoint_left]
      intro x hxq hxX
      have hxOld : x ∈ (L.path i).support :=
        hsub x hxq.1
      have hxInterior : x ∈ Erdos718.walkInteriorSet (L.path i) := by
        refine ⟨hxOld, ?_, ?_⟩
        · intro h
          apply hxq.2.1
          simpa only [hji] using h
        · intro h
          apply hxq.2.2
          simpa only [hji] using h
      exact Set.disjoint_left.mp (L.avoids i) hxInterior hxX
    · simp only [newPath, hji, ↓reduceDIte]
      exact L.avoids j
  · intro j l hjl
    by_cases hji : j = i
    · by_cases hli : l = i
      · exact (hjl (hji.trans hli.symm)).elim
      · rw [Set.disjoint_left]
        intro x hxq hxl
        have hxOld := hsub x (by
          simpa only [newPath, hji, ↓reduceDIte, Set.mem_ofPred_eq,
            Walk.support_copy] using hxq)
        have hil : i ≠ l := fun h => hli h.symm
        have hdisj := Set.disjoint_left.mp (L.disjoint hil) hxOld
        exact hdisj (by
          simpa only [newPath, hli, ↓reduceDIte] using hxl)
    · by_cases hli : l = i
      · have hdisj := L.disjoint hji
        rw [Set.disjoint_left]
        intro x hxj hxq
        apply Set.disjoint_left.mp hdisj
        · simpa only [newPath, hji, ↓reduceDIte] using hxj
        · exact hsub x (by
            simpa only [newPath, hli, ↓reduceDIte, Set.mem_ofPred_eq,
              Walk.support_copy] using hxq)
      · simpa only [newPath, hji, hli, ↓reduceDIte] using L.disjoint hjl

lemma pairLinkageTotalLength_replaceSubset_lt
    (L : Erdos718.PairLinkage G X terminal)
    (i : J) (q : G.Walk (terminal (.inl i)) (terminal (.inr i)))
    (hq : q.IsPath)
    (hsub : ∀ x, x ∈ q.support → x ∈ (L.path i).support)
    (hlt : q.length < (L.path i).length) :
    pairLinkageTotalLength (pairLinkageReplaceSubset L i q hq hsub) <
      pairLinkageTotalLength L := by
  classical
  unfold pairLinkageTotalLength
  apply Finset.sum_lt_sum
  · intro j hj
    by_cases hji : j = i
    · subst j
      simpa [pairLinkageReplaceSubset, Walk.length_copy] using hlt.le
    · simp [pairLinkageReplaceSubset, hji]
  · refine ⟨i, Finset.mem_univ i, ?_⟩
    simpa [pairLinkageReplaceSubset, Walk.length_copy] using hlt

/-- Choose a prescribed linkage of minimum total length. -/
theorem exists_minimal_pairLinkageTotalLength
    (h : Nonempty (Erdos718.PairLinkage G X terminal)) :
    ∃ L : Erdos718.PairLinkage G X terminal,
      ∀ Q : Erdos718.PairLinkage G X terminal,
        pairLinkageTotalLength L ≤ pairLinkageTotalLength Q := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ L : Erdos718.PairLinkage G X terminal, pairLinkageTotalLength L = n
  have hP : ∃ n, P n := by
    obtain ⟨L⟩ := h
    exact ⟨pairLinkageTotalLength L, L, rfl⟩
  let n₀ := Nat.find hP
  obtain ⟨L, hL⟩ := Nat.find_spec hP
  refine ⟨L, ?_⟩
  intro Q
  have := Nat.find_min' hP ⟨Q, rfl⟩
  rw [hL]
  exact this

/-! ### Shortening two consecutive completed-boundary edges -/

lemma Walk.IsPath.getVert_inj_of_le {W : Type w} {G : SimpleGraph W}
    {a b : W} {p : G.Walk a b} (hp : p.IsPath)
    {i j : ℕ} (hi : i ≤ p.length) (hj : j ≤ p.length)
    (h : p.getVert i = p.getVert j) : i = j := by
  have hi' : i < p.support.length := by rw [p.length_support]; omega
  have hj' : j < p.support.length := by rw [p.length_support]; omega
  rw [p.getVert_eq_support_getElem hi,
    p.getVert_eq_support_getElem hj] at h
  exact (List.Nodup.getElem_inj_iff hp.support_nodup).mp h

/-- A minimum-total-length linkage has no path with a chord joining vertices
at distance two along that path. -/
theorem not_adj_getVert_add_two_of_minimal
    {J : Type} [Fintype J] {G : SimpleGraph W} {X : Set W}
    {terminal : Sum J J ↪ W}
    (L : Erdos718.PairLinkage G X terminal)
    (hminimal : ∀ Q : Erdos718.PairLinkage G X terminal,
      pairLinkageTotalLength L ≤ pairLinkageTotalLength Q)
    (i : J) (n : ℕ) (hn : n + 2 ≤ (L.path i).length) :
    ¬G.Adj ((L.path i).getVert n) ((L.path i).getVert (n + 2)) := by
  classical
  intro hadj
  let p := L.path i
  change n + 2 ≤ p.length at hn
  let r := ((p.take n).concat hadj).append (p.drop (n + 2))
  let q := r.toPath
  have hrsub : ∀ x, x ∈ r.support → x ∈ p.support := by
    intro x hx
    simp only [r, Walk.support_append, Walk.support_concat,
      List.mem_append, List.mem_cons, List.mem_singleton] at hx
    rcases hx with (hx | rfl | hx) | hx
    · rw [Walk.support_take] at hx
      exact List.mem_of_mem_take hx
    · exact p.getVert_mem_support (n + 2)
    · simp at hx
    · rw [Walk.drop_support_eq_support_drop_min] at hx
      exact List.mem_of_mem_drop (List.mem_of_mem_tail hx)
  have hqsub : ∀ x, x ∈ (q : G.Walk
      (terminal (.inl i)) (terminal (.inr i))).support →
      x ∈ p.support := by
    intro x hx
    exact hrsub x (r.support_toPath_subset_support hx)
  have hqpath : (q : G.Walk
      (terminal (.inl i)) (terminal (.inr i))).IsPath := q.property
  have hrlen : r.length + 1 = p.length := by
    simp only [r, Walk.length_append, Walk.length_concat,
      Walk.take_length, Walk.drop_length]
    omega
  have hqlt : (q : G.Walk
      (terminal (.inl i)) (terminal (.inr i))).length < p.length := by
    have hfin : (q : G.Walk
        (terminal (.inl i)) (terminal (.inr i))).support.toFinset ⊆
        r.support.toFinset := by
      intro x hx
      rw [List.mem_toFinset] at hx ⊢
      exact r.support_toPath_subset_support hx
    have hcard := Finset.card_le_card hfin
    have hqcard := List.toFinset_card_of_nodup q.property.support_nodup
    have hrcard := List.toFinset_card_le r.support
    have hqlen := (q : G.Walk
      (terminal (.inl i)) (terminal (.inr i))).length_support
    have hrlenSupp := r.length_support
    omega
  let Q := pairLinkageReplaceSubset L i
    (q : G.Walk (terminal (.inl i)) (terminal (.inr i)))
    hqpath hqsub
  have hQlt : pairLinkageTotalLength Q < pairLinkageTotalLength L :=
    pairLinkageTotalLength_replaceSubset_lt L i
      (q : G.Walk (terminal (.inl i)) (terminal (.inr i)))
      hqpath hqsub hqlt
  exact (Nat.not_lt_of_ge (hminimal Q)) hQlt

/-- In a shortest torso linkage no path contains two consecutive edges whose
three vertices all lie in the completed separator. -/
theorem no_separator_triple_of_minimal
    {J : Type} [Fintype J] {G : SimpleGraph V}
    (s : Erdos718.Separation G)
    {X : Set (s.left : Set V)}
    {terminal : Sum J J ↪ (s.left : Set V)}
    (L : Erdos718.PairLinkage (leftTorso s) X terminal)
    (hminimal : ∀ Q : Erdos718.PairLinkage (leftTorso s) X terminal,
      pairLinkageTotalLength L ≤ pairLinkageTotalLength Q) (i : J) (n : ℕ)
    (hn : n + 2 ≤ (L.path i).length) :
    ¬((L.path i).getVert n : V) ∈ s.separator ∨
      ¬((L.path i).getVert (n + 1) : V) ∈ s.separator ∨
      ¬((L.path i).getVert (n + 2) : V) ∈ s.separator := by
  classical
  by_contra h
  push Not at h
  let p := L.path i
  change n + 2 ≤ p.length at hn
  have hn0 : n ≤ p.length := by omega
  have hn2 : n + 2 ≤ p.length := hn
  have hne : p.getVert n ≠ p.getVert (n + 2) := by
    intro heq
    have := Walk.IsPath.getVert_inj_of_le (L.isPath i) hn0 hn2 heq
    omega
  have hadj : (leftTorso s).Adj (p.getVert n) (p.getVert (n + 2)) := by
    exact Or.inr ⟨h.1, h.2.2, hne⟩
  let r := ((p.take n).concat hadj).append (p.drop (n + 2))
  let q := r.toPath
  have hrsub : ∀ x, x ∈ r.support → x ∈ p.support := by
    intro x hx
    simp only [r, Walk.support_append, Walk.support_concat,
      List.mem_append, List.mem_cons, List.mem_singleton] at hx
    rcases hx with (hx | rfl | hx) | hx
    · rw [Walk.support_take] at hx
      exact List.mem_of_mem_take hx
    · exact p.getVert_mem_support (n + 2)
    · simp at hx
    · rw [Walk.drop_support_eq_support_drop_min] at hx
      exact List.mem_of_mem_drop (List.mem_of_mem_tail hx)
  have hqsub : ∀ x, x ∈ (q : (leftTorso s).Walk
      (terminal (.inl i)) (terminal (.inr i))).support →
      x ∈ p.support := by
    intro x hx
    exact hrsub x (r.support_toPath_subset_support hx)
  have hqpath : (q : (leftTorso s).Walk
      (terminal (.inl i)) (terminal (.inr i))).IsPath := q.property
  have hrlen : r.length + 1 = p.length := by
    simp only [r, Walk.length_append, Walk.length_concat,
      Walk.take_length, Walk.drop_length]
    omega
  have hqlt : (q : (leftTorso s).Walk
      (terminal (.inl i)) (terminal (.inr i))).length < p.length := by
    have hfin : (q : (leftTorso s).Walk
        (terminal (.inl i)) (terminal (.inr i))).support.toFinset ⊆
        r.support.toFinset := by
      intro x hx
      rw [List.mem_toFinset] at hx ⊢
      exact r.support_toPath_subset_support hx
    have hcard := Finset.card_le_card hfin
    have hqcard := List.toFinset_card_of_nodup q.property.support_nodup
    have hrcard := List.toFinset_card_le r.support
    have hqlen := (q : (leftTorso s).Walk
      (terminal (.inl i)) (terminal (.inr i))).length_support
    have hrlenSupp := r.length_support
    omega
  let Q := pairLinkageReplaceSubset L i
    (q : (leftTorso s).Walk (terminal (.inl i)) (terminal (.inr i)))
    hqpath hqsub
  have hQlt : pairLinkageTotalLength Q < pairLinkageTotalLength L :=
    pairLinkageTotalLength_replaceSubset_lt L i
      (q : (leftTorso s).Walk (terminal (.inl i)) (terminal (.inr i)))
      hqpath hqsub hqlt
  exact (Nat.not_lt_of_ge (hminimal Q)) hQlt

/-- The local shortening property needed to route all virtual torso edges
through the other side of a separation. -/
def HasNoSeparatorTriple
    {J : Type} [Fintype J] {G : SimpleGraph V}
    (s : Erdos718.Separation G)
    {X : Set (s.left : Set V)}
    {terminal : Sum J J ↪ (s.left : Set V)}
    (L : Erdos718.PairLinkage (leftTorso s) X terminal) : Prop :=
  ∀ (i : J) (n : ℕ), n + 2 ≤ (L.path i).length →
    ¬((L.path i).getVert n : V) ∈ s.separator ∨
      ¬((L.path i).getVert (n + 1) : V) ∈ s.separator ∨
      ¬((L.path i).getVert (n + 2) : V) ∈ s.separator

theorem hasNoSeparatorTriple_of_minimal
    {J : Type} [Fintype J] {G : SimpleGraph V}
    (s : Erdos718.Separation G)
    {X : Set (s.left : Set V)}
    {terminal : Sum J J ↪ (s.left : Set V)}
    (L : Erdos718.PairLinkage (leftTorso s) X terminal)
    (hminimal : ∀ Q : Erdos718.PairLinkage (leftTorso s) X terminal,
      pairLinkageTotalLength L ≤ pairLinkageTotalLength Q) :
    HasNoSeparatorTriple s L :=
  fun i n hn => no_separator_triple_of_minimal s L hminimal i n hn

/-! ### The virtual separator edges of a minimal torso linkage -/

/-- Occurrences of torso edges whose two endpoints lie in the completed
separator. -/
def SeparatorEdgeOccurrence
    {J : Type} [Fintype J] {G : SimpleGraph V}
    (s : Erdos718.Separation G)
    {X : Set (s.left : Set V)}
    {terminal : Sum J J ↪ (s.left : Set V)}
    (L : Erdos718.PairLinkage (leftTorso s) X terminal) :=
  {o : Σ i : J, Fin (L.path i).length //
    ((L.path o.1).getVert o.2 : V) ∈ s.separator ∧
      ((L.path o.1).getVert (o.2 + 1) : V) ∈ s.separator}

noncomputable instance SeparatorEdgeOccurrence.instFintype
    {J : Type} [Fintype J] {G : SimpleGraph V}
    (s : Erdos718.Separation G)
    {X : Set (s.left : Set V)}
    {terminal : Sum J J ↪ (s.left : Set V)}
    (L : Erdos718.PairLinkage (leftTorso s) X terminal) :
    Fintype (SeparatorEdgeOccurrence s L) := by
  classical
  unfold SeparatorEdgeOccurrence
  infer_instance

lemma getVert_ne_of_linkage_index_ne
    {J : Type} [Fintype J] {G : SimpleGraph V}
    {s : Erdos718.Separation G} {X : Set (s.left : Set V)}
    {terminal : Sum J J ↪ (s.left : Set V)}
    (L : Erdos718.PairLinkage (leftTorso s) X terminal)
    {i j : J} (hij : i ≠ j) {m n : ℕ}
    (hm : m ≤ (L.path i).length) (hn : n ≤ (L.path j).length) :
    (L.path i).getVert m ≠ (L.path j).getVert n := by
  intro h
  have hmSupp := (L.path i).getVert_mem_support m
  have hnSupp := (L.path j).getVert_mem_support n
  exact (Set.disjoint_left.mp (L.disjoint hij) hmSupp (h ▸ hnSupp)).elim

/-- The directed endpoints of all virtual separator edges form an embedding
into the right side.  Minimality is used exactly to rule out two adjacent
virtual edges on one torso path. -/
def separatorEdgeTerminal
    {J : Type} [Fintype J] {G : SimpleGraph V}
    (s : Erdos718.Separation G)
    {X : Set (s.left : Set V)}
    {terminal : Sum J J ↪ (s.left : Set V)}
    (L : Erdos718.PairLinkage (leftTorso s) X terminal)
    (hnoTriple : HasNoSeparatorTriple s L) :
    Sum (SeparatorEdgeOccurrence s L) (SeparatorEdgeOccurrence s L) ↪
      (s.right : Set V) := by
  classical
  let endpoint : Sum (SeparatorEdgeOccurrence s L)
      (SeparatorEdgeOccurrence s L) → (s.right : Set V)
    | .inl o => ⟨(L.path o.1.1).getVert o.1.2,
        (Finset.mem_inter.mp o.2.1).2⟩
    | .inr o => ⟨(L.path o.1.1).getVert (o.1.2 + 1),
        (Finset.mem_inter.mp o.2.2).2⟩
  have samePathPosition {i j : J} {m n : ℕ}
      (hm : m ≤ (L.path i).length) (hn : n ≤ (L.path j).length)
      (hval : (L.path i).getVert m = (L.path j).getVert n) :
      i = j → m = n := by
    intro hij
    subst j
    exact Walk.IsPath.getVert_inj_of_le (L.isPath i) hm hn hval
  refine ⟨endpoint, ?_⟩
  intro z w hzw
  have hval := congrArg Subtype.val hzw
  cases z with
  | inl o =>
      cases w with
      | inl p =>
          have hval' :
              (L.path o.1.1).getVert o.1.2 =
                (L.path p.1.1).getVert p.1.2 := Subtype.ext hval
          have hi : o.1.1 = p.1.1 := by
            by_contra hne
            exact getVert_ne_of_linkage_index_ne L hne o.1.2.2.le
              p.1.2.2.le hval'
          have hn : (o.1.2 : ℕ) = p.1.2 :=
            samePathPosition o.1.2.2.le p.1.2.2.le hval' hi
          have hopIndex : o.1 = p.1 :=
            Sigma.ext hi <| (Fin.heq_ext_iff (by rw [hi])).mpr hn
          exact congrArg Sum.inl (Subtype.ext hopIndex)
      | inr p =>
          have hpbound : (p.1.2 : ℕ) + 1 ≤ (L.path p.1.1).length := by
            omega
          have hval' :
              (L.path o.1.1).getVert o.1.2 =
                (L.path p.1.1).getVert (p.1.2 + 1) := Subtype.ext hval
          have hi : o.1.1 = p.1.1 := by
            by_contra hne
            exact getVert_ne_of_linkage_index_ne L hne o.1.2.2.le
              hpbound hval'
          have hn : (o.1.2 : ℕ) = p.1.2 + 1 :=
            samePathPosition o.1.2.2.le hpbound hval' hi
          have htriple := hnoTriple o.1.1 p.1.2 (by omega)
          have hpStart :
              ((L.path o.1.1).getVert p.1.2 : V) ∈ s.separator := by
            have hget := congrArg (fun i =>
              ((L.path i).getVert (p.1.2 : ℕ) : V)) hi
            rw [hget]
            exact p.2.1
          have hpEnd :
              ((L.path o.1.1).getVert (p.1.2 + 1) : V) ∈ s.separator := by
            have hget := congrArg (fun i =>
              ((L.path i).getVert ((p.1.2 : ℕ) + 1) : V)) hi
            rw [hget]
            exact p.2.2
          have hoEnd :
              ((L.path o.1.1).getVert (p.1.2 + 2) : V) ∈ s.separator := by
            simpa only [hn, Nat.add_assoc] using o.2.2
          rcases htriple with h0 | h1 | h2
          · exact (h0 hpStart).elim
          · exact (h1 hpEnd).elim
          · exact (h2 hoEnd).elim
  | inr o =>
      cases w with
      | inl p =>
          have hobound : (o.1.2 : ℕ) + 1 ≤ (L.path o.1.1).length := by
            omega
          have hval' :
              (L.path o.1.1).getVert (o.1.2 + 1) =
                (L.path p.1.1).getVert p.1.2 := Subtype.ext hval
          have hi : o.1.1 = p.1.1 := by
            by_contra hne
            exact getVert_ne_of_linkage_index_ne L hne hobound
              p.1.2.2.le hval'
          have hn : (o.1.2 : ℕ) + 1 = p.1.2 :=
            samePathPosition hobound p.1.2.2.le hval' hi
          have hpbound : (p.1.2 : ℕ) + 1 ≤ (L.path p.1.1).length := by
            omega
          have hpbound' :
              (p.1.2 : ℕ) + 1 ≤ (L.path o.1.1).length := by
            have hlen := congrArg (fun i => (L.path i).length) hi
            omega
          have htriple := hnoTriple o.1.1 o.1.2 (by omega :
              (o.1.2 : ℕ) + 2 ≤ (L.path o.1.1).length)
          have hoStart := o.2.1
          have hoEnd := o.2.2
          have hpEnd :
              ((L.path o.1.1).getVert ((o.1.2 : ℕ) + 2) : V) ∈
                s.separator := by
            have hpEnd' :
                ((L.path o.1.1).getVert ((p.1.2 : ℕ) + 1) : V) ∈
                  s.separator := by
              have hget := congrArg (fun i =>
                ((L.path i).getVert ((p.1.2 : ℕ) + 1) : V)) hi
              rw [hget]
              exact p.2.2
            have hpos : (p.1.2 : ℕ) + 1 = (o.1.2 : ℕ) + 2 := by omega
            rw [hpos] at hpEnd'
            exact hpEnd'
          rcases htriple with h0 | h1 | h2
          · exact (h0 hoStart).elim
          · exact (h1 hoEnd).elim
          · exact (h2 hpEnd).elim
      | inr p =>
          have hobound : (o.1.2 : ℕ) + 1 ≤ (L.path o.1.1).length := by
            omega
          have hpbound : (p.1.2 : ℕ) + 1 ≤ (L.path p.1.1).length := by
            omega
          have hval' :
              (L.path o.1.1).getVert (o.1.2 + 1) =
                (L.path p.1.1).getVert (p.1.2 + 1) := Subtype.ext hval
          have hi : o.1.1 = p.1.1 := by
            by_contra hne
            exact getVert_ne_of_linkage_index_ne L hne hobound hpbound hval'
          have hn : (o.1.2 : ℕ) + 1 = p.1.2 + 1 :=
            samePathPosition hobound hpbound hval' hi
          have hbase : (o.1.2 : ℕ) = p.1.2 := by omega
          have hopIndex : o.1 = p.1 :=
            Sigma.ext hi <| (Fin.heq_ext_iff (by rw [hi])).mpr hbase
          exact congrArg Sum.inr (Subtype.ext hopIndex)

@[simp] lemma separatorEdgeTerminal_inl_val
    {J : Type} [Fintype J] {G : SimpleGraph V}
    (s : Erdos718.Separation G)
    {X : Set (s.left : Set V)}
    {terminal : Sum J J ↪ (s.left : Set V)}
    (L : Erdos718.PairLinkage (leftTorso s) X terminal)
    (hnoTriple : HasNoSeparatorTriple s L)
    (o : SeparatorEdgeOccurrence s L) :
    ((separatorEdgeTerminal s L hnoTriple (.inl o) :
      (s.right : Set V)) : V) = (L.path o.1.1).getVert o.1.2 := rfl

@[simp] lemma separatorEdgeTerminal_inr_val
    {J : Type} [Fintype J] {G : SimpleGraph V}
    (s : Erdos718.Separation G)
    {X : Set (s.left : Set V)}
    {terminal : Sum J J ↪ (s.left : Set V)}
    (L : Erdos718.PairLinkage (leftTorso s) X terminal)
    (hnoTriple : HasNoSeparatorTriple s L)
    (o : SeparatorEdgeOccurrence s L) :
    ((separatorEdgeTerminal s L hnoTriple (.inr o) :
      (s.right : Set V)) : V) = (L.path o.1.1).getVert (o.1.2 + 1) := rfl

end ThomasWollanMassed
end Erdos717
