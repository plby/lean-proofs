/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Linkedness transfer from a restricted left torso through the right side. -/

import ErdosProblems.Erdos717.LeftTorsoMass
import ErdosProblems.Erdos717.RestrictLinkage

open Function Set
open SimpleGraph
open scoped Sym2

namespace Erdos717
namespace ThomasWollanMassed

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Reverse the two sides of a separation. -/
def separationSwap {G : SimpleGraph V} (s : Erdos718.Separation G) :
    Erdos718.Separation G where
  left := s.right
  right := s.left
  cover := by rw [Finset.union_comm, s.cover]
  not_adj := by
    intro a b haR haL hbL hbR hab
    exact s.not_adj hbL hbR haR haL hab.symm

@[simp] lemma separationSwap_left {G : SimpleGraph V}
    (s : Erdos718.Separation G) : (separationSwap s).left = s.right := rfl

@[simp] lemma separationSwap_right {G : SimpleGraph V}
    (s : Erdos718.Separation G) : (separationSwap s).right = s.left := rfl

@[simp] lemma separationSwap_separator {G : SimpleGraph V}
    (s : Erdos718.Separation G) :
    (separationSwap s).separator = s.separator := by
  simp only [Erdos718.Separation.separator, separationSwap]
  exact Finset.inter_comm _ _

/-- A separation of a supergraph is also a separation of every subgraph. -/
def separationOfLE {G H : SimpleGraph V} (h : G ≤ H)
    (s : Erdos718.Separation H) : Erdos718.Separation G where
  left := s.left
  right := s.right
  cover := s.cover
  not_adj := fun {_ _} haL haR hbR hbL hab =>
    s.not_adj haL haR hbR hbL (h hab)

@[simp] lemma separationOfLE_left {G H : SimpleGraph V} (h : G ≤ H)
    (s : Erdos718.Separation H) : (separationOfLE h s).left = s.left := rfl

@[simp] lemma separationOfLE_right {G H : SimpleGraph V} (h : G ≤ H)
    (s : Erdos718.Separation H) : (separationOfLE h s).right = s.right := rfl

@[simp] lemma separationOfLE_separator {G H : SimpleGraph V} (h : G ≤ H)
    (s : Erdos718.Separation H) :
    (separationOfLE h s).separator = s.separator := rfl

/-- The strict-right incident-edge count is preserved by `composeRight`. -/
lemma incidentEdges_composeRight
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (s : Erdos718.Separation G)
    (t : Erdos718.Separation (G.induce (s.right : Set V)))
    (hseparator : rightSeparator s ⊆ t.left) :
    incidentEdges G
        ((composeRight s t hseparator).right \
          (composeRight s t hseparator).left) =
      incidentEdges (G.induce (s.right : Set V))
        (t.right \ t.left) := by
  classical
  let f : (s.right : Set V) ↪ V := Function.Embedding.subtype _
  have hf : f = Function.Embedding.subtype (s.right : Set V) := rfl
  have hmap : (t.right \ t.left).map f =
      (composeRight s t hseparator).right \
        (composeRight s t hseparator).left :=
    (composeRight_strictRight s t hseparator).symm
  have hclosed : ∀ {a b : V}, G.Adj a b →
      (a ∈ (t.right \ t.left).map f ∨
        b ∈ (t.right \ t.left).map f) →
      a ∈ (s.right : Set V) ∧ b ∈ (s.right : Set V) := by
    intro a b hab htouch
    rw [hmap] at htouch
    obtain ⟨haq, hbq⟩ := edge_endpoints_right_of_touches_strictRight
      (composeRight s t hseparator) hab htouch
    have hqsub : (composeRight s t hseparator).right ⊆ s.right := by
      intro x hx
      rw [composeRight_right s t hseparator, Finset.mem_map] at hx
      obtain ⟨z, hz, rfl⟩ := hx
      exact z.property
    exact ⟨hqsub haq, hqsub hbq⟩
  have hi := incidentEdges_induce_of_closed G (s.right : Set V)
    (t.right \ t.left) hclosed
  calc
    incidentEdges G
        ((composeRight s t hseparator).right \
          (composeRight s t hseparator).left) =
        incidentEdges G ((t.right \ t.left).map f) := by rw [hmap]
    _ = incidentEdges (G.induce (s.right : Set V))
        (t.right \ t.left) := by rw [hf]; exact hi.symm

/-- Completing the separator creates no new edge incident with a vertex set
which is disjoint from that separator. -/
lemma incidentEdges_leftTorso_eq_induce_left
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (s : Erdos718.Separation G) (R : Finset (s.left : Set V))
    (hR : ∀ x ∈ R, (x : V) ∉ s.separator) :
    incidentEdges (leftTorso s) R =
      incidentEdges (G.induce (s.left : Set V)) R := by
  classical
  unfold incidentEdges
  congr 1
  ext e
  simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset,
    SimpleGraph.mem_edgeSet]
  induction e using Sym2.inductionOn with
  | _ a b =>
      constructor
      · rintro ⟨hab, htouch⟩
        refine ⟨?_, htouch⟩
        have htouch' := (not_pair_subset_compl_iff R a b).mp htouch
        rcases (leftTorso_adj_iff.mp hab) with habG | habS
        · exact habG
        · rcases htouch' with ha | hb
          · exact (hR a ha habS.1).elim
          · exact (hR b hb habS.2.1).elim
      · rintro ⟨hab, htouch⟩
        exact ⟨Or.inl hab, htouch⟩

/-- The ambient region consisting of the original right side together with
an indicated part of the left side. -/
def expandedLeftRegion {G : SimpleGraph V} (s : Erdos718.Separation G)
    (A : Set (s.left : Set V)) : Set V :=
  {x | x ∈ (s.right : Set V) ∨ ∃ a ∈ A, (a : V) = x}

/-- Glue the right side of a separation of the left torso to the original
right side.  The old separator is assumed to lie on the nested right. -/
def composeNestedRight {G : SimpleGraph V}
    (s : Erdos718.Separation G)
    (t : Erdos718.Separation (leftTorso s))
    (hseparator : ∀ x : (s.left : Set V),
      (x : V) ∈ s.separator → x ∈ t.right) :
    Erdos718.Separation G where
  left := t.left.map (Function.Embedding.subtype _)
  right := s.right ∪ t.right.map (Function.Embedding.subtype _)
  cover := by
    ext x
    simp only [Finset.mem_union, Finset.mem_map, Finset.mem_univ,
      iff_true]
    rcases s.mem_left_or_mem_right x with hxL | hxR
    · let x' : (s.left : Set V) := ⟨x, hxL⟩
      rcases t.mem_left_or_mem_right x' with hxtL | hxtR
      · exact Or.inl ⟨x', hxtL, rfl⟩
      · exact Or.inr (Or.inr ⟨x', hxtR, rfl⟩)
    · exact Or.inr (Or.inl hxR)
  not_adj := by
    intro a b haL haR hbR hbL hab
    rw [Finset.mem_map] at haL
    obtain ⟨a', haLt, haval⟩ := haL
    change (a' : V) = a at haval
    have haNotSRight : a ∉ s.right := fun h => haR (Finset.mem_union_left _ h)
    have haNotTRight : a' ∉ t.right := by
      intro h
      exact haR (Finset.mem_union_right _
        (Finset.mem_map.mpr ⟨a', h, haval⟩))
    rcases Finset.mem_union.mp hbR with hbSR | hbTR
    · by_cases hbSL : b ∈ s.left
      · let b' : (s.left : Set V) := ⟨b, hbSL⟩
        have hbSep : b ∈ s.separator := by
          exact Finset.mem_inter.mpr ⟨hbSL, hbSR⟩
        have hbTRight : b' ∈ t.right := hseparator b' hbSep
        have hbNotTLeft : b' ∉ t.left := by
          intro h
          exact hbL (Finset.mem_map.mpr ⟨b', h, rfl⟩)
        exact t.not_adj haLt haNotTRight hbTRight hbNotTLeft (by
          change (leftTorso s).Adj a' b'
          apply Or.inl
          change G.Adj (a' : V) (b' : V)
          rw [haval]
          exact hab)
      · have haNotSRight' : (a' : V) ∉ s.right := by
          rw [haval]
          exact haNotSRight
        exact s.not_adj a'.property haNotSRight' hbSR hbSL (by
          change G.Adj (a' : V) b
          rw [haval]
          exact hab)
    · rw [Finset.mem_map] at hbTR
      obtain ⟨b', hbTR, hbval⟩ := hbTR
      change (b' : V) = b at hbval
      have hbNotTL : b' ∉ t.left := by
        intro h
        exact hbL (Finset.mem_map.mpr ⟨b', h, hbval⟩)
      exact t.not_adj haLt haNotTRight hbTR hbNotTL (by
        change (leftTorso s).Adj a' b'
        apply Or.inl
        change G.Adj (a' : V) (b' : V)
        rw [haval, hbval]
        exact hab)

@[simp] lemma composeNestedRight_left {G : SimpleGraph V}
    (s : Erdos718.Separation G) (t : Erdos718.Separation (leftTorso s))
    (hseparator) :
    (composeNestedRight s t hseparator).left =
      t.left.map (Function.Embedding.subtype _) := rfl

@[simp] lemma composeNestedRight_right {G : SimpleGraph V}
    (s : Erdos718.Separation G) (t : Erdos718.Separation (leftTorso s))
    (hseparator) :
    (composeNestedRight s t hseparator).right =
      s.right ∪ t.right.map (Function.Embedding.subtype _) := rfl

lemma composeNestedRight_separator {G : SimpleGraph V}
    (s : Erdos718.Separation G) (t : Erdos718.Separation (leftTorso s))
    (hseparator : ∀ x : (s.left : Set V),
      (x : V) ∈ s.separator → x ∈ t.right) :
    (composeNestedRight s t hseparator).separator =
      t.separator.map (Function.Embedding.subtype _) := by
  classical
  ext x
  simp only [Erdos718.Separation.separator, composeNestedRight,
    Finset.mem_inter, Finset.mem_map, Finset.mem_union]
  constructor
  · rintro ⟨⟨a, haL, haval⟩, hxR | ⟨b, hbR, hbval⟩⟩
    · have haR : a ∈ t.right := by
        change (a : V) = x at haval
        have hxSep : x ∈ s.separator :=
          Finset.mem_inter.mpr ⟨haval ▸ a.property, hxR⟩
        apply hseparator a
        rw [haval]
        exact hxSep
      exact ⟨a, ⟨haL, haR⟩, haval⟩
    · have hab : a = b := Subtype.ext (haval.trans hbval.symm)
      subst b
      exact ⟨a, ⟨haL, hbR⟩, haval⟩
  · rintro ⟨a, ⟨haL, haR⟩, haval⟩
    exact ⟨⟨a, haL, haval⟩,
      Or.inr ⟨a, haR, haval⟩⟩

@[simp] lemma composeNestedRight_separator_card {G : SimpleGraph V}
    (s : Erdos718.Separation G) (t : Erdos718.Separation (leftTorso s))
    (hseparator) :
    (composeNestedRight s t hseparator).separator.card =
      t.separator.card := by
  rw [composeNestedRight_separator, Finset.card_map]

lemma expandedLeftRegion_eq_composeNestedRight
    {G : SimpleGraph V} (s : Erdos718.Separation G)
    (t : Erdos718.Separation (leftTorso s)) (hseparator) :
    expandedLeftRegion s (t.right : Set (s.left : Set V)) =
      ((composeNestedRight s t hseparator).right : Set V) := by
  ext x
  simp only [expandedLeftRegion, Set.mem_setOf_eq,
    composeNestedRight_right, Finset.mem_coe, Finset.mem_union,
    Finset.mem_map]
  tauto

/-- Glue the original right side to the left side of a nested torso
separation.  This is the first case in Claim 2.1. -/
def composeNestedLeft {G : SimpleGraph V}
    (s : Erdos718.Separation G)
    (t : Erdos718.Separation (leftTorso s))
    (hseparator : ∀ x : (s.left : Set V),
      (x : V) ∈ s.separator → x ∈ t.left) :
    Erdos718.Separation G where
  left := s.right ∪ t.left.map (Function.Embedding.subtype _)
  right := t.right.map (Function.Embedding.subtype _)
  cover := by
    ext x
    simp only [Finset.mem_union, Finset.mem_map, Finset.mem_univ,
      iff_true]
    rcases s.mem_left_or_mem_right x with hxL | hxR
    · let x' : (s.left : Set V) := ⟨x, hxL⟩
      rcases t.mem_left_or_mem_right x' with hxtL | hxtR
      · exact Or.inl (Or.inr ⟨x', hxtL, rfl⟩)
      · exact Or.inr ⟨x', hxtR, rfl⟩
    · exact Or.inl (Or.inl hxR)
  not_adj := by
    intro a b haL haR hbR hbL hab
    rw [Finset.mem_map] at hbR
    obtain ⟨b', hbRt, hbval⟩ := hbR
    change (b' : V) = b at hbval
    have hbNotSRight : b ∉ s.right := fun h => hbL (Finset.mem_union_left _ h)
    have hbNotTLeft : b' ∉ t.left := by
      intro h
      exact hbL (Finset.mem_union_right _
        (Finset.mem_map.mpr ⟨b', h, hbval⟩))
    rcases Finset.mem_union.mp haL with haSR | haTL
    · by_cases haSL : a ∈ s.left
      · let a' : (s.left : Set V) := ⟨a, haSL⟩
        have haSep : a ∈ s.separator := Finset.mem_inter.mpr ⟨haSL, haSR⟩
        have haTLeft : a' ∈ t.left := hseparator a' haSep
        have haNotTRight : a' ∉ t.right := by
          intro h
          exact haR (Finset.mem_map.mpr ⟨a', h, rfl⟩)
        exact t.not_adj haTLeft haNotTRight hbRt hbNotTLeft (by
          apply Or.inl
          change G.Adj (a' : V) (b' : V)
          rw [hbval]
          exact hab)
      · have hbNotSRight' : (b' : V) ∉ s.right := by
          rw [hbval]
          exact hbNotSRight
        exact s.not_adj b'.property hbNotSRight' haSR haSL (by
          change G.Adj (b' : V) a
          rw [hbval]
          exact hab.symm)
    · rw [Finset.mem_map] at haTL
      obtain ⟨a', haTL, haval⟩ := haTL
      change (a' : V) = a at haval
      have haNotTR : a' ∉ t.right := by
        intro h
        exact haR (Finset.mem_map.mpr ⟨a', h, haval⟩)
      exact t.not_adj haTL haNotTR hbRt hbNotTLeft (by
        apply Or.inl
        change G.Adj (a' : V) (b' : V)
        rw [haval, hbval]
        exact hab)

lemma composeNestedLeft_separator {G : SimpleGraph V}
    (s : Erdos718.Separation G) (t : Erdos718.Separation (leftTorso s))
    (hseparator : ∀ x : (s.left : Set V),
      (x : V) ∈ s.separator → x ∈ t.left) :
    (composeNestedLeft s t hseparator).separator =
      t.separator.map (Function.Embedding.subtype _) := by
  classical
  ext x
  simp only [Erdos718.Separation.separator, composeNestedLeft,
    Finset.mem_inter, Finset.mem_union, Finset.mem_map]
  constructor
  · rintro ⟨hxS | ⟨a, haL, haval⟩, ⟨b, hbR, hbval⟩⟩
    · have hxL : x ∈ s.left := hbval ▸ b.property
      let b' : (s.left : Set V) := ⟨x, hxL⟩
      have hbEq : b' = b := Subtype.ext hbval.symm
      have hbL : b' ∈ t.left := hseparator b'
        (Finset.mem_inter.mpr ⟨hxL, hxS⟩)
      exact ⟨b', ⟨hbL, hbEq ▸ hbR⟩, rfl⟩
    · have hab : a = b := Subtype.ext (haval.trans hbval.symm)
      subst b
      exact ⟨a, ⟨haL, hbR⟩, haval⟩
  · rintro ⟨a, ⟨haL, haR⟩, haval⟩
    exact ⟨Or.inr ⟨a, haL, haval⟩, ⟨a, haR, haval⟩⟩

@[simp] lemma composeNestedLeft_separator_card {G : SimpleGraph V}
    (s : Erdos718.Separation G) (t : Erdos718.Separation (leftTorso s))
    (hseparator) :
    (composeNestedLeft s t hseparator).separator.card = t.separator.card := by
  rw [composeNestedLeft_separator, Finset.card_map]

lemma composeNestedLeft_strictRight {G : SimpleGraph V}
    (s : Erdos718.Separation G) (t : Erdos718.Separation (leftTorso s))
    (hseparator : ∀ x : (s.left : Set V),
      (x : V) ∈ s.separator → x ∈ t.left) :
    (composeNestedLeft s t hseparator).right \
        (composeNestedLeft s t hseparator).left =
      (t.right \ t.left).map (Function.Embedding.subtype _) := by
  classical
  ext x
  simp only [composeNestedLeft, Finset.mem_sdiff, Finset.mem_map,
    Finset.mem_union]
  constructor
  · rintro ⟨⟨a, haR, haval⟩, hnot⟩
    have haL : a ∉ t.left := fun h => hnot (Or.inr ⟨a, h, haval⟩)
    exact ⟨a, ⟨haR, haL⟩, haval⟩
  · rintro ⟨a, ⟨haR, haL⟩, haval⟩
    change (a : V) = x at haval
    refine ⟨⟨a, haR, haval⟩, ?_⟩
    rintro (hxS | ⟨b, hbL, hbval⟩)
    · have hxL : x ∈ s.left := haval ▸ a.property
      have haSep : (a : V) ∈ s.separator := by
        rw [haval]
        exact Finset.mem_inter.mpr ⟨hxL, hxS⟩
      exact haL (hseparator a haSep)
    · have hab : a = b := Subtype.ext (haval.trans hbval.symm)
      exact haL (hab ▸ hbL)

lemma incidentEdges_composeNestedLeft
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (s : Erdos718.Separation G)
    (t : Erdos718.Separation (leftTorso s))
    (hseparator : ∀ x : (s.left : Set V),
      (x : V) ∈ s.separator → x ∈ t.left) :
    incidentEdges G
        ((composeNestedLeft s t hseparator).right \
          (composeNestedLeft s t hseparator).left) =
      incidentEdges (G.induce (s.left : Set V)) (t.right \ t.left) := by
  classical
  let f : (s.left : Set V) ↪ V := Function.Embedding.subtype _
  have hmap : (t.right \ t.left).map f =
      (composeNestedLeft s t hseparator).right \
        (composeNestedLeft s t hseparator).left :=
    (composeNestedLeft_strictRight s t hseparator).symm
  have hclosed : ∀ {a b : V}, G.Adj a b →
      (a ∈ (t.right \ t.left).map f ∨
        b ∈ (t.right \ t.left).map f) →
      a ∈ (s.left : Set V) ∧ b ∈ (s.left : Set V) := by
    intro a b hab htouch
    rw [hmap] at htouch
    obtain ⟨haq, hbq⟩ := edge_endpoints_right_of_touches_strictRight
      (composeNestedLeft s t hseparator) hab htouch
    have hqsub : (composeNestedLeft s t hseparator).right ⊆ s.left := by
      intro x hx
      change x ∈ t.right.map (Function.Embedding.subtype _) at hx
      rw [Finset.mem_map] at hx
      obtain ⟨z, _hz, rfl⟩ := hx
      exact z.property
    exact ⟨hqsub haq, hqsub hbq⟩
  have hi := incidentEdges_induce_of_closed G (s.left : Set V)
    (t.right \ t.left) hclosed
  calc
    incidentEdges G
        ((composeNestedLeft s t hseparator).right \
          (composeNestedLeft s t hseparator).left) =
        incidentEdges G ((t.right \ t.left).map f) := by rw [hmap]
    _ = incidentEdges (G.induce (s.left : Set V))
        (t.right \ t.left) := hi.symm

/-- Lifting an induced-torso linkage preserves every vertex index. -/
lemma getVert_liftInduce
    {I : Type} [Fintype I] {G : SimpleGraph V}
    {A X : Set V} {terminal : Sum I I ↪ V}
    (hA : Set.range terminal ⊆ A)
    (L : Erdos718.PairLinkage (G.induce A)
      {a : A | (a : V) ∈ X} (terminalIntoSet A terminal hA))
    (i : I) (n : ℕ) :
    ((Erdos718.PairLinkage.liftInduce hA L).path i).getVert n =
      ((L.path i).getVert n : V) := by
  dsimp only [Erdos718.PairLinkage.liftInduce]
  rw [Walk.getVert_copy, Walk.getVert_map]
  rfl

@[simp] lemma length_liftInduce
    {I : Type} [Fintype I] {G : SimpleGraph V}
    {A X : Set V} {terminal : Sum I I ↪ V}
    (hA : Set.range terminal ⊆ A)
    (L : Erdos718.PairLinkage (G.induce A)
      {a : A | (a : V) ∈ X} (terminalIntoSet A terminal hA))
    (i : I) :
    ((Erdos718.PairLinkage.liftInduce hA L).path i).length =
      (L.path i).length := by
  dsimp only [Erdos718.PairLinkage.liftInduce]
  rw [Walk.length_copy, Walk.length_map]

/-- A linkage chosen shortest inside `A` has the no-triple property after
it is lifted to the full torso. -/
theorem hasNoSeparatorTriple_liftInduce_of_minimal
    {I : Type} [Fintype I] {G : SimpleGraph V}
    (s : Erdos718.Separation G)
    {A X : Set (s.left : Set V)}
    {terminal : Sum I I ↪ (s.left : Set V)}
    (hA : Set.range terminal ⊆ A)
    (L₀ : Erdos718.PairLinkage ((leftTorso s).induce A)
      {a : A | (a : (s.left : Set V)) ∈ X}
      (terminalIntoSet A terminal hA))
    (hminimal : ∀ Q : Erdos718.PairLinkage ((leftTorso s).induce A)
      {a : A | (a : (s.left : Set V)) ∈ X}
      (terminalIntoSet A terminal hA),
      pairLinkageTotalLength L₀ ≤ pairLinkageTotalLength Q) :
    HasNoSeparatorTriple s (Erdos718.PairLinkage.liftInduce hA L₀) := by
  intro i n hn
  by_contra hall
  push Not at hall
  have hn₀ : n + 2 ≤ (L₀.path i).length := by
    simpa only [length_liftInduce] using hn
  have hne₀ : (L₀.path i).getVert n ≠
      (L₀.path i).getVert (n + 2) := by
    intro h
    have := Walk.IsPath.getVert_inj_of_le (L₀.isPath i)
      (by omega) hn₀ h
    omega
  have hsep0 : (((L₀.path i).getVert n : A) :
      (s.left : Set V)) ∈ {x : (s.left : Set V) | (x : V) ∈ s.separator} := by
    change (((L₀.path i).getVert n : A) : V) ∈ s.separator
    simpa only [getVert_liftInduce] using hall.1
  have hsep2 : (((L₀.path i).getVert (n + 2) : A) :
      (s.left : Set V)) ∈ {x : (s.left : Set V) | (x : V) ∈ s.separator} := by
    change (((L₀.path i).getVert (n + 2) : A) : V) ∈ s.separator
    simpa only [getVert_liftInduce] using hall.2.2
  have hadjTorso : (leftTorso s).Adj
      ((L₀.path i).getVert n : A)
      ((L₀.path i).getVert (n + 2) : A) := by
    apply Or.inr
    refine ⟨hsep0, hsep2, ?_⟩
    intro h
    exact hne₀ (Subtype.ext h)
  have hadjInduced : ((leftTorso s).induce A).Adj
      ((L₀.path i).getVert n) ((L₀.path i).getVert (n + 2)) :=
    hadjTorso
  exact (not_adj_getVert_add_two_of_minimal L₀ hminimal i n hn₀)
    hadjInduced

/-- If `Y` is linked inside the torso induced on `A`, then its ambient copy
is linked inside `A` together with the original right side. -/
theorem isLinkedSet_induce_expandedLeftRegion
    {G : SimpleGraph V} (s : Erdos718.Separation G)
    (A Y : Set (s.left : Set V)) (hYA : Y ⊆ A)
    (hleft : Erdos718.IsLinkedSet ((leftTorso s).induce A)
      {a : A | (a : (s.left : Set V)) ∈ Y})
    (hright : Erdos718.IsLinkedSet (G.induce (s.right : Set V))
      (rightSeparator s : Set (s.right : Set V))) :
    Erdos718.IsLinkedSet (G.induce (expandedLeftRegion s A))
      {z : expandedLeftRegion s A | (z : V) ∈ liftLeftSet s Y} := by
  classical
  intro I _ terminal hrange
  let ambientTerminal : Sum I I ↪ V :=
    terminal.trans (Function.Embedding.subtype _)
  have hambientY : Set.range ambientTerminal ⊆ liftLeftSet s Y := by
    rintro _ ⟨z, rfl⟩
    exact hrange ⟨z, rfl⟩
  have hambientLeft : Set.range ambientTerminal ⊆
      (s.left : Set V) := by
    intro x hx
    obtain ⟨y, hyY, hyx⟩ := hambientY hx
    rw [← hyx]
    exact y.property
  let terminalLeft : Sum I I ↪ (s.left : Set V) :=
    terminalIntoSet (s.left : Set V) ambientTerminal hambientLeft
  have hterminalY : Set.range terminalLeft ⊆ Y := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨y, hyY, hyval⟩ := hambientY ⟨z, rfl⟩
    have heq : terminalLeft z = y := by
      apply Subtype.ext
      exact hyval.symm
    exact heq ▸ hyY
  have hterminalA : Set.range terminalLeft ⊆ A := hterminalY.trans hYA
  have hL₀ : Nonempty (Erdos718.PairLinkage ((leftTorso s).induce A)
      {a : A | (a : (s.left : Set V)) ∈ Y}
      (terminalIntoSet A terminalLeft hterminalA)) :=
    hleft I (terminalIntoSet A terminalLeft hterminalA) (by
      rintro _ ⟨z, rfl⟩
      exact hterminalY ⟨z, rfl⟩)
  obtain ⟨L₀, hminimal⟩ := exists_minimal_pairLinkageTotalLength hL₀
  let L : Erdos718.PairLinkage (leftTorso s) Y terminalLeft :=
    Erdos718.PairLinkage.liftInduce hterminalA L₀
  have hnoTriple : HasNoSeparatorTriple s L := by
    exact hasNoSeparatorTriple_liftInduce_of_minimal
      s hterminalA L₀ hminimal
  have hvirtual : Set.range (separatorEdgeTerminal s L hnoTriple) ⊆
      (rightSeparator s : Set (s.right : Set V)) := by
    rintro z ⟨q, rfl⟩
    change separatorEdgeTerminal s L hnoTriple q ∈ rightSeparator s
    rw [mem_rightSeparator]
    cases q with
    | inl o => exact o.2.1
    | inr o => exact o.2.2
  obtain ⟨M⟩ := hright (SeparatorEdgeOccurrence s L)
    (separatorEdgeTerminal s L hnoTriple) hvirtual
  let LG := Erdos718.PairLinkage.expandLeftTorso s L hnoTriple M
  have hLGsupport : ∀ i x, x ∈ (LG.path i).support →
      x ∈ expandedLeftRegion s A := by
    intro i x hx
    have hallowed := Erdos718.PairLinkage.support_expandLeftTorso_allowed
      s L hnoTriple M i hx
    rcases hallowed with ⟨y, hy, hyx⟩ | ⟨o, _hoi, hxo⟩
    · right
      refine ⟨y, ?_, hyx⟩
      exact Erdos718.PairLinkage.support_liftInduce_subset
        hterminalA L₀ i hy
    · left
      exact mem_right_of_mem_central_support s L hnoTriple M o hxo
  have hterminalRegion : Set.range (leftTerminalToGraph s terminalLeft) ⊆
      expandedLeftRegion s A := by
    rintro _ ⟨z, rfl⟩
    right
    refine ⟨terminalLeft z, hterminalA ⟨z, rfl⟩, rfl⟩
  let LR := Erdos718.PairLinkage.restrictInduce LG hLGsupport hterminalRegion
  have hterm : terminalIntoSet (expandedLeftRegion s A)
      (leftTerminalToGraph s terminalLeft) hterminalRegion = terminal := by
    apply Function.Embedding.ext
    intro z
    apply Subtype.ext
    rfl
  exact ⟨by simpa only [hterm] using LR⟩

end ThomasWollanMassed
end Erdos717
