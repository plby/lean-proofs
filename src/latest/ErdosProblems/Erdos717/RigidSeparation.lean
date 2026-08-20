/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Rigid separations and right-side restriction for the Thomas--Wollan
minimal-counterexample argument.
-/

import ErdosProblems.Erdos717.NoIsolated

open Function Set
open SimpleGraph
open scoped Sym2

namespace Erdos717
namespace ThomasWollanMassed

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The graph/terminal-set form of a failure of the second mass condition. -/
def ViolatesSecondFor (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (k : ℕ) (s : Erdos718.Separation G) : Prop :=
  X ⊆ s.left ∧ s.separator.card < X.card ∧
    8 * k * (s.right \ s.left).card <
      incidentEdges G (s.right \ s.left)

/-- The separator, regarded as a finset in the right-hand induced graph. -/
def rightSeparator {G : SimpleGraph V} (s : Erdos718.Separation G) :
    Finset (s.right : Set V) :=
  MassedCounterexample.restrictFinset (s.right : Set V) s.separator
    (fun _ hx => (Finset.mem_inter.mp hx).2)

@[simp] lemma rightSeparator_card {G : SimpleGraph V}
    (s : Erdos718.Separation G) :
    (rightSeparator s).card = s.separator.card := by
  exact MassedCounterexample.card_restrictFinset _ _ _

@[simp] lemma mem_rightSeparator {G : SimpleGraph V}
    (s : Erdos718.Separation G) (x : (s.right : Set V)) :
    x ∈ rightSeparator s ↔ (x : V) ∈ s.separator := by
  exact MassedCounterexample.mem_restrictFinset _ _ _ x

/-- A vertex of the right side is outside its separator exactly when its
underlying vertex lies in the strict right side. -/
lemma mem_univ_sdiff_rightSeparator_iff {G : SimpleGraph V}
    (s : Erdos718.Separation G) (x : (s.right : Set V)) :
    x ∈ Finset.univ \ rightSeparator s ↔
      (x : V) ∈ s.right \ s.left := by
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
    mem_rightSeparator, Erdos718.Separation.separator,
    Finset.mem_inter]
  exact ⟨fun h => ⟨x.property, fun hxL => h ⟨hxL, x.property⟩⟩,
    fun h hsep => h.2 hsep.1⟩

/-- Every edge incident with the strict right side of a separation has both
ends in the right side. -/
lemma edge_endpoints_right_of_touches_strictRight {G : SimpleGraph V}
    (s : Erdos718.Separation G) {a b : V} (hab : G.Adj a b)
    (htouch : a ∈ s.right \ s.left ∨ b ∈ s.right \ s.left) :
    a ∈ s.right ∧ b ∈ s.right := by
  rcases htouch with ha | hb
  · rw [Finset.mem_sdiff] at ha
    refine ⟨ha.1, ?_⟩
    rcases s.mem_left_or_mem_right b with hbL | hbR
    · by_cases hbR : b ∈ s.right
      · exact hbR
      · exact (s.not_adj hbL hbR ha.1 ha.2 hab.symm).elim
    · exact hbR
  · rw [Finset.mem_sdiff] at hb
    refine ⟨?_, hb.1⟩
    rcases s.mem_left_or_mem_right a with haL | haR
    · by_cases haR : a ∈ s.right
      · exact haR
      · exact (s.not_adj haL haR hb.1 hb.2 hab).elim
    · exact haR

lemma not_pair_subset_compl_iff {W : Type*} [Fintype W] [DecidableEq W]
    (S : Finset W) (a b : W) :
    ¬s(a, b).toFinset ⊆ Finset.univ \ S ↔ a ∈ S ∨ b ∈ S := by
  simp only [Sym2.toFinset_mk_eq, Finset.insert_subset_iff,
    Finset.singleton_subset_iff, Finset.mem_sdiff, Finset.mem_univ,
    true_and]
  tauto

/-- Inducing on `A` preserves the incident-edge count of `S` when every
edge touching the image of `S` has both endpoints in `A`. -/
lemma incidentEdges_induce_of_closed (G : SimpleGraph V)
    [DecidableRel G.Adj] (A : Set V) [Fintype A] [DecidableEq A]
    (S : Finset A)
    (hclosed : ∀ {a b : V}, G.Adj a b →
      (a ∈ S.map (Function.Embedding.subtype A) ∨
        b ∈ S.map (Function.Embedding.subtype A)) →
      a ∈ A ∧ b ∈ A) :
    incidentEdges (G.induce A) S =
      incidentEdges G (S.map (Function.Embedding.subtype A)) := by
  classical
  let f : A ↪ V := Function.Embedding.subtype A
  unfold incidentEdges
  rw [← Finset.card_map f.sym2Map]
  congr 1
  ext e
  constructor
  · intro he
    rw [Finset.mem_map] at he
    obtain ⟨e₀, he₀, rfl⟩ := he
    simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset] at he₀ ⊢
    induction e₀ using Sym2.inductionOn with
    | _ a b =>
        change G.Adj (a : V) (b : V) ∧
          ¬s((a : V), (b : V)).toFinset ⊆
            Finset.univ \ S.map f
        rw [not_pair_subset_compl_iff] at he₀ ⊢
        exact ⟨he₀.1, he₀.2.imp
          (fun ha => Finset.mem_map.mpr ⟨a, ha, rfl⟩)
          (fun hb => Finset.mem_map.mpr ⟨b, hb, rfl⟩)⟩
  · intro he
    simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset] at he
    induction e using Sym2.inductionOn with
    | _ a b =>
        rw [not_pair_subset_compl_iff] at he
        obtain ⟨haA, hbA⟩ := hclosed he.1 he.2
        let a' : A := ⟨a, haA⟩
        let b' : A := ⟨b, hbA⟩
        refine Finset.mem_map.mpr ⟨s(a', b'), ?_, rfl⟩
        simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset]
        rw [not_pair_subset_compl_iff]
        refine ⟨he.1, ?_⟩
        rcases he.2 with ha | hb
        · left
          rw [Finset.mem_map] at ha
          obtain ⟨z, hz, hza⟩ := ha
          have : z = a' := Subtype.ext hza
          simpa [this] using hz
        · right
          rw [Finset.mem_map] at hb
          obtain ⟨z, hz, hzb⟩ := hb
          have : z = b' := Subtype.ext hzb
          simpa [this] using hz

/-- Restricting to the right side preserves exactly the edges incident with
the strict right side. -/
lemma incidentEdges_induce_right (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Erdos718.Separation G) :
    incidentEdges (G.induce (s.right : Set V))
        (Finset.univ \ rightSeparator s) =
      incidentEdges G (s.right \ s.left) := by
  classical
  let f : (s.right : Set V) ↪ V := Function.Embedding.subtype _
  unfold incidentEdges
  rw [← Finset.card_map f.sym2Map]
  congr 1
  ext e
  constructor
  · intro he
    rw [Finset.mem_map] at he
    obtain ⟨e₀, he₀, rfl⟩ := he
    simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset] at he₀ ⊢
    induction e₀ using Sym2.inductionOn with
    | _ a b =>
        change G.Adj (a : V) (b : V) ∧
          ¬s((a : V), (b : V)).toFinset ⊆
            Finset.univ \ (s.right \ s.left)
        rw [not_pair_subset_compl_iff] at he₀ ⊢
        refine ⟨he₀.1, ?_⟩
        exact he₀.2.imp
          (fun ha => (mem_univ_sdiff_rightSeparator_iff s a).mp ha)
          (fun hb => (mem_univ_sdiff_rightSeparator_iff s b).mp hb)
  · intro he
    simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset] at he
    induction e using Sym2.inductionOn with
    | _ a b =>
        rw [not_pair_subset_compl_iff] at he
        have htouch : a ∈ s.right \ s.left ∨ b ∈ s.right \ s.left := he.2
        obtain ⟨haR, hbR⟩ := edge_endpoints_right_of_touches_strictRight s
          he.1 htouch
        let a' : (s.right : Set V) := ⟨a, haR⟩
        let b' : (s.right : Set V) := ⟨b, hbR⟩
        refine Finset.mem_map.mpr ⟨s(a', b'), ?_, ?_⟩
        · simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset]
          rw [not_pair_subset_compl_iff]
          refine ⟨he.1, ?_⟩
          exact htouch.imp
            (fun ha => (mem_univ_sdiff_rightSeparator_iff s a').mpr ha)
            (fun hb => (mem_univ_sdiff_rightSeparator_iff s b').mpr hb)
        · rfl

/-! ### Nesting a separation inside the right side -/

/-- Replace the right side of `s` by a separation of the graph induced on
that side. -/
def composeRight {G : SimpleGraph V} (s : Erdos718.Separation G)
    (t : Erdos718.Separation (G.induce (s.right : Set V)))
    (hseparator : rightSeparator s ⊆ t.left) :
    Erdos718.Separation G where
  left := (s.left \ s.right) ∪
    t.left.map (Function.Embedding.subtype _)
  right := t.right.map (Function.Embedding.subtype _)
  cover := by
    ext x
    simp only [Finset.mem_union, Finset.mem_map, Finset.mem_univ,
      iff_true]
    rcases s.mem_left_or_mem_right x with hxL | hxR
    · by_cases hxR : x ∈ s.right
      · let x' : (s.right : Set V) := ⟨x, hxR⟩
        rcases t.mem_left_or_mem_right x' with hxLt | hxRt
        · exact Or.inl (Or.inr ⟨x', hxLt, rfl⟩)
        · exact Or.inr ⟨x', hxRt, rfl⟩
      · exact Or.inl (Or.inl (Finset.mem_sdiff.mpr ⟨hxL, hxR⟩))
    · let x' : (s.right : Set V) := ⟨x, hxR⟩
      rcases t.mem_left_or_mem_right x' with hxL | hxR
      · exact Or.inl (Or.inr ⟨x', hxL, rfl⟩)
      · exact Or.inr ⟨x', hxR, rfl⟩
  not_adj := by
    intro a b haL haR hbR hbL hab
    rw [Finset.mem_map] at hbR
    obtain ⟨b', hbRt, hbval⟩ := hbR
    have hbval' : (b' : V) = b := hbval
    have hbNotLt : b' ∉ t.left := by
      intro hbLt
      apply hbL
      exact Finset.mem_union.mpr (Or.inr
        (Finset.mem_map.mpr ⟨b', hbLt, hbval'⟩))
    rcases Finset.mem_union.mp haL with haLs | haLt
    · rw [Finset.mem_sdiff] at haLs
      have hbNotLs : b ∉ s.left := by
        intro hbLs
        have hbSep : b' ∈ rightSeparator s := by
          rw [mem_rightSeparator]
          exact Finset.mem_inter.mpr ⟨hbval' ▸ hbLs, b'.property⟩
        exact hbNotLt (hseparator hbSep)
      have hbNotLs' : (b' : V) ∉ s.left := by
        simpa only [hbval'] using hbNotLs
      exact s.not_adj haLs.1 haLs.2 b'.property hbNotLs' (by rwa [hbval'])
    · rw [Finset.mem_map] at haLt
      obtain ⟨a', haLt, haval⟩ := haLt
      have haval' : (a' : V) = a := haval
      have haRt : a' ∉ t.right := by
        intro h
        exact haR (Finset.mem_map.mpr ⟨a', h, haval'⟩)
      exact t.not_adj haLt haRt hbRt hbNotLt (by
        change G.Adj (a' : V) (b' : V)
        rwa [haval', hbval'])

lemma composeRight_right {G : SimpleGraph V} (s : Erdos718.Separation G)
    (t : Erdos718.Separation (G.induce (s.right : Set V)))
    (hseparator : rightSeparator s ⊆ t.left) :
    (composeRight s t hseparator).right =
      t.right.map (Function.Embedding.subtype _) := rfl

lemma composeRight_separator {G : SimpleGraph V}
    (s : Erdos718.Separation G)
    (t : Erdos718.Separation (G.induce (s.right : Set V)))
    (hseparator : rightSeparator s ⊆ t.left) :
    (composeRight s t hseparator).separator =
      t.separator.map (Function.Embedding.subtype _) := by
  classical
  ext x
  simp only [Erdos718.Separation.separator, composeRight,
    Finset.mem_inter, Finset.mem_union, Finset.mem_map]
  constructor
  · rintro ⟨haL | ⟨a, haL, haval⟩, ⟨b, hbR, hbval⟩⟩
    · rw [Finset.mem_sdiff] at haL
      exact (haL.2 (hbval ▸ b.property)).elim
    · have hab : a = b := by
        apply Subtype.ext
        exact haval.trans hbval.symm
      subst b
      exact ⟨a, ⟨haL, hbR⟩, haval⟩
  · rintro ⟨a, ⟨haL, haR⟩, haval⟩
    exact ⟨Or.inr ⟨a, haL, haval⟩, ⟨a, haR, haval⟩⟩

lemma composeRight_strictRight {G : SimpleGraph V}
    (s : Erdos718.Separation G)
    (t : Erdos718.Separation (G.induce (s.right : Set V)))
    (hseparator : rightSeparator s ⊆ t.left) :
    (composeRight s t hseparator).right \
        (composeRight s t hseparator).left =
      (t.right \ t.left).map (Function.Embedding.subtype _) := by
  classical
  ext x
  simp only [composeRight, Finset.mem_sdiff, Finset.mem_map,
    Finset.mem_union]
  constructor
  · rintro ⟨⟨a, haR, haval⟩, hnot⟩
    have haL : a ∉ t.left := by
      intro h
      exact hnot (Or.inr ⟨a, h, haval⟩)
    exact ⟨a, ⟨haR, haL⟩, haval⟩
  · rintro ⟨a, ha, haval⟩
    refine ⟨⟨a, ha.1, haval⟩, ?_⟩
    rintro (hxLs | ⟨b, hbL, hbval⟩)
    · exact hxLs.2 (haval ▸ a.property)
    · have hab : a = b := by
        apply Subtype.ext
        exact haval.trans hbval.symm
      exact ha.2 (hab ▸ hbL)

@[simp] lemma composeRight_separator_card {G : SimpleGraph V}
    (s : Erdos718.Separation G)
    (t : Erdos718.Separation (G.induce (s.right : Set V)))
    (hseparator : rightSeparator s ⊆ t.left) :
    (composeRight s t hseparator).separator.card = t.separator.card := by
  rw [composeRight_separator s t hseparator, Finset.card_map]

@[simp] lemma composeRight_strictRight_card {G : SimpleGraph V}
    (s : Erdos718.Separation G)
    (t : Erdos718.Separation (G.induce (s.right : Set V)))
    (hseparator : rightSeparator s ⊆ t.left) :
    ((composeRight s t hseparator).right \
      (composeRight s t hseparator).left).card =
      (t.right \ t.left).card := by
  rw [composeRight_strictRight s t hseparator, Finset.card_map]

lemma subset_left_composeRight {G : SimpleGraph V}
    (s : Erdos718.Separation G)
    (t : Erdos718.Separation (G.induce (s.right : Set V)))
    {X : Finset V} (hX : X ⊆ s.left)
    (hseparator : rightSeparator s ⊆ t.left) :
    X ⊆ (composeRight s t hseparator).left := by
  intro x hx
  have hxL := hX hx
  by_cases hxR : x ∈ s.right
  · let x' : (s.right : Set V) := ⟨x, hxR⟩
    have hxSep : x' ∈ rightSeparator s := by
      rw [mem_rightSeparator]
      exact Finset.mem_inter.mpr ⟨hxL, hxR⟩
    exact Finset.mem_union.mpr (Or.inr
      (Finset.mem_map.mpr ⟨x', hseparator hxSep, rfl⟩))
  · exact Finset.mem_union.mpr
      (Or.inl (Finset.mem_sdiff.mpr ⟨hxL, hxR⟩))

/-- A right-cardinality-minimal violation for an arbitrary finite graph. -/
theorem exists_minimal_violatesSecondFor (G : SimpleGraph V)
    [DecidableRel G.Adj] (X : Finset V) (k : ℕ)
    (hbad : ∃ s : Erdos718.Separation G,
      ViolatesSecondFor G X k s) :
    ∃ s : Erdos718.Separation G,
      ViolatesSecondFor G X k s ∧
      ∀ t : Erdos718.Separation G,
        ViolatesSecondFor G X k t → s.right.card ≤ t.right.card := by
  classical
  let P : ℕ → Prop := fun n => ∃ s : Erdos718.Separation G,
    ViolatesSecondFor G X k s ∧ s.right.card = n
  have hP : ∃ n, P n := by
    obtain ⟨s, hs⟩ := hbad
    exact ⟨s.right.card, s, hs, rfl⟩
  let n₀ := Nat.find hP
  obtain ⟨s, hs, hscard⟩ := Nat.find_spec hP
  refine ⟨s, hs, ?_⟩
  intro t ht
  have hle : n₀ ≤ t.right.card := Nat.find_min' hP ⟨t, ht, rfl⟩
  rwa [hscard]

lemma strictRight_card_add_separator_card_for
    {G : SimpleGraph V} (s : Erdos718.Separation G) :
    (s.right \ s.left).card + s.separator.card = s.right.card := by
  have hdisj : Disjoint (s.right \ s.left) s.separator := by
    apply Finset.disjoint_left.mpr
    intro x hxR hxS
    exact (Finset.mem_sdiff.mp hxR).2 (Finset.mem_inter.mp hxS).1
  calc
    (s.right \ s.left).card + s.separator.card =
        ((s.right \ s.left) ∪ s.separator).card := by
          rw [Finset.card_union_of_disjoint hdisj]
    _ = s.right.card := by
      rw [← Erdos718.Separation.right_eq_strictRight_union_separator]

/-- The induced right side of a right-cardinality-minimal violation is
eight-massed, in graph/finset form. -/
theorem isEightKMassed_induce_right_of_minimal_violationFor
    (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) (k : ℕ)
    (s : Erdos718.Separation G) (hs : ViolatesSecondFor G X k s)
    (hminimal : ∀ t : Erdos718.Separation G,
      ViolatesSecondFor G X k t → s.right.card ≤ t.right.card) :
    IsEightKMassed (G.induce (s.right : Set V)) (rightSeparator s) k := by
  classical
  constructor
  · rw [incidentEdges_induce_right, rightSeparator_card]
    have hcard : Fintype.card (s.right : Set V) = s.right.card := by simp
    rw [hcard]
    have hsplit := strictRight_card_add_separator_card_for s
    have hdiff : s.right.card - s.separator.card =
        (s.right \ s.left).card := by omega
    rw [hdiff]
    exact hs.2.2
  · intro t hSepLeft horder
    by_contra hbound
    have hviolateInduced : 8 * k * (t.right \ t.left).card <
        incidentEdges (G.induce (s.right : Set V))
          (t.right \ t.left) := Nat.lt_of_not_ge hbound
    let q := composeRight s t hSepLeft
    have hqX : X ⊆ q.left :=
      subset_left_composeRight s t hs.1 hSepLeft
    have hqOrder : q.separator.card < X.card := by
      rw [composeRight_separator_card s t hSepLeft]
      exact horder.trans_le (by
        rw [rightSeparator_card]
        exact hs.2.1.le)
    have hqIncident : incidentEdges G (q.right \ q.left) =
        incidentEdges (G.induce (s.right : Set V))
          (t.right \ t.left) := by
      let f : (s.right : Set V) ↪ V := Function.Embedding.subtype _
      have hf : f = Function.Embedding.subtype (s.right : Set V) := by rfl
      have hmap : (t.right \ t.left).map f = q.right \ q.left :=
        (composeRight_strictRight s t hSepLeft).symm
      have hclosed : ∀ {a b : V}, G.Adj a b →
          (a ∈ (t.right \ t.left).map f ∨
            b ∈ (t.right \ t.left).map f) →
          a ∈ (s.right : Set V) ∧ b ∈ (s.right : Set V) := by
        intro a b hab htouch
        rw [hmap] at htouch
        obtain ⟨haq, hbq⟩ :=
          edge_endpoints_right_of_touches_strictRight q hab htouch
        have hqsub : q.right ⊆ s.right := by
          intro x hx
          rw [composeRight_right s t hSepLeft, Finset.mem_map] at hx
          obtain ⟨z, hz, rfl⟩ := hx
          exact z.property
        exact ⟨hqsub haq, hqsub hbq⟩
      have hi := incidentEdges_induce_of_closed G (s.right : Set V)
        (t.right \ t.left) hclosed
      calc
        incidentEdges G (q.right \ q.left) =
            incidentEdges G ((t.right \ t.left).map f) := by rw [hmap]
        _ = incidentEdges (G.induce (s.right : Set V))
              (t.right \ t.left) := by rw [hf]; exact hi.symm
    have hqBad : ViolatesSecondFor G X k q := by
      refine ⟨hqX, hqOrder, ?_⟩
      rw [composeRight_strictRight_card s t hSepLeft, hqIncident]
      exact hviolateInduced
    have hleftStrict : (t.left \ t.right).Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      have hleftSub : t.left ⊆ t.right := by
        intro x hxL
        by_contra hxR
        have hx : x ∈ t.left \ t.right := Finset.mem_sdiff.mpr ⟨hxL, hxR⟩
        simpa [hempty] using hx
      have hSepSub : rightSeparator s ⊆ t.separator := by
        intro x hx
        exact Finset.mem_inter.mpr ⟨hSepLeft hx, hleftSub (hSepLeft hx)⟩
      have hcardle := Finset.card_le_card hSepSub
      rw [rightSeparator_card] at hcardle
      have horder' : t.separator.card < s.separator.card := by
        simpa only [rightSeparator_card] using horder
      exact (Nat.not_le_of_lt horder') hcardle
    have hrightLt : t.right.card < s.right.card := by
      have hproper : t.right ⊂ (Finset.univ : Finset (s.right : Set V)) := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, ?_⟩
        intro heq
        obtain ⟨x, hx⟩ := hleftStrict
        rw [Finset.mem_sdiff] at hx
        exact hx.2 (heq ▸ Finset.mem_univ x)
      simpa using Finset.card_lt_card hproper
    have hqRight : q.right.card = t.right.card := by
      rw [composeRight_right s t hSepLeft, Finset.card_map]
    have hmin := hminimal q hqBad
    rw [hqRight] at hmin
    exact (Nat.not_le_of_lt hrightLt) hmin

namespace MassedCounterexample

variable {k : ℕ}

/-- A separation witnessing failure of the second eight-massed condition. -/
def ViolatesSecond (C : MassedCounterexample k)
    (s : Erdos718.Separation C.G) : Prop :=
  C.X ⊆ s.left ∧ s.separator.card < C.X.card ∧
    8 * k * (s.right \ s.left).card <
      incidentEdges C.G (s.right \ s.left)

lemma strictRight_card_add_separator_card
    (C : MassedCounterexample k) (s : Erdos718.Separation C.G) :
    (s.right \ s.left).card + s.separator.card = s.right.card := by
  have hdisj : Disjoint (s.right \ s.left) s.separator := by
    apply Finset.disjoint_left.mpr
    intro x hxR hxS
    exact (Finset.mem_sdiff.mp hxR).2 (Finset.mem_inter.mp hxS).1
  calc
    (s.right \ s.left).card + s.separator.card =
        ((s.right \ s.left) ∪ s.separator).card := by
          rw [Finset.card_union_of_disjoint hdisj]
    _ = s.right.card := by
      rw [← Erdos718.Separation.right_eq_strictRight_union_separator]

/-- Among a nonempty finite family of violating separations, one has a
right side of minimum cardinality. -/
theorem exists_minimal_violatesSecond (C : MassedCounterexample k)
    (hbad : ∃ s : Erdos718.Separation C.G, C.ViolatesSecond s) :
    ∃ s : Erdos718.Separation C.G,
      C.ViolatesSecond s ∧
      ∀ t : Erdos718.Separation C.G,
        C.ViolatesSecond t → s.right.card ≤ t.right.card := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ s : Erdos718.Separation C.G,
      C.ViolatesSecond s ∧ s.right.card = n
  have hP : ∃ n, P n := by
    obtain ⟨s, hs⟩ := hbad
    exact ⟨s.right.card, s, hs, rfl⟩
  let n₀ := Nat.find hP
  obtain ⟨s, hs, hscard⟩ := Nat.find_spec hP
  refine ⟨s, hs, ?_⟩
  intro t ht
  have hle : n₀ ≤ t.right.card :=
    Nat.find_min' hP ⟨t, ht, rfl⟩
  rwa [hscard]

/-- The right side of a right-cardinality-minimal violation is itself an
eight-massed pair with its old separator as distinguished set. -/
theorem isEightKMassed_induce_right_of_minimal_violation
    (C : MassedCounterexample k) (s : Erdos718.Separation C.G)
    (hs : C.ViolatesSecond s)
    (hminimal : ∀ t : Erdos718.Separation C.G,
      C.ViolatesSecond t → s.right.card ≤ t.right.card) :
    IsEightKMassed (C.G.induce (s.right : Set C.V))
      (rightSeparator s) k := by
  classical
  constructor
  · rw [incidentEdges_induce_right]
    rw [rightSeparator_card]
    have hcard : Fintype.card (s.right : Set C.V) = s.right.card := by simp
    rw [hcard]
    have hsplit := strictRight_card_add_separator_card C s
    have hdiff : s.right.card - s.separator.card =
        (s.right \ s.left).card := by omega
    rw [hdiff]
    exact hs.2.2
  · intro t hSepLeft horder
    by_contra hbound
    have hviolateInduced :
        8 * k * (t.right \ t.left).card <
          incidentEdges (C.G.induce (s.right : Set C.V))
            (t.right \ t.left) := Nat.lt_of_not_ge hbound
    let q := composeRight s t hSepLeft
    have hqX : C.X ⊆ q.left :=
      subset_left_composeRight s t hs.1 hSepLeft
    have hqOrder : q.separator.card < C.X.card := by
      rw [composeRight_separator_card s t hSepLeft]
      exact horder.trans_le (by
        rw [rightSeparator_card]
        exact hs.2.1.le)
    have hqIncident : incidentEdges C.G (q.right \ q.left) =
        incidentEdges (C.G.induce (s.right : Set C.V))
          (t.right \ t.left) := by
      let f : (s.right : Set C.V) ↪ C.V := Function.Embedding.subtype _
      have hf : f = Function.Embedding.subtype (s.right : Set C.V) := by
        rfl
      have hmap : (t.right \ t.left).map f = q.right \ q.left := by
        exact (composeRight_strictRight s t hSepLeft).symm
      have hclosed : ∀ {a b : C.V}, C.G.Adj a b →
          (a ∈ (t.right \ t.left).map f ∨
            b ∈ (t.right \ t.left).map f) →
          a ∈ (s.right : Set C.V) ∧ b ∈ (s.right : Set C.V) := by
        intro a b hab htouch
        rw [hmap] at htouch
        obtain ⟨haq, hbq⟩ :=
          edge_endpoints_right_of_touches_strictRight q hab htouch
        have hqsub : q.right ⊆ s.right := by
          intro x hx
          rw [composeRight_right s t hSepLeft, Finset.mem_map] at hx
          obtain ⟨z, hz, rfl⟩ := hx
          exact z.property
        exact ⟨hqsub haq, hqsub hbq⟩
      have hi := incidentEdges_induce_of_closed C.G (s.right : Set C.V)
        (t.right \ t.left) hclosed
      calc
        incidentEdges C.G (q.right \ q.left) =
            incidentEdges C.G ((t.right \ t.left).map f) := by
              rw [hmap]
        _ = incidentEdges (C.G.induce (s.right : Set C.V))
              (t.right \ t.left) := by
              rw [hf]
              exact hi.symm
    have hqStrictCard : (q.right \ q.left).card =
        (t.right \ t.left).card :=
      composeRight_strictRight_card s t hSepLeft
    have hqBad : C.ViolatesSecond q := by
      refine ⟨hqX, hqOrder, ?_⟩
      rw [hqStrictCard, hqIncident]
      exact hviolateInduced
    have hleftStrict : (t.left \ t.right).Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      have hleftSub : t.left ⊆ t.right := by
        intro x hxL
        by_contra hxR
        have : x ∈ t.left \ t.right := Finset.mem_sdiff.mpr ⟨hxL, hxR⟩
        simpa [hempty] using this
      have hSepSub : rightSeparator s ⊆ t.separator := by
        intro x hx
        exact Finset.mem_inter.mpr ⟨hSepLeft hx, hleftSub (hSepLeft hx)⟩
      have hcardle := Finset.card_le_card hSepSub
      rw [rightSeparator_card] at hcardle
      have horder' : t.separator.card < s.separator.card := by
        simpa only [rightSeparator_card] using horder
      exact (Nat.not_le_of_lt horder') hcardle
    have hrightLt : t.right.card < s.right.card := by
      have hproper : t.right ⊂ (Finset.univ : Finset (s.right : Set C.V)) := by
        refine Finset.ssubset_iff_subset_ne.mpr
          ⟨Finset.subset_univ _, ?_⟩
        intro heq
        obtain ⟨x, hx⟩ := hleftStrict
        rw [Finset.mem_sdiff] at hx
        exact hx.2 (heq ▸ Finset.mem_univ x)
      have := Finset.card_lt_card hproper
      simpa using this
    have hqRight : q.right.card = t.right.card := by
      rw [composeRight_right s t hSepLeft, Finset.card_map]
    have hmin := hminimal q hqBad
    rw [hqRight] at hmin
    exact (Nat.not_le_of_lt hrightLt) hmin

/-- Lexicographic vertex-minimality turns the massed right side of a
minimal violation into a linked set. -/
theorem linked_induce_right_of_minimal_violation
    (C : MassedCounterexample k) (hlex : C.IsLexMinimal)
    (s : Erdos718.Separation C.G) (hs : C.ViolatesSecond s)
    (hminimal : ∀ t : Erdos718.Separation C.G,
      C.ViolatesSecond t → s.right.card ≤ t.right.card) :
    Erdos718.IsLinkedSet (C.G.induce (s.right : Set C.V))
      (rightSeparator s : Set (s.right : Set C.V)) := by
  classical
  by_contra hnot
  let D : MassedCounterexample k := {
    V := (s.right : Set C.V)
    fintypeV := inferInstance
    decEqV := inferInstance
    G := C.G.induce (s.right : Set C.V)
    decAdj := inferInstance
    X := rightSeparator s
    card_le := by
      rw [rightSeparator_card]
      exact hs.2.1.le.trans C.card_le
    massed := isEightKMassed_induce_right_of_minimal_violation
      C s hs hminimal
    not_linked := hnot
  }
  have hleftStrict : (s.left \ s.right).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    have hleftSub : s.left ⊆ s.right := by
      intro x hxL
      by_contra hxR
      have : x ∈ s.left \ s.right := Finset.mem_sdiff.mpr ⟨hxL, hxR⟩
      simpa [hempty] using this
    have hXSep : C.X ⊆ s.separator := by
      intro x hx
      exact Finset.mem_inter.mpr ⟨hs.1 hx, hleftSub (hs.1 hx)⟩
    have hcard := Finset.card_le_card hXSep
    exact (Nat.not_le_of_lt hs.2.1) hcard
  have hrightLt : s.right.card < Fintype.card C.V := by
    have hproper : s.right ⊂ (Finset.univ : Finset C.V) := by
      refine Finset.ssubset_iff_subset_ne.mpr
        ⟨Finset.subset_univ _, ?_⟩
      intro heq
      obtain ⟨x, hx⟩ := hleftStrict
      rw [Finset.mem_sdiff] at hx
      exact hx.2 (heq ▸ Finset.mem_univ x)
    simpa using Finset.card_lt_card hproper
  have hminimalVertices := (hlex D).1
  change Fintype.card C.V ≤ Fintype.card (s.right : Set C.V) at hminimalVertices
  have hrightCard : Fintype.card (s.right : Set C.V) = s.right.card := by
    simp
  rw [hrightCard] at hminimalVertices
  exact (Nat.not_le_of_lt hrightLt) hminimalVertices

/-- An original separation whose strict right side is too dense and whose
order is at most `|X|` has a massed right side.  Nested violations are ruled
out directly by the second mass condition of `C`. -/
theorem isEightKMassed_induce_right_of_dense_boundary
    (C : MassedCounterexample k) (s : Erdos718.Separation C.G)
    (hX : C.X ⊆ s.left) (horder : s.separator.card ≤ C.X.card)
    (hdense : 8 * k * (s.right \ s.left).card <
      incidentEdges C.G (s.right \ s.left)) :
    IsEightKMassed (C.G.induce (s.right : Set C.V))
      (rightSeparator s) k := by
  classical
  constructor
  · rw [incidentEdges_induce_right, rightSeparator_card]
    have hcard : Fintype.card (s.right : Set C.V) = s.right.card := by simp
    rw [hcard]
    have hsplit := strictRight_card_add_separator_card_for s
    have hdiff : s.right.card - s.separator.card =
        (s.right \ s.left).card := by omega
    rw [hdiff]
    exact hdense
  · intro t hSepLeft htOrder
    let q := composeRight s t hSepLeft
    have hqX : C.X ⊆ q.left :=
      subset_left_composeRight s t hX hSepLeft
    have hqOrder : q.separator.card < C.X.card := by
      rw [composeRight_separator_card s t hSepLeft]
      exact htOrder.trans_le ((rightSeparator_card s).trans_le horder)
    have hmass := C.massed.2 q hqX hqOrder
    have hqIncident : incidentEdges C.G (q.right \ q.left) =
        incidentEdges (C.G.induce (s.right : Set C.V))
          (t.right \ t.left) := by
      let f : (s.right : Set C.V) ↪ C.V := Function.Embedding.subtype _
      have hf : f = Function.Embedding.subtype (s.right : Set C.V) := by rfl
      have hmap : (t.right \ t.left).map f = q.right \ q.left :=
        (composeRight_strictRight s t hSepLeft).symm
      have hclosed : ∀ {a b : C.V}, C.G.Adj a b →
          (a ∈ (t.right \ t.left).map f ∨
            b ∈ (t.right \ t.left).map f) →
          a ∈ (s.right : Set C.V) ∧ b ∈ (s.right : Set C.V) := by
        intro a b hab htouch
        rw [hmap] at htouch
        obtain ⟨haq, hbq⟩ :=
          edge_endpoints_right_of_touches_strictRight q hab htouch
        have hqsub : q.right ⊆ s.right := by
          intro x hx
          rw [composeRight_right s t hSepLeft, Finset.mem_map] at hx
          obtain ⟨z, hz, rfl⟩ := hx
          exact z.property
        exact ⟨hqsub haq, hqsub hbq⟩
      have hi := incidentEdges_induce_of_closed C.G (s.right : Set C.V)
        (t.right \ t.left) hclosed
      calc
        incidentEdges C.G (q.right \ q.left) =
            incidentEdges C.G ((t.right \ t.left).map f) := by rw [hmap]
        _ = incidentEdges (C.G.induce (s.right : Set C.V))
              (t.right \ t.left) := by rw [hf]; exact hi.symm
    rw [composeRight_strictRight_card s t hSepLeft, hqIncident] at hmass
    exact hmass

/-- Vertex-minimality makes the dense boundary side linked whenever its
strict left side is nonempty. -/
theorem linked_induce_right_of_dense_boundary
    (C : MassedCounterexample k) (hlex : C.IsLexMinimal)
    (s : Erdos718.Separation C.G)
    (hX : C.X ⊆ s.left) (horder : s.separator.card ≤ C.X.card)
    (hdense : 8 * k * (s.right \ s.left).card <
      incidentEdges C.G (s.right \ s.left))
    (hleft : (s.left \ s.right).Nonempty) :
    Erdos718.IsLinkedSet (C.G.induce (s.right : Set C.V))
      (rightSeparator s : Set (s.right : Set C.V)) := by
  classical
  by_contra hnot
  let D : MassedCounterexample k := {
    V := (s.right : Set C.V)
    fintypeV := inferInstance
    decEqV := inferInstance
    G := C.G.induce (s.right : Set C.V)
    decAdj := inferInstance
    X := rightSeparator s
    card_le := by rw [rightSeparator_card]; exact horder.trans C.card_le
    massed := isEightKMassed_induce_right_of_dense_boundary
      C s hX horder hdense
    not_linked := hnot
  }
  have hrightLt : s.right.card < Fintype.card C.V := by
    have hproper : s.right ⊂ (Finset.univ : Finset C.V) := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, ?_⟩
      intro heq
      obtain ⟨x, hx⟩ := hleft
      rw [Finset.mem_sdiff] at hx
      exact hx.2 (heq ▸ Finset.mem_univ x)
    simpa using Finset.card_lt_card hproper
  have hvertices := (hlex D).1
  change Fintype.card C.V ≤ Fintype.card (s.right : Set C.V) at hvertices
  have hcard : Fintype.card (s.right : Set C.V) = s.right.card := by simp
  rw [hcard] at hvertices
  exact (Nat.not_le_of_lt hrightLt) hvertices

/-- A rigid separation has a nonempty strict right side and its separator is
linked inside the graph induced by the right side. -/
def IsRigidSeparation (C : MassedCounterexample k)
    (s : Erdos718.Separation C.G) : Prop :=
  C.X ⊆ s.left ∧ (s.right \ s.left).Nonempty ∧
    Erdos718.IsLinkedSet (C.G.induce (s.right : Set C.V))
      (rightSeparator s : Set (s.right : Set C.V))

/-- There is no rigid separation of order at most the distinguished-set
cardinality. -/
def HasNoSmallRigidSeparation (C : MassedCounterexample k) : Prop :=
  ∀ s : Erdos718.Separation C.G,
    C.IsRigidSeparation s → C.X.card < s.separator.card

end MassedCounterexample

end ThomasWollanMassed
end Erdos717
