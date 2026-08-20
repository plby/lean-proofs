/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos518.Alternating

/-!
# Extending a clique by an alternating tail

This file proves the constructive part of Chen--Chen's clique-extension obstruction.  A
finite clique is first put in a Hamilton order ending at a prescribed vertex `e`.  An
alternating list

`y₁, x₁, y₂, x₂, …, yₐ, xₐ`

is then appended.  The hypotheses record exactly the edges used by this list: `yⱼ-xⱼ`,
`xⱼ-yⱼ₊₁`, and the initial bridge `e-y₁`.  The result includes exact support,
length, and intersection-cardinality statements for later use with the predecessor clique.
-/

open scoped SimpleGraph

namespace Erdos518

universe u

variable {V : Type u}

/-- A canonical Hamilton ordering of a finite set, with `e` forced to be last. -/
noncomputable def cliqueHamiltonOrder [DecidableEq V] (S : Finset V) (e : V) : List V :=
  (S.erase e).toList ++ [e]

@[simp] lemma cliqueHamiltonOrder_ne_nil [DecidableEq V] (S : Finset V) (e : V) :
    cliqueHamiltonOrder S e ≠ [] := by
  simp [cliqueHamiltonOrder]

@[simp] lemma getLast_cliqueHamiltonOrder [DecidableEq V] (S : Finset V) (e : V) :
    (cliqueHamiltonOrder S e).getLast (cliqueHamiltonOrder_ne_nil S e) = e := by
  simp [cliqueHamiltonOrder]

@[simp] lemma getLast?_cliqueHamiltonOrder [DecidableEq V] (S : Finset V) (e : V) :
    (cliqueHamiltonOrder S e).getLast? = some e := by
  simp [cliqueHamiltonOrder]

lemma nodup_cliqueHamiltonOrder [DecidableEq V] (S : Finset V) (e : V) :
    (cliqueHamiltonOrder S e).Nodup := by
  rw [cliqueHamiltonOrder]
  exact (S.erase e).nodup_toList.append (by simp)
    (List.disjoint_singleton.mpr (by simp))

@[simp] lemma toFinset_cliqueHamiltonOrder [DecidableEq V] {S : Finset V} {e : V}
    (he : e ∈ S) : (cliqueHamiltonOrder S e).toFinset = S := by
  simp [cliqueHamiltonOrder, he]

@[simp] lemma length_cliqueHamiltonOrder [DecidableEq V] {S : Finset V} {e : V}
    (he : e ∈ S) : (cliqueHamiltonOrder S e).length = S.card := by
  rw [← List.toFinset_card_of_nodup (nodup_cliqueHamiltonOrder S e)]
  simp [he]

/-- The canonical ordering of a clique is a path and ends at the prescribed vertex. -/
lemma isPath_cliqueHamiltonOrder [DecidableEq V] {G : SimpleGraph V}
    {S : Finset V} {e : V} (hS : G.IsClique (S : Set V)) (he : e ∈ S) :
    IsPath G (cliqueHamiltonOrder S e) := by
  have hN := nodup_cliqueHamiltonOrder S e
  refine ⟨cliqueHamiltonOrder_ne_nil S e, hN, ?_⟩
  apply List.isChain_iff_forall_rel_of_append_cons_cons.mpr
  intro a b l₁ l₂ hab
  have ha : a ∈ S := by
    rw [← toFinset_cliqueHamiltonOrder he]
    exact List.mem_toFinset.mpr (by rw [hab]; simp)
  have hb : b ∈ S := by
    rw [← toFinset_cliqueHamiltonOrder he]
    exact List.mem_toFinset.mpr (by rw [hab]; simp)
  have hne : a ≠ b := by
    intro h
    subst b
    rw [hab] at hN
    have htail : (a :: a :: l₂).Nodup := hN.of_append_right
    simp at htail
  exact hS ha hb hne

/-- The explicit clique-extension list. -/
noncomputable def cliqueExtension [DecidableEq V] (S : Finset V) (e : V)
    (ys xs : List V) : List V :=
  cliqueHamiltonOrder S e ++ alternate ys xs

@[simp] lemma toFinset_cliqueExtension [DecidableEq V] {S : Finset V} {e : V}
    (he : e ∈ S) (ys xs : List V) :
    (cliqueExtension S e ys xs).toFinset = S ∪ ys.toFinset ∪ xs.toFinset := by
  simp [cliqueExtension, he, Finset.union_assoc]

@[simp] lemma length_cliqueExtension [DecidableEq V] {S : Finset V} {e : V}
    (he : e ∈ S) (ys xs : List V) :
    (cliqueExtension S e ys xs).length = S.card + ys.length + xs.length := by
  simp [cliqueExtension, he, Nat.add_assoc]

/-- The local edge conditions imply that the ordinary interleaving `alternate ys xs` is a
chain.  The first `Forall₂` supplies `yⱼ-xⱼ`; the second supplies `xⱼ-yⱼ₊₁`. -/
lemma isChain_alternate_of_aligned_edges {G : SimpleGraph V} {ys xs : List V}
    (hyx : List.Forall₂ G.Adj ys xs)
    (hxy : List.Forall₂ G.Adj xs.dropLast ys.tail) :
    (alternate ys xs).IsChain G.Adj := by
  induction ys generalizing xs with
  | nil =>
      have hxs : xs = [] := by simpa using hyx.length_eq.symm
      subst xs
      simp
  | cons y ys ih =>
      cases xs with
      | nil => simp at hyx
      | cons x xs =>
          cases hyx with
          | cons hyx₀ hyxTail =>
              cases ys with
              | nil =>
                  have hxs : xs = [] := by simpa using hyxTail.length_eq.symm
                  subst xs
                  simpa [alternate] using hyx₀
              | cons y' ys =>
                  cases xs with
                  | nil => simp at hyxTail
                  | cons x' xs =>
                      simp only [List.dropLast_cons_cons, List.tail_cons] at hxy
                      cases hxy with
                      | cons hxy₀ hxyTail =>
                          have htail :
                              (alternate (y' :: ys) (x' :: xs)).IsChain G.Adj :=
                            ih hyxTail hxyTail
                          rw [alternate_cons_cons, List.isChain_cons_cons]
                          exact ⟨hyx₀, .cons_cons hxy₀ htail⟩

/-- Appending the aligned alternating tail to the clique ordering gives a simple path. -/
theorem isPath_cliqueExtension [DecidableEq V] {G : SimpleGraph V}
    {S : Finset V} {e : V} {ys xs : List V}
    (hS : G.IsClique (S : Set V)) (he : e ∈ S)
    (hys0 : ys ≠ []) (hysN : ys.Nodup) (hxsN : xs.Nodup)
    (hyxDisj : List.Disjoint ys xs)
    (hysOut : ∀ y ∈ ys, y ∉ S) (hxsOut : ∀ x ∈ xs, x ∉ S)
    (hyx : List.Forall₂ G.Adj ys xs)
    (hxy : List.Forall₂ G.Adj xs.dropLast ys.tail)
    (heFirst : G.Adj e (ys.head hys0)) :
    IsPath G (cliqueExtension S e ys xs) := by
  have hClique := isPath_cliqueHamiltonOrder hS he
  have hAltN : (alternate ys xs).Nodup := nodup_alternate hysN hxsN hyxDisj
  have hDisj : List.Disjoint (cliqueHamiltonOrder S e) (alternate ys xs) := by
    rw [List.disjoint_left]
    intro v hvS hvAlt
    have hvSin : v ∈ S := by
      rw [← toFinset_cliqueHamiltonOrder he]
      exact List.mem_toFinset.mpr hvS
    rcases mem_alternate.mp hvAlt with hvY | hvX
    · exact hysOut v hvY hvSin
    · exact hxsOut v hvX hvSin
  refine ⟨by simp [cliqueExtension], ?_, ?_⟩
  · exact hClique.2.1.append hAltN hDisj
  · have hAltChain := isChain_alternate_of_aligned_edges hyx hxy
    apply hClique.2.2.append hAltChain
    intro a ha b hb
    have ha' : a = e := by
      simpa using ha.symm
    have hb' : b = ys.head hys0 := by
      rw [head?_alternate_of_left_ne_nil hys0] at hb
      rw [List.head?_eq_some_head hys0] at hb
      simpa using hb.symm
    simpa [ha', hb'] using heFirst

/-- Constructive clique extension with exact support and cardinality. -/
theorem exists_cliqueExtension_path [DecidableEq V] {G : SimpleGraph V}
    {S : Finset V} {e : V} {ys xs : List V}
    (hS : G.IsClique (S : Set V)) (he : e ∈ S)
    (hys0 : ys ≠ []) (hysN : ys.Nodup) (hxsN : xs.Nodup)
    (hyxDisj : List.Disjoint ys xs)
    (hysOut : ∀ y ∈ ys, y ∉ S) (hxsOut : ∀ x ∈ xs, x ∉ S)
    (hyx : List.Forall₂ G.Adj ys xs)
    (hxy : List.Forall₂ G.Adj xs.dropLast ys.tail)
    (heFirst : G.Adj e (ys.head hys0)) :
    ∃ p : List V, IsPath G p ∧
      p.toFinset = S ∪ ys.toFinset ∪ xs.toFinset ∧
      p.length = S.card + ys.length + xs.length ∧
      p.toFinset.card = S.card + ys.length + xs.length ∧
      (p.toFinset ∩ S).card = S.card := by
  let p := cliqueExtension S e ys xs
  have hp := isPath_cliqueExtension hS he hys0 hysN hxsN hyxDisj
    hysOut hxsOut hyx hxy heFirst
  refine ⟨p, hp, toFinset_cliqueExtension he ys xs, length_cliqueExtension he ys xs,
    ?_, ?_⟩
  · rw [List.toFinset_card_of_nodup hp.2.1]
    exact length_cliqueExtension he ys xs
  · have hsub : S ⊆ p.toFinset := by
      rw [toFinset_cliqueExtension he ys xs]
      exact Finset.subset_union_left.trans Finset.subset_union_left
    rw [Finset.inter_eq_right.mpr hsub]

/-- Exact intersection count with an ambient set `X`: the clique and all `x`-vertices lie
in `X`, while every `y`-vertex lies outside it. -/
theorem cliqueExtension_inter_card [DecidableEq V]
    {S X : Finset V} {e : V} {ys xs : List V}
    (he : e ∈ S) (hxsN : xs.Nodup)
    (hxsOut : ∀ x ∈ xs, x ∉ S)
    (hSX : S ⊆ X) (hxsX : ∀ x ∈ xs, x ∈ X)
    (hysX : ∀ y ∈ ys, y ∉ X) :
    ((cliqueExtension S e ys xs).toFinset ∩ X).card = S.card + xs.length := by
  have hEq : (cliqueExtension S e ys xs).toFinset ∩ X = S ∪ xs.toFinset := by
    rw [toFinset_cliqueExtension he ys xs]
    ext v
    simp only [Finset.mem_inter, Finset.mem_union, List.mem_toFinset]
    constructor
    · rintro ⟨((hvS | hvY) | hvXs), hvX⟩
      · exact Or.inl hvS
      · exact (hysX v hvY hvX).elim
      · exact Or.inr hvXs
    · rintro (hvS | hvXs)
      · exact ⟨Or.inl (Or.inl hvS), hSX hvS⟩
      · exact ⟨Or.inr hvXs, hxsX v hvXs⟩
  rw [hEq, Finset.card_union_of_disjoint]
  · rw [List.toFinset_card_of_nodup hxsN]
  · rw [Finset.disjoint_left]
    intro v hvS hvXs
    exact hxsOut v (by simpa using hvXs) hvS

end Erdos518
