/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos518.Defs

/-!
# A dense bipartite path lemma

This is the finite, integral form of the dense bipartite path lemma used in the
solution of Erdős Problem 518 (Chen's Lemma 2.3, also PVW Lemma 2.2).  Only the
degrees on one side are assumed large.  The inequality is written without
division: `|X| + |Y| ≤ 2 |N(y) ∩ X|`.

The proof orders `Y`.  For each two consecutive vertices it reserves a distinct
common neighbour in `X`, and for the last vertex it reserves one further
neighbour.  The degree bound makes each of these candidate sets have at least
`|Y|` members, so a greedy system of distinct representatives exists.
-/

open scoped SimpleGraph

namespace Erdos518

universe u

variable {V : Type u}

noncomputable section

private noncomputable def neighborsIn (G : SimpleGraph V) (X : Finset V) (y : V) :
    Finset V := by
  classical
  exact X.filter (G.Adj y)

@[simp] private lemma mem_neighborsIn {G : SimpleGraph V} {X : Finset V} {x y : V} :
    x ∈ neighborsIn G X y ↔ x ∈ X ∧ G.Adj y x := by
  classical
  simp [neighborsIn]

private lemma neighborsIn_subset (G : SimpleGraph V) (X : Finset V) (y : V) :
    neighborsIn G X y ⊆ X := by
  classical
  exact Finset.filter_subset _ _

open Classical in
/-- The candidate sets for the `X`-vertices of an alternating path through `ys`.
For consecutive `y,z` we use their common neighbours; at the end we use the
neighbours of the final vertex. -/
private noncomputable def linkSets (G : SimpleGraph V) (X : Finset V) :
    List V → List (Finset V)
  | [] => []
  | [y] => [neighborsIn G X y]
  | y :: z :: ys =>
      (neighborsIn G X y ∩ neighborsIn G X z) :: linkSets G X (z :: ys)

@[simp] private lemma linkSets_length (G : SimpleGraph V) (X : Finset V) (ys : List V) :
    (linkSets G X ys).length = ys.length := by
  induction ys using List.twoStepInduction with
  | nil => rfl
  | singleton y => rfl
  | cons_cons y z ys _ ih =>
      simp only [linkSets, List.length_cons]
      rw [ih z]
      simp

private lemma linkSets_subset (G : SimpleGraph V) (X : Finset V) (ys : List V) :
    ∀ s ∈ linkSets G X ys, s ⊆ X := by
  classical
  induction ys using List.twoStepInduction with
  | nil => simp [linkSets]
  | singleton y =>
      simpa [linkSets] using neighborsIn_subset G X y
  | cons_cons y z ys _ ih =>
      intro s hs
      simp only [linkSets, List.mem_cons] at hs
      rcases hs with rfl | hs
      · exact (Finset.inter_subset_left.trans (neighborsIn_subset G X y))
      · exact ih z s hs

/-- Choose distinct representatives from a list of sets, provided that every
set has at least as many elements as there are sets.  The extra parameter `X`
records a common ambient set, which is useful below. -/
private lemma exists_distinct_representatives
    (X : Finset V) (ss : List (Finset V))
    (hcard : ∀ s ∈ ss, ss.length ≤ s.card)
    (hsub : ∀ s ∈ ss, s ⊆ X) :
    ∃ xs : List V,
      xs.Nodup ∧ (∀ x ∈ xs, x ∈ X) ∧ List.Forall₂ (fun x s ↦ x ∈ s) xs ss := by
  classical
  induction ss with
  | nil => exact ⟨[], by simp⟩
  | cons s ss ih =>
      have hcard' : ∀ t ∈ ss, ss.length ≤ t.card := by
        intro t ht
        have := hcard t (by simp [ht])
        simp only [List.length_cons] at this
        omega
      have hsub' : ∀ t ∈ ss, t ⊆ X := by
        exact fun t ht ↦ hsub t (by simp [ht])
      obtain ⟨xs, hxs, hxsX, hfit⟩ := ih hcard' hsub'
      have hslarge : xs.toFinset.card < s.card := by
        rw [List.toFinset_card_of_nodup hxs]
        have hlen := hfit.length_eq
        have hs := hcard s (by simp)
        simp only [List.length_cons] at hs
        omega
      obtain ⟨x, hxin, hxnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hslarge
      refine ⟨x :: xs, ?_, ?_, List.Forall₂.cons hxin hfit⟩
      · simpa using And.intro hxnot hxs
      · intro a ha
        simp only [List.mem_cons] at ha
        rcases ha with rfl | ha
        · exact hsub s (by simp) hxin
        · exact hxsX a ha

private def weave : List V → List V → List V
  | y :: ys, x :: xs => y :: x :: weave ys xs
  | _, _ => []

@[simp] private lemma weave_length {ys xs : List V} (h : ys.length = xs.length) :
    (weave ys xs).length = 2 * ys.length := by
  induction ys generalizing xs with
  | nil =>
      have : xs = [] := List.eq_nil_of_length_eq_zero h.symm
      subst xs
      simp [weave]
  | cons y ys ih =>
      cases xs with
      | nil => simp at h
      | cons x xs =>
          simp only [List.length_cons, Nat.succ_inj] at h
          simp [weave, ih h]
          omega

@[simp] private lemma mem_weave {ys xs : List V} (h : ys.length = xs.length) (v : V) :
    v ∈ weave ys xs ↔ v ∈ ys ∨ v ∈ xs := by
  induction ys generalizing xs with
  | nil =>
      have : xs = [] := List.eq_nil_of_length_eq_zero h.symm
      simp [this, weave]
  | cons y ys ih =>
      cases xs with
      | nil => simp at h
      | cons x xs =>
          simp only [List.length_cons, Nat.succ_inj] at h
          simp only [weave, List.mem_cons, ih h]
          tauto

private lemma nodup_weave {ys xs : List V} (hlen : ys.length = xs.length)
    (hys : ys.Nodup) (hxs : xs.Nodup)
    (hcross : ∀ y ∈ ys, ∀ x ∈ xs, y ≠ x) : (weave ys xs).Nodup := by
  induction ys generalizing xs with
  | nil => simp [weave]
  | cons y ys ih =>
      cases xs with
      | nil => simp at hlen
      | cons x xs =>
          simp only [List.length_cons, Nat.succ_inj] at hlen
          have hy_not_ys : y ∉ ys := (List.nodup_cons.mp hys).1
          have hys' : ys.Nodup := (List.nodup_cons.mp hys).2
          have hx_not_xs : x ∉ xs := (List.nodup_cons.mp hxs).1
          have hxs' : xs.Nodup := (List.nodup_cons.mp hxs).2
          have hyx : y ≠ x := hcross y (by simp) x (by simp)
          have hcross' : ∀ z ∈ ys, ∀ w ∈ xs, z ≠ w := by
            exact fun z hz w hw ↦ hcross z (by simp [hz]) w (by simp [hw])
          have htail := ih hlen hys' hxs' hcross'
          have hy_not_tail : y ∉ weave ys xs := by
            rw [mem_weave hlen]
            rintro (hyys | hyxs)
            · exact hy_not_ys hyys
            · exact (hcross y (by simp) y (by simp [hyxs])) rfl
          have hx_not_tail : x ∉ weave ys xs := by
            rw [mem_weave hlen]
            rintro (hxys | hxxs)
            · exact (hcross x (by simp [hxys]) x (by simp)) rfl
            · exact hx_not_xs hxxs
          simp only [weave, List.nodup_cons]
          refine ⟨?_, hx_not_tail, htail⟩
          simpa [hyx] using hy_not_tail

private lemma isChain_weave {G : SimpleGraph V} {X : Finset V} {ys xs : List V}
    (hfit : List.Forall₂ (fun x s ↦ x ∈ s) xs (linkSets G X ys)) :
    (weave ys xs).IsChain G.Adj := by
  classical
  induction ys using List.twoStepInduction generalizing xs with
  | nil =>
      have : xs = [] := List.forall₂_nil_right_iff.mp hfit
      subst xs
      simp [weave]
  | singleton y =>
      obtain ⟨x, xs, hx, htail, rfl⟩ := List.forall₂_cons_right_iff.mp hfit
      have : xs = [] := List.forall₂_nil_right_iff.mp htail
      subst xs
      simpa [linkSets, weave] using (mem_neighborsIn.mp hx).2
  | cons_cons y z ys _ ih =>
      obtain ⟨x, xs, hx, htail, rfl⟩ := List.forall₂_cons_right_iff.mp hfit
      have hlen := htail.length_eq
      rw [linkSets_length] at hlen
      cases xs with
      | nil => simp at hlen
      | cons x' xs =>
          have hchain := ih z htail
          have hmem : x ∈ neighborsIn G X y ∩ neighborsIn G X z := by
            simpa [linkSets] using hx
          have hyx : G.Adj y x := (mem_neighborsIn.mp (Finset.mem_inter.mp hmem).1).2
          have hzx : G.Adj z x := (mem_neighborsIn.mp (Finset.mem_inter.mp hmem).2).2
          simpa [weave] using And.intro hyx (And.intro hzx.symm hchain)

open Classical in
private lemma card_common_neighbors {G : SimpleGraph V} {X Y : Finset V} {y z : V}
    (hy : X.card + Y.card ≤ 2 * (neighborsIn G X y).card)
    (hz : X.card + Y.card ≤ 2 * (neighborsIn G X z).card) :
    Y.card ≤ (neighborsIn G X y ∩ neighborsIn G X z).card := by
  let A := neighborsIn G X y
  let B := neighborsIn G X z
  have hUsub : A ∪ B ⊆ X := Finset.union_subset
    (neighborsIn_subset G X y) (neighborsIn_subset G X z)
  have hU : (A ∪ B).card ≤ X.card := Finset.card_le_card hUsub
  have hIE := Finset.card_inter_add_card_union A B
  change X.card + Y.card ≤ 2 * A.card at hy
  change X.card + Y.card ≤ 2 * B.card at hz
  change Y.card ≤ (A ∩ B).card
  omega

private lemma card_neighbors {G : SimpleGraph V} {X Y : Finset V} {y : V}
    (hy : X.card + Y.card ≤ 2 * (neighborsIn G X y).card) :
    Y.card ≤ (neighborsIn G X y).card := by
  have hsub := Finset.card_le_card (neighborsIn_subset G X y)
  omega

private lemma linkSets_large {G : SimpleGraph V} {X Y : Finset V} (ys : List V)
    (hdeg : ∀ y ∈ Y, X.card + Y.card ≤ 2 * (neighborsIn G X y).card)
    (hysY : ∀ y ∈ ys, y ∈ Y) :
    ∀ s ∈ linkSets G X ys, Y.card ≤ s.card := by
  classical
  induction ys using List.twoStepInduction with
  | nil => simp [linkSets]
  | singleton y =>
      intro s hs
      simp only [linkSets, List.mem_singleton] at hs
      subst s
      exact card_neighbors (hdeg y (hysY y (by simp)))
  | cons_cons y z ys _ ih =>
      intro s hs
      simp only [linkSets, List.mem_cons] at hs
      rcases hs with rfl | hs
      · exact card_common_neighbors
          (hdeg y (hysY y (by simp))) (hdeg z (hysY z (by simp)))
      · exact (ih z (fun w hw ↦ hysY w (by simp [hw]))) s hs

open Classical in
/-- **Dense bipartite path lemma (Chen / Pokrovskiy--Versteegen--Williams).**

Let `X,Y` be disjoint finite vertex sets and let `Y` be nonempty.  If every
`y ∈ Y` has at least half of `|X|+|Y|` neighbours in `X` (expressed by the
integral inequality below), there is a simple path containing all of `Y`, with
exactly `2|Y|` vertices, all in `X ∪ Y`.  In fact exactly `|Y|` vertices of the
path belong to `X`.
-/
theorem exists_path_of_dense_bipartite (G : SimpleGraph V) (X Y : Finset V)
    (hXY : Disjoint X Y) (hY : Y.Nonempty)
    (hdeg : ∀ y ∈ Y,
      X.card + Y.card ≤ 2 * (X.filter (G.Adj y)).card) :
    ∃ p : List V,
      IsPath G p ∧
      p.length = 2 * Y.card ∧
      (∀ v ∈ p, v ∈ X ∪ Y) ∧
      (∀ y ∈ Y, y ∈ p) ∧
      (p.toFinset ∩ X).card = Y.card := by
  classical
  let ys := Y.toList
  have hysN : ys.Nodup := Finset.nodup_toList Y
  have hysLen : ys.length = Y.card := Finset.length_toList Y
  have hysY : ∀ y ∈ ys, y ∈ Y := by
    intro y hy
    exact Finset.mem_toList.mp hy
  have hdeg' : ∀ y ∈ Y,
      X.card + Y.card ≤ 2 * (neighborsIn G X y).card := by
    simpa [neighborsIn] using hdeg
  have hlarge : ∀ s ∈ linkSets G X ys, (linkSets G X ys).length ≤ s.card := by
    intro s hs
    rw [linkSets_length, hysLen]
    exact linkSets_large ys hdeg' hysY s hs
  obtain ⟨xs, hxsN, hxsX, hfit⟩ :=
    exists_distinct_representatives X (linkSets G X ys) hlarge
      (linkSets_subset G X ys)
  have hxyLen : ys.length = xs.length := by
    rw [hfit.length_eq, linkSets_length]
  let p := weave ys xs
  have hpLen : p.length = 2 * Y.card := by
    simpa [p, hysLen] using weave_length hxyLen
  have hcross : ∀ y ∈ ys, ∀ x ∈ xs, y ≠ x := by
    intro y hy x hx hEq
    subst x
    exact Finset.disjoint_left.mp hXY (hxsX y hx) (hysY y hy)
  have hpN : p.Nodup := by
    exact nodup_weave hxyLen hysN hxsN hcross
  have hpChain : p.IsChain G.Adj := by
    exact isChain_weave hfit
  have hpNonempty : p ≠ [] := by
    intro hp
    have : p.length = 0 := by simp [hp]
    rw [hpLen] at this
    have hypos : 0 < Y.card := Finset.card_pos.mpr hY
    omega
  refine ⟨p, ⟨hpNonempty, hpN, hpChain⟩, hpLen, ?_, ?_, ?_⟩
  · intro v hv
    change v ∈ weave ys xs at hv
    rw [mem_weave hxyLen] at hv
    rcases hv with hv | hv
    · exact Finset.mem_union_right X (hysY v hv)
    · exact Finset.mem_union_left Y (hxsX v hv)
  · intro y hy
    change y ∈ weave ys xs
    rw [mem_weave hxyLen]
    exact Or.inl (Finset.mem_toList.mpr hy)
  · have hinter : p.toFinset ∩ X = xs.toFinset := by
      ext v
      simp only [Finset.mem_inter, List.mem_toFinset]
      change (v ∈ weave ys xs ∧ v ∈ X) ↔ v ∈ xs
      rw [mem_weave hxyLen]
      constructor
      · rintro ⟨hvy | hvx, hvX⟩
        · exact False.elim (Finset.disjoint_left.mp hXY hvX (hysY v hvy))
        · exact hvx
      · intro hvx
        exact ⟨Or.inr hvx, hxsX v hvx⟩
    rw [hinter, List.toFinset_card_of_nodup hxsN, ← hxyLen, hysLen]

end
end Erdos518
