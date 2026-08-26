/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# Zhao's Lemma 6.12: the finite decreasing-prefix argument

The mathematical content of Lemma 6.12 in Yi Zhao's 2011 proof is an
elementary lemma about a finite decreasing sequence of nonnegative weights.
The weights are the contributions `d(B,e) N` of the edges of a cluster
matching.  One takes the shortest prefix whose sum reaches
`f_b + 3 γ n`.  Its overshoot is less than one edge contribution, and its
cardinality is bounded by comparing the average of a decreasing prefix with
the average of the whole sequence.

This file isolates and proves that exact finite argument.  The final theorem
`zhao_lemma_6_12` is phrased for an ordered enumeration of a matching; the
submatching it returns is the image of the selected prefix.
-/

open scoped BigOperators

noncomputable section

namespace Erdos547b.ZhaoLemma612

open Finset

/-- A prefix of a nonincreasing real sequence has at least the average of the
whole sequence.  This is the denominator-free form used in Zhao's proof. -/
theorem antitone_mul_sum_range_le_mul_prefix
    (w : ℕ → ℝ) (hw : Antitone w) {j m : ℕ} (hjm : j ≤ m) :
    (j : ℝ) * (∑ i ∈ range m, w i) ≤
      (m : ℝ) * (∑ i ∈ range j, w i) := by
  induction m with
  | zero =>
      have : j = 0 := Nat.eq_zero_of_le_zero hjm
      simp [this]
  | succ m ih =>
      by_cases hj : j = m + 1
      · subst j
        simp
      · have hjm' : j ≤ m := by omega
        have hprefix_last : (j : ℝ) * w m ≤ ∑ i ∈ range j, w i := by
          calc
            (j : ℝ) * w m = ∑ _i ∈ range j, w m := by simp
            _ ≤ ∑ i ∈ range j, w i := by
              apply sum_le_sum
              intro i hi
              have him : i ≤ m := (Nat.le_of_lt (mem_range.mp hi)).trans hjm'
              exact hw him
        rw [sum_range_succ]
        have hmain := ih hjm'
        calc
          (j : ℝ) * ((∑ i ∈ range m, w i) + w m) =
              (j : ℝ) * (∑ i ∈ range m, w i) + (j : ℝ) * w m := by ring
          _ ≤ (m : ℝ) * (∑ i ∈ range j, w i) +
              (∑ i ∈ range j, w i) := add_le_add hmain hprefix_last
          _ = (m + 1 : ℕ) * (∑ i ∈ range j, w i) := by
            norm_num
            ring

/-- The first prefix crossing a nonnegative target overshoots that target by
strictly less than the uniform upper bound for one summand. -/
theorem exists_first_prefix
    (w : ℕ → ℝ) (m : ℕ) (target cap : ℝ)
    (htarget : 0 ≤ target) (hcap : 0 < cap)
    (hwcap : ∀ i < m, w i ≤ cap)
    (htotal : target ≤ ∑ i ∈ range m, w i) :
    ∃ j ≤ m,
      target ≤ ∑ i ∈ range j, w i ∧
      (∑ i ∈ range j, w i) < target + cap := by
  let p : ℕ → Prop := fun j => target ≤ ∑ i ∈ range j, w i
  have hex : ∃ j, p j := ⟨m, htotal⟩
  let j := Nat.find hex
  have hjtarget : target ≤ ∑ i ∈ range j, w i := Nat.find_spec hex
  have hjm : j ≤ m := Nat.find_min' hex htotal
  refine ⟨j, hjm, hjtarget, ?_⟩
  have hjdef : j = Nat.find hex := rfl
  rcases hj : j with _ | j
  · simp only [sum_range_zero]
    linarith
  · have hprev_not : ¬p j := by
      apply Nat.find_min hex
      rw [← hjdef, hj]
      exact Nat.lt_succ_self j
    have hprev : (∑ i ∈ range j, w i) < target := lt_of_not_ge hprev_not
    have hjltm : j < m := by
      rw [hj] at hjm
      omega
    rw [sum_range_succ]
    have hwj : w j ≤ cap := hwcap j hjltm
    linarith

/-- Combined decreasing-prefix lemma.  Besides the target interval it records
the exact cross-multiplied cardinality estimate used by Zhao:
`j * total ≤ m * prefix < m * (target + cap)`.
-/
theorem exists_small_decreasing_prefix
    (w : ℕ → ℝ) (m : ℕ) (target cap : ℝ)
    (hwanti : Antitone w)
    (hm : 0 < m)
    (htarget : 0 ≤ target) (hcap : 0 < cap)
    (hwcap : ∀ i < m, w i ≤ cap)
    (htotal : target ≤ ∑ i ∈ range m, w i) :
    ∃ j ≤ m,
      target ≤ ∑ i ∈ range j, w i ∧
      (∑ i ∈ range j, w i) < target + cap ∧
      (j : ℝ) * (∑ i ∈ range m, w i) < (m : ℝ) * (target + cap) := by
  obtain ⟨j, hjm, hjlower, hjupper⟩ :=
    exists_first_prefix w m target cap htarget hcap hwcap htotal
  refine ⟨j, hjm, hjlower, hjupper, ?_⟩
  calc
    (j : ℝ) * (∑ i ∈ range m, w i) ≤
        (m : ℝ) * (∑ i ∈ range j, w i) :=
      antitone_mul_sum_range_le_mul_prefix w hwanti hjm
    _ < (m : ℝ) * (target + cap) := by
      exact mul_lt_mul_of_pos_left hjupper (Nat.cast_pos.mpr hm)

/-!
## Ordered finite matchings

At this layer an edge matching is represented by its finite edge set.  A
`Finset` contained in it is a submatching.  The following definitions and
lemmas turn an injective ordered enumeration into the prefix submatching used
in the paper.
-/

/-- The first `j` edges in an ordered enumeration. -/
def orderedPrefix {Edge : Type*} [DecidableEq Edge]
    (edge : ℕ → Edge) (j : ℕ) : Finset Edge :=
  (range j).image edge

theorem orderedPrefix_subset {Edge : Type*} [DecidableEq Edge]
    (edge : ℕ → Edge) {j m : ℕ} (hjm : j ≤ m) :
    orderedPrefix edge j ⊆ orderedPrefix edge m := by
  exact image_subset_image (range_mono hjm)

theorem card_orderedPrefix {Edge : Type*} [DecidableEq Edge]
    (edge : ℕ → Edge) {j m : ℕ}
    (hinj : Set.InjOn edge (range m : Set ℕ)) (hjm : j ≤ m) :
    (orderedPrefix edge j).card = j := by
  calc
    (orderedPrefix edge j).card = (range j).card := by
      rw [orderedPrefix, card_image_iff]
      exact hinj.mono (by simpa using range_mono hjm)
    _ = j := card_range j

theorem sum_orderedPrefix {Edge : Type*} [DecidableEq Edge]
    (edge : ℕ → Edge) (contribution : Edge → ℝ) {j m : ℕ}
    (hinj : Set.InjOn edge (range m : Set ℕ)) (hjm : j ≤ m) :
    ∑ e ∈ orderedPrefix edge j, contribution e =
      ∑ i ∈ range j, contribution (edge i) := by
  rw [orderedPrefix]
  exact sum_image (hinj.mono (by simpa using range_mono hjm))

/-- The edge list obtained by sorting a finite matching in decreasing order
of contribution.  `mergeSort` only needs a total preorder, so equal-weight
distinct edges cause no tie-breaking issue. -/
def decreasingList {Edge : Type*} [DecidableEq Edge]
    (M : Finset Edge) (contribution : Edge → ℝ) : List Edge :=
  M.toList.mergeSort fun a b => decide (contribution b ≤ contribution a)

theorem decreasingList_perm {Edge : Type*} [DecidableEq Edge]
    (M : Finset Edge) (contribution : Edge → ℝ) :
    (decreasingList M contribution).Perm M.toList := by
  exact List.mergeSort_perm _ _

theorem decreasingList_length {Edge : Type*} [DecidableEq Edge]
    (M : Finset Edge) (contribution : Edge → ℝ) :
    (decreasingList M contribution).length = M.card := by
  rw [decreasingList, List.length_mergeSort, Finset.length_toList]

theorem decreasingList_nodup {Edge : Type*} [DecidableEq Edge]
    (M : Finset Edge) (contribution : Edge → ℝ) :
    (decreasingList M contribution).Nodup := by
  rw [decreasingList, List.nodup_mergeSort]
  exact M.nodup_toList

theorem mem_decreasingList_iff {Edge : Type*} [DecidableEq Edge]
    (M : Finset Edge) (contribution : Edge → ℝ) (e : Edge) :
    e ∈ decreasingList M contribution ↔ e ∈ M := by
  rw [(decreasingList_perm M contribution).mem_iff]
  simp

theorem pairwise_decreasingList {Edge : Type*} [DecidableEq Edge]
    (M : Finset Edge) (contribution : Edge → ℝ) :
    (decreasingList M contribution).Pairwise
      (fun a b => contribution b ≤ contribution a) := by
  let cmp : Edge → Edge → Bool :=
    fun a b => decide (contribution b ≤ contribution a)
  have htrans : ∀ a b c, cmp a b = true → cmp b c = true → cmp a c = true := by
    intro a b c hab hbc
    simp only [cmp, decide_eq_true_eq] at hab hbc ⊢
    exact hbc.trans hab
  have htotal : ∀ a b, (cmp a b || cmp b a) = true := by
    intro a b
    simp only [cmp, decide_eq_true_eq, Bool.or_eq_true]
    exact (le_total (contribution b) (contribution a)).imp id id
  have hpair := List.pairwise_mergeSort htrans htotal M.toList
  simpa only [decreasingList, cmp, decide_eq_true_eq] using hpair

/-- Order-free form of the prefix lemma.  The proof constructs Zhao's
decreasing ordering with `decreasingList`, so callers only supply the finite
matching edge set and its contributions. -/
theorem exists_small_submatching
    {Edge : Type*} [DecidableEq Edge]
    (M : Finset Edge) (contribution : Edge → ℝ)
    (target cap cardBound : ℝ)
    (hnonneg : ∀ e ∈ M, 0 ≤ contribution e)
    (htarget : 0 ≤ target) (hcap : 0 < cap)
    (hedgecap : ∀ e ∈ M, contribution e ≤ cap)
    (htotal : target ≤ ∑ e ∈ M, contribution e)
    (htotalpos : 0 < ∑ e ∈ M, contribution e)
    (hcard : (M.card : ℝ) * (target + cap) ≤
      cardBound * (∑ e ∈ M, contribution e)) :
    ∃ Mb : Finset Edge,
      Mb ⊆ M ∧
      target ≤ ∑ e ∈ Mb, contribution e ∧
      (∑ e ∈ Mb, contribution e) < target + cap ∧
      ((Mb.card : ℕ) : ℝ) ≤ cardBound := by
  have hM : M.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hMempty
    subst M
    simp at htotalpos
  obtain ⟨e0, he0⟩ := hM
  let L := decreasingList M contribution
  let edge : ℕ → Edge := fun i => L.getD i e0
  let w : ℕ → ℝ := fun i => if i < L.length then contribution (edge i) else 0
  have hlen : L.length = M.card := decreasingList_length M contribution
  have hLnodup : L.Nodup := decreasingList_nodup M contribution
  have hLpair : L.Pairwise (fun a b => contribution b ≤ contribution a) :=
    pairwise_decreasingList M contribution
  have hLmem (e : Edge) : e ∈ L ↔ e ∈ M := by
    exact mem_decreasingList_iff M contribution e
  have hedge_first {i : ℕ} (hi : i < M.card) : edge i = L[i] := by
    change L.getD i e0 = L[i]
    exact List.getD_eq_getElem L e0 (by rwa [hlen])
  have hedge_mem {i : ℕ} (hi : i < M.card) : edge i ∈ M := by
    rw [hedge_first hi, ← hLmem]
    exact List.getElem_mem (by rwa [hlen])
  have henum : orderedPrefix edge M.card = M := by
    ext e
    constructor
    · intro he
      rw [orderedPrefix, Finset.mem_image] at he
      obtain ⟨i, hi, hie⟩ := he
      have hi' : i < M.card := mem_range.mp hi
      rw [← hie]
      exact hedge_mem hi'
    · intro he
      have heL : e ∈ L := (hLmem e).mpr he
      rw [List.mem_iff_getElem] at heL
      obtain ⟨i, hiL, hie⟩ := heL
      rw [orderedPrefix, Finset.mem_image]
      refine ⟨i, mem_range.mpr ?_, ?_⟩
      · rwa [← hlen]
      · rw [hedge_first (by rwa [← hlen]), hie]
  have hinj : Set.InjOn edge (range M.card : Set ℕ) := by
    intro i hi j hj hij
    have hi' : i < M.card := mem_range.mp hi
    have hj' : j < M.card := mem_range.mp hj
    have hiL : i < L.length := by rwa [hlen]
    have hjL : j < L.length := by rwa [hlen]
    have hget : L.get ⟨i, hiL⟩ = L.get ⟨j, hjL⟩ := by
      simpa [List.get_eq_getElem, hedge_first hi', hedge_first hj'] using hij
    have hfin : (⟨i, hiL⟩ : Fin L.length) = ⟨j, hjL⟩ :=
      (List.nodup_iff_injective_get.mp hLnodup) hget
    exact congrArg Fin.val hfin
  have hweight : ∀ i < M.card, contribution (edge i) = w i := by
    intro i hi
    change contribution (edge i) =
      (if i < L.length then contribution (edge i) else 0)
    rw [if_pos (by rwa [hlen])]
  have hwanti : Antitone w := by
    intro i j hij
    change (if j < L.length then contribution (edge j) else 0) ≤
      (if i < L.length then contribution (edge i) else 0)
    by_cases hjL : j < L.length
    · have hiL : i < L.length := lt_of_le_of_lt hij hjL
      rw [if_pos hiL, if_pos hjL]
      have hrel := hLpair.rel_get_of_le
        (a := (⟨i, hiL⟩ : Fin L.length))
        (b := (⟨j, hjL⟩ : Fin L.length)) hij
      have hiM : i < M.card := by rwa [← hlen]
      have hjM : j < M.card := by rwa [← hlen]
      simpa [hedge_first hiM, hedge_first hjM] using hrel
    · rw [if_neg hjL]
      by_cases hiL : i < L.length
      · rw [if_pos hiL]
        have hiM : i < M.card := by rwa [← hlen]
        exact hnonneg (edge i) (hedge_mem hiM)
      · rw [if_neg hiL]
  have hwcap : ∀ i < M.card, w i ≤ cap := by
    intro i hi
    rw [← hweight i hi]
    exact hedgecap (edge i) (hedge_mem hi)
  have hm : 0 < M.card := Finset.card_pos.mpr ⟨e0, he0⟩
  have hsum_m : (∑ i ∈ range M.card, w i) = ∑ e ∈ M, contribution e := by
    calc
      (∑ i ∈ range M.card, w i) =
          ∑ i ∈ range M.card, contribution (edge i) := by
        apply sum_congr rfl
        intro i hi
        rw [hweight i (mem_range.mp hi)]
      _ = ∑ e ∈ orderedPrefix edge M.card, contribution e :=
        (sum_orderedPrefix edge contribution hinj le_rfl).symm
      _ = ∑ e ∈ M, contribution e := by rw [henum]
  have htotal' : target ≤ ∑ i ∈ range M.card, w i := by rwa [hsum_m]
  obtain ⟨j, hjm, hjlower, hjupper, hjcross⟩ :=
    exists_small_decreasing_prefix w M.card target cap hwanti hm htarget hcap hwcap htotal'
  let Mb := orderedPrefix edge j
  have hsum_j : (∑ e ∈ Mb, contribution e) = ∑ i ∈ range j, w i := by
    calc
      (∑ e ∈ Mb, contribution e) = ∑ i ∈ range j, contribution (edge i) := by
        simpa [Mb] using sum_orderedPrefix edge contribution hinj hjm
      _ = ∑ i ∈ range j, w i := by
        apply sum_congr rfl
        intro i hi
        rw [hweight i (lt_of_lt_of_le (mem_range.mp hi) hjm)]
  have hcard_j : Mb.card = j := by
    simpa [Mb] using card_orderedPrefix edge hinj hjm
  refine ⟨Mb, ?_, ?_, ?_, ?_⟩
  · rw [← henum]
    exact orderedPrefix_subset edge hjm
  · rwa [hsum_j]
  · rwa [hsum_j]
  · rw [hcard_j]
    have hjcross' : (j : ℝ) * (∑ e ∈ M, contribution e) <
        (M.card : ℝ) * (target + cap) := by
      rwa [hsum_m] at hjcross
    have hjbound : (j : ℝ) * (∑ e ∈ M, contribution e) <
        cardBound * (∑ e ∈ M, contribution e) := hjcross'.trans_le hcard
    nlinarith

/-- A source-faithful strengthening of `exists_small_submatching`: zero-weight
edges are removed before taking the decreasing prefix.  Thus every selected
edge has strictly positive contribution, while the total weight and all
quantitative conclusions are unchanged. -/
theorem exists_small_submatching_positive
    {Edge : Type*} [DecidableEq Edge]
    (M : Finset Edge) (contribution : Edge → ℝ)
    (target cap cardBound : ℝ)
    (hnonneg : ∀ e ∈ M, 0 ≤ contribution e)
    (htarget : 0 ≤ target) (hcap : 0 < cap)
    (hedgecap : ∀ e ∈ M, contribution e ≤ cap)
    (htotal : target ≤ ∑ e ∈ M, contribution e)
    (htotalpos : 0 < ∑ e ∈ M, contribution e)
    (hcard : ((M.card : ℕ) : ℝ) * (target + cap) ≤
      cardBound * ∑ e ∈ M, contribution e) :
    ∃ Mb : Finset Edge,
      Mb ⊆ M ∧
      target ≤ ∑ e ∈ Mb, contribution e ∧
      (∑ e ∈ Mb, contribution e) < target + cap ∧
      ((Mb.card : ℕ) : ℝ) ≤ cardBound ∧
      ∀ e ∈ Mb, 0 < contribution e := by
  classical
  let Mpos := M.filter fun e ↦ 0 < contribution e
  have hMpos : Mpos ⊆ M := Finset.filter_subset _ _
  have hsum : (∑ e ∈ Mpos, contribution e) =
      ∑ e ∈ M, contribution e := by
    apply Finset.sum_subset hMpos
    intro e heM heNot
    have hnotPos : ¬ 0 < contribution e := by
      intro hePos
      exact heNot (Finset.mem_filter.mpr ⟨heM, hePos⟩)
    exact le_antisymm (le_of_not_gt hnotPos) (hnonneg e heM)
  have hcardPos : (((Mpos.card : ℕ) : ℝ) * (target + cap)) ≤
      cardBound * ∑ e ∈ Mpos, contribution e := by
    calc
      ((Mpos.card : ℕ) : ℝ) * (target + cap) ≤
          ((M.card : ℕ) : ℝ) * (target + cap) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast Finset.card_le_card hMpos
        · linarith
      _ ≤ cardBound * ∑ e ∈ M, contribution e := hcard
      _ = cardBound * ∑ e ∈ Mpos, contribution e := by rw [hsum]
  obtain ⟨Mb, hMbPos, hlow, hupp, hMbCard⟩ :=
    exists_small_submatching Mpos contribution target cap cardBound
      (fun e he ↦ hnonneg e (hMpos he)) htarget hcap
      (fun e he ↦ hedgecap e (hMpos he)) (by rw [hsum]; exact htotal)
      (by rw [hsum]; exact htotalpos) hcardPos
  refine ⟨Mb, hMbPos.trans hMpos, hlow, hupp, hMbCard, ?_⟩
  intro e he
  exact (Finset.mem_filter.mp (hMbPos he)).2

/-- The ordered finite-submatching form of the decreasing-prefix lemma.
`cardBound` is separated from the paper's constant hierarchy: its only
required numerical input is precisely the cross-multiplied inequality which
the hierarchy proves. -/
theorem exists_small_ordered_submatching
    {Edge : Type*} [DecidableEq Edge]
    (M : Finset Edge) (edge : ℕ → Edge) (contribution : Edge → ℝ)
    (w : ℕ → ℝ) (m : ℕ) (target cap cardBound : ℝ)
    (henum : orderedPrefix edge m = M)
    (hinj : Set.InjOn edge (range m : Set ℕ))
    (hweight : ∀ i < m, contribution (edge i) = w i)
    (hwanti : Antitone w) (hm : 0 < m)
    (htarget : 0 ≤ target) (hcap : 0 < cap)
    (hwcap : ∀ i < m, w i ≤ cap)
    (htotal : target ≤ ∑ e ∈ M, contribution e)
    (htotalpos : 0 < ∑ e ∈ M, contribution e)
    (hcard : (m : ℝ) * (target + cap) ≤
      cardBound * (∑ e ∈ M, contribution e)) :
    ∃ Mb : Finset Edge,
      Mb ⊆ M ∧
      target ≤ ∑ e ∈ Mb, contribution e ∧
      (∑ e ∈ Mb, contribution e) < target + cap ∧
      ((Mb.card : ℕ) : ℝ) ≤ cardBound := by
  have hsum_m : (∑ i ∈ range m, w i) = ∑ e ∈ M, contribution e := by
    calc
      (∑ i ∈ range m, w i) = ∑ i ∈ range m, contribution (edge i) := by
        apply sum_congr rfl
        intro i hi
        rw [hweight i (mem_range.mp hi)]
      _ = ∑ e ∈ orderedPrefix edge m, contribution e :=
        (sum_orderedPrefix edge contribution hinj le_rfl).symm
      _ = ∑ e ∈ M, contribution e := by rw [henum]
  have htotal' : target ≤ ∑ i ∈ range m, w i := by
    rwa [hsum_m]
  obtain ⟨j, hjm, hjlower, hjupper, hjcross⟩ :=
    exists_small_decreasing_prefix w m target cap hwanti hm htarget hcap hwcap htotal'
  let Mb := orderedPrefix edge j
  have hsum_j : (∑ e ∈ Mb, contribution e) = ∑ i ∈ range j, w i := by
    calc
      (∑ e ∈ Mb, contribution e) = ∑ i ∈ range j, contribution (edge i) := by
        simpa [Mb] using sum_orderedPrefix edge contribution hinj hjm
      _ = ∑ i ∈ range j, w i := by
        apply sum_congr rfl
        intro i hi
        rw [hweight i (lt_of_lt_of_le (mem_range.mp hi) hjm)]
  have hcard_j : Mb.card = j := by
    simpa [Mb] using card_orderedPrefix edge hinj hjm
  refine ⟨Mb, ?_, ?_, ?_, ?_⟩
  · rw [← henum]
    exact orderedPrefix_subset edge hjm
  · rwa [hsum_j]
  · rwa [hsum_j]
  · rw [hcard_j]
    have hjcross' : (j : ℝ) * (∑ e ∈ M, contribution e) <
        (m : ℝ) * (target + cap) := by
      rwa [hsum_m] at hjcross
    have : (j : ℝ) * (∑ e ∈ M, contribution e) <
        cardBound * (∑ e ∈ M, contribution e) := hjcross'.trans_le hcard
    exact le_of_lt ((mul_lt_mul_iff_of_pos_right htotalpos).mp this)

/-- Zhao's Lemma 6.12 with the constants appearing in the paper.  Here
`dQuarter` denotes `d^(1/4)`, `target` is `f_b + 3 γ n`, and `cap` is `2N`.
The hypothesis `target + cap ≤ 2 dQuarter * lower` is exactly the final
constant-hierarchy estimate cited as (6.1) and (6.5) in Zhao's proof; `lower`
is `(1 - 10 sqrt d) n`.
-/
theorem zhao_lemma_6_12
    {Edge : Type*} [DecidableEq Edge]
    (M : Finset Edge) (edge : ℕ → Edge) (contribution : Edge → ℝ)
    (w : ℕ → ℝ) (m k : ℕ)
    (target cap dQuarter lower : ℝ)
    (henum : orderedPrefix edge m = M)
    (hinj : Set.InjOn edge (range m : Set ℕ))
    (hweight : ∀ i < m, contribution (edge i) = w i)
    (hwanti : Antitone w) (hm : 0 < m) (hmk : m ≤ k)
    (htarget : 0 ≤ target) (hcap : 0 < cap)
    (hwcap : ∀ i < m, w i ≤ cap)
    (htotal : target ≤ ∑ e ∈ M, contribution e)
    (hlower : lower ≤ ∑ e ∈ M, contribution e)
    (hlowerpos : 0 < lower) (hdQuarter : 0 ≤ dQuarter)
    (hhierarchy : target + cap ≤ 2 * dQuarter * lower) :
    ∃ Mb : Finset Edge,
      Mb ⊆ M ∧
      target ≤ ∑ e ∈ Mb, contribution e ∧
      (∑ e ∈ Mb, contribution e) < target + cap ∧
      ((Mb.card : ℕ) : ℝ) ≤ 2 * dQuarter * k := by
  have htotalpos : 0 < ∑ e ∈ M, contribution e := hlowerpos.trans_le hlower
  have htargetcap : 0 ≤ target + cap := by linarith
  have hmk : (m : ℝ) ≤ (k : ℝ) := by exact_mod_cast hmk
  have hcard : (m : ℝ) * (target + cap) ≤
      (2 * dQuarter * k) * (∑ e ∈ M, contribution e) := by
    calc
      (m : ℝ) * (target + cap) ≤ (k : ℝ) * (target + cap) :=
        mul_le_mul_of_nonneg_right hmk htargetcap
      _ ≤ (k : ℝ) * (2 * dQuarter * lower) :=
        mul_le_mul_of_nonneg_left hhierarchy (Nat.cast_nonneg k)
      _ = (2 * dQuarter * k) * lower := by ring
      _ ≤ (2 * dQuarter * k) * (∑ e ∈ M, contribution e) := by
        exact mul_le_mul_of_nonneg_left hlower
          (mul_nonneg (mul_nonneg (by norm_num) hdQuarter) (Nat.cast_nonneg k))
  exact exists_small_ordered_submatching M edge contribution w m target cap
    (2 * dQuarter * k) henum hinj hweight hwanti hm htarget hcap hwcap
    htotal htotalpos hcard

/-- Order-free version of `zhao_lemma_6_12`.  This is the convenient API for
an actual finite cluster matching: the decreasing enumeration is constructed
internally and does not appear among the hypotheses. -/
theorem zhao_lemma_6_12_unordered
    {Edge : Type*} [DecidableEq Edge]
    (M : Finset Edge) (contribution : Edge → ℝ) (k : ℕ)
    (target cap dQuarter lower : ℝ)
    (hmk : M.card ≤ k)
    (hnonneg : ∀ e ∈ M, 0 ≤ contribution e)
    (htarget : 0 ≤ target) (hcap : 0 < cap)
    (hedgecap : ∀ e ∈ M, contribution e ≤ cap)
    (htotal : target ≤ ∑ e ∈ M, contribution e)
    (hlower : lower ≤ ∑ e ∈ M, contribution e)
    (hlowerpos : 0 < lower) (hdQuarter : 0 ≤ dQuarter)
    (hhierarchy : target + cap ≤ 2 * dQuarter * lower) :
    ∃ Mb : Finset Edge,
      Mb ⊆ M ∧
      target ≤ ∑ e ∈ Mb, contribution e ∧
      (∑ e ∈ Mb, contribution e) < target + cap ∧
      ((Mb.card : ℕ) : ℝ) ≤ 2 * dQuarter * k := by
  have htotalpos : 0 < ∑ e ∈ M, contribution e := hlowerpos.trans_le hlower
  have htargetcap : 0 ≤ target + cap := by linarith
  have hmk' : (M.card : ℝ) ≤ (k : ℝ) := by exact_mod_cast hmk
  have hcard : (M.card : ℝ) * (target + cap) ≤
      (2 * dQuarter * k) * (∑ e ∈ M, contribution e) := by
    calc
      (M.card : ℝ) * (target + cap) ≤ (k : ℝ) * (target + cap) :=
        mul_le_mul_of_nonneg_right hmk' htargetcap
      _ ≤ (k : ℝ) * (2 * dQuarter * lower) :=
        mul_le_mul_of_nonneg_left hhierarchy (Nat.cast_nonneg k)
      _ = (2 * dQuarter * k) * lower := by ring
      _ ≤ (2 * dQuarter * k) * (∑ e ∈ M, contribution e) := by
        exact mul_le_mul_of_nonneg_left hlower
          (mul_nonneg (mul_nonneg (by norm_num) hdQuarter) (Nat.cast_nonneg k))
  exact exists_small_submatching M contribution target cap (2 * dQuarter * k)
    hnonneg htarget hcap hedgecap htotal htotalpos hcard

/-- Literal numerical shape of Zhao (2011), Lemma 6.12.

* `total ≥ (1 - 10 √d)n` is the lemma's displayed hypothesis;
* `f_b < d^(1/4)n` is its small-`f_b` case;
* every edge contributes between `0` and `2N`;
* the two explicit hierarchy inequalities are exactly the uses of (6.1) and
  (6.5) in the published proof.

The result is equation (6.13), including `|M_b| ≤ 2 d^(1/4) k`.
-/
theorem zhao_lemma_6_12_source_constants
    {Edge : Type*} [DecidableEq Edge]
    (M : Finset Edge) (contribution : Edge → ℝ) (k : ℕ)
    (f_b γ n N d : ℝ)
    (hmk : M.card ≤ k)
    (hfb : 0 ≤ f_b) (hγ : 0 ≤ γ) (hn : 0 ≤ n) (hN : 0 < N) (hd : 0 ≤ d)
    (hnonneg : ∀ e ∈ M, 0 ≤ contribution e)
    (hedgecap : ∀ e ∈ M, contribution e ≤ 2 * N)
    (htotal : (1 - 10 * Real.sqrt d) * n ≤ ∑ e ∈ M, contribution e)
    (hlowerpos : 0 < (1 - 10 * Real.sqrt d) * n)
    (hfbsmall : f_b < Real.sqrt (Real.sqrt d) * n)
    (htargetHierarchy :
      Real.sqrt (Real.sqrt d) * n + 3 * γ * n ≤
        (1 - 10 * Real.sqrt d) * n)
    (hcardHierarchy :
      f_b + 3 * γ * n + 2 * N ≤
        2 * Real.sqrt (Real.sqrt d) * ((1 - 10 * Real.sqrt d) * n)) :
    ∃ M_b : Finset Edge,
      M_b ⊆ M ∧
      f_b + 3 * γ * n ≤ ∑ e ∈ M_b, contribution e ∧
      (∑ e ∈ M_b, contribution e) < f_b + 3 * γ * n + 2 * N ∧
      ((M_b.card : ℕ) : ℝ) ≤ 2 * Real.sqrt (Real.sqrt d) * k := by
  have hdQuarter : 0 ≤ Real.sqrt (Real.sqrt d) := Real.sqrt_nonneg _
  have htarget : 0 ≤ f_b + 3 * γ * n := by positivity
  have hcap : 0 < 2 * N := by positivity
  have htargetTotal : f_b + 3 * γ * n ≤ ∑ e ∈ M, contribution e := by
    calc
      f_b + 3 * γ * n ≤ Real.sqrt (Real.sqrt d) * n + 3 * γ * n := by
        linarith
      _ ≤ (1 - 10 * Real.sqrt d) * n := htargetHierarchy
      _ ≤ ∑ e ∈ M, contribution e := htotal
  exact zhao_lemma_6_12_unordered M contribution k
    (f_b + 3 * γ * n) (2 * N) (Real.sqrt (Real.sqrt d))
    ((1 - 10 * Real.sqrt d) * n) hmk hnonneg htarget hcap hedgecap
    htargetTotal htotal hlowerpos hdQuarter (by simpa [add_assoc] using hcardHierarchy)

#print axioms antitone_mul_sum_range_le_mul_prefix
#print axioms exists_first_prefix
#print axioms exists_small_decreasing_prefix
#print axioms orderedPrefix_subset
#print axioms card_orderedPrefix
#print axioms sum_orderedPrefix
#print axioms decreasingList_perm
#print axioms pairwise_decreasingList
#print axioms exists_small_submatching
#print axioms exists_small_submatching_positive
#print axioms exists_small_ordered_submatching
#print axioms zhao_lemma_6_12
#print axioms zhao_lemma_6_12_unordered
#print axioms zhao_lemma_6_12_source_constants

end Erdos547b.ZhaoLemma612
