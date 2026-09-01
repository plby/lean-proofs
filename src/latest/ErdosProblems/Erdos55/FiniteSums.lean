import Mathlib

/-!
# Finite distinct subset sums for Erdős Problem 55

This file records the elementary finite subset-sum machinery used in the
Conlon--Fox--Pham argument.  A subset sum always uses each integer at most
once: the witnesses are members of the powerset of a `Finset`.

The main result is the interval-extension lemma.  If the subset sums of `s`
cover `[L,U]`, and a fresh integer `a` is at most the length `U - L + 1` of
that interval, then adjoining `a` extends coverage through `U + a`.  The
list and sorted-finset forms iterate this observation without losing either
endpoint.
-/

open scoped BigOperators

namespace Erdos55

/-! ## Finite subset-sum values -/

/-- The finite set of all sums of subsets of `s`.

Because the witnesses belong to `s.powerset`, every element of `s` is used
at most once. -/
def subsetSumValues (s : Finset ℕ) : Finset ℕ :=
  s.powerset.image fun t ↦ ∑ x ∈ t, x

@[simp]
theorem mem_subsetSumValues {s : Finset ℕ} {n : ℕ} :
    n ∈ subsetSumValues s ↔ ∃ t : Finset ℕ, t ⊆ s ∧ (∑ x ∈ t, x) = n := by
  simp [subsetSumValues]

@[simp]
theorem subsetSumValues_empty : subsetSumValues ∅ = {0} := by
  ext n
  simp [mem_subsetSumValues, eq_comm]

@[simp]
theorem zero_mem_subsetSumValues (s : Finset ℕ) : 0 ∈ subsetSumValues s := by
  rw [mem_subsetSumValues]
  exact ⟨∅, Finset.empty_subset _, by simp⟩

theorem sum_mem_subsetSumValues (s : Finset ℕ) :
    (∑ x ∈ s, x) ∈ subsetSumValues s := by
  rw [mem_subsetSumValues]
  exact ⟨s, Finset.Subset.rfl, rfl⟩

/-- Enlarging the underlying set can only enlarge its set of subset sums. -/
theorem subsetSumValues_mono {s t : Finset ℕ} (hst : s ⊆ t) :
    subsetSumValues s ⊆ subsetSumValues t := by
  intro n hn
  rw [mem_subsetSumValues] at hn ⊢
  obtain ⟨u, hus, rfl⟩ := hn
  exact ⟨u, hus.trans hst, rfl⟩

/-- A subset sum remains available after adjoining one element. -/
theorem subsetSumValues_subset_insert (a : ℕ) (s : Finset ℕ) :
    subsetSumValues s ⊆ subsetSumValues (insert a s) :=
  subsetSumValues_mono (Finset.subset_insert a s)

/-- Adding a fresh element gives exactly the old subset sums and their
translate by that element. -/
theorem subsetSumValues_insert {a : ℕ} {s : Finset ℕ} (ha : a ∉ s) :
    subsetSumValues (insert a s) =
      subsetSumValues s ∪ (subsetSumValues s).image (fun n ↦ n + a) := by
  ext n
  constructor
  · intro hn
    rw [mem_subsetSumValues] at hn
    obtain ⟨u, hu, rfl⟩ := hn
    by_cases hau : a ∈ u
    · apply Finset.mem_union_right
      rw [Finset.mem_image]
      refine ⟨∑ x ∈ u.erase a, x, ?_, ?_⟩
      · rw [mem_subsetSumValues]
        refine ⟨u.erase a, ?_, rfl⟩
        intro x hx
        have hxu : x ∈ u := Finset.mem_of_mem_erase hx
        have hxas : x = a ∨ x ∈ s := by
          simpa only [Finset.mem_insert] using hu hxu
        exact hxas.resolve_left (fun hxa ↦ (Finset.ne_of_mem_erase hx) hxa)
      · rw [← Finset.sum_erase_add _ _ hau]
    · apply Finset.mem_union_left
      rw [mem_subsetSumValues]
      refine ⟨u, ?_, rfl⟩
      intro x hx
      have hxas : x = a ∨ x ∈ s := by
        simpa only [Finset.mem_insert] using hu hx
      exact hxas.resolve_left (fun hxa ↦ hau (hxa ▸ hx))
  · intro hn
    rw [Finset.mem_union] at hn
    rcases hn with hn | hn
    · exact subsetSumValues_subset_insert a s hn
    · rw [Finset.mem_image] at hn
      obtain ⟨m, hm, rfl⟩ := hn
      rw [mem_subsetSumValues] at hm ⊢
      obtain ⟨u, hus, rfl⟩ := hm
      refine ⟨insert a u, ?_, ?_⟩
      · exact Finset.insert_subset_insert a hus
      · have hau : a ∉ u := fun hau ↦ ha (hus hau)
        simp [hau, add_comm]

/-- The translated old subset sums occur after a fresh element is adjoined. -/
theorem translate_subsetSumValues_insert {a : ℕ} {s : Finset ℕ} (ha : a ∉ s) :
    (subsetSumValues s).image (fun n ↦ n + a) ⊆
      subsetSumValues (insert a s) := by
  rw [subsetSumValues_insert ha]
  exact Finset.subset_union_right

theorem add_mem_subsetSumValues_insert {a m : ℕ} {s : Finset ℕ}
    (ha : a ∉ s) (hm : m ∈ subsetSumValues s) :
    m + a ∈ subsetSumValues (insert a s) := by
  apply translate_subsetSumValues_insert ha
  exact Finset.mem_image.mpr ⟨m, hm, rfl⟩

/-- For disjoint sets, every subset of the union splits uniquely into its two
parts; at the level of values this gives a sumset decomposition. -/
theorem subsetSumValues_union {s t : Finset ℕ} (hdisj : Disjoint s t) :
    subsetSumValues (s ∪ t) =
      Finset.image₂ (fun m n : ℕ ↦ m + n) (subsetSumValues s) (subsetSumValues t) := by
  ext n
  constructor
  · intro hn
    rw [mem_subsetSumValues] at hn
    obtain ⟨u, hu, rfl⟩ := hn
    let us := u ∩ s
    let ut := u ∩ t
    have hus : us ⊆ s := Finset.inter_subset_right
    have hut : ut ⊆ t := Finset.inter_subset_right
    have hust : Disjoint us ut := hdisj.mono hus hut
    have hu_eq : u = us ∪ ut := by
      ext x
      simp only [us, ut, Finset.mem_union, Finset.mem_inter]
      constructor
      · intro hx
        rcases Finset.mem_union.mp (hu hx) with hxs | hxt
        · exact Or.inl ⟨hx, hxs⟩
        · exact Or.inr ⟨hx, hxt⟩
      · rintro (⟨hx, -⟩ | ⟨hx, -⟩) <;> exact hx
    rw [hu_eq, Finset.sum_union hust]
    apply Finset.mem_image₂.mpr
    refine ⟨∑ x ∈ us, x, ?_, ∑ x ∈ ut, x, ?_, rfl⟩
    · rw [mem_subsetSumValues]
      exact ⟨us, hus, rfl⟩
    · rw [mem_subsetSumValues]
      exact ⟨ut, hut, rfl⟩
  · intro hn
    rw [Finset.mem_image₂] at hn
    obtain ⟨m, hm, k, hk, rfl⟩ := hn
    rw [mem_subsetSumValues] at hm hk ⊢
    obtain ⟨us, hus, rfl⟩ := hm
    obtain ⟨ut, hut, rfl⟩ := hk
    have hust : Disjoint us ut := hdisj.mono hus hut
    refine ⟨us ∪ ut, ?_, ?_⟩
    · exact Finset.union_subset_union hus hut
    · rw [Finset.sum_union hust]

theorem add_mem_subsetSumValues_union {s t : Finset ℕ} (hdisj : Disjoint s t)
    {m n : ℕ} (hm : m ∈ subsetSumValues s) (hn : n ∈ subsetSumValues t) :
    m + n ∈ subsetSumValues (s ∪ t) := by
  rw [subsetSumValues_union hdisj]
  exact Finset.mem_image₂.mpr ⟨m, hm, n, hn, rfl⟩

/-! ## Graham's interval-extension lemma -/

/-- All integers in the closed interval `[L,U]` occur as distinct subset sums
of `s`. -/
def CoversInterval (s : Finset ℕ) (L U : ℕ) : Prop :=
  Finset.Icc L U ⊆ subsetSumValues s

theorem CoversInterval.mono {s t : Finset ℕ} {L U : ℕ}
    (h : CoversInterval s L U) (hst : s ⊆ t) : CoversInterval t L U :=
  fun _ hn ↦ subsetSumValues_mono hst (h hn)

/-- **Graham interval extension, one step.**  A fresh element no larger than
the number of integers in the covered interval extends its upper endpoint by
exactly that element. -/
theorem coversInterval_insert {s : Finset ℕ} {a L U : ℕ}
    (hLU : L ≤ U) (ha : a ∉ s) (ha_small : a ≤ U - L + 1)
    (hcover : CoversInterval s L U) :
    CoversInterval (insert a s) L (U + a) := by
  intro n hn
  have hn_bounds : L ≤ n ∧ n ≤ U + a := Finset.mem_Icc.mp hn
  by_cases hnU : n ≤ U
  · apply subsetSumValues_subset_insert a s
    exact hcover (Finset.mem_Icc.mpr ⟨hn_bounds.1, hnU⟩)
  · have ha_le_n : a ≤ n := by omega
    have hL : L ≤ n - a := by omega
    have hU : n - a ≤ U := by omega
    have hdiff : n - a ∈ subsetSumValues s :=
      hcover (Finset.mem_Icc.mpr ⟨hL, hU⟩)
    have hadd := add_mem_subsetSumValues_insert ha hdiff
    simpa [Nat.sub_add_cancel ha_le_n] using hadd

/-- **Iterated Graham extension, ordered-list form.**

The `i`th new element is required to be no larger than the original interval
length plus the sum of its predecessors.  `Nodup` and disjointness from `s`
ensure that every use is a genuinely distinct subset-sum choice. -/
theorem coversInterval_add_list {s : Finset ℕ} {L U : ℕ} (l : List ℕ)
    (hLU : L ≤ U) (hnodup : l.Nodup) (hdisj : Disjoint l.toFinset s)
    (hsmall : ∀ (i : ℕ) (hi : i < l.length),
      l[i] ≤ U - L + 1 + (l.take i).sum)
    (hcover : CoversInterval s L U) :
    CoversInterval (s ∪ l.toFinset) L (U + l.sum) := by
  induction l generalizing s U with
  | nil => simpa using hcover
  | cons a l ih =>
      have ha_s : a ∉ s := by
        have hd : a ∉ s ∧ Disjoint l.toFinset s := by
          simpa [List.toFinset_cons, Finset.disjoint_insert_left] using hdisj
        exact hd.1
      have ha_small : a ≤ U - L + 1 := by
        have h := hsmall 0 (by simp)
        simpa using h
      have hfirst : CoversInterval (insert a s) L (U + a) :=
        coversInterval_insert hLU ha_s ha_small hcover
      have hnodup_l : l.Nodup := hnodup.tail
      have ha_l : a ∉ l := (List.nodup_cons.mp hnodup).1
      have hdisj_l : Disjoint l.toFinset (insert a s) := by
        rw [Finset.disjoint_insert_right]
        refine ⟨?_, ?_⟩
        · simpa using ha_l
        · exact hdisj.mono_left (by simp)
      have hsmall_l : ∀ (i : ℕ) (hi : i < l.length),
          l[i] ≤ (U + a) - L + 1 + (l.take i).sum := by
        intro i hi
        have h := hsmall (i + 1) (by simp; omega)
        simp only [List.getElem_cons_succ, List.take_succ_cons, List.sum_cons] at h
        omega
      have htail := ih (U := U + a) (s := insert a s) (by omega)
        hnodup_l hdisj_l hsmall_l hfirst
      simpa [List.toFinset_cons, Finset.union_assoc, Finset.union_left_comm,
        Finset.union_comm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

/-- **Iterated Graham extension, finset form.**  The elements of `t` are
adjoined in increasing order.  The hypothesis displayed here is often called
the complete-sequence or Graham condition. -/
theorem coversInterval_add_finset {s t : Finset ℕ} {L U : ℕ}
    (hLU : L ≤ U) (hdisj : Disjoint t s)
    (hsmall : ∀ (i : ℕ) (hi : i < t.card),
      (t.sort (· ≤ ·))[i]'(by simpa using hi) ≤
        U - L + 1 + ((t.sort (· ≤ ·)).take i).sum)
    (hcover : CoversInterval s L U) :
    CoversInterval (s ∪ t) L (U + ∑ x ∈ t, x) := by
  let l := t.sort (· ≤ ·)
  have hlen : l.length = t.card := Finset.length_sort (s := t) (· ≤ ·)
  have hlfin : l.toFinset = t := Finset.sort_toFinset t (· ≤ ·)
  have hlsum : l.sum = ∑ x ∈ t, x := by
    have hnodup : l.Nodup := by
      simp [l]
    calc
      l.sum = ∑ x ∈ l.toFinset, x := by
        simpa using (List.sum_toFinset (fun x : ℕ ↦ x) hnodup).symm
      _ = ∑ x ∈ t, x := by rw [hlfin]
  have hsmall_l : ∀ (i : ℕ) (hi : i < l.length),
      l[i]'hi ≤ U - L + 1 + (l.take i).sum := by
    intro i hi
    have hi' : i < t.card := by simpa [hlen] using hi
    simpa [l] using hsmall i hi'
  have hout := coversInterval_add_list l hLU (Finset.sort_nodup t (· ≤ ·))
    (by simpa [hlfin] using hdisj) hsmall_l hcover
  simpa [hlfin, hlsum] using hout

/-- The usual zero-based Graham lemma: under the complete-sequence condition,
the subset sums of `t` fill the whole interval from zero to the total sum. -/
theorem graham_subsetSums_Icc {t : Finset ℕ}
    (hsmall : ∀ (i : ℕ) (hi : i < t.card),
      (t.sort (· ≤ ·))[i]'(by simpa using hi) ≤
        1 + ((t.sort (· ≤ ·)).take i).sum) :
    CoversInterval t 0 (∑ x ∈ t, x) := by
  have hbase : CoversInterval (∅ : Finset ℕ) 0 0 := by
    intro n hn
    simp only [Finset.mem_Icc] at hn
    have hn0 : n = 0 := by omega
    subst n
    exact zero_mem_subsetSumValues ∅
  have h := coversInterval_add_finset (s := (∅ : Finset ℕ)) (t := t)
    (L := 0) (U := 0) (by simp) (by simp) (by simpa using hsmall) hbase
  simpa using h

end Erdos55
