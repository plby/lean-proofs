import ErdosProblems.Erdos118.PartialWordResponses

/-!
Explicit fresh extensions of literal words at interior leaves. These local
operations do not assert a coloring theorem or a full-order family of plays.
-/

namespace Erdos118.InteriorWords

open Negative Negative.Exact Erdos590.Larson PartialWordResponses

/-- A nonempty, unfinished body with at least one later body still to come. -/
structure Position where
  root : ℕ
  done : G2
  size : ℕ
  entries : List ℕ
  room : done.length + 1 < root
  started : 0 < entries.length
  unfinished : entries.length < size
  increasing : (partialWord root done size entries).Pairwise (· < ·)

def Position.word (P : Position) : List ℕ :=
  partialWord P.root P.done P.size P.entries

theorem fresh_list {H : Set ℕ} (hH : H.Infinite) (b k : ℕ) :
    ∃ v : List ℕ, v.length = k ∧ v.Pairwise (· < ·) ∧
      ∀ x ∈ v, x ∈ H ∧ b < x := by
  let f := enumOf H
  have hf : StrictMono f := enumOf_strictMono hH
  refine ⟨enumSlice f (b + 1) k, length_enumSlice _ _ _,
    enumSlice_pairwise f hf _ _, ?_⟩
  intro x hx
  obtain ⟨i, _, rfl⟩ := mem_enumSlice.mp hx
  refine ⟨enumOf_mem hH _, ?_⟩
  have hi : b + 1 + i ≤ f (b + 1 + i) := hf.le_apply
  omega

theorem start {H : Set ℕ} (hH : H.Infinite) (b r k : ℕ) :
    ∃ P : Position, r + 1 < P.root ∧ P.done = [] ∧
      P.entries.length = 1 ∧ k + 1 < P.size ∧
      ∀ z ∈ P.word, z ∈ H ∧ b < z := by
  obtain ⟨m, hmH, hm⟩ := hH.exists_gt (max b (r + 1))
  obtain ⟨n, hnH, hn⟩ := hH.exists_gt (max m (k + 1))
  obtain ⟨x, hxH, hx⟩ := hH.exists_gt n
  have hbm : b < m := (le_max_left _ _).trans_lt hm
  have hrm : r + 1 < m := (le_max_right _ _).trans_lt hm
  have hmn : m < n := (le_max_left _ _).trans_lt hn
  have hkn : k + 1 < n := (le_max_right _ _).trans_lt hn
  let P : Position :=
    { root := m, done := [], size := n, entries := [x]
      room := by simp; omega
      started := by simp
      unfinished := by simp; omega
      increasing := by simp [partialWord, hmn, hx, hmn.trans hx] }
  refine ⟨P, hrm, rfl, rfl, hkn, ?_⟩
  intro z hz
  change z ∈ m :: [n, x] at hz
  rcases List.mem_cons.mp hz with rfl | hz
  · exact ⟨hmH, hbm⟩
  · rcases List.mem_cons.mp hz with rfl | hz
    · exact ⟨hnH, hbm.trans hmn⟩
    · have hz' : z = x := by simpa using hz
      subst z
      exact ⟨hxH, (hbm.trans hmn).trans hx⟩

theorem advance_leaf (P : Position) {H : Set ℕ} (hH : H.Infinite)
    (b j : ℕ) (hj : P.entries.length < j) (hjn : j < P.size) :
    ∃ Q : Position, ∃ v : List ℕ,
      Q.root = P.root ∧ Q.done = P.done ∧ Q.size = P.size ∧
      Q.entries.length = j ∧ Q.word = P.word ++ v ∧ v ≠ [] ∧
      ∀ z ∈ v, z ∈ H ∧ b < z := by
  let L := max b P.word.sum
  obtain ⟨v, hvlen, hvpair, hv⟩ := fresh_list hH L (j - P.entries.length)
  have hlen : (P.entries ++ v).length = j := by
    simp only [List.length_append, hvlen]
    omega
  have hword : partialWord P.root P.done P.size (P.entries ++ v) =
      P.word ++ v := by
    simp [partialWord, Position.word, List.append_assoc]
  have hcross : ∀ x ∈ P.word, ∀ y ∈ v, x < y := by
    intro x hx y hy
    exact ((nat_le_sum_of_mem hx).trans (le_max_right _ _)).trans_lt (hv y hy).2
  let Q : Position :=
    { root := P.root, done := P.done, size := P.size, entries := P.entries ++ v
      room := P.room
      started := by rw [hlen]; omega
      unfinished := hlen ▸ hjn
      increasing := hword ▸ List.pairwise_append.mpr ⟨P.increasing, hvpair, hcross⟩ }
  refine ⟨Q, v, rfl, rfl, rfl, hlen, hword, ?_, ?_⟩
  · intro he
    simp [he] at hvlen
    omega
  · exact fun z hz ↦ ⟨(hv z hz).1, (le_max_left _ _).trans_lt (hv z hz).2⟩

/-- Finish the old body, skip any prescribed finite number of whole bodies,
and stop at the first leaf of a new body with arbitrarily large capacity. -/
theorem advance_body (P : Position) {H : Set ℕ} (hH : H.Infinite)
    (b j k : ℕ) (hpj : P.done.length < j) (hjr : j + 1 < P.root) :
    ∃ Q : Position, ∃ v : List ℕ,
      Q.root = P.root ∧ Q.done.length = j ∧ Q.entries.length = 1 ∧
      k + 1 < Q.size ∧ Q.word = P.word ++ v ∧ v ≠ [] ∧
      ∀ z ∈ v, z ∈ H ∧ b < z := by
  let L := max b P.word.sum
  obtain ⟨a, halen, hapair, ha⟩ := fresh_list hH L (P.size - P.entries.length)
  let q := L + a.sum + 1
  let f := enumOf H
  have hf : StrictMono f := enumOf_strictMono hH
  let t := CoordinateModel.normalizeTail f q
    (List.replicate (j - P.done.length - 1) [])
  have htlen : t.length = j - P.done.length - 1 := by simp [t]
  have ht := CoordinateModel.normalizeTail_spec hf q
    (List.replicate (j - P.done.length - 1) [])
  have hLq : L < q := by simp [q]
  have haq : ∀ z ∈ a, z < q := by
    intro z hz
    have h := nat_le_sum_of_mem hz
    dsimp [q]
    omega
  have htailpair : (a ++ t.flatMap levelWord).Pairwise (· < ·) :=
    List.pairwise_append.mpr ⟨hapair, ht.2.1,
      fun x hx y hy ↦ (haq x hx).trans (ht.1 y hy)⟩
  have htail : ∀ z ∈ a ++ t.flatMap levelWord, z ∈ H ∧ L < z := by
    intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact ha z hz
    · obtain ⟨i, hi⟩ := ht.2.2 z hz
      exact ⟨hi ▸ enumOf_mem hH i, hLq.trans (ht.1 z hz)⟩
  let p' := P.done ++ [P.entries ++ a] ++ t
  have hbodylen : (P.entries ++ a).length = P.size := by
    simp only [List.length_append, halen]
    have h := P.unfinished
    omega
  have hp'len : p'.length = j := by
    simp only [p', List.length_append, List.length_singleton, htlen]
    omega
  let U := P.root :: p'.flatMap levelWord
  have hU : U = P.word ++ (a ++ t.flatMap levelWord) := by
    simp [U, p', Position.word, partialWord, levelWord, hbodylen, List.append_assoc]
  have hUpair : U.Pairwise (· < ·) := by
    rw [hU]
    refine List.pairwise_append.mpr ⟨P.increasing, htailpair, ?_⟩
    intro x hx y hy
    exact ((nat_le_sum_of_mem hx).trans (le_max_right _ _)).trans_lt (htail y hy).2
  obtain ⟨n, hnH, hn⟩ := hH.exists_gt (max (k + 1) (max b U.sum))
  obtain ⟨x, hxH, hx⟩ := hH.exists_gt n
  have hkn : k + 1 < n := (le_max_left _ _).trans_lt hn
  have hbn : b < n := (le_max_left b U.sum).trans_lt
    ((le_max_right _ _).trans_lt hn)
  have hUn : ∀ z ∈ U, z < n := by
    intro z hz
    exact (nat_le_sum_of_mem hz).trans_lt ((le_max_right b U.sum).trans_lt
      ((le_max_right _ _).trans_lt hn))
  have hQword : partialWord P.root p' n [x] = U ++ [n, x] := by
    simp [partialWord, U]
  let Q : Position :=
    { root := P.root, done := p', size := n, entries := [x]
      room := hp'len ▸ hjr
      started := by simp
      unfinished := by simp; omega
      increasing := by
        rw [hQword]
        refine List.pairwise_append.mpr ⟨hUpair, by simp [hx], ?_⟩
        intro z hz y hy
        have hy' : y = n ∨ y = x := by simpa using hy
        rcases hy' with rfl | rfl
        · exact hUn z hz
        · exact (hUn z hz).trans hx }
  let v := (a ++ t.flatMap levelWord) ++ [n, x]
  refine ⟨Q, v, rfl, hp'len, rfl, hkn, ?_, ?_, ?_⟩
  · change partialWord P.root p' n [x] = P.word ++ v
    rw [hQword, hU, List.append_assoc]
  · simp [v]
  · intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact ⟨(htail z hz).1, (le_max_left _ _).trans_lt (htail z hz).2⟩
    · have hz' : z = n ∨ z = x := by simpa using hz
      rcases hz' with rfl | rfl
      · exact ⟨hnH, hbn⟩
      · exact ⟨hxH, hbn.trans hx⟩

theorem complete (P : Position) {H : Set ℕ} (hH : H.Infinite) (b : ℕ) :
    ∃ x : G, ∃ v : List ℕ, x.1.length = P.root ∧
      word x.1 = P.word ++ v ∧ v ≠ [] ∧
      ∀ z ∈ v, z ∈ H ∧ b < z := by
  obtain ⟨y, hyH, hy⟩ := hH.exists_gt (max b P.word.sum)
  have hby : b < y := (le_max_left _ _).trans_lt hy
  have hPy : ∀ z ∈ P.word, z < y :=
    fun z hz ↦ (nat_le_sum_of_mem hz).trans_lt ((le_max_right _ _).trans_lt hy)
  have hword : partialWord P.root P.done P.size (P.entries ++ [y]) =
      P.word ++ [y] := by
    simp [partialWord, Position.word, List.append_assoc]
  have hp : P.done.length < P.root := by have h := P.room; omega
  have hu : (P.entries ++ [y]).length ≤ P.size := by
    have h := P.unfinished
    simp only [List.length_append, List.length_singleton]
    omega
  have hgood : (partialWord P.root P.done P.size (P.entries ++ [y])).Pairwise
      (· < ·) := by
    rw [hword]
    apply List.pairwise_append.mpr
    refine ⟨P.increasing, by simp, ?_⟩
    intro z hz t ht
    have he : t = y := by simpa using ht
    exact he ▸ hPy z hz
  obtain ⟨x, r, hxr, hr⟩ := completion_above P.root P.done P.size
    (P.entries ++ [y]) hp hu hgood hH b
  have hfull : word x.1 = P.word ++ (y :: r) := by
    rw [hword, List.append_assoc] at hxr
    exact hxr
  have hroot : x.1.length = P.root := by
    have he := congrArg (fun l : List ℕ ↦ l.headD 0) hfull
    simpa [word, Position.word, partialWord] using he
  refine ⟨x, y :: r, hroot, hfull, List.cons_ne_nil _ _, ?_⟩
  intro z hz
  rcases List.mem_cons.mp hz with rfl | hz
  · exact ⟨hyH, hby⟩
  · exact hr z hz

end Erdos118.InteriorWords
