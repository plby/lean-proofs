import ErdosProblems.Erdos118.WordResponses

/-! Every valid partially filled literal word can be completed above any
finite bound, using fresh coordinates in any infinite alphabet. -/

namespace Erdos118.PartialWordResponses

open Negative Negative.Exact Erdos590.Larson

def partialWord (m : ℕ) (p : G2) (n : ℕ) (u : List ℕ) : List ℕ :=
  m :: (p.flatMap levelWord ++ (n :: u))

theorem completion_above (m : ℕ) (p : G2) (n : ℕ) (u : List ℕ)
    (hp : p.length < m) (hu : u.length ≤ n)
    (hgood : (partialWord m p n u).Pairwise (· < ·))
    {H : Set ℕ} (hH : H.Infinite) (b : ℕ) :
    ∃ x : G, ∃ r : List ℕ, word x.1 = partialWord m p n u ++ r ∧
      ∀ z ∈ r, z ∈ H ∧ b < z := by
  let f := enumOf H
  have hf : StrictMono f := enumOf_strictMono hH
  let P := partialWord m p n u
  let L := max b P.sum
  let v := enumSlice f (L + 1) (n - u.length)
  have hvlen : v.length = n - u.length := length_enumSlice _ _ _
  have hvpair : v.Pairwise (· < ·) := enumSlice_pairwise f hf _ _
  have hv : ∀ z ∈ v, z ∈ H ∧ L < z := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := mem_enumSlice.mp hz
    refine ⟨enumOf_mem hH _, ?_⟩
    have hh : L + 1 + i ≤ f (L + 1 + i) := hf.le_apply
    omega
  let q := L + v.sum + 1
  let k := m - p.length - 1
  let t := CoordinateModel.normalizeTail f q (List.replicate k [])
  have htlen : t.length = k := by simp [t]
  have ht := CoordinateModel.normalizeTail_spec hf q (List.replicate k [])
  have htbound : ∀ z ∈ t.flatMap levelWord, q < z := ht.1
  have htpair : (t.flatMap levelWord).Pairwise (· < ·) := ht.2.1
  have htmem : ∀ z ∈ t.flatMap levelWord, z ∈ H := by
    intro z hz
    obtain ⟨i, rfl⟩ := ht.2.2 z hz
    exact enumOf_mem hH i
  let a := u ++ v
  have halen : a.length = n := by
    simp only [a, List.length_append, hvlen]
    exact Nat.add_sub_of_le hu
  let s := p ++ [a] ++ t
  have hslen : s.length = m := by
    simp only [s, List.length_append, List.length_singleton, htlen]
    dsimp [k]
    omega
  have hword : word s = P ++ (v ++ t.flatMap levelWord) := by
    rw [word, hslen]
    simp only [s, List.flatMap_append, List.flatMap_cons,
      List.nil_append, levelWord, halen, a, P, partialWord, List.cons_append,
      List.append_assoc]
  have hPL : ∀ z ∈ P, z ≤ L :=
    fun _ hz ↦ (nat_le_sum_of_mem hz).trans (le_max_right _ _)
  have hLq : L < q := by simp [q]
  have hvq : ∀ z ∈ v, z < q := by
    intro z hz
    have hzsum := nat_le_sum_of_mem hz
    dsimp [q]
    omega
  have htailpair : (v ++ t.flatMap levelWord).Pairwise (· < ·) :=
    List.pairwise_append.mpr ⟨hvpair, htpair,
      fun z hz w hw ↦ (hvq z hz).trans (htbound w hw)⟩
  have hcross : ∀ z ∈ P, ∀ w ∈ v ++ t.flatMap levelWord, z < w := by
    intro z hz w hw
    rcases List.mem_append.mp hw with hw | hw
    · exact (hPL z hz).trans_lt (hv w hw).2
    · exact (hPL z hz).trans_lt (hLq.trans (htbound w hw))
  have hsgood : (word s).Pairwise (· < ·) := by
    rw [hword]
    exact List.pairwise_append.mpr ⟨hgood, htailpair, hcross⟩
  refine ⟨⟨s, hsgood⟩, v ++ t.flatMap levelWord, hword, ?_⟩
  intro z hz
  rcases List.mem_append.mp hz with hz | hz
  · exact ⟨(hv z hz).1, (le_max_left _ _).trans_lt (hv z hz).2⟩
  · exact ⟨htmem z hz, (le_max_left _ _).trans_lt (hLq.trans (htbound z hz))⟩

def completionFamily (P : List ℕ) : Set (Finset ℕ) :=
  {s | ∃ x : G, ∃ r : List ℕ, word x.1 = P ++ r ∧ r.toFinset = s}

theorem completionFamily_thin (P : List ℕ) :
    NashWilliams.FinThin (completionFamily P) := by
  rintro _ ⟨x, r, hxr, rfl⟩ _ ⟨y, s, hys, rfl⟩ hrs
  have hr : r.Pairwise (· < ·) := by
    have h := x.2
    rw [hxr] at h
    exact (List.pairwise_append.mp h).2.1
  have hs : s.Pairwise (· < ·) := by
    have h := y.2
    rw [hys] at h
    exact (List.pairwise_append.mp h).2.1
  obtain ⟨z, hz⟩ := (pairwise_isPrefix_iff_initSeg hr hs).2 hrs
  have hprefix : word x.1 <+: word y.1 := by
    refine ⟨z, ?_⟩
    rw [hxr, hys, List.append_assoc, hz]
  have hxy := WordResponses.word_prefix_rigid hprefix
  have hwords := congrArg word hxy
  rw [hxr, hys] at hwords
  exact congrArg List.toFinset (List.append_cancel_left hwords)

theorem completionFamily_hits (m : ℕ) (p : G2) (n : ℕ) (u : List ℕ)
    (hp : p.length < m) (hu : u.length ≤ n)
    (hgood : (partialWord m p n u).Pairwise (· < ·))
    {H : Set ℕ} (hH : H.Infinite) :
    ∃ s ∈ completionFamily (partialWord m p n u), (↑s : Set ℕ) ⊆ H := by
  obtain ⟨x, r, hword, hr⟩ := completion_above m p n u hp hu hgood hH 0
  exact ⟨r.toFinset, ⟨x, r, hword, rfl⟩,
    fun _ hz ↦ (hr _ (List.mem_toFinset.mp hz)).1⟩

def bodyResponseFamily (m : ℕ) (p : G2) (n : ℕ) (u : List ℕ)
    (hp : p.length < m) (hu : u.length ≤ n)
    (hgood : (partialWord m p n u).Pairwise (· < ·)) : RamseyGame.ResponseFamily where
  members := completionFamily (partialWord m p n u)
  thin := completionFamily_thin _
  hits := fun _ hH ↦ completionFamily_hits m p n u hp hu hgood hH

end Erdos118.PartialWordResponses
