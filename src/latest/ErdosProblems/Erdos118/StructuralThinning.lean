import ErdosProblems.Erdos118.RootInterleaving
import Mathlib.Data.Nat.Pairing

/-!
A full-order family with disjoint supports at different roots, and an
explicit triangle-free obstruction to alphabet-only thinning. The obstruction
is not the negative witness for Problem 118: it has a full independent copy.
-/

open Set Ordinal

namespace Erdos118.StructuralThinning

open Negative Negative.Exact WeakPigeon Erdos590.Larson

def slice (f : ℕ → ℕ) (i k : ℕ) : ℕ := f (Nat.pair i k)

theorem slice_strictMono {f : ℕ → ℕ} (hf : StrictMono f) (i : ℕ) :
    StrictMono (slice f i) := fun _ _ h ↦ hf (Nat.pair_lt_pair_right i h)

theorem slice_eq_iff {f : ℕ → ℕ} (hf : StrictMono f) {i j a b : ℕ} :
    slice f i a = slice f j b ↔ i = j ∧ a = b := by
  exact hf.injective.eq_iff.trans Nat.pair_eq_pair

def allocated (f : ℕ → ℕ) (r : ℕ) : Set ℕ :=
  insert (slice f 0 r) (Set.range (slice f (r + 1)))

theorem allocated_disjoint {f : ℕ → ℕ} (hf : StrictMono f)
    {r s : ℕ} (hrs : r ≠ s) : Disjoint (allocated f r) (allocated f s) := by
  rw [Set.disjoint_left]
  intro x hx hy
  rcases hx with hxr | ⟨i, hi⟩ <;> rcases hy with hys | ⟨j, hj⟩
  · exact hrs ((slice_eq_iff hf).mp (hxr.symm.trans hys)).2
  · have h := ((slice_eq_iff hf).mp (hxr.symm.trans hj.symm)).1
    omega
  · have h := ((slice_eq_iff hf).mp (hi.trans hys)).1
    omega
  · have h := ((slice_eq_iff hf).mp (hi.trans hj.symm)).1
    exact hrs (Nat.add_right_cancel h)

def normalize (f : ℕ → ℕ) (s : G2) : G2 :=
  CoordinateModel.normalizeTail (slice f (s.length + 1)) (slice f 0 s.length)
    (CoordinateModel.padded (slice f 0) s)

@[simp] theorem normalize_length {f : ℕ → ℕ} (hf : StrictMono f) (s : G2) :
    (normalize f s).length = slice f 0 s.length := by
  simp [normalize, CoordinateModel.padded_length (slice_strictMono hf 0)]

theorem normalize_good {f : ℕ → ℕ} (hf : StrictMono f) (s : G2) :
    (word (normalize f s)).Pairwise (· < ·) := by
  rw [word, normalize_length hf, List.pairwise_cons]
  have h := CoordinateModel.normalizeTail_spec (slice_strictMono hf (s.length + 1))
    (slice f 0 s.length) (CoordinateModel.padded (slice f 0) s)
  exact ⟨h.1, h.2.1⟩

theorem normalize_allocated {f : ℕ → ℕ} (hf : StrictMono f) (s : G2) :
    ∀ x ∈ word (normalize f s), x ∈ allocated f s.length := by
  rw [word, normalize_length hf]
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _
      ((CoordinateModel.normalizeTail_spec (slice_strictMono hf (s.length + 1))
        _ _).2.2 x hx)

theorem normalize_mono {f : ℕ → ℕ} (hf : StrictMono f)
    {s t : G2} (hst : G2LT s t) : G2LT (normalize f s) (normalize f t) := by
  change List.Shortlex SL s t at hst
  change List.Shortlex SL (normalize f s) (normalize f t)
  rw [List.shortlex_def] at hst ⊢
  rcases hst with hlen | ⟨hlen, hlex⟩
  · left
    simpa only [normalize_length hf] using (slice_strictMono hf 0) hlen
  · right
    refine ⟨by simp only [normalize_length hf, hlen], ?_⟩
    unfold normalize CoordinateModel.padded
    rw [hlen]
    apply CoordinateModel.normalizeTail_lex_mono (slice_strictMono hf (t.length + 1))
    induction (List.replicate (slice f 0 t.length - t.length) ([] : List ℕ)) with
    | nil => exact hlex
    | cons _ _ ih => exact List.Lex.cons ih

def normalized {f : ℕ → ℕ} (hf : StrictMono f) (s : G2) : G :=
  ⟨normalize f s, normalize_good hf s⟩

/-- Exact order survives allocation of a different infinite alphabet to each
root. This is not merely an infinite independent set construction. -/
theorem exists_disjoint_root_family {H : Set ℕ} (hH : H.Infinite) :
    ∃ W : Set G, W ⊆ CoordinateModel.Supported H ∧ typeLT W = lambda ∧
      ∀ s ∈ W, ∀ t ∈ W, s.1.length ≠ t.1.length →
        Disjoint (WordResponses.support s) (WordResponses.support t) := by
  let f := enumOf H
  have hf : StrictMono f := enumOf_strictMono hH
  let W : Set G := Set.range (normalized hf)
  refine ⟨W, ?_, ?_, ?_⟩
  · rintro x ⟨s, rfl⟩ z hz
    rcases normalize_allocated hf s z hz with hz | ⟨i, rfl⟩
    · rw [hz]
      exact enumOf_mem hH _
    · exact enumOf_mem hH _
  · apply le_antisymm
    · exact (Ordinal.type_set_le W).trans_eq (type_G.trans lambda_eq_natural_inner_power.symm)
    · rw [lambda_eq_natural_inner_power, ← g2_type]
      exact (RelEmbedding.ofMonotone
        (r := G2LT) (s := ((· < ·) : W → W → Prop))
        (fun s ↦ ⟨normalized hf s, s, rfl⟩)
        (fun _ _ h ↦ normalize_mono hf h)).ordinal_type_le
  · rintro x ⟨s, rfl⟩ y ⟨t, rfl⟩ hroots
    have hst : s.length ≠ t.length := by
      intro h
      apply hroots
      simp only [normalized, normalize_length hf, h]
    apply Finset.disjoint_left.mpr
    intro z hz₁ hz₂
    exact Set.disjoint_left.mp (allocated_disjoint hf hst)
      (normalize_allocated hf s z (List.mem_toFinset.mp hz₁))
      (normalize_allocated hf t z (List.mem_toFinset.mp hz₂))

def firstMarker (s : G) : ℕ := (s.1.headD []).length

def Forward (s t : G) : Prop := s.1.length < t.1.length ∧ firstMarker s = t.1.length

def shiftGraph : SimpleGraph G where
  Adj s t := Forward s t ∨ Forward t s
  symm := ⟨fun _ _ h ↦ h.symm⟩
  loopless := ⟨by intro s h; rcases h with h | h <;> exact (Nat.lt_irrefl _ h.1)⟩

theorem shift_no_triangle (s t u : G) (hst : shiftGraph.Adj s t)
    (hsu : shiftGraph.Adj s u) (htu : shiftGraph.Adj t u) : False := by
  rcases hst with ⟨hst, hst'⟩ | ⟨hst, hst'⟩ <;>
    rcases hsu with ⟨hsu, hsu'⟩ | ⟨hsu, hsu'⟩ <;>
    rcases htu with ⟨htu, htu'⟩ | ⟨htu, htu'⟩ <;> omega

theorem shift_cliqueFree_three : shiftGraph.CliqueFree 3 := by
  classical
  intro s ⟨hc, hcard⟩
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := s.card_eq_three.mp hcard
  exact shift_no_triangle a b c
    (hc (by simp) (by simp) hab) (hc (by simp) (by simp) hac)
    (hc (by simp) (by simp) hbc)

theorem shift_adj_roots_ne {s t : G} (h : shiftGraph.Adj s t) :
    s.1.length ≠ t.1.length := by
  rcases h with h | h
  · exact Nat.ne_of_lt h.1
  · exact (Nat.ne_of_lt h.1).symm

theorem forward_common_coordinate {s t : G} (h : Forward s t) :
    t.1.length ∈ WordResponses.support s ∧ t.1.length ∈ WordResponses.support t := by
  have hs : s.1 ≠ [] := by
    intro he
    have hq : firstMarker s = 0 := by simp [firstMarker, he]
    have hlt := h.1
    rw [he, ← h.2, hq] at hlt
    exact Nat.not_lt_zero _ hlt
  refine ⟨?_, List.mem_toFinset.mpr (List.mem_cons_self ..)⟩
  rw [← h.2]
  apply List.mem_toFinset.mpr
  obtain ⟨a, l, hl⟩ := List.exists_cons_of_ne_nil hs
  simp [firstMarker, word, hl, levelWord]

theorem root_firstMarker_of_word {s : G} {m n : ℕ} {r : List ℕ}
    (h : word s.1 = m :: n :: r) : s.1.length = m ∧ firstMarker s = n := by
  cases hs : s.1 with
  | nil => simp [word, hs] at h
  | cons a l =>
    simp only [word, hs, List.flatMap_cons, levelWord, List.cons_append] at h
    exact ⟨(List.cons.inj h).1, by
      simpa only [firstMarker, hs, List.headD_cons] using
        (List.cons.inj (List.cons.inj h).2).1⟩

/-- No choice of an infinite coordinate alphabet can remove all shift edges. -/
theorem shift_edge_in_every_alphabet {H : Set ℕ} (hH : H.Infinite) :
    ∃ s ∈ CoordinateModel.Supported H, ∃ t ∈ CoordinateModel.Supported H,
      shiftGraph.Adj s t := by
  obtain ⟨m, hmH, hm⟩ := hH.exists_gt 0
  obtain ⟨n, hnH, hmn⟩ := hH.exists_gt m
  obtain ⟨s, r, hs, hr⟩ := PartialWordResponses.completion_above m [] n [] hm
    (Nat.zero_le n) (by simpa [PartialWordResponses.partialWord] using hmn) hH 0
  have hsword : word s.1 = m :: n :: r := by
    simpa only [PartialWordResponses.partialWord, List.flatMap_nil, List.nil_append,
      List.cons_append] using hs
  have hsdata := root_firstMarker_of_word hsword
  have hsH : s ∈ CoordinateModel.Supported H := by
    intro x hx
    rw [hsword] at hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hmH
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact hnH
      · exact (hr x hx).1
  let f := enumOf H
  have hf : StrictMono f := enumOf_strictMono hH
  let raw := CoordinateModel.normalizeTail f n (List.replicate n [])
  have hlen : raw.length = n := by simp [raw]
  have hraw := CoordinateModel.normalizeTail_spec hf n (List.replicate n [])
  have hgood : (word raw).Pairwise (· < ·) := by
    rw [word, hlen, List.pairwise_cons]
    exact ⟨hraw.1, hraw.2.1⟩
  let t : G := ⟨raw, hgood⟩
  have htH : t ∈ CoordinateModel.Supported H := by
    intro x hx
    change x ∈ word raw at hx
    rw [word, hlen] at hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hnH
    · obtain ⟨i, rfl⟩ := hraw.2.2 x hx
      exact enumOf_mem hH i
  refine ⟨s, hsH, t, htH, Or.inl ?_⟩
  change s.1.length < raw.length ∧ firstMarker s = raw.length
  rw [hlen, hsdata.1, hsdata.2]
  exact ⟨hmn, rfl⟩

/-- Even the global-pair conclusion cannot hold on an entire thinned alphabet. -/
theorem shift_not_globally_red_on_alphabet {H : Set ℕ} (hH : H.Infinite) :
    ¬ (∀ s ∈ CoordinateModel.Supported H, ∀ t ∈ CoordinateModel.Supported H,
      s.1.length ≠ t.1.length → ¬ shiftGraph.Adj s t) := by
  intro hred
  obtain ⟨s, hs, t, ht, hadj⟩ := shift_edge_in_every_alphabet hH
  exact hred s hs t ht (shift_adj_roots_ne hadj) hadj

/-- The obstruction has a full independent copy after structural thinning. -/
theorem shift_independent_full_type {H : Set ℕ} (hH : H.Infinite) :
    ∃ W ⊆ CoordinateModel.Supported H, shiftGraph.IsIndepSet W ∧ typeLT W = lambda := by
  obtain ⟨W, hWH, htype, hdisj⟩ := exists_disjoint_root_family hH
  refine ⟨W, hWH, ?_, htype⟩
  intro s hs t ht _ hadj
  have hd := hdisj s hs t ht (shift_adj_roots_ne hadj)
  rcases hadj with h | h
  · exact Finset.disjoint_left.mp hd (forward_common_coordinate h).1
      (forward_common_coordinate h).2
  · exact Finset.disjoint_left.mp hd (forward_common_coordinate h).2
      (forward_common_coordinate h).1

end Erdos118.StructuralThinning
