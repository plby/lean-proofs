/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos651.Definitions

/-!
# Finite uniform hypergraph Ramsey selection

This file proves the finite two-colour Ramsey theorem for uniform hypergraphs.  The proof is the
usual induction on the uniformity.  At the successor step we repeatedly choose a new vertex and
apply the theorem in one lower uniformity to make the colour seen from that vertex constant on a
large reservoir.  Among twice as many canonized vertices as are needed, one of the two colours
occurs often enough.
-/

namespace Erdos651

open Filter

/-- `H` is monochromatic for `c` on its `r`-element subsets. -/
def MonochromaticOn {α : Type*} [DecidableEq α]
    (r : ℕ) (c : Finset α → Bool) (H : Finset α) : Prop :=
  ∃ b : Bool, ∀ A : Finset α, A ⊆ H → A.card = r → c A = b

/-- An explicit (very large) finite two-colour uniform Ramsey bound. -/
def uniformRamseyBound : ℕ → ℕ → ℕ
  | 0, m => m
  | r + 1, m => (fun t => 1 + uniformRamseyBound r t)^[2 * m] 0
termination_by r _ => r

/-- The number of vertices required to construct a canonized chain of length `q`, assuming the
Ramsey theorem in uniformity `r`. -/
private def canonicalBound (r q : ℕ) : ℕ :=
  (fun t => 1 + uniformRamseyBound r t)^[q] 0

private lemma canonicalBound_zero (r : ℕ) : canonicalBound r 0 = 0 := by
  rfl

private lemma canonicalBound_succ (r q : ℕ) :
    canonicalBound r (q + 1) = 1 + uniformRamseyBound r (canonicalBound r q) := by
  simp [canonicalBound, Function.iterate_succ_apply']

/-- A chain whose vertex `x` is labelled by the common colour of all edges consisting of `x` and
`r` later vertices.  Storing the label beside the vertex makes the final pigeonhole step clean. -/
private def IsCanonicalChain {α : Type*} [DecidableEq α]
    (r : ℕ) (c : Finset α → Bool) : List (α × Bool) → Prop
  | [] => True
  | (x, b) :: ps =>
      x ∉ ps.map Prod.fst ∧ IsCanonicalChain r c ps ∧
        ∀ A : Finset α, A ⊆ (ps.map Prod.fst).toFinset → A.card = r →
          c (insert x A) = b

private lemma IsCanonicalChain.fst_nodup {α : Type*} [DecidableEq α]
    {r : ℕ} {c : Finset α → Bool} {ps : List (α × Bool)}
    (h : IsCanonicalChain r c ps) : (ps.map Prod.fst).Nodup := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
      rcases p with ⟨x, b⟩
      simp only [IsCanonicalChain] at h
      simpa using List.nodup_cons.mpr ⟨h.1, ih h.2.1⟩

private lemma IsCanonicalChain.filter_snd {α : Type*} [DecidableEq α]
    {r : ℕ} {c : Finset α → Bool} {ps : List (α × Bool)}
    (h : IsCanonicalChain r c ps) (b : Bool) :
    IsCanonicalChain r c (ps.filter fun p => decide (p.2 = b)) := by
  induction ps with
  | nil => simp [IsCanonicalChain]
  | cons p ps ih =>
      rcases p with ⟨x, d⟩
      simp only [IsCanonicalChain] at h
      by_cases hdb : d = b
      · subst d
        simp only [List.filter_cons, decide_true, if_true, IsCanonicalChain]
        refine ⟨?_, ih h.2.1, ?_⟩
        · intro hx
          apply h.1
          simp only [List.mem_map] at hx ⊢
          obtain ⟨p, hp, rfl⟩ := hx
          exact ⟨p, List.mem_of_mem_filter hp, rfl⟩
        · intro A hA hcard
          exact h.2.2 A (hA.trans (by
            intro y hy
            simp only [List.mem_toFinset, List.mem_map] at hy ⊢
            obtain ⟨p, hp, rfl⟩ := hy
            exact ⟨p, List.mem_of_mem_filter hp, rfl⟩)) hcard
      · simp only [List.filter_cons, hdb, decide_false, Bool.false_eq]
        exact ih h.2.1

private lemma IsCanonicalChain.monochromatic_of_constant_snd
    {α : Type*} [DecidableEq α] {r : ℕ} {c : Finset α → Bool}
    {ps : List (α × Bool)} (h : IsCanonicalChain r c ps) (b : Bool)
    (hb : ∀ p ∈ ps, p.2 = b) :
    ∀ A : Finset α, A ⊆ (ps.map Prod.fst).toFinset → A.card = r + 1 → c A = b := by
  induction ps with
  | nil =>
      intro A hA hcard
      have : A = ∅ := Finset.subset_empty.mp (by simpa using hA)
      subst A
      simp at hcard
  | cons p ps ih =>
      rcases p with ⟨x, d⟩
      simp only [IsCanonicalChain] at h
      intro A hA hcard
      have hd : d = b := hb (x, d) (by simp)
      by_cases hx : x ∈ A
      · have herase : A.erase x ⊆ (ps.map Prod.fst).toFinset := by
          intro y hy
          have hyA : y ∈ A := Finset.mem_of_mem_erase hy
          have hy' := hA hyA
          simp only [List.map_cons, List.toFinset_cons, Finset.mem_insert] at hy'
          rcases hy' with rfl | hy'
          · exact False.elim ((Finset.ne_of_mem_erase hy) rfl)
          · exact hy'
        have hcardErase : (A.erase x).card = r := by
          rw [Finset.card_erase_of_mem hx]
          omega
        have hc := h.2.2 (A.erase x) herase hcardErase
        rw [Finset.insert_erase hx] at hc
        exact hc.trans hd
      · apply ih h.2.1 (fun p hp => hb p (by simp [hp])) A ?_ hcard
        intro y hy
        have hy' := hA hy
        simp only [List.map_cons, List.toFinset_cons, Finset.mem_insert] at hy'
        exact hy'.resolve_left (fun hxy => hx (hxy ▸ hy))

/-- The explicit bound has the required two-colour uniform Ramsey property, on an arbitrary finite
ambient set. -/
theorem uniformRamseyBound_spec (r m : ℕ) {α : Type*} [DecidableEq α]
    (X : Finset α) (hX : uniformRamseyBound r m ≤ X.card)
    (c : Finset α → Bool) :
    ∃ H : Finset α, H ⊆ X ∧ H.card = m ∧ MonochromaticOn r c H := by
  induction r generalizing m α with
  | zero =>
      obtain ⟨H, hHX, hcard⟩ := Finset.exists_subset_card_eq hX
      have hcard' : H.card = m := by simpa [uniformRamseyBound] using hcard
      refine ⟨H, hHX, hcard', c ∅, ?_⟩
      intro A _ hA
      simpa [Finset.card_eq_zero.mp hA]
  | succ r ihr =>
      have chain : ∀ (q : ℕ) (Y : Finset α),
          canonicalBound r q ≤ Y.card → (d : Finset α → Bool) →
          ∃ ps : List (α × Bool), ps.length = q ∧ IsCanonicalChain r d ps ∧
            ∀ p ∈ ps, p.1 ∈ Y := by
        intro q
        induction q with
        | zero =>
            intro Y _ d
            exact ⟨[], rfl, trivial, by simp⟩
        | succ q ihq =>
            intro Y hY d
            rw [canonicalBound_succ] at hY
            have hYpos : 0 < Y.card := by omega
            obtain ⟨x, hxY⟩ := Finset.card_pos.mp hYpos
            let Z := Y.erase x
            have hZ : uniformRamseyBound r (canonicalBound r q) ≤ Z.card := by
              dsimp [Z]
              rw [Finset.card_erase_of_mem hxY]
              omega
            obtain ⟨K, hKZ, hKcard, hKmono⟩ :=
              ihr (canonicalBound r q) Z hZ (fun A => d (insert x A))
            rcases hKmono with ⟨b, hb⟩
            obtain ⟨ps, hpslen, hpscan, hpsK⟩ :=
              ihq K (by simpa [hKcard]) d
            refine ⟨(x, b) :: ps, by simp [hpslen], ?_, ?_⟩
            · simp only [IsCanonicalChain]
              refine ⟨?_, hpscan, ?_⟩
              · intro hx
                simp only [List.mem_map] at hx
                obtain ⟨p, hp, hp1⟩ := hx
                have hpxK : p.1 ∈ K := hpsK p hp
                have hpxZ : p.1 ∈ Z := hKZ hpxK
                have hne : p.1 ≠ x := by
                  exact (Finset.mem_erase.mp hpxZ).1
                exact hne hp1
              · intro A hA hcard
                apply hb A ?_ hcard
                intro y hy
                have : y ∈ (ps.map Prod.fst).toFinset := hA hy
                simp only [List.mem_toFinset, List.mem_map] at this
                obtain ⟨p, hp, rfl⟩ := this
                exact hpsK p hp
            · intro p hp
              simp only [List.mem_cons] at hp
              rcases hp with rfl | hp
              · exact hxY
              · exact (Finset.mem_erase.mp (hKZ (hpsK p hp))).2
      have hbound : canonicalBound r (2 * m) ≤ X.card := by
        simpa [uniformRamseyBound, canonicalBound] using hX
      obtain ⟨ps, hpslen, hpscan, hpsX⟩ := chain (2 * m) X hbound c
      have htrue_or_false :
          m ≤ (ps.filter fun p => p.2).length ∨
            m ≤ (ps.filter fun p => !p.2).length := by
        have hpartition := ps.length_eq_length_filter_add (fun p => p.2)
        rw [hpslen] at hpartition
        omega
      rcases htrue_or_false with hmany | hmany
      · let qs := ps.filter fun p => p.2
        have hqscan : IsCanonicalChain r c qs := by
          simpa [qs] using hpscan.filter_snd true
        have hqsnd : ∀ p ∈ qs, p.2 = true := by
          intro p hp
          change p ∈ ps.filter (fun p => p.2) at hp
          exact (List.mem_filter.mp hp).2
        have hqnodup := hqscan.fst_nodup
        have hqcard : (qs.map Prod.fst).toFinset.card = qs.length := by
          rw [List.toFinset_card_of_nodup hqnodup]
          simp
        have hmq : m ≤ (qs.map Prod.fst).toFinset.card := by
          rw [hqcard]
          simpa [qs] using hmany
        obtain ⟨H, hHq, hHcard⟩ := Finset.exists_subset_card_eq hmq
        refine ⟨H, ?_, hHcard, true, ?_⟩
        · intro x hx
          have hxq : x ∈ (qs.map Prod.fst).toFinset := hHq hx
          simp only [List.mem_toFinset, List.mem_map] at hxq
          obtain ⟨p, hpq, rfl⟩ := hxq
          apply hpsX p
          change p ∈ ps.filter (fun p => p.2) at hpq
          exact (List.mem_filter.mp hpq).1
        · intro A hAH hAcard
          exact hqscan.monochromatic_of_constant_snd true hqsnd A (hAH.trans hHq) hAcard
      · let qs := ps.filter fun p => !p.2
        have hqscan : IsCanonicalChain r c qs := by
          simpa [qs] using hpscan.filter_snd false
        have hqsnd : ∀ p ∈ qs, p.2 = false := by
          intro p hp
          change p ∈ ps.filter (fun p => !p.2) at hp
          have hp' := (List.mem_filter.mp hp).2
          simpa using hp'
        have hqnodup := hqscan.fst_nodup
        have hqcard : (qs.map Prod.fst).toFinset.card = qs.length := by
          rw [List.toFinset_card_of_nodup hqnodup]
          simp
        have hmq : m ≤ (qs.map Prod.fst).toFinset.card := by
          rw [hqcard]
          simpa [qs] using hmany
        obtain ⟨H, hHq, hHcard⟩ := Finset.exists_subset_card_eq hmq
        refine ⟨H, ?_, hHcard, false, ?_⟩
        · intro x hx
          have hxq : x ∈ (qs.map Prod.fst).toFinset := hHq hx
          simp only [List.mem_toFinset, List.mem_map] at hxq
          obtain ⟨p, hpq, rfl⟩ := hxq
          apply hpsX p
          change p ∈ ps.filter (fun p => !p.2) at hpq
          exact (List.mem_filter.mp hpq).1
        · intro A hAH hAcard
          exact hqscan.monochromatic_of_constant_snd false hqsnd A (hAH.trans hHq) hAcard

/-- Finite two-colour Ramsey theorem for `r`-uniform hypergraphs. -/
theorem finite_uniform_ramsey (r m : ℕ) :
    ∃ N : ℕ, ∀ {α : Type*} [DecidableEq α] (X : Finset α), N ≤ X.card →
      ∀ c : Finset α → Bool,
        ∃ H : Finset α, H ⊆ X ∧ H.card = m ∧ MonochromaticOn r c H := by
  exact ⟨uniformRamseyBound r m, fun X hX c => uniformRamseyBound_spec r m X hX c⟩

/-- The specialization of finite uniform Ramsey selection to triples. -/
theorem finite_triple_ramsey (m : ℕ) :
    ∃ N : ℕ, ∀ {α : Type*} [DecidableEq α] (X : Finset α), N ≤ X.card →
      ∀ c : Finset α → Bool,
        ∃ H : Finset α, H ⊆ X ∧ H.card = m ∧ MonochromaticOn 3 c H :=
  finite_uniform_ramsey 3 m

/-- The specialization of finite uniform Ramsey selection to quadruples. -/
theorem finite_quadruple_ramsey (m : ℕ) :
    ∃ N : ℕ, ∀ {α : Type*} [DecidableEq α] (X : Finset α), N ≤ X.card →
      ∀ c : Finset α → Bool,
        ∃ H : Finset α, H ⊆ X ∧ H.card = m ∧ MonochromaticOn 4 c H :=
  finite_uniform_ramsey 4 m

/-- A Ramsey threshold sequence that is pointwise at least the requested clique size. -/
def uniformRamseySequence (r m : ℕ) : ℕ := uniformRamseyBound r m + m

lemma le_uniformRamseySequence (r m : ℕ) : m ≤ uniformRamseySequence r m := by
  simp [uniformRamseySequence]

lemma tendsto_uniformRamseySequence (r : ℕ) :
    Tendsto (uniformRamseySequence r) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro b
  filter_upwards [eventually_ge_atTop b] with m hm
  exact hm.trans (le_uniformRamseySequence r m)

/-- Selection at the unbounded Ramsey threshold sequence. -/
theorem uniformRamseySequence_spec (r m : ℕ) {α : Type*} [DecidableEq α]
    (X : Finset α) (hX : uniformRamseySequence r m ≤ X.card)
    (c : Finset α → Bool) :
    ∃ H : Finset α, H ⊆ X ∧ H.card = m ∧ MonochromaticOn r c H := by
  apply uniformRamseyBound_spec r m X ?_ c
  exact (Nat.le_add_right _ _).trans hX

end Erdos651
