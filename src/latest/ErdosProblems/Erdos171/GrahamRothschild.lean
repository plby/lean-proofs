/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos171.SubspaceOps

/-!
# The line case of the finite Graham--Rothschild theorem

This file proves the precise finite Ramsey theorem for combinatorial lines used
by Dodos--Kanellopoulos--Tyros in their proof of density Hales--Jewett.  The
proof is the standard repeated-Hales--Jewett fusion (Shelah's ``first moving
block'' proof): after passing to a block subspace, the color of a line depends
only on its first moving block.  A final pigeonhole argument makes those block
colors equal.

Only the line case is stated.  A superficially stronger statement obtained by
coloring Mathlib's *labelled* higher-dimensional `Subspace`s is false without
an ordering convention: in dimension two one may color a parameter word by
which labelled variable occurs first.  Lines have only one variable, so this
obstruction is absent here.
-/

namespace Erdos171

open Function
open Combinatorics

namespace GrahamRothschild

universe u v w x

variable {α : Type u} {P : Type v} {B : Type w} {I : Type x}

/-- A line already moves in the old (prefix) coordinates. -/
def PrefixMoving (q : Line α (P ⊕ Fin m)) : Prop :=
  ∃ p : P, q.idxFun (Sum.inl p) = none

/-- Two lines have the same first moving coordinate among their `Fin m` tail
coordinates.  This definition remains useful when either line also moves in
the prefix. -/
def SameFirstTail (q r : Line α (P ⊕ Fin m)) : Prop :=
  ∃ i : Fin m,
    q.idxFun (Sum.inr i) = none ∧
      r.idxFun (Sum.inr i) = none ∧
      ∀ j : Fin m, j < i →
        q.idxFun (Sum.inr j) ≠ none ∧ r.idxFun (Sum.inr j) ≠ none

/-- The fusion invariant.  Lines agreeing on the prefix have equal colors if
the prefix already moves, or if their first moving tail block is the same. -/
def IsFirstBlockCanonical (C : Line α I → Bool)
    (U : Subspace (P ⊕ Fin m) α I) : Prop :=
  ∀ q r : Line α (P ⊕ Fin m),
    (∀ p : P, q.idxFun (Sum.inl p) = r.idxFun (Sum.inl p)) →
    (PrefixMoving q ∨ SameFirstTail q r) →
    C (U.lineMap q) = C (U.lineMap r)

/-- Replace the current block by a word over letters and pointers into the
prefix.  The current block is the `0` coordinate of `Fin (m+1)`; all later
blocks are shifted down by one. -/
def specializeIdx (x : B → α ⊕ P) (q : Line α (P ⊕ Fin (m + 1))) :
    ((P ⊕ B) ⊕ Fin m) → Option α
  | Sum.inl (Sum.inl p) => q.idxFun (Sum.inl p)
  | Sum.inl (Sum.inr b) => (x b).elim some (fun p => q.idxFun (Sum.inl p))
  | Sum.inr j => q.idxFun (Sum.inr j.succ)

/-- The patterns for which specializing the current block still leaves a
proper line.  The only excluded case is when the current block is the unique
source of a wildcard before all later blocks. -/
def Specializable (q : Line α (P ⊕ Fin (m + 1))) : Prop :=
  PrefixMoving q ∨ q.idxFun (Sum.inr 0) ≠ none

theorem specializeIdx_proper (x : B → α ⊕ P)
    (q : Line α (P ⊕ Fin (m + 1))) (hq : Specializable q) :
    ∃ i, specializeIdx x q i = none := by
  rcases hq with hp | h0
  · obtain ⟨p, hp⟩ := hp
    exact ⟨Sum.inl (Sum.inl p), hp⟩
  · obtain ⟨i, hi⟩ := q.proper
    cases i with
    | inl p => exact ⟨Sum.inl (Sum.inl p), hi⟩
    | inr i =>
      cases i using Fin.cases with
      | zero => exact (h0 hi).elim
      | succ j => exact ⟨Sum.inr j, hi⟩

/-- Specialization as a proper line. -/
def specializeLine (x : B → α ⊕ P) (q : Line α (P ⊕ Fin (m + 1)))
    (hq : Specializable q) : Line α ((P ⊕ B) ⊕ Fin m) where
  idxFun := specializeIdx x q
  proper := specializeIdx_proper x q hq

/-- Compress a Hales--Jewett line in the current block to one new parameter
coordinate. -/
def compressSubspace (h : Line (α ⊕ P) B) :
    Subspace (P ⊕ Fin (m + 1)) α ((P ⊕ B) ⊕ Fin m) where
  idxFun
    | Sum.inl (Sum.inl p) => Sum.inr (Sum.inl p)
    | Sum.inl (Sum.inr b) =>
        (h.idxFun b).elim (Sum.inr (Sum.inr 0)) (Sum.elim Sum.inl (Sum.inr ∘ Sum.inl))
    | Sum.inr j => Sum.inr (Sum.inr j.succ)
  proper
    | Sum.inl p => ⟨Sum.inl (Sum.inl p), rfl⟩
    | Sum.inr i => by
        cases i using Fin.cases with
        | zero =>
            obtain ⟨b, hb⟩ := h.proper
            exact ⟨Sum.inl (Sum.inr b), by simp [hb]⟩
        | succ j => exact ⟨Sum.inr j, rfl⟩

theorem compress_lineMap_eq_specialize_inl
    (h : Line (α ⊕ P) B) (q : Line α (P ⊕ Fin (m + 1)))
    (hq : Specializable q) (a : α)
    (h0 : q.idxFun (Sum.inr 0) = some a) :
    (compressSubspace (m := m) h).lineMap q =
      specializeLine (h (Sum.inl a)) q hq := by
  ext i
  cases i with
  | inl i =>
    cases i with
    | inl p => rfl
    | inr b =>
      cases hb : h.idxFun b with
      | none => simp [compressSubspace, Subspace.lineMap, specializeLine, specializeIdx, hb, h0]
      | some z =>
        cases z <;>
          simp [compressSubspace, Subspace.lineMap, specializeLine, specializeIdx, hb,
            Line.coe_apply]
  | inr j => rfl

theorem compress_lineMap_eq_specialize_inr
    (h : Line (α ⊕ P) B) (q : Line α (P ⊕ Fin (m + 1)))
    (hq : Specializable q) (p : P)
    (h0 : q.idxFun (Sum.inr 0) = q.idxFun (Sum.inl p)) :
    (compressSubspace (m := m) h).lineMap q = specializeLine (h (Sum.inr p)) q hq := by
  ext i
  cases i with
  | inl i =>
    cases i with
    | inl p' => rfl
    | inr b =>
      cases hb : h.idxFun b with
      | none => simp [compressSubspace, Subspace.lineMap, specializeLine, specializeIdx, hb, h0]
      | some z =>
        cases z <;>
          simp [compressSubspace, Subspace.lineMap, specializeLine, specializeIdx, hb,
            Line.coe_apply]
  | inr j => rfl

theorem specialize_prefix_eq (x : B → α ⊕ P)
    (q r : Line α (P ⊕ Fin (m + 1)))
    (hq : Specializable q) (hr : Specializable r)
    (hpre : ∀ p : P, q.idxFun (Sum.inl p) = r.idxFun (Sum.inl p)) :
    ∀ s : P ⊕ B,
      (specializeLine x q hq).idxFun (Sum.inl s) =
        (specializeLine x r hr).idxFun (Sum.inl s) := by
  intro s
  cases s with
  | inl p => exact hpre p
  | inr b =>
      cases hx : x b with
      | inl a => simp [specializeLine, specializeIdx, hx]
      | inr p => simpa [specializeLine, specializeIdx, hx] using hpre p

theorem specialize_prefixMoving (x : B → α ⊕ P)
    (q : Line α (P ⊕ Fin (m + 1))) (hq : Specializable q)
    (hp : PrefixMoving q) :
    PrefixMoving (P := P ⊕ B) (m := m) (specializeLine x q hq) := by
  obtain ⟨p, hp⟩ := hp
  exact ⟨Sum.inl p, hp⟩

theorem specialize_sameFirstTail_succ (x : B → α ⊕ P)
    (q r : Line α (P ⊕ Fin (m + 1)))
    (hq : Specializable q) (hr : Specializable r) (i : Fin m)
    (hqi : q.idxFun (Sum.inr i.succ) = none)
    (hri : r.idxFun (Sum.inr i.succ) = none)
    (hmin : ∀ j : Fin (m + 1), j < i.succ →
      q.idxFun (Sum.inr j) ≠ none ∧ r.idxFun (Sum.inr j) ≠ none) :
    SameFirstTail (P := P ⊕ B) (specializeLine x q hq) (specializeLine x r hr) := by
  refine ⟨i, hqi, hri, ?_⟩
  intro j hj
  exact hmin j.succ (by simpa using hj)

theorem compress_prefix_eq_of_current_none
    (h : Line (α ⊕ P) B) (q r : Line α (P ⊕ Fin (m + 1)))
    (hpre : ∀ p : P, q.idxFun (Sum.inl p) = r.idxFun (Sum.inl p))
    (hq0 : q.idxFun (Sum.inr 0) = none)
    (hr0 : r.idxFun (Sum.inr 0) = none) :
    ∀ s : P ⊕ B,
      ((compressSubspace (m := m) h).lineMap q).idxFun (Sum.inl s) =
        ((compressSubspace (m := m) h).lineMap r).idxFun (Sum.inl s) := by
  intro s
  cases s with
  | inl p => exact hpre p
  | inr b =>
      cases hb : h.idxFun b with
      | none => simp [compressSubspace, Subspace.lineMap, hb, hq0, hr0]
      | some z =>
          cases z with
          | inl a => simp [compressSubspace, Subspace.lineMap, hb]
          | inr p => simpa [compressSubspace, Subspace.lineMap, hb] using hpre p

theorem compress_prefixMoving_of_current_none
    (h : Line (α ⊕ P) B) (q : Line α (P ⊕ Fin (m + 1)))
    (hq0 : q.idxFun (Sum.inr 0) = none) :
    PrefixMoving (P := P ⊕ B) (m := m) ((compressSubspace (m := m) h).lineMap q) := by
  obtain ⟨b, hb⟩ := h.proper
  refine ⟨Sum.inr b, ?_⟩
  simp [compressSubspace, Subspace.lineMap, hb, hq0]

/-- Repeated Hales--Jewett fusion.  The returned subspace is canonical for the
first moving tail block, relative to an arbitrary finite prefix type `P`. -/
theorem exists_firstBlockCanonical (α : Type) [Finite α] (P : Type) [Finite P] :
    ∀ m : ℕ, ∃ (I : Type) (_ : Fintype I),
      ∀ C : Line α I → Bool,
        ∃ U : Subspace (P ⊕ Fin m) α I, IsFirstBlockCanonical C U := by
  classical
  let := Fintype.ofFinite α
  let := Fintype.ofFinite P
  intro m
  induction m generalizing P with
  | zero =>
      refine ⟨P ⊕ Fin 0, inferInstance, fun C => ⟨default, ?_⟩⟩
      intro q r hpre _
      have hqr : q = r := by
        apply Line.ext
        funext i
        cases i with
        | inl p => exact hpre p
        | inr i => exact Fin.elim0 i
      subst r
      rfl
  | succ m ih =>
      let pattern := {q : Line α (P ⊕ Fin (m + 1)) // Specializable q}
      obtain ⟨B, instB, hB⟩ :=
        Line.exists_mono_in_high_dimension (α ⊕ P) (pattern → Bool)
      let : Fintype B := instB
      obtain ⟨I, instI, hI⟩ := ih (P := P ⊕ B)
      let : Fintype I := instI
      refine ⟨I, instI, fun C => ?_⟩
      obtain ⟨V, hV⟩ := hI C
      let D : (B → α ⊕ P) → pattern → Bool := fun x q =>
        C (V.lineMap (specializeLine x q.1 q.2))
      obtain ⟨h, c, hc⟩ := hB D
      let Q : Subspace (P ⊕ Fin (m + 1)) α ((P ⊕ B) ⊕ Fin m) :=
        compressSubspace h
      refine ⟨V.comp Q, ?_⟩
      intro q r hpre hkey
      have hcolors (z z' : α ⊕ P) : D (h z) = D (h z') :=
        (hc z).trans (hc z').symm
      rcases hkey with hp | htail
      · obtain ⟨p, hp⟩ := hp
        have hrp : r.idxFun (Sum.inl p) = none := by rw [← hpre p]; exact hp
        have hsq : Specializable q := Or.inl ⟨p, hp⟩
        have hsr : Specializable r := Or.inl ⟨p, hrp⟩
        cases hq0 : q.idxFun (Sum.inr 0) with
        | none =>
          cases hr0 : r.idxFun (Sum.inr 0) with
          | none =>
            have hqcomp := compress_lineMap_eq_specialize_inr
              (m := m) h q hsq p (by rw [hq0, hp])
            have hrcomp := compress_lineMap_eq_specialize_inr
              (m := m) h r hsr p (by rw [hr0, hrp])
            calc
              C ((V.comp Q).lineMap q) =
                  C (V.lineMap (specializeLine (h (Sum.inr p)) q hsq)) := by
                    rw [Subspace.lineMap_comp, show Q = compressSubspace h from rfl, hqcomp]
              _ = C (V.lineMap (specializeLine (h (Sum.inr p)) r hsr)) := by
                    apply hV
                    · exact specialize_prefix_eq _ q r hsq hsr hpre
                    · exact Or.inl (specialize_prefixMoving _ q hsq ⟨p, hp⟩)
              _ = C ((V.comp Q).lineMap r) := by
                    rw [Subspace.lineMap_comp, show Q = compressSubspace h from rfl, hrcomp]
          | some b =>
            have hqcomp := compress_lineMap_eq_specialize_inr
              (m := m) h q hsq p (by rw [hq0, hp])
            have hrcomp := compress_lineMap_eq_specialize_inl
              (m := m) h r hsr b hr0
            have hmono := congrFun (hcolors (Sum.inr p) (Sum.inl b)) ⟨q, hsq⟩
            calc
              C ((V.comp Q).lineMap q) =
                  C (V.lineMap (specializeLine (h (Sum.inr p)) q hsq)) := by
                    rw [Subspace.lineMap_comp, show Q = compressSubspace h from rfl, hqcomp]
              _ = C (V.lineMap (specializeLine (h (Sum.inl b)) q hsq)) := hmono
              _ = C (V.lineMap (specializeLine (h (Sum.inl b)) r hsr)) := by
                    apply hV
                    · exact specialize_prefix_eq _ q r hsq hsr hpre
                    · exact Or.inl (specialize_prefixMoving _ q hsq ⟨p, hp⟩)
              _ = C ((V.comp Q).lineMap r) := by
                    rw [Subspace.lineMap_comp, show Q = compressSubspace h from rfl, hrcomp]
        | some a =>
          cases hr0 : r.idxFun (Sum.inr 0) with
          | none =>
            have hqcomp := compress_lineMap_eq_specialize_inl
              (m := m) h q hsq a hq0
            have hrcomp := compress_lineMap_eq_specialize_inr
              (m := m) h r hsr p (by rw [hr0, hrp])
            have hmono := congrFun (hcolors (Sum.inl a) (Sum.inr p)) ⟨q, hsq⟩
            calc
              C ((V.comp Q).lineMap q) =
                  C (V.lineMap (specializeLine (h (Sum.inl a)) q hsq)) := by
                    rw [Subspace.lineMap_comp, show Q = compressSubspace h from rfl, hqcomp]
              _ = C (V.lineMap (specializeLine (h (Sum.inr p)) q hsq)) := hmono
              _ = C (V.lineMap (specializeLine (h (Sum.inr p)) r hsr)) := by
                    apply hV
                    · exact specialize_prefix_eq _ q r hsq hsr hpre
                    · exact Or.inl (specialize_prefixMoving _ q hsq ⟨p, hp⟩)
              _ = C ((V.comp Q).lineMap r) := by
                    rw [Subspace.lineMap_comp, show Q = compressSubspace h from rfl, hrcomp]
          | some b =>
            have hqcomp := compress_lineMap_eq_specialize_inl
              (m := m) h q hsq a hq0
            have hrcomp := compress_lineMap_eq_specialize_inl
              (m := m) h r hsr b hr0
            have hmono := congrFun (hcolors (Sum.inl a) (Sum.inl b)) ⟨q, hsq⟩
            calc
              C ((V.comp Q).lineMap q) =
                  C (V.lineMap (specializeLine (h (Sum.inl a)) q hsq)) := by
                    rw [Subspace.lineMap_comp, show Q = compressSubspace h from rfl, hqcomp]
              _ = C (V.lineMap (specializeLine (h (Sum.inl b)) q hsq)) := hmono
              _ = C (V.lineMap (specializeLine (h (Sum.inl b)) r hsr)) := by
                    apply hV
                    · exact specialize_prefix_eq _ q r hsq hsr hpre
                    · exact Or.inl (specialize_prefixMoving _ q hsq ⟨p, hp⟩)
              _ = C ((V.comp Q).lineMap r) := by
                    rw [Subspace.lineMap_comp, show Q = compressSubspace h from rfl, hrcomp]
      · obtain ⟨i, hqi, hri, hmin⟩ := htail
        cases i using Fin.cases with
        | zero =>
          have hpref := compress_prefix_eq_of_current_none h q r hpre hqi hri
          have hmov := compress_prefixMoving_of_current_none h q hqi
          rw [Subspace.lineMap_comp, Subspace.lineMap_comp]
          exact hV _ _ hpref (Or.inl hmov)
        | succ i =>
          have hq0ne := (hmin 0 (by simp)).1
          have hr0ne := (hmin 0 (by simp)).2
          cases hq0 : q.idxFun (Sum.inr 0) with
          | none => exact (hq0ne hq0).elim
          | some a =>
            cases hr0 : r.idxFun (Sum.inr 0) with
            | none => exact (hr0ne hr0).elim
            | some b =>
              have hsq : Specializable q := Or.inr (by simp [hq0])
              have hsr : Specializable r := Or.inr (by simp [hr0])
              have hqcomp := compress_lineMap_eq_specialize_inl
                (m := m) h q hsq a hq0
              have hrcomp := compress_lineMap_eq_specialize_inl
                (m := m) h r hsr b hr0
              have hmono := congrFun (hcolors (Sum.inl a) (Sum.inl b)) ⟨q, hsq⟩
              calc
                C ((V.comp Q).lineMap q) =
                    C (V.lineMap (specializeLine (h (Sum.inl a)) q hsq)) := by
                      rw [Subspace.lineMap_comp, show Q = compressSubspace h from rfl, hqcomp]
                _ = C (V.lineMap (specializeLine (h (Sum.inl b)) q hsq)) := hmono
                _ = C (V.lineMap (specializeLine (h (Sum.inl b)) r hsr)) := by
                      apply hV
                      · exact specialize_prefix_eq _ q r hsq hsr hpre
                      · exact Or.inr (specialize_sameFirstTail_succ _ q r hsq hsr i hqi hri hmin)
                _ = C ((V.comp Q).lineMap r) := by
                      rw [Subspace.lineMap_comp, show Q = compressSubspace h from rfl, hrcomp]

/-- A line moving in exactly one tail coordinate. -/
def singletonTailLine (a₀ : α) (i : Fin m) : Line α (Empty ⊕ Fin m) where
  idxFun
    | Sum.inl e => nomatch e
    | Sum.inr j => if j = i then none else some a₀
  proper := ⟨Sum.inr i, by simp⟩

/-- Moving tail coordinates of a line with empty prefix. -/
def tailMoving (q : Line α (Empty ⊕ Fin m)) : Finset (Fin m) :=
  Finset.univ.filter fun i => q.idxFun (Sum.inr i) = none

theorem tailMoving_nonempty (q : Line α (Empty ⊕ Fin m)) :
    (tailMoving q).Nonempty := by
  obtain ⟨i, hi⟩ := q.proper
  cases i with
  | inl e => exact Empty.elim e
  | inr i => exact ⟨i, by simpa [tailMoving] using hi⟩

noncomputable def firstTailMoving (q : Line α (Empty ⊕ Fin m)) : Fin m :=
  (tailMoving q).min' (tailMoving_nonempty q)

theorem firstTailMoving_mem (q : Line α (Empty ⊕ Fin m)) :
    firstTailMoving q ∈ tailMoving q :=
  Finset.min'_mem _ _

theorem firstTailMoving_idxFun (q : Line α (Empty ⊕ Fin m)) :
    q.idxFun (Sum.inr (firstTailMoving q)) = none := by
  simpa [tailMoving] using firstTailMoving_mem q

theorem firstTailMoving_min (q : Line α (Empty ⊕ Fin m)) (j : Fin m)
    (hj : j < firstTailMoving q) : q.idxFun (Sum.inr j) ≠ none := by
  intro hnone
  have hjmem : j ∈ tailMoving q := by simpa [tailMoving, hnone]
  exact (not_le_of_gt hj) (Finset.min'_le _ _ hjmem)

theorem sameFirstTail_singleton (a₀ : α) (q : Line α (Empty ⊕ Fin m)) :
    SameFirstTail q (singletonTailLine a₀ (firstTailMoving q)) := by
  refine ⟨firstTailMoving q, firstTailMoving_idxFun q, by simp [singletonTailLine], ?_⟩
  intro j hj
  exact ⟨firstTailMoving_min q j hj, by simp [singletonTailLine, ne_of_lt hj]⟩

/-- Restrict a finite parameter cube to the coordinates in `s`, using the
increasing enumeration of `s` as the new parameter order. -/
noncomputable def restrictToFinset (a₀ : α) (s : Finset (Fin M))
    {d : ℕ} (hs : s.card = d) : Subspace (Fin d) α (Empty ⊕ Fin M) where
  idxFun
    | Sum.inl e => nomatch e
    | Sum.inr i => if hi : i ∈ s then
        Sum.inr ((s.orderIsoOfFin hs).symm ⟨i, hi⟩)
      else Sum.inl a₀
  proper j := by
    let i : Fin M := s.orderEmbOfFin hs j
    have hi : i ∈ s := s.orderEmbOfFin_mem hs j
    refine ⟨Sum.inr i, ?_⟩
    change (if hi' : i ∈ s then
      Sum.inr ((s.orderIsoOfFin hs).symm ⟨i, hi'⟩) else Sum.inl a₀) = Sum.inr j
    rw [dif_pos hi]
    have hsub : (⟨i, hi⟩ : s) = s.orderIsoOfFin hs j := by
      apply Subtype.ext
      rfl
    rw [hsub, (s.orderIsoOfFin hs).symm_apply_apply]

theorem restrictToFinset_moving_mem (a₀ : α) (s : Finset (Fin M))
    {d : ℕ} (hs : s.card = d) (q : Line α (Fin d)) (i : Fin M)
    (hi : ((restrictToFinset a₀ s hs).lineMap q).idxFun (Sum.inr i) = none) :
    i ∈ s := by
  by_contra his
  simp [restrictToFinset, Subspace.lineMap, his] at hi

/-- Boolean pigeonhole in the exact form used after fusion. -/
theorem exists_bool_homogeneous_finset (d : ℕ) (f : Fin (2 * d) → Bool) :
    ∃ (s : Finset (Fin (2 * d))) (c : Bool),
      s.card = d ∧ ∀ i ∈ s, f i = c := by
  classical
  let st : Finset (Fin (2 * d)) := Finset.univ.filter fun i => f i = true
  let sf : Finset (Fin (2 * d)) := Finset.univ.filter fun i => f i ≠ true
  have hsum : st.card + sf.card = 2 * d := by
    simpa [st, sf] using
      (Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (2 * d))))
        (fun i => f i = true))
  by_cases ht : d ≤ st.card
  · obtain ⟨s, hsst, hcard⟩ := Finset.exists_subset_card_eq ht
    exact ⟨s, true, hcard, fun i hi => (Finset.mem_filter.mp (hsst hi)).2⟩
  · have hf : d ≤ sf.card := by omega
    obtain ⟨s, hssf, hcard⟩ := Finset.exists_subset_card_eq hf
    refine ⟨s, false, hcard, ?_⟩
    intro i hi
    have hne : f i ≠ true := (Finset.mem_filter.mp (hssf hi)).2
    cases h : f i <;> simp_all

/-- The finite line-color Graham--Rothschild theorem, with an arbitrary finite
ambient coordinate type. -/
theorem exists_mono_lines_fintype (α : Type) [Finite α] [Nonempty α] (d : ℕ) :
    ∃ (I : Type) (_ : Fintype I), ∀ C : Line α I → Bool,
      ∃ U : Subspace (Fin d) α I, ∃ c : Bool,
        ∀ q : Line α (Fin d), C (U.lineMap q) = c := by
  classical
  obtain ⟨I, instI, hI⟩ := exists_firstBlockCanonical α Empty (2 * d)
  refine ⟨I, instI, fun C => ?_⟩
  let : Fintype I := instI
  obtain ⟨V, hV⟩ := hI C
  let a₀ : α := Classical.arbitrary α
  let blockColor : Fin (2 * d) → Bool := fun i =>
    C (V.lineMap (singletonTailLine a₀ i))
  obtain ⟨s, c, hs, hsc⟩ := exists_bool_homogeneous_finset d blockColor
  let Q : Subspace (Fin d) α (Empty ⊕ Fin (2 * d)) := restrictToFinset a₀ s hs
  refine ⟨V.comp Q, c, ?_⟩
  intro q
  let r : Line α (Empty ⊕ Fin (2 * d)) := Q.lineMap q
  let i : Fin (2 * d) := firstTailMoving r
  have hi0 : r.idxFun (Sum.inr i) = none := firstTailMoving_idxFun r
  have his : i ∈ s := restrictToFinset_moving_mem a₀ s hs q i hi0
  have hcanon : C (V.lineMap r) = C (V.lineMap (singletonTailLine a₀ i)) := by
    apply hV
    · intro e
      exact Empty.elim e
    · exact Or.inr (sameFirstTail_singleton a₀ r)
  calc
    C ((V.comp Q).lineMap q) = C (V.lineMap r) := by
      rw [Subspace.lineMap_comp]
    _ = C (V.lineMap (singletonTailLine a₀ i)) := hcanon
    _ = blockColor i := rfl
    _ = c := hsc i his

/-- Reindex the coordinates of a line. -/
def lineReindex (e : I ≃ J) (q : Line α I) : Line α J where
  idxFun j := q.idxFun (e.symm j)
  proper := by
    obtain ⟨i, hi⟩ := q.proper
    exact ⟨e i, by simpa⟩

@[simp] theorem reindex_lineMap {η α I J : Type*}
    (e : I ≃ J) (U : Subspace η α I) (q : Line α η) :
    (U.reindex (Equiv.refl _) (Equiv.refl _) e).lineMap q =
      lineReindex e (U.lineMap q) := by
  apply Line.ext
  funext j
  cases h : U.idxFun (e.symm j) <;>
    simp [Subspace.reindex, Subspace.lineMap, lineReindex, h]

/-- Fin-indexed form of finite Graham--Rothschild for line colorings. -/
theorem exists_mono_lines_fin (α : Type) [Finite α] [Nonempty α] (d : ℕ) :
    ∃ n : ℕ, ∀ C : Line α (Fin n) → Bool,
      ∃ U : Subspace (Fin d) α (Fin n), ∃ c : Bool,
        ∀ q : Line α (Fin d), C (U.lineMap q) = c := by
  classical
  obtain ⟨I, instI, hI⟩ := exists_mono_lines_fintype α d
  let : Fintype I := instI
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  refine ⟨Fintype.card I, fun C => ?_⟩
  let D : Line α I → Bool := fun q => C (lineReindex e q)
  obtain ⟨U, c, hU⟩ := hI D
  refine ⟨U.reindex (Equiv.refl _) (Equiv.refl _) e, c, ?_⟩
  intro q
  rw [reindex_lineMap]
  exact hU q

/-- Embed the first `n` coordinates as an `n`-dimensional subspace of a
larger cube, fixing all remaining coordinates. -/
def initialSubspace (a₀ : α) {n N : ℕ} (h : n ≤ N) :
    Subspace (Fin n) α (Fin N) where
  idxFun i := if hi : i.val < n then Sum.inr ⟨i.val, hi⟩ else Sum.inl a₀
  proper j := by
    let i : Fin N := ⟨j.val, j.isLt.trans_le h⟩
    refine ⟨i, ?_⟩
    change (if hi : i.val < n then Sum.inr ⟨i.val, hi⟩ else Sum.inl a₀) = Sum.inr j
    rw [dif_pos j.isLt]

/-- Threshold form: every sufficiently high finite cube has the line-color
Graham--Rothschild property. -/
theorem exists_mono_lines_fin_of_ge (α : Type) [Finite α] [Nonempty α] (d : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ C : Line α (Fin n) → Bool,
      ∃ U : Subspace (Fin d) α (Fin n), ∃ c : Bool,
        ∀ q : Line α (Fin d), C (U.lineMap q) = c := by
  classical
  obtain ⟨N, hN⟩ := exists_mono_lines_fin α d
  refine ⟨N, ?_⟩
  intro n hn C
  let a₀ : α := Classical.arbitrary α
  let E : Subspace (Fin N) α (Fin n) := initialSubspace a₀ hn
  let D : Line α (Fin N) → Bool := fun q => C (E.lineMap q)
  obtain ⟨U, c, hU⟩ := hN D
  refine ⟨E.comp U, c, ?_⟩
  intro q
  rw [Subspace.lineMap_comp]
  exact hU q

/-- Set-coloring formulation matching Proposition 2 of
Dodos--Kanellopoulos--Tyros: inside every sufficiently high cube, every family
of lines has a finite-dimensional subspace whose lines all belong to the family
or all avoid it. -/
theorem exists_subspace_lines_subset_or_disjoint
    (α : Type) [Finite α] [Nonempty α] (d : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ ℒ : Set (Line α (Fin n)),
      ∃ U : Subspace (Fin d) α (Fin n),
        (∀ q : Line α (Fin d), U.lineMap q ∈ ℒ) ∨
          (∀ q : Line α (Fin d), U.lineMap q ∉ ℒ) := by
  classical
  obtain ⟨N, hN⟩ := exists_mono_lines_fin_of_ge α d
  refine ⟨N, ?_⟩
  intro n hn ℒ
  let C : Line α (Fin n) → Bool := fun q => decide (q ∈ ℒ)
  obtain ⟨U, c, hU⟩ := hN n hn C
  refine ⟨U, ?_⟩
  cases c with
  | false =>
      right
      intro q hq
      have hc := hU q
      simp [C, hq] at hc
  | true =>
      left
      intro q
      have hc := hU q
      simpa [C] using hc

end GrahamRothschild

end Erdos171
