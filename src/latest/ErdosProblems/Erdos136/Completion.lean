/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos136.Definitions

/-!
# Deterministic completion of the partial colouring for Erdős 136

This file isolates the finite, deterministic part of the upper-bound
construction.  Old and fresh colours live in a sum, so disjointness of the
two palettes is part of the type.  The certificate below records precisely
the local consequences of the corrected edge-disjoint triangle-block
construction and of avoiding the three bad-event types on the leave.

No probability or asymptotics occur here.
-/

namespace Erdos136
namespace Completion

open Finset

attribute [local instance] Classical.propDecidable

/-- The six genuine unordered edges of the labelled complete graph `K₄`. -/
abbrev Edge4 := (⊤ : SimpleGraph (Fin 4)).edgeSet

/-- The positions on which a function takes a specified value. -/
def fiber {α : Type*} [DecidableEq α] (f : Edge4 → α) (a : α) : Finset Edge4 :=
  Finset.univ.filter fun e ↦ f e = a

@[simp] lemma mem_fiber {α : Type*} [DecidableEq α] (f : Edge4 → α) (a : α)
    (e : Edge4) : e ∈ fiber f a ↔ f e = a := by
  simp [fiber]

/-- A repeated value is witnessed by two distinct edge positions. -/
lemma two_le_card_fiber_iff {α : Type*} [DecidableEq α]
    (f : Edge4 → α) (a : α) :
    2 ≤ (fiber f a).card ↔
      ∃ e e' : Edge4, e ≠ e' ∧ f e = a ∧ f e' = a := by
  constructor
  · intro h
    have h' : 1 < (fiber f a).card := by omega
    obtain ⟨e, he, e', he', hne⟩ := Finset.one_lt_card.mp h'
    exact ⟨e, e', hne, (mem_fiber f a e).mp he,
      (mem_fiber f a e').mp he'⟩
  · rintro ⟨e, e', hne, he, he'⟩
    have h' : 1 < (fiber f a).card := Finset.one_lt_card.mpr
      ⟨e, (mem_fiber f a e).mpr he, e', (mem_fiber f a e').mpr he', hne⟩
    omega

/-- A fiber has size at most two exactly when no three pairwise-distinct
positions lie in it.  This is convenient when applying the structural
classification of three edges of `K₄`. -/
lemma card_fiber_le_two_of_no_three {α : Type*} [DecidableEq α]
    (f : Edge4 → α) (a : α)
    (h : ∀ e₁ e₂ e₃ : Edge4,
      e₁ ≠ e₂ → e₁ ≠ e₃ → e₂ ≠ e₃ →
      f e₁ = a → f e₂ = a → f e₃ = a → False) :
    (fiber f a).card ≤ 2 := by
  by_contra hcard
  have hthree : 2 < (fiber f a).card := by omega
  obtain ⟨e₁, he₁, e₂, he₂, e₃, he₃, h₁₂, h₁₃, h₂₃⟩ :=
    Finset.two_lt_card.mp hthree
  exact h e₁ e₂ e₃ h₁₂ h₁₃ h₂₃
    ((mem_fiber f a e₁).mp he₁) ((mem_fiber f a e₂).mp he₂)
    ((mem_fiber f a e₃).mp he₃)

/-- Turn an edge-level exclusion of two distinct repeated values into the
fiber uniqueness condition used by `K4Certificate`. -/
lemma repeat_unique_of_pair_exclusion {α : Type*} [DecidableEq α]
    (f : Edge4 → α)
    (h : ∀ (a b : α) (e₁ e₂ f₁ f₂ : Edge4),
      a ≠ b → e₁ ≠ e₂ → f₁ ≠ f₂ →
      f e₁ = a → f e₂ = a → f f₁ = b → f f₂ = b → False) :
    ∀ a b, 2 ≤ (fiber f a).card → 2 ≤ (fiber f b).card → a = b := by
  intro a b ha hb
  by_contra hab
  obtain ⟨e₁, e₂, he, he₁, he₂⟩ := (two_le_card_fiber_iff f a).mp ha
  obtain ⟨f₁, f₂, hf, hf₁, hf₂⟩ := (two_le_card_fiber_iff f b).mp hb
  exact h a b e₁ e₂ f₁ f₂ hab he hf he₁ he₂ hf₁ hf₂

lemma card_edge4 : Fintype.card Edge4 = 6 := by
  rw [SimpleGraph.card_edgeSet,
    SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
  norm_num [Nat.choose]

/-- If six positions have fibers of size at most two and at most one value
has a nonsingleton fiber, then at least five values occur.  This is the
finite pigeonhole calculation used by the completion lemma. -/
lemma five_le_card_image_of_fibers
    {α : Type*} [DecidableEq α] (f : Edge4 → α)
    (h₂ : ∀ a, (fiber f a).card ≤ 2)
    (huniq : ∀ a b, 2 ≤ (fiber f a).card → 2 ≤ (fiber f b).card → a = b) :
    5 ≤ (Finset.univ.image f).card := by
  classical
  let I : Finset α := Finset.univ.image f
  have hsum : ∑ a ∈ I, (fiber f a).card = 6 := by
    have h := Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset Edge4)) (t := I) (f := f)
      (fun e _ ↦ Finset.mem_image.mpr ⟨e, Finset.mem_univ e, rfl⟩)
    have h' : ∑ a ∈ I, (fiber f a).card = (Finset.univ : Finset Edge4).card := by
      simpa only [I, fiber] using h.symm
    have huniv : (Finset.univ : Finset Edge4).card = 6 := by
      exact card_edge4
    omega

  by_contra hnot
  change ¬ 5 ≤ I.card at hnot
  have hI : I.card ≤ 4 := by omega
  by_cases hex : ∃ a ∈ I, 2 ≤ (fiber f a).card
  · obtain ⟨a, haI, ha⟩ := hex
    have hpoint : ∀ b ∈ I, (fiber f b).card ≤ if b = a then 2 else 1 := by
      intro b hb
      split_ifs with hba
      · exact h₂ b
      · have : ¬ 2 ≤ (fiber f b).card := fun hb₂ ↦ hba (huniq b a hb₂ ha)
        omega
    have hbound : ∑ b ∈ I, (fiber f b).card ≤ I.card + 1 := by
      calc
        ∑ b ∈ I, (fiber f b).card ≤ ∑ b ∈ I, (if b = a then 2 else 1) :=
          Finset.sum_le_sum hpoint
        _ = I.card + 1 := by
          calc
            ∑ b ∈ I, (if b = a then 2 else 1) =
                ∑ b ∈ I, (1 + if b = a then 1 else 0) := by
              apply Finset.sum_congr rfl
              intro b _
              split_ifs <;> omega
            _ = I.card + 1 := by
              rw [Finset.sum_add_distrib]
              simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
              rw [Finset.sum_ite_eq']
              simp [haI]
    omega
  · have hpoint : ∀ a ∈ I, (fiber f a).card ≤ 1 := by
      intro a haI
      have : ¬ 2 ≤ (fiber f a).card := fun ha ↦ hex ⟨a, haI, ha⟩
      omega
    have hbound : ∑ a ∈ I, (fiber f a).card ≤ I.card := by
      calc
        ∑ a ∈ I, (fiber f a).card ≤ ∑ _a ∈ I, 1 := Finset.sum_le_sum hpoint
        _ = I.card := by simp
    omega

/-- Injectively renaming colours does not change the number of colours used
by a finite colouring. -/
lemma card_image_injective_comp
    {ι α β : Type*} [Fintype ι] [DecidableEq α] [DecidableEq β]
    (f : ι → α) (g : α → β) (hg : Function.Injective g) :
    (Finset.univ.image (fun i ↦ g (f i))).card =
      (Finset.univ.image f).card := by
  rw [show Finset.univ.image (fun i ↦ g (f i)) =
      (Finset.univ.image f).image g by
    rw [Finset.image_image]
    rfl]
  exact Finset.card_image_of_injective _ hg

/-- Combine an optional old colour and a fresh colour.  The sum type makes
the palettes definitionally disjoint. -/
def combined {Old Fresh : Type*} (old : Edge4 → Option Old)
    (fresh : Edge4 → Fresh) : Edge4 → Sum Old Fresh :=
  fun e ↦ (old e).elim (Sum.inr (fresh e)) Sum.inl

/-- A local certificate for the six edges of one `K₄`.

* `oldAtMostTwo` is (P1): one old colour class is a matching or a two-edge
  path on this four-set.
* `oldRepeatUnique` is the exact local consequence of the corrected (P0)
  edge-disjoint triangle blocks together with (P2) and (P3).
* `freshAtMostTwo` is absence of bad event A (formerly (B1)).
* `freshRepeatUnique` is absence of A and B (formerly (B1),(B2)).
* `mixedRepeatForbidden` is the triangle-block closure plus absence of A and
  C (formerly (B1),(B3)).

The last three fields are stated as their exact finite consequences, which
makes this structure suitable as the output of either a local-lemma proof
or an exhaustive finite construction.
-/
structure K4Certificate {Old Fresh : Type*}
    [DecidableEq Old] [DecidableEq Fresh]
    (old : Edge4 → Option Old) (fresh : Edge4 → Fresh) : Prop where
  oldAtMostTwo : ∀ c, (fiber old (some c)).card ≤ 2
  oldRepeatUnique :
    ∀ c d, 2 ≤ (fiber old (some c)).card →
      2 ≤ (fiber old (some d)).card → c = d
  freshAtMostTwo :
    ∀ c, (fiber (combined old fresh) (Sum.inr c)).card ≤ 2
  freshRepeatUnique :
    ∀ c d,
      2 ≤ (fiber (combined old fresh) (Sum.inr c)).card →
      2 ≤ (fiber (combined old fresh) (Sum.inr d)).card → c = d
  mixedRepeatForbidden :
    ∀ c d,
      2 ≤ (fiber old (some c)).card →
      ¬ 2 ≤ (fiber (combined old fresh) (Sum.inr d)).card

lemma fiber_combined_old {Old Fresh : Type*}
    [DecidableEq Old] [DecidableEq Fresh]
    (old : Edge4 → Option Old) (fresh : Edge4 → Fresh) (c : Old) :
    fiber (combined old fresh) (Sum.inl c) = fiber old (some c) := by
  ext e
  simp only [mem_fiber, combined]
  cases old e <;> simp

/-- The deterministic six-edge completion theorem. -/
theorem five_colors_of_certificate
    {Old Fresh : Type*} [DecidableEq Old] [DecidableEq Fresh]
    {old : Edge4 → Option Old} {fresh : Edge4 → Fresh}
    (h : K4Certificate old fresh) :
    5 ≤ (Finset.univ.image (combined old fresh)).card := by
  apply five_le_card_image_of_fibers
  · intro c
    cases c with
    | inl c => simpa [fiber_combined_old] using h.oldAtMostTwo c
    | inr c => simpa [combined] using h.freshAtMostTwo c
  · intro a b ha hb
    cases a with
    | inl a =>
        cases b with
        | inl b =>
            congr 1
            apply h.oldRepeatUnique a b
            · simpa [fiber_combined_old] using ha
            · simpa [fiber_combined_old] using hb
        | inr b =>
            exact (h.mixedRepeatForbidden a b
              (by simpa [fiber_combined_old] using ha)
              (by simpa [combined] using hb)).elim
    | inr a =>
        cases b with
        | inl b =>
            exact (h.mixedRepeatForbidden b a
              (by simpa [fiber_combined_old] using hb)
              (by simpa [combined] using ha)).elim
        | inr b =>
            congr 1
            apply h.freshRepeatUnique a b <;> simpa [combined] using ‹_›

/-- Pull an optional old colouring of `Kₙ` back to one embedded `K₄`. -/
def pullOld {n : ℕ} {Old : Type*}
    (old : SimpleGraph.TopEdgeLabeling (Fin n) (Option Old))
    (v : Fin 4 ↪ Fin n) : Edge4 → Option Old :=
  old.pullback v

/-- Pull a fresh colouring of `Kₙ` back to one embedded `K₄`. -/
def pullFresh {n : ℕ} {Fresh : Type*}
    (fresh : SimpleGraph.TopEdgeLabeling (Fin n) Fresh)
    (v : Fin 4 ↪ Fin n) : Edge4 → Fresh :=
  fresh.pullback v

/-! ## Explicit corrected triangle blocks -/

/-- A genuine edge of the complete graph on `V`. -/
abbrev Edge (V : Type*) := (⊤ : SimpleGraph V).edgeSet

/-- The edge with endpoints `x,y`, with its non-loop proof. -/
def topEdge {V : Type*} (x y : V) (hxy : x ≠ y) : Edge V :=
  ⟨s(x, y), by simpa⟩

/-- The six named edges of `K₄`, used for finite structural case splits. -/
def edge01 : Edge4 := topEdge 0 1 (by decide)
def edge02 : Edge4 := topEdge 0 2 (by decide)
def edge03 : Edge4 := topEdge 0 3 (by decide)
def edge12 : Edge4 := topEdge 1 2 (by decide)
def edge13 : Edge4 := topEdge 1 3 (by decide)
def edge23 : Edge4 := topEdge 2 3 (by decide)

/-- Exhaustive, proof-producing classification of the six genuine edges of
`K₄`.  This avoids any native evaluator in downstream finite case splits. -/
theorem edge4_cases (e : Edge4) :
    e = edge01 ∨ e = edge02 ∨ e = edge03 ∨ e = edge12 ∨
      e = edge13 ∨ e = edge23 := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ x y =>
      fin_cases x <;> fin_cases y
      all_goals simp at he
      all_goals simp_all [edge01, edge02, edge03, edge12, edge13, edge23,
        topEdge]

/-- Two edges of `K₄` are a perfect matching when they have no common
endpoint. -/
def IsMatchingPair (e f : Edge4) : Prop :=
  ¬ ∃ x : Fin 4, x ∈ e.1 ∧ x ∈ f.1

/-- The three perfect matchings of `K₄`, with both edge orders included. -/
theorem matchingPair_cases {e f : Edge4} (hef : e ≠ f) :
    IsMatchingPair e f ↔
      (e = edge01 ∧ f = edge23) ∨ (e = edge23 ∧ f = edge01) ∨
      (e = edge02 ∧ f = edge13) ∨ (e = edge13 ∧ f = edge02) ∨
      (e = edge03 ∧ f = edge12) ∨ (e = edge12 ∧ f = edge03) := by
  rcases edge4_cases e with h | h | h | h | h | h <;> subst e <;>
    rcases edge4_cases f with h | h | h | h | h | h <;> subst f <;>
    simp_all [IsMatchingPair, edge01, edge02, edge03, edge12, edge13,
      edge23, topEdge, Sym2.mem_iff]

/-- One block used by the partial colouring: the two apex edges have
`pathColor`, while the opposite edge has the distinct `mateColor`. -/
structure TriangleBlock (V Old : Type*) where
  apex : V
  left : V
  right : V
  apex_ne_left : apex ≠ left
  apex_ne_right : apex ≠ right
  left_ne_right : left ≠ right
  pathColor : Old
  mateColor : Old
  colors_ne : pathColor ≠ mateColor

namespace TriangleBlock

variable {V Old : Type*}

/-- The three unordered edges supported by a triangle block. -/
def Supports (T : TriangleBlock V Old) (e : Edge V) : Prop :=
  e.1 = s(T.apex, T.left) ∨ e.1 = s(T.apex, T.right) ∨
    e.1 = s(T.left, T.right)

/-- The colour prescribed by a block on a supported edge. -/
noncomputable def edgeColor (T : TriangleBlock V Old) (e : Edge V) : Old :=
  if e.1 = s(T.apex, T.left) ∨ e.1 = s(T.apex, T.right) then
    T.pathColor
  else T.mateColor

end TriangleBlock

/-- An explicit edge-disjoint triangle-block decomposition of an old
partial colouring.

`owner_iff_support` says both that every block owns all and only its three
triangle edges and that two distinct blocks cannot share an edge (because
`owner` is a function).  `same_old_path_same_owner` is the corrected closure
invariant omitted by the abbreviated statement of the construction.
The three mate-isolation clauses are (P2).
-/
structure TriangleBlockDecomposition (V Old Block : Type*) where
  old : SimpleGraph.TopEdgeLabeling V (Option Old)
  block : Block → TriangleBlock V Old
  owner : Edge V → Option Block
  owner_iff_support :
    ∀ e b, owner e = some b ↔ (block b).Supports e
  old_eq_owner :
    ∀ e, old e = (owner e).map fun b ↦ (block b).edgeColor e
  same_old_path_same_owner :
    ∀ (x y z : V) (hxy : x ≠ y) (hyz : y ≠ z) (_hxz : x ≠ z) (c : Old),
      old (topEdge x y hxy) = some c →
      old (topEdge y z hyz) = some c →
      owner (topEdge x y hxy) = owner (topEdge y z hyz)
  mate_isolated_at_apex :
    ∀ (b : Block) (t : V) (h : (block b).apex ≠ t),
      old (topEdge (block b).apex t h) ≠ some (block b).mateColor
  mate_isolated_at_left :
    ∀ (b : Block) (t : V) (h : (block b).left ≠ t),
      old (topEdge (block b).left t h) = some (block b).mateColor →
      t = (block b).right
  mate_isolated_at_right :
    ∀ (b : Block) (t : V) (h : (block b).right ≠ t),
      old (topEdge (block b).right t h) = some (block b).mateColor →
      t = (block b).left

/-- The functional owner makes the triangle blocks genuinely edge-disjoint:
an edge supported by two blocks forces the blocks to be equal. -/
theorem TriangleBlockDecomposition.eq_of_supports
    {V Old Block : Type*} (P : TriangleBlockDecomposition V Old Block)
    {b b' : Block} {e : Edge V}
    (hb : (P.block b).Supports e) (hb' : (P.block b').Supports e) : b = b' := by
  have h₁ : P.owner e = some b := (P.owner_iff_support e b).2 hb
  have h₂ : P.owner e = some b' := (P.owner_iff_support e b').2 hb'
  exact Option.some.inj (h₁.symm.trans h₂)

/-- The full old-colouring interface required by deterministic completion.
Besides the explicit block decomposition it records (P1), (P3), and their
finite `K₄` consequence that two distinct old colours cannot both repeat.
Keeping that consequence as a field lets the probabilistic construction
prove it once from its block data, without repeating a 36-case edge
enumeration at every use of the completion theorem. -/
structure TriangleBlockPartialGood (n : ℕ) (Old Block : Type*)
    [DecidableEq Old] extends
    TriangleBlockDecomposition (Fin n) Old Block where
  oldAtMostTwoOnK4 :
    ∀ (v : Fin 4 ↪ Fin n) (c : Old),
      (fiber (pullOld old v) (some c)).card ≤ 2
  oldRepeatUniqueOnK4 :
    ∀ (v : Fin 4 ↪ Fin n) (c d : Old),
      2 ≤ (fiber (pullOld old v) (some c)).card →
      2 ≤ (fiber (pullOld old v) (some d)).card → c = d
  oldFourCycleUsesThree :
    ∀ (a b c d : Fin n)
      (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d) (hda : d ≠ a)
      (_hac : a ≠ c) (_hbd : b ≠ d)
      (cab cbc ccd cda : Old),
      old (topEdge a b hab) = some cab →
      old (topEdge b c hbc) = some cbc →
      old (topEdge c d hcd) = some ccd →
      old (topEdge d a hda) = some cda →
      3 ≤ ({cab, cbc, ccd, cda} : Finset Old).card

/-- The exact finite consequences of avoiding the leave bad events A/B/C.

`noA` excludes a fresh colour on three leave edges; `noAB` excludes two
distinct repeated fresh colours (the alternating leave four-cycle); and
`noAC` excludes a fresh repeated matching opposite an old repeated colour.
The latter incorporates the path-closing edge supplied by the explicit
triangle-block invariant when the old repeated pair is adjacent.
-/
structure AvoidsABC {n : ℕ} {Old Fresh : Type*}
    [DecidableEq Old] [DecidableEq Fresh]
    (old : SimpleGraph.TopEdgeLabeling (Fin n) (Option Old))
    (fresh : SimpleGraph.TopEdgeLabeling (Fin n) Fresh) : Prop where
  noA : ∀ (v : Fin 4 ↪ Fin n) (c : Fresh),
    (fiber (combined (pullOld old v) (pullFresh fresh v)) (Sum.inr c)).card ≤ 2
  noAB : ∀ (v : Fin 4 ↪ Fin n) (c d : Fresh),
    2 ≤ (fiber (combined (pullOld old v) (pullFresh fresh v)) (Sum.inr c)).card →
    2 ≤ (fiber (combined (pullOld old v) (pullFresh fresh v)) (Sum.inr d)).card →
    c = d
  noAC : ∀ (v : Fin 4 ↪ Fin n) (c : Old) (d : Fresh),
    2 ≤ (fiber (pullOld old v) (some c)).card →
    ¬ 2 ≤ (fiber (combined (pullOld old v) (pullFresh fresh v)) (Sum.inr d)).card

/-- Combine an old partial edge colouring and a colouring of its leave into
a genuine complete-graph edge colouring with an explicitly disjoint sum
palette. -/
def completeLabeling {n : ℕ} {Old Fresh : Type*}
    (old : SimpleGraph.TopEdgeLabeling (Fin n) (Option Old))
    (fresh : SimpleGraph.TopEdgeLabeling (Fin n) Fresh) :
    SimpleGraph.TopEdgeLabeling (Fin n) (Sum Old Fresh) :=
  fun e ↦ (old e).elim (Sum.inr (fresh e)) Sum.inl

lemma pullback_completeLabeling {n : ℕ} {Old Fresh : Type*}
    (old : SimpleGraph.TopEdgeLabeling (Fin n) (Option Old))
    (fresh : SimpleGraph.TopEdgeLabeling (Fin n) Fresh)
    (v : Fin 4 ↪ Fin n) :
    (completeLabeling old fresh).pullback v =
      combined (pullOld old v) (pullFresh fresh v) := by
  rfl

/-- A global deterministic certificate: each embedded `K₄` satisfies the
finite triangle-block/bad-event certificate. -/
def CompletionCertificate {n : ℕ} {Old Fresh : Type*}
    [DecidableEq Old] [DecidableEq Fresh]
    (old : SimpleGraph.TopEdgeLabeling (Fin n) (Option Old))
    (fresh : SimpleGraph.TopEdgeLabeling (Fin n) Fresh) : Prop :=
  ∀ v : Fin 4 ↪ Fin n, K4Certificate (pullOld old v) (pullFresh fresh v)

/-- Package the old triangle-block facts and absence of A/B/C into the
six-edge certificate used by `five_colors_of_certificate`. -/
theorem completionCertificate_of_triangleBlocks
    {n : ℕ} {Old Fresh Block : Type*}
    [DecidableEq Old] [DecidableEq Fresh]
    (P : TriangleBlockPartialGood n Old Block)
    (fresh : SimpleGraph.TopEdgeLabeling (Fin n) Fresh)
    (hABC : AvoidsABC P.old fresh) :
    CompletionCertificate P.old fresh := by
  intro v
  exact
    { oldAtMostTwo := P.oldAtMostTwoOnK4 v
      oldRepeatUnique := P.oldRepeatUniqueOnK4 v
      freshAtMostTwo := hABC.noA v
      freshRepeatUnique := hABC.noAB v
      mixedRepeatForbidden := hABC.noAC v }

/-- Generic `TopEdgeLabeling` form of deterministic completion. -/
theorem completeLabeling_has_five_colors {n : ℕ} {Old Fresh : Type*}
    [DecidableEq Old] [DecidableEq Fresh]
    (old : SimpleGraph.TopEdgeLabeling (Fin n) (Option Old))
    (fresh : SimpleGraph.TopEdgeLabeling (Fin n) Fresh)
    (h : CompletionCertificate old fresh) :
    ∀ v : Fin 4 ↪ Fin n,
      5 ≤ (Finset.univ.image ((completeLabeling old fresh).pullback v)).card := by
  intro v
  rw [pullback_completeLabeling]
  exact five_colors_of_certificate (h v)

/-- Adapter to the exact public predicate in `Definitions.lean`. -/
theorem completeFinLabeling_is45 {n oldK freshK : ℕ}
    (old : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin oldK)))
    (fresh : SimpleGraph.TopEdgeLabeling (Fin n) (Fin freshK))
    (h : CompletionCertificate old fresh) :
    Is45Coloring ((completeLabeling old fresh).compRight finSumFinEquiv) := by
  intro v
  have hv := completeLabeling_has_five_colors old fresh h v
  change 5 ≤ (Finset.univ.image (fun e : Edge4 ↦
    finSumFinEquiv (combined (pullOld old v) (pullFresh fresh v) e))).card
  rw [card_image_injective_comp _ _ finSumFinEquiv.injective]
  simpa only [← pullback_completeLabeling] using hv

/-- End-to-end deterministic completion from the explicit corrected
triangle blocks and the A/B/C avoidance certificate. -/
theorem completeTriangleBlocksFin_is45 {n oldK freshK : ℕ} {Block : Type*}
    (P : TriangleBlockPartialGood n (Fin oldK) Block)
    (fresh : SimpleGraph.TopEdgeLabeling (Fin n) (Fin freshK))
    (hABC : AvoidsABC P.old fresh) :
    Is45Coloring ((completeLabeling P.old fresh).compRight finSumFinEquiv) := by
  exact completeFinLabeling_is45 P.old fresh
    (completionCertificate_of_triangleBlocks P fresh hABC)

end Completion
end Erdos136
