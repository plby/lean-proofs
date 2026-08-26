import ErdosProblems.Erdos118.Reused591.LabeledCode
import ErdosProblems.Erdos118.Reused591.GamePayoff

namespace Erdos118.Reused591

/-!
# Canonical labels determined by actual coordinate cuts

The labels are computed from the literal words, not from a chosen game
outcome. Geometric admissibility means that every cut is at a leaf
strictly before its body's last leaf and strictly before the last body.
This module proves exact terminal clarity for that computed labeling.
The macro-extension construction must separately establish geometric
admissibility and the scheduling of its coarsened atomic trace.
-/

namespace Erdos591.Positive.Game.CutLabels

open Erdos591.Negative.Exact Payoff

noncomputable def body (s t : List (List ℕ)) (i : ℕ) : Finset ℕ := by
  classical
  exact ((Finset.range (s.getD i []).length).filter (fun j => LeafCut s t i j)).image
    (fun j => j + 1)

theorem mem_body (s t : List (List ℕ)) (i k : ℕ) :
    k ∈ body s t i ↔ ∃ j, LeafCut s t i j ∧ j + 1 = k := by
  classical
  simp only [body, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨j, ⟨_, hj⟩, heq⟩
    exact ⟨j, hj, heq⟩
  · rintro ⟨j, hj, heq⟩
    exact ⟨j, ⟨hj.2.1, hj⟩, heq⟩

@[simp] theorem succ_mem_body (s t : List (List ℕ)) (i j : ℕ) :
    j + 1 ∈ body s t i ↔ LeafCut s t i j := by
  rw [mem_body]
  simp

theorem body_nonempty (s t : List (List ℕ)) (i : ℕ) :
    (body s t i).Nonempty ↔ ∃ j, LeafCut s t i j := by
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨j, hj, _⟩ := (mem_body s t i k).1 hk
    exact ⟨j, hj⟩
  · rintro ⟨j, hj⟩
    exact ⟨j + 1, (succ_mem_body s t i j).2 hj⟩

noncomputable def root (s t : List (List ℕ)) : Finset ℕ := by
  classical
  exact ((Finset.range s.length).filter (fun i => (body s t i).Nonempty)).image
    (fun i => i + 1)

theorem mem_root (s t : List (List ℕ)) (k : ℕ) :
    k ∈ root s t ↔ ∃ i j, LeafCut s t i j ∧ i + 1 = k := by
  classical
  simp only [root, Finset.mem_image, Finset.mem_filter, Finset.mem_range, body_nonempty]
  constructor
  · rintro ⟨i, ⟨_, j, hij⟩, heq⟩
    exact ⟨i, j, hij, heq⟩
  · rintro ⟨i, j, hij, heq⟩
    exact ⟨i, ⟨hij.1, j, hij⟩, heq⟩

@[simp] theorem succ_mem_root (s t : List (List ℕ)) (i : ℕ) :
    i + 1 ∈ root s t ↔ ∃ j, LeafCut s t i j := by
  rw [mem_root]
  constructor
  · rintro ⟨i', j, hj, heq⟩
    have hi : i' = i := by omega
    exact ⟨j, hi ▸ hj⟩
  · rintro ⟨j, hj⟩
    exact ⟨i, j, hj, rfl⟩

theorem body_empty_of_not_selected {s t : List (List ℕ)} {i : ℕ}
    (hi : i + 1 ∉ root s t) : body s t i = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  intro hne
  exact hi ((succ_mem_root s t i).2 ((body_nonempty s t i).1 hne))

/-- These are the purely geometric facts supplied by uninterrupted
macro-extensions; no graph color or partition relation occurs here. -/
structure Admissible (s t : List (List ℕ)) : Prop where
  strict : ∀ i j, LeafCut s t i j → i + 1 < s.length ∧ j + 1 < (s.getD i []).length
  leaves : ∀ k, Cut (word s) (word t) k →
    ∃ i j, LeafCut s t i j ∧ k = leafPosition s i j

theorem root_bounds {s t : List (List ℕ)} (h : Admissible s t) :
    ∀ k ∈ root s t, 0 < k ∧ k < s.length := by
  intro k hk
  obtain ⟨i, j, hij, rfl⟩ := (mem_root s t k).1 hk
  exact ⟨Nat.zero_lt_succ i, (h.strict i j hij).1⟩

theorem body_bounds {s t : List (List ℕ)} (h : Admissible s t) (i : ℕ) :
    ∀ k ∈ body s t i, 0 < k ∧ k < (s.getD i []).length := by
  intro k hk
  obtain ⟨j, hij, rfl⟩ := (mem_body s t i k).1 hk
  exact ⟨Nat.zero_lt_succ j, (h.strict i j hij).2⟩

noncomputable def bodies (s t : List (List ℕ)) : List LabeledCode.Body :=
  s.mapIdx fun i a => (body s t i, a)

@[simp] theorem bodies_length (s t : List (List ℕ)) : (bodies s t).length = s.length := by
  simp [bodies]

@[simp] theorem erase_bodies (s t : List (List ℕ)) : LabeledCode.erase (bodies s t) = s := by
  apply List.ext_getElem
  · simp [LabeledCode.erase]
  · intro i hi hj
    simp [LabeledCode.erase, bodies]

theorem bodyLabels_getD (s t : List (List ℕ)) (i : ℕ) (hi : i < s.length) :
    ((bodies s t).map Prod.fst).getD i ∅ = body s t i := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp [bodies]

noncomputable def cursor (s t : List (List ℕ)) : LabeledWord :=
  LabeledCode.terminalCursor (root s t) (bodies s t)

@[simp] theorem cursor_coordinates (s t : List (List ℕ)) :
    (cursor s t).coordinates = word s := by
  simp [cursor, LabeledCode.terminalCursor]

@[simp] theorem cursor_terminal (s t : List (List ℕ)) : (cursor s t).terminal = true := rfl

/-- Every clause of the original clarity predicate holds for the
computed actual-cut labeling, assuming the stated geometric bounds. -/
theorem clearSide (s t : G) (h : Admissible s.val t.val) :
    ClearSide (cursor s.val t.val) s t := by
  refine ⟨(cursor_coordinates s.val t.val).symm, ?_, root_bounds h, ?_,
    succ_mem_root s.val t.val, ?_, h.leaves⟩
  · simp [cursor, LabeledCode.terminalCursor]
  · intro i hi k hk
    have hlabel : k ∈ body s.val t.val i := by
      simpa only [cursor, LabeledCode.terminalCursor, bodyLabels_getD _ _ i hi] using hk
    exact body_bounds h i k hlabel
  · intro i hi j
    change j + 1 ∈ ((bodies s.val t.val).map Prod.fst).getD i ∅ ↔ _
    rw [bodyLabels_getD _ _ i hi]
    exact succ_mem_body s.val t.val i j

theorem body_subset {s t : List (List ℕ)} {i : ℕ} {D : Finset ℕ}
    (hD : ∀ j, LeafCut s t i j → j + 1 ∈ D) : body s t i ⊆ D := by
  intro k hk
  obtain ⟨j, hj, rfl⟩ := (mem_body s t i k).1 hk
  exact hD j hj

theorem root_subset {s t : List (List ℕ)} {C : Finset ℕ}
    (hC : ∀ i j, LeafCut s t i j → i + 1 ∈ C) : root s t ⊆ C := by
  intro k hk
  obtain ⟨i, j, hij, rfl⟩ := (mem_root s t k).1 hk
  exact hC i j hij

#print axioms clearSide
#print axioms body_subset
#print axioms root_subset

end Erdos591.Positive.Game.CutLabels

end Erdos118.Reused591
