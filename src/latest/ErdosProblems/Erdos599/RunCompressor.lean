/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FiniteRelationTrace

/-!
# Compressing indexed two-colour walks into alternating runs

The alternating-path construction naturally produces an injective stream of
vertices together with an *explicit* direction for every traversed edge.  It
is important that the direction is data rather than inferred from two edge
predicates: an edge may belong to both path families.

This file cuts such a stream into maximal constant-direction intervals and
turns every interval into a `ProjectedRun`.  The infinite construction is
used when colour changes are unbounded.  The finite construction below uses
`colourRuns` to retain the corresponding bounded decomposition.
-/

namespace Erdos599.Alternating

open Set DirectedPath

universe u

variable {V : Type u} {D : Digraph V}

namespace RunCompressor

/-! ## First-change boundaries -/

/-- The first position strictly after `n` carrying a different colour. -/
noncomputable def firstChange (colour : ℕ → Direction)
    (hchange : ∀ n, ∃ m, n < m ∧ colour m ≠ colour n) (n : ℕ) : ℕ :=
  Nat.find (hchange n)

theorem lt_firstChange (colour : ℕ → Direction)
    (hchange : ∀ n, ∃ m, n < m ∧ colour m ≠ colour n) (n : ℕ) :
    n < firstChange colour hchange n :=
  (Nat.find_spec (hchange n)).1

theorem colour_firstChange_ne (colour : ℕ → Direction)
    (hchange : ∀ n, ∃ m, n < m ∧ colour m ≠ colour n) (n : ℕ) :
    colour (firstChange colour hchange n) ≠ colour n :=
  (Nat.find_spec (hchange n)).2

theorem colour_eq_of_lt_firstChange (colour : ℕ → Direction)
    (hchange : ∀ n, ∃ m, n < m ∧ colour m ≠ colour n)
    {n k : ℕ} (hnk : n ≤ k) (hk : k < firstChange colour hchange n) :
    colour k = colour n := by
  by_contra hne
  have hle : firstChange colour hchange n ≤ k :=
    Nat.find_min' (hchange n) ⟨lt_of_le_of_ne hnk (by
      intro h
      subst k
      exact hne rfl), hne⟩
  omega

/-- Endpoints of the maximal constant-colour runs.  Run `i` is the half-open
edge interval `[runBoundary i, runBoundary (i+1))`. -/
noncomputable def runBoundary (colour : ℕ → Direction)
    (hchange : ∀ n, ∃ m, n < m ∧ colour m ≠ colour n) : ℕ → ℕ
  | 0 => 0
  | n + 1 => firstChange colour hchange (runBoundary colour hchange n)

@[simp] theorem runBoundary_zero (colour : ℕ → Direction) (hchange) :
    runBoundary colour hchange 0 = 0 := rfl

@[simp] theorem runBoundary_succ (colour : ℕ → Direction)
    (hchange) (n : ℕ) :
    runBoundary colour hchange (n + 1) =
      firstChange colour hchange (runBoundary colour hchange n) := rfl

theorem runBoundary_lt_succ (colour : ℕ → Direction) (hchange) (n : ℕ) :
    runBoundary colour hchange n < runBoundary colour hchange (n + 1) := by
  rw [runBoundary_succ]
  exact lt_firstChange colour hchange _

theorem runBoundary_strictMono (colour : ℕ → Direction) (hchange) :
    StrictMono (runBoundary colour hchange) :=
  strictMono_nat_of_lt_succ (runBoundary_lt_succ colour hchange)

theorem colour_runBoundary_succ_ne (colour : ℕ → Direction)
    (hchange) (n : ℕ) :
    colour (runBoundary colour hchange (n + 1)) ≠
      colour (runBoundary colour hchange n) := by
  rw [runBoundary_succ]
  exact colour_firstChange_ne colour hchange _

/-- Every raw edge in run `i` has the colour at its lower boundary. -/
theorem colour_eq_on_run (colour : ℕ → Direction) (hchange)
    {i k : ℕ} (hlo : runBoundary colour hchange i ≤ k)
    (hhi : k < runBoundary colour hchange (i + 1)) :
    colour k = colour (runBoundary colour hchange i) := by
  rw [runBoundary_succ] at hhi
  exact colour_eq_of_lt_firstChange colour hchange hlo hhi

/-! ## Directed interval paths -/

/-- The forward-oriented walk on `a,a+1,...,a+n`. -/
def forwardIntervalWalk (vertex : ℕ → V) (a : ℕ) :
    (n : ℕ) →
      (∀ k < n, D.Adj (vertex (a + k)) (vertex (a + k + 1))) →
        Walk D (vertex a) (vertex (a + n))
  | 0, _ => .nil
  | n + 1, h =>
      (forwardIntervalWalk vertex a n
        (fun k hk ↦ h k (hk.trans (Nat.lt_succ_self n)))).concat
        (by simpa [Nat.add_assoc] using h n (Nat.lt_succ_self n))

@[simp] theorem forwardIntervalWalk_support (vertex : ℕ → V)
    (a n : ℕ) (h) :
    (forwardIntervalWalk (D := D) vertex a n h).support =
      List.ofFn (fun i : Fin (n + 1) ↦ vertex (a + i)) := by
  induction n with
  | zero => simp [forwardIntervalWalk]
  | succ n ih =>
      rw [forwardIntervalWalk, Walk.support_concat, ih]
      rw [@List.ofFn_succ_last V (n + 1)
        (fun i : Fin ((n + 1) + 1) ↦ vertex (a + i))]
      congr 1 <;> simp

theorem forwardIntervalWalk_isPath (vertex : ℕ → V)
    (a n : ℕ)
    (hinj : ∀ {i j}, i ≤ a + n → j ≤ a + n → vertex i = vertex j → i = j)
    (h) :
    (forwardIntervalWalk (D := D) vertex a n h).IsPath := by
  rw [Walk.isPath_iff, forwardIntervalWalk_support]
  exact List.nodup_ofFn.mpr fun i j hij ↦ Fin.ext
    (Nat.add_left_cancel (hinj (by omega) (by omega) hij))

def forwardIntervalPath (vertex : ℕ → V)
    (a n : ℕ)
    (hinj : ∀ {i j}, i ≤ a + n → j ≤ a + n → vertex i = vertex j → i = j)
    (h : ∀ k < n, D.Adj (vertex (a + k)) (vertex (a + k + 1))) :
    FinitePath D where
  start := vertex a
  finish := vertex (a + n)
  walk := forwardIntervalWalk vertex a n h
  isPath := forwardIntervalWalk_isPath vertex a n hinj h

/-- The reverse-oriented walk on `a+n,...,a+1,a`. -/
def backwardIntervalWalk (vertex : ℕ → V) (a : ℕ) :
    (n : ℕ) →
      (∀ k < n, D.Adj (vertex (a + k + 1)) (vertex (a + k))) →
        Walk D (vertex (a + n)) (vertex a)
  | 0, _ => .nil
  | n + 1, h =>
      .cons (by simpa [Nat.add_assoc] using h n (Nat.lt_succ_self n))
        (backwardIntervalWalk vertex a n
          (fun k hk ↦ h k (hk.trans (Nat.lt_succ_self n))))

@[simp] theorem backwardIntervalWalk_support (vertex : ℕ → V)
    (a n : ℕ) (h) :
    (backwardIntervalWalk (D := D) vertex a n h).support =
      (List.ofFn (fun i : Fin (n + 1) ↦ vertex (a + i))).reverse := by
  induction n with
  | zero => simp [backwardIntervalWalk]
  | succ n ih =>
      rw [backwardIntervalWalk, Walk.support_cons, ih]
      rw [@List.ofFn_succ_last V (n + 1)
        (fun i : Fin ((n + 1) + 1) ↦ vertex (a + i))]
      simp

theorem backwardIntervalWalk_isPath (vertex : ℕ → V)
    (a n : ℕ)
    (hinj : ∀ {i j}, i ≤ a + n → j ≤ a + n → vertex i = vertex j → i = j)
    (h) :
    (backwardIntervalWalk (D := D) vertex a n h).IsPath := by
  rw [Walk.isPath_iff, backwardIntervalWalk_support, List.nodup_reverse]
  exact List.nodup_ofFn.mpr fun i j hij ↦ Fin.ext
    (Nat.add_left_cancel (hinj (by omega) (by omega) hij))

def backwardIntervalPath (vertex : ℕ → V)
    (a n : ℕ)
    (hinj : ∀ {i j}, i ≤ a + n → j ≤ a + n → vertex i = vertex j → i = j)
    (h : ∀ k < n, D.Adj (vertex (a + k + 1)) (vertex (a + k))) :
    FinitePath D where
  start := vertex (a + n)
  finish := vertex a
  walk := backwardIntervalWalk vertex a n h
  isPath := backwardIntervalWalk_isPath vertex a n hinj h

theorem set_ofFn_add_eq_image_Icc (vertex : ℕ → V) (a n : ℕ) :
    {x | x ∈ List.ofFn (fun i : Fin (n + 1) ↦ vertex (a + i))} =
      vertex '' Set.Icc a (a + n) := by
  ext x
  simp only [Set.mem_setOf_eq, List.mem_ofFn, Set.mem_image, Set.mem_Icc]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨a + i, ⟨Nat.le_add_right _ _, by omega⟩, rfl⟩
  · rintro ⟨k, ⟨hak, hka⟩, rfl⟩
    refine ⟨⟨k - a, by omega⟩, ?_⟩
    rw [Nat.add_sub_of_le hak]

theorem forwardIntervalPath_support (vertex : ℕ → V)
    (a n : ℕ)
    (hinj : ∀ {i j}, i ≤ a + n → j ≤ a + n → vertex i = vertex j → i = j)
    (h) :
    (forwardIntervalPath (D := D) vertex a n hinj h).support =
      vertex '' Set.Icc a (a + n) := by
  rw [FinitePath.support, forwardIntervalPath, forwardIntervalWalk_support]
  exact set_ofFn_add_eq_image_Icc vertex a n

theorem backwardIntervalPath_support (vertex : ℕ → V)
    (a n : ℕ)
    (hinj : ∀ {i j}, i ≤ a + n → j ≤ a + n → vertex i = vertex j → i = j)
    (h) :
    (backwardIntervalPath (D := D) vertex a n hinj h).support =
      vertex '' Set.Icc a (a + n) := by
  rw [FinitePath.support, backwardIntervalPath, backwardIntervalWalk_support]
  simp only [List.mem_reverse]
  exact set_ofFn_add_eq_image_Icc vertex a n

theorem walk_edgeSet_append {a b c : V} (p : Walk D a b) (q : Walk D b c) :
    (p.append q).edgeSet = p.edgeSet ∪ q.edgeSet := by
  induction p with
  | nil => simp
  | cons h p ih =>
      simp only [Walk.cons_append, Walk.edgeSet_cons, ih, Set.union_assoc]

/-- Every edge of a forward interval path is one of its indexed raw edges. -/
theorem forwardIntervalWalk_edgeSet_subset (vertex : ℕ → V) (a n : ℕ)
    (hAdj : ∀ k < n, D.Adj (vertex (a + k)) (vertex (a + k + 1)))
    {E : Set (V × V)}
    (hE : ∀ k < n, (vertex (a + k), vertex (a + k + 1)) ∈ E) :
    (forwardIntervalWalk vertex a n hAdj).edgeSet ⊆ E := by
  induction n with
  | zero => simp [forwardIntervalWalk, Walk.edgeSet]
  | succ n ih =>
      rw [forwardIntervalWalk, Walk.concat, walk_edgeSet_append]
      intro e he
      rcases he with he | he
      · exact ih (fun k hk ↦ hAdj k (hk.trans (Nat.lt_succ_self n)))
          (fun k hk ↦ hE k (hk.trans (Nat.lt_succ_self n))) he
      · simp only [Walk.edgeSet_cons, Walk.edgeSet_nil, Set.union_empty,
          Set.mem_singleton_iff] at he
        subst e
        simpa [Nat.add_assoc] using hE n (Nat.lt_succ_self n)

theorem forwardIntervalPath_edgeSet_subset (vertex : ℕ → V) (a n : ℕ)
    (hinj : ∀ {i j}, i ≤ a + n → j ≤ a + n → vertex i = vertex j → i = j)
    (hAdj : ∀ k < n, D.Adj (vertex (a + k)) (vertex (a + k + 1)))
    {E : Set (V × V)}
    (hE : ∀ k < n, (vertex (a + k), vertex (a + k + 1)) ∈ E) :
    (forwardIntervalPath vertex a n hinj hAdj).edgeSet ⊆ E :=
  forwardIntervalWalk_edgeSet_subset vertex a n hAdj hE

theorem forwardIntervalWalk_raw_edge_mem (vertex : ℕ → V) (a : ℕ) :
    ∀ {n : ℕ}
      (hAdj : ∀ k < n, D.Adj (vertex (a + k)) (vertex (a + k + 1)))
      {k : ℕ}, k < n →
      (vertex (a + k), vertex (a + k + 1)) ∈
        (forwardIntervalWalk vertex a n hAdj).edgeSet := by
  intro n
  induction n with
  | zero => intro hAdj k hk; omega
  | succ n ih =>
      intro hAdj k hk
      rw [forwardIntervalWalk, Walk.concat, walk_edgeSet_append]
      by_cases hkn : k < n
      · left
        exact ih (fun j hj ↦ hAdj j (hj.trans (Nat.lt_succ_self n))) hkn
      · right
        have hknEq : k = n := by omega
        subst k
        simp [Walk.edgeSet_cons, Nat.add_assoc]

theorem forwardIntervalPath_edgeSet_eq (vertex : ℕ → V) (a n : ℕ)
    (hinj : ∀ {i j}, i ≤ a + n → j ≤ a + n → vertex i = vertex j → i = j)
    (hAdj : ∀ k < n, D.Adj (vertex (a + k)) (vertex (a + k + 1))) :
    (forwardIntervalPath vertex a n hinj hAdj).edgeSet =
      {e | ∃ k, k < n ∧ e = (vertex (a + k), vertex (a + k + 1))} := by
  apply Set.Subset.antisymm
  · apply forwardIntervalPath_edgeSet_subset
    intro k hk
    exact ⟨k, hk, rfl⟩
  · rintro e ⟨k, hk, rfl⟩
    exact forwardIntervalWalk_raw_edge_mem vertex a hAdj hk

/-- Every edge of a backward interval path is a reversed indexed raw edge. -/
theorem backwardIntervalWalk_edgeSet_subset (vertex : ℕ → V) (a n : ℕ)
    (hAdj : ∀ k < n, D.Adj (vertex (a + k + 1)) (vertex (a + k)))
    {E : Set (V × V)}
    (hE : ∀ k < n, (vertex (a + k + 1), vertex (a + k)) ∈ E) :
    (backwardIntervalWalk vertex a n hAdj).edgeSet ⊆ E := by
  induction n with
  | zero => simp [backwardIntervalWalk, Walk.edgeSet]
  | succ n ih =>
      rw [backwardIntervalWalk, Walk.edgeSet_cons]
      intro e he
      rcases he with he | he
      · simp only [Set.mem_singleton_iff] at he
        subst e
        simpa [Nat.add_assoc] using hE n (Nat.lt_succ_self n)
      · exact ih (fun k hk ↦ hAdj k (hk.trans (Nat.lt_succ_self n)))
          (fun k hk ↦ hE k (hk.trans (Nat.lt_succ_self n))) he

theorem backwardIntervalPath_edgeSet_subset (vertex : ℕ → V) (a n : ℕ)
    (hinj : ∀ {i j}, i ≤ a + n → j ≤ a + n → vertex i = vertex j → i = j)
    (hAdj : ∀ k < n, D.Adj (vertex (a + k + 1)) (vertex (a + k)))
    {E : Set (V × V)}
    (hE : ∀ k < n, (vertex (a + k + 1), vertex (a + k)) ∈ E) :
    (backwardIntervalPath vertex a n hinj hAdj).edgeSet ⊆ E :=
  backwardIntervalWalk_edgeSet_subset vertex a n hAdj hE

theorem backwardIntervalWalk_raw_edge_mem (vertex : ℕ → V) (a : ℕ) :
    ∀ {n : ℕ}
      (hAdj : ∀ k < n, D.Adj (vertex (a + k + 1)) (vertex (a + k)))
      {k : ℕ}, k < n →
      (vertex (a + k + 1), vertex (a + k)) ∈
        (backwardIntervalWalk vertex a n hAdj).edgeSet := by
  intro n
  induction n with
  | zero => intro hAdj k hk; omega
  | succ n ih =>
      intro hAdj k hk
      rw [backwardIntervalWalk, Walk.edgeSet_cons]
      by_cases hkn : k < n
      · right
        exact ih (fun j hj ↦ hAdj j (hj.trans (Nat.lt_succ_self n))) hkn
      · left
        have hknEq : k = n := by omega
        subst k
        simp [Nat.add_assoc]

theorem backwardIntervalPath_edgeSet_eq (vertex : ℕ → V) (a n : ℕ)
    (hinj : ∀ {i j}, i ≤ a + n → j ≤ a + n → vertex i = vertex j → i = j)
    (hAdj : ∀ k < n, D.Adj (vertex (a + k + 1)) (vertex (a + k))) :
    (backwardIntervalPath vertex a n hinj hAdj).edgeSet =
      {e | ∃ k, k < n ∧ e = (vertex (a + k + 1), vertex (a + k))} := by
  apply Set.Subset.antisymm
  · apply backwardIntervalPath_edgeSet_subset
    intro k hk
    exact ⟨k, hk, rfl⟩
  · rintro e ⟨k, hk, rfl⟩
    exact backwardIntervalWalk_raw_edge_mem vertex a hAdj hk

/-! ## Infinite compression -/

/-- An injective stream with an explicit direction on every edge. -/
structure InfiniteInput (D : Digraph V) where
  vertex : ℕ → V
  vertex_injective : Function.Injective vertex
  colour : ℕ → Direction
  forward_adj : ∀ n, colour n = .forward →
    D.Adj (vertex n) (vertex (n + 1))
  backward_adj : ∀ n, colour n = .backward →
    D.Adj (vertex (n + 1)) (vertex n)

namespace InfiniteInput

variable (S : InfiniteInput D)

/-- The compressed run at index `i`. -/
noncomputable def projectedRun
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (i : ℕ) : ProjectedRun D S.vertex := by
  let a := runBoundary S.colour hchange i
  let b := runBoundary S.colour hchange (i + 1)
  have hab : a < b := runBoundary_lt_succ S.colour hchange i
  have habsub : a + (b - a) = b := Nat.add_sub_of_le hab.le
  have hinj : ∀ {r s}, r ≤ a + (b - a) → s ≤ a + (b - a) →
      S.vertex r = S.vertex s → r = s := by
    intro r s _ _ h
    exact S.vertex_injective h
  have hc (k : ℕ) (hk : k < b - a) : S.colour (a + k) = S.colour a := by
    exact colour_eq_on_run S.colour hchange (i := i) (k := a + k)
      (by change a ≤ a + k; omega) (by change a + k < b; omega)
  if hdir : S.colour a = .forward then
      let p := forwardIntervalPath (D := D) S.vertex a (b - a) hinj
        (fun k hk ↦ S.forward_adj (a + k) ((hc k hk).trans hdir))
      refine {
        first := a
        last := b
        first_lt_last := hab
        link := {
          path := p
          direction := .forward
          nontrivial := ?_
        }
        entry_eq := rfl
        exit_eq := ?_
        support_eq := ?_
      }
      · intro heq
        apply Nat.ne_of_lt hab
        apply S.vertex_injective
        simpa [p, forwardIntervalPath, habsub] using heq
      · simpa [Link.exit, p, forwardIntervalPath, habsub]
      · simpa [p, habsub] using
          (forwardIntervalPath_support (D := D) S.vertex a (b - a) hinj _)
  else
      have hback : S.colour a = .backward := by
        cases h : S.colour a
        · exact (hdir h).elim
        · rfl
      let p := backwardIntervalPath (D := D) S.vertex a (b - a) hinj
        (fun k hk ↦ S.backward_adj (a + k) ((hc k hk).trans hback))
      refine {
        first := a
        last := b
        first_lt_last := hab
        link := {
          path := p
          direction := .backward
          nontrivial := ?_
        }
        entry_eq := rfl
        exit_eq := ?_
        support_eq := ?_
      }
      · intro heq
        apply Nat.ne_of_lt hab
        apply S.vertex_injective
        simpa [p, backwardIntervalPath, habsub] using heq.symm
      · simpa [Link.exit, p, backwardIntervalPath, habsub]
      · simpa [p, habsub] using
          (backwardIntervalPath_support (D := D) S.vertex a (b - a) hinj _)

@[simp] theorem projectedRun_first (hchange) (i : ℕ) :
    (S.projectedRun hchange i).first = runBoundary S.colour hchange i := by
  unfold projectedRun
  dsimp only
  split <;> rfl

@[simp] theorem projectedRun_last (hchange) (i : ℕ) :
    (S.projectedRun hchange i).last = runBoundary S.colour hchange (i + 1) := by
  unfold projectedRun
  dsimp only
  split <;> rfl

@[simp] theorem projectedRun_direction (hchange) (i : ℕ) :
    (S.projectedRun hchange i).link.direction =
      S.colour (runBoundary S.colour hchange i) := by
  simp only [projectedRun]
  split
  · rename_i h
    exact h.symm
  · rename_i h
    have hback : S.colour (runBoundary S.colour hchange i) = .backward := by
      cases hc : S.colour (runBoundary S.colour hchange i)
      · exact (h hc).elim
      · rfl
    exact hback.symm

theorem projectedRun_support (hchange) (i : ℕ) :
    (S.projectedRun hchange i).link.path.support =
      S.vertex '' Set.Icc (runBoundary S.colour hchange i)
        (runBoundary S.colour hchange (i + 1)) :=
  by
    rw [(S.projectedRun hchange i).support_eq,
      S.projectedRun_first hchange i, S.projectedRun_last hchange i]

/-- Forward-oriented raw edges in the `i`th maximal interval. -/
def forwardRunEdges
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (i : ℕ) : Set (V × V) :=
  {e | ∃ k, runBoundary S.colour hchange i ≤ k ∧
    k < runBoundary S.colour hchange (i + 1) ∧
    e = (S.vertex k, S.vertex (k + 1))}

/-- Backward-oriented raw edges in the `i`th maximal interval. -/
def backwardRunEdges
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (i : ℕ) : Set (V × V) :=
  {e | ∃ k, runBoundary S.colour hchange i ≤ k ∧
    k < runBoundary S.colour hchange (i + 1) ∧
    e = (S.vertex (k + 1), S.vertex k)}

theorem projectedRun_edgeSet_subset_forward (hchange) (i : ℕ)
    (hdir : S.colour (runBoundary S.colour hchange i) = .forward) :
    (S.projectedRun hchange i).link.path.edgeSet ⊆
      S.forwardRunEdges hchange i := by
  unfold projectedRun
  dsimp only
  rw [dif_pos hdir]
  apply forwardIntervalPath_edgeSet_subset
  · intro r s _ _ hrs
    exact S.vertex_injective hrs
  · intro k hk
    refine ⟨runBoundary S.colour hchange i + k, by omega, ?_, rfl⟩
    have hb := runBoundary_lt_succ S.colour hchange i
    have habsub := Nat.add_sub_of_le hb.le
    omega

theorem projectedRun_edgeSet_subset_backward (hchange) (i : ℕ)
    (hdir : S.colour (runBoundary S.colour hchange i) = .backward) :
    (S.projectedRun hchange i).link.path.edgeSet ⊆
      S.backwardRunEdges hchange i := by
  unfold projectedRun
  dsimp only
  rw [dif_neg (by simpa [hdir])]
  apply backwardIntervalPath_edgeSet_subset
  · intro r s _ _ hrs
    exact S.vertex_injective hrs
  · intro k hk
    refine ⟨runBoundary S.colour hchange i + k, by omega, ?_, rfl⟩
    have hb := runBoundary_lt_succ S.colour hchange i
    have habsub := Nat.add_sub_of_le hb.le
    omega

theorem projectedRun_edgeSet_eq_forward (hchange) (i : ℕ)
    (hdir : S.colour (runBoundary S.colour hchange i) = .forward) :
    (S.projectedRun hchange i).link.path.edgeSet =
      S.forwardRunEdges hchange i := by
  unfold projectedRun
  dsimp only
  rw [dif_pos hdir, forwardIntervalPath_edgeSet_eq]
  ext e
  simp only [Set.mem_setOf_eq, forwardRunEdges]
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨runBoundary S.colour hchange i + k, by omega, ?_, rfl⟩
    have hb := runBoundary_lt_succ S.colour hchange i
    have habsub := Nat.add_sub_of_le hb.le
    omega
  · rintro ⟨k, hlo, hhi, rfl⟩
    refine ⟨k - runBoundary S.colour hchange i, ?_, ?_⟩
    · omega
    · rw [Nat.add_sub_of_le hlo]

theorem projectedRun_edgeSet_eq_backward (hchange) (i : ℕ)
    (hdir : S.colour (runBoundary S.colour hchange i) = .backward) :
    (S.projectedRun hchange i).link.path.edgeSet =
      S.backwardRunEdges hchange i := by
  unfold projectedRun
  dsimp only
  rw [dif_neg (by simpa [hdir]), backwardIntervalPath_edgeSet_eq]
  ext e
  simp only [Set.mem_setOf_eq, backwardRunEdges]
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨runBoundary S.colour hchange i + k, by omega, ?_, rfl⟩
    have hb := runBoundary_lt_succ S.colour hchange i
    have habsub := Nat.add_sub_of_le hb.le
    omega
  · rintro ⟨k, hlo, hhi, rfl⟩
    refine ⟨k - runBoundary S.colour hchange i, ?_, ?_⟩
    · omega
    · rw [Nat.add_sub_of_le hlo]

/-- Exact provenance interface used by macro compilers: every edge of a
compressed link is an indexed raw edge in its maximal interval, oriented by
the link direction. -/
theorem projectedRun_edge_provenance (hchange) (i : ℕ) {e : V × V}
    (he : e ∈ (S.projectedRun hchange i).link.path.edgeSet) :
    ((S.projectedRun hchange i).link.direction = .forward ∧
        e ∈ S.forwardRunEdges hchange i) ∨
      ((S.projectedRun hchange i).link.direction = .backward ∧
        e ∈ S.backwardRunEdges hchange i) := by
  cases hdir : S.colour (runBoundary S.colour hchange i) with
  | forward =>
      left
      exact ⟨(S.projectedRun_direction hchange i).trans hdir,
        S.projectedRun_edgeSet_subset_forward hchange i hdir he⟩
  | backward =>
      right
      exact ⟨(S.projectedRun_direction hchange i).trans hdir,
        S.projectedRun_edgeSet_subset_backward hchange i hdir he⟩

/-- Maximal-run compression of an infinite injective two-colour stream. -/
noncomputable def toInfiniteRunWalk
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n) :
    InfiniteRunWalk D where
  vertex := S.vertex
  vertex_injective := S.vertex_injective
  run := S.projectedRun hchange
  starts_zero := by simp
  consecutive := by intro i; simp [Nat.add_assoc]
  ordered := by
    intro i j hij
    simp only [projectedRun_last, projectedRun_first]
    exact (runBoundary_strictMono S.colour hchange).monotone (by omega)
  directions_alternate := by
    intro i
    simp only [projectedRun_direction]
    exact (colour_runBoundary_succ_ne S.colour hchange i).symm

@[simp] theorem toInfiniteRunWalk_run_first (hchange) (i : ℕ) :
    ((S.toInfiniteRunWalk hchange).run i).first =
      runBoundary S.colour hchange i :=
  S.projectedRun_first hchange i

@[simp] theorem toInfiniteRunWalk_run_last (hchange) (i : ℕ) :
    ((S.toInfiniteRunWalk hchange).run i).last =
      runBoundary S.colour hchange (i + 1) :=
  S.projectedRun_last hchange i

@[simp] theorem toInfiniteRunWalk_run_direction (hchange) (i : ℕ) :
    ((S.toInfiniteRunWalk hchange).run i).link.direction =
      S.colour (runBoundary S.colour hchange i) :=
  S.projectedRun_direction hchange i

theorem toInfiniteRunWalk_run_support (hchange) (i : ℕ) :
    ((S.toInfiniteRunWalk hchange).run i).link.path.support =
      S.vertex '' Set.Icc (runBoundary S.colour hchange i)
        (runBoundary S.colour hchange (i + 1)) :=
  S.projectedRun_support hchange i

end InfiniteInput

/-! ## Finite run lists -/

/-- Number of raw edges in all runs strictly before run `i`. -/
def runLower (runs : List (List Direction)) (i : ℕ) : ℕ :=
  ((runs.take i).map List.length).sum

@[simp] theorem runLower_zero (runs : List (List Direction)) :
    runLower runs 0 = 0 := by simp [runLower]

theorem runLower_succ (runs : List (List Direction)) {i : ℕ}
    (hi : i < runs.length) :
    runLower runs (i + 1) = runLower runs i + (runs.get ⟨i, hi⟩).length := by
  induction runs generalizing i with
  | nil => simp at hi
  | cons r runs ih =>
      cases i with
      | zero => simp [runLower]
      | succ i =>
          simp only [List.length_cons, Nat.add_lt_add_iff_right] at hi
          simp only [runLower, List.take_succ_cons, List.map_cons, List.sum_cons,
            List.get_cons_succ]
          convert congrArg (fun n ↦ r.length + n) (ih hi) using 1 <;>
            simp only [runLower, Nat.add_assoc]

theorem runLower_mono (runs : List (List Direction))
    : Monotone (runLower runs) := by
  apply monotone_nat_of_le_succ
  intro i
  by_cases hi : i < runs.length
  · rw [runLower_succ runs hi]
    exact Nat.le_add_right _ _
  · have hlen : runs.length ≤ i := Nat.le_of_not_gt hi
    rw [runLower, runLower, List.take_of_length_le hlen,
      List.take_of_length_le (hlen.trans (Nat.le_succ i))]

theorem runLower_strictMonoOn (runs : List (List Direction))
    (hne : ∀ r ∈ runs, r ≠ []) {i j : ℕ}
    (hij : i < j) (hj : j ≤ runs.length) :
    runLower runs i < runLower runs j := by
  have hilen : i < runs.length := lt_of_lt_of_le hij hj
  rw [show runLower runs i < runLower runs j ↔
      runLower runs i < runLower runs j from Iff.rfl]
  have hpos : 0 < (runs.get ⟨i, hilen⟩).length :=
    List.length_pos_iff_ne_nil.2
      (hne _ (List.get_mem runs ⟨i, hilen⟩))
  have hstep : runLower runs i < runLower runs (i + 1) := by
    rw [runLower_succ runs hilen]
    exact Nat.lt_add_of_pos_right hpos
  exact hstep.trans_le (runLower_mono runs (Nat.succ_le_iff.mpr hij))

@[simp] theorem runLower_length (runs : List (List Direction)) :
    runLower runs runs.length = runs.flatten.length := by
  simp [runLower]

/-- Lookup in a run agrees with lookup at its offset in the flattened list. -/
theorem getElem_flatten_run (runs : List (List Direction))
    {i k : ℕ} (hi : i < runs.length) (hk : k < runs[i].length) :
    runs.flatten[runLower runs i + k]'(by
      have hs : runLower runs (i + 1) =
          runLower runs i + runs[i].length := by
        simpa only [List.get_eq_getElem] using runLower_succ runs hi
      have hle : runLower runs (i + 1) ≤ runLower runs runs.length :=
        runLower_mono runs (Nat.succ_le_of_lt hi)
      rw [runLower_length] at hle
      omega) = runs[i][k] := by
  induction runs generalizing i with
  | nil => simp at hi
  | cons r runs ih =>
      cases i with
      | zero =>
          have hkr : k < r.length := by simpa using hk
          simpa [runLower] using
            (List.getElem_append_left (as := r) (bs := runs.flatten) hkr)
      | succ i =>
          have hi' : i < runs.length := by simpa using hi
          have hk' : k < runs[i].length := by simpa using hk
          have h := ih hi' hk'
          have hflat : runLower runs i + k < runs.flatten.length := by
            have hs := runLower_succ runs hi'
            have hle := runLower_mono runs (Nat.succ_le_of_lt hi')
            rw [runLower_length] at hle
            have hkget : k < (runs.get ⟨i, hi'⟩).length := by
              simpa only [List.get_eq_getElem] using hk'
            exact (Nat.add_lt_add_left hkget _).trans_le (hs ▸ hle)
          have happ :
              (r ++ runs.flatten)[r.length + (runLower runs i + k)]'(by
                simp only [List.length_append]
                omega) = runs[i][k] := by
            rw [List.getElem_append_right (Nat.le_add_right _ _)]
            simpa using h
          simpa [runLower, Nat.add_assoc] using happ

/-- The maximal colour blocks of a nonempty finite colour list are nonempty
and flatten back to the original list. -/
def finiteColourRuns (colours : List Direction) : List (List Direction) :=
  colourRuns colours

@[simp] theorem finiteColourRuns_flatten (colours : List Direction) :
    (finiteColourRuns colours).flatten = colours :=
  flatten_colourRuns colours

theorem finiteColourRuns_run_ne_nil (colours : List Direction)
    {r : List Direction} (hr : r ∈ finiteColourRuns colours) : r ≠ [] :=
  colourRun_ne_nil hr

theorem finiteColourRuns_chain (colours : List Direction) :
    (finiteColourRuns colours).IsChain (fun a b ↦
      ∃ ha : a ≠ [], ∃ hb : b ≠ [], a.getLast ha ≠ b.head hb) :=
  colourRuns_boundary_ne

theorem finiteColourRun_isChain_eq (colours : List Direction)
    {r : List Direction} (hr : r ∈ finiteColourRuns colours) :
    r.IsChain (fun a b ↦ a = b) := by
  have h := List.isChain_of_mem_splitBy (r := fun a b : Direction ↦ a == b) hr
  simpa only [beq_iff_eq] using h

/-- Every position in a maximal colour block equals its head. -/
theorem finiteColourRun_get_eq_head (colours : List Direction)
    (i : Fin (finiteColourRuns colours).length)
    (k : Fin ((finiteColourRuns colours).get i).length) :
    ((finiteColourRuns colours).get i).get k =
      ((finiteColourRuns colours).get i).head
        (finiteColourRuns_run_ne_nil colours
          (List.get_mem _ i)) := by
  have hr : (finiteColourRuns colours).get i ∈ finiteColourRuns colours :=
    List.get_mem _ i
  have hchain : ((finiteColourRuns colours).get i).IsChain
      (fun a b ↦ id a = b) := by
    simpa using finiteColourRun_isChain_eq colours hr
  have h := hchain.iterate_eq_of_apply_eq k.1 k.2
  rw [Function.iterate_id, id_eq] at h
  rw [List.get_eq_getElem, List.head_eq_getElem]
  exact h.symm

/-- Directions of adjacent maximal blocks differ. -/
theorem finiteColourRuns_head_ne_head (colours : List Direction)
    (i : Fin ((finiteColourRuns colours).length - 1)) :
    ((finiteColourRuns colours).get ⟨i.1, by omega⟩).head
        (finiteColourRuns_run_ne_nil colours (List.get_mem _ _)) ≠
      ((finiteColourRuns colours).get ⟨i.1 + 1, by omega⟩).head
        (finiteColourRuns_run_ne_nil colours (List.get_mem _ _)) := by
  have hc := finiteColourRuns_chain colours
  rw [List.isChain_iff_getElem] at hc
  rcases hc i.1 (by omega) with ⟨ha, hb, hne⟩
  intro heq
  apply hne
  have hcurNe : (finiteColourRuns colours)[i.1] ≠ [] :=
    finiteColourRuns_run_ne_nil colours (List.getElem_mem ..)
  have hlast : (finiteColourRuns colours)[i.1].getLast ha =
      (finiteColourRuns colours)[i.1].head hcurNe := by
    rw [List.getLast_eq_getElem]
    exact finiteColourRun_get_eq_head colours
      ⟨i.1, by omega⟩ ⟨_, by
        exact Nat.sub_lt (List.length_pos_iff_ne_nil.2 hcurNe) (by omega)⟩
  exact hlast.trans heq

/-! ## Finite compression -/

/-- A positive finite injective vertex stream with an explicit direction on
each of its `lastEdge` edges. -/
structure FiniteInput (D : Digraph V) where
  lastEdge : ℕ
  lastEdge_pos : 0 < lastEdge
  vertex : ℕ → V
  vertex_injective_on : ∀ {i j}, i ≤ lastEdge → j ≤ lastEdge →
    vertex i = vertex j → i = j
  colour : Fin lastEdge → Direction
  forward_adj : ∀ n, colour n = .forward →
    D.Adj (vertex n) (vertex (n + 1))
  backward_adj : ∀ n, colour n = .backward →
    D.Adj (vertex (n + 1)) (vertex n)

namespace FiniteInput

variable (S : FiniteInput D)

def colours : List Direction := List.ofFn S.colour

def runs : List (List Direction) := finiteColourRuns S.colours

@[simp] theorem colours_length : S.colours.length = S.lastEdge := by
  simp [colours]

@[simp] theorem runs_flatten : S.runs.flatten = S.colours := by
  simp [runs]

theorem runs_ne_nil : S.runs ≠ [] := by
  apply colourRuns_ne_nil
  rw [List.ne_nil_iff_length_pos, S.colours_length]
  exact S.lastEdge_pos

theorem runs_length_pos : 0 < S.runs.length :=
  List.length_pos_iff_ne_nil.2 S.runs_ne_nil

theorem run_ne_nil {r : List Direction} (hr : r ∈ S.runs) : r ≠ [] :=
  finiteColourRuns_run_ne_nil S.colours hr

theorem runLower_total : runLower S.runs S.runs.length = S.lastEdge := by
  rw [runLower_length, S.runs_flatten, S.colours_length]

theorem runUpper_le_lastEdge (i : Fin S.runs.length) :
    runLower S.runs i + (S.runs.get i).length ≤ S.lastEdge := by
  rw [← runLower_succ S.runs i.2, ← S.runLower_total]
  exact runLower_mono S.runs (Nat.succ_le_of_lt i.2)

/-- The direction of the `i`th maximal block. -/
def runDirection (i : Fin S.runs.length) : Direction :=
  (S.runs.get i).head (S.run_ne_nil (List.get_mem _ i))

/-- Raw colour at any edge offset inside run `i`. -/
theorem colour_run_offset (i : Fin S.runs.length)
    {k : ℕ} (hk : k < (S.runs.get i).length) :
    S.colour ⟨runLower S.runs i + k, by
      exact lt_of_lt_of_le (Nat.add_lt_add_left hk _) (S.runUpper_le_lastEdge i)⟩ =
      S.runDirection i := by
  have hflat := getElem_flatten_run S.runs i.2 hk
  have hindex : runLower S.runs i + k < S.lastEdge :=
    lt_of_lt_of_le (Nat.add_lt_add_left hk _) (S.runUpper_le_lastEdge i)
  have hindexColours : runLower S.runs i + k < S.colours.length := by
    simpa using hindex
  have hflat' := hflat
  simp only [S.runs_flatten] at hflat'
  change S.colours[runLower S.runs i + k]'hindexColours =
    (S.runs.get i).get ⟨k, hk⟩ at hflat'
  have hrun := finiteColourRun_get_eq_head S.colours i ⟨k, hk⟩
  change (S.runs.get i).get ⟨k, hk⟩ =
    (S.runs.get i).head (S.run_ne_nil (List.get_mem _ i)) at hrun
  change S.colour ⟨runLower S.runs i + k, _⟩ =
    (S.runs.get i).head (S.run_ne_nil (List.get_mem _ i))
  calc
    S.colour ⟨runLower S.runs i + k, _⟩ =
        S.colours[runLower S.runs i + k]'hindexColours := by
          simp [colours]
    _ = (S.runs.get i).get ⟨k, hk⟩ := hflat'
    _ = (S.runs.get i).head (S.run_ne_nil (List.get_mem _ i)) := hrun

/-- The `i`th compressed projected run. -/
noncomputable def projectedRun (i : Fin S.runs.length) :
    ProjectedRun D S.vertex := by
  let a := runLower S.runs i
  let n := (S.runs.get i).length
  have hn : 0 < n := List.length_pos_iff_ne_nil.2
    (S.run_ne_nil (List.get_mem _ i))
  have hab : a < a + n := Nat.lt_add_of_pos_right hn
  have hupper : a + n ≤ S.lastEdge := S.runUpper_le_lastEdge i
  have hinj : ∀ {r s}, r ≤ a + n → s ≤ a + n →
      S.vertex r = S.vertex s → r = s := by
    intro r s hr hs h
    exact S.vertex_injective_on (hr.trans hupper) (hs.trans hupper) h
  if hdir : S.runDirection i = .forward then
      let p := forwardIntervalPath (D := D) S.vertex a n hinj
        (fun k hk ↦ S.forward_adj _ ((S.colour_run_offset i hk).trans hdir))
      refine {
        first := a
        last := a + n
        first_lt_last := hab
        link := { path := p, direction := .forward, nontrivial := ?_ }
        entry_eq := rfl
        exit_eq := rfl
        support_eq := ?_
      }
      · intro h
        exact Nat.ne_of_lt hab (S.vertex_injective_on
          ((Nat.le_add_right _ _).trans hupper) hupper h)
      · exact forwardIntervalPath_support (D := D) S.vertex a n hinj _
  else
      have hback : S.runDirection i = .backward := by
        cases h : S.runDirection i
        · exact (hdir h).elim
        · rfl
      let p := backwardIntervalPath (D := D) S.vertex a n hinj
        (fun k hk ↦ S.backward_adj _ ((S.colour_run_offset i hk).trans hback))
      refine {
        first := a
        last := a + n
        first_lt_last := hab
        link := { path := p, direction := .backward, nontrivial := ?_ }
        entry_eq := rfl
        exit_eq := rfl
        support_eq := ?_
      }
      · intro h
        exact Nat.ne_of_lt hab (S.vertex_injective_on
          ((Nat.le_add_right _ _).trans hupper) hupper h.symm)
      · exact backwardIntervalPath_support (D := D) S.vertex a n hinj _

@[simp] theorem projectedRun_first (i : Fin S.runs.length) :
    (S.projectedRun i).first = runLower S.runs i := by
  unfold projectedRun
  dsimp only
  split <;> rfl

@[simp] theorem projectedRun_last (i : Fin S.runs.length) :
    (S.projectedRun i).last = runLower S.runs (i.1 + 1) := by
  rw [runLower_succ S.runs i.2]
  unfold projectedRun
  dsimp only
  split <;> rfl

@[simp] theorem projectedRun_direction (i : Fin S.runs.length) :
    (S.projectedRun i).link.direction = S.runDirection i := by
  unfold projectedRun
  dsimp only
  split
  · rename_i h
    exact h.symm
  · rename_i h
    have hb : S.runDirection i = .backward := by
      cases hc : S.runDirection i
      · exact (h hc).elim
      · rfl
    exact hb.symm

theorem projectedRun_support (i : Fin S.runs.length) :
    (S.projectedRun i).link.path.support =
      S.vertex '' Set.Icc (runLower S.runs i) (runLower S.runs (i.1 + 1)) := by
  rw [(S.projectedRun i).support_eq, S.projectedRun_first i,
    S.projectedRun_last i]

/-- Explicit forward-oriented raw edge set of a finite maximal run. -/
def forwardRunEdges (i : Fin S.runs.length) : Set (V × V) :=
  {e | ∃ k, k < (S.runs.get i).length ∧
    e = (S.vertex (runLower S.runs i + k),
      S.vertex (runLower S.runs i + k + 1))}

/-- Explicit backward-oriented raw edge set of a finite maximal run. -/
def backwardRunEdges (i : Fin S.runs.length) : Set (V × V) :=
  {e | ∃ k, k < (S.runs.get i).length ∧
    e = (S.vertex (runLower S.runs i + k + 1),
      S.vertex (runLower S.runs i + k))}

theorem projectedRun_edgeSet_eq_forward (i : Fin S.runs.length)
    (hdir : S.runDirection i = .forward) :
    (S.projectedRun i).link.path.edgeSet = S.forwardRunEdges i := by
  unfold projectedRun
  dsimp only
  rw [dif_pos hdir, forwardIntervalPath_edgeSet_eq]
  rfl

theorem projectedRun_edgeSet_eq_backward (i : Fin S.runs.length)
    (hdir : S.runDirection i = .backward) :
    (S.projectedRun i).link.path.edgeSet = S.backwardRunEdges i := by
  unfold projectedRun
  dsimp only
  rw [dif_neg (by simpa [hdir]), backwardIntervalPath_edgeSet_eq]
  rfl

/-- Exact edge provenance for a finite compressed run.  This is the finite
counterpart of `InfiniteInput.projectedRun_edge_provenance`: every link edge
is one of the explicitly indexed retained edges, with the orientation
determined by the maximal run direction. -/
theorem projectedRun_edge_provenance (i : Fin S.runs.length) {e : V × V}
    (he : e ∈ (S.projectedRun i).link.path.edgeSet) :
    ((S.projectedRun i).link.direction = .forward ∧ e ∈ S.forwardRunEdges i) ∨
      ((S.projectedRun i).link.direction = .backward ∧ e ∈ S.backwardRunEdges i) := by
  cases hdir : S.runDirection i with
  | forward =>
      left
      refine ⟨(S.projectedRun_direction i).trans hdir, ?_⟩
      rw [S.projectedRun_edgeSet_eq_forward i hdir] at he
      exact he
  | backward =>
      right
      refine ⟨(S.projectedRun_direction i).trans hdir, ?_⟩
      rw [S.projectedRun_edgeSet_eq_backward i hdir] at he
      exact he

/-- The explicit direction-oriented union of all raw run edges. -/
def orientedEdgeSet : Set (V × V) :=
  ⋃ i : Fin S.runs.length,
    if S.runDirection i = .forward then S.forwardRunEdges i
    else S.backwardRunEdges i

/-- Equality identifying the nonempty run-list length with `lastIndex + 1`. -/
theorem runCount_eq : S.runs.length - 1 + 1 = S.runs.length := by
  have := S.runs_length_pos
  omega

/-- Convert the native `FiniteRunWalk` index into a maximal-block index. -/
def runIndex (i : Fin (S.runs.length - 1 + 1)) : Fin S.runs.length :=
  Fin.cast S.runCount_eq i

@[simp] theorem runIndex_val (i : Fin (S.runs.length - 1 + 1)) :
    (S.runIndex i).1 = i.1 := rfl

theorem final_projectedRun_last :
    (S.projectedRun (S.runIndex
      ⟨S.runs.length - 1, Nat.lt_succ_self _⟩)).last = S.lastEdge := by
  rw [S.projectedRun_last, S.runIndex_val]
  have hlen : S.runs.length - 1 + 1 = S.runs.length := S.runCount_eq
  rw [hlen, S.runLower_total]

/-- Maximal-run compression of a positive finite injective two-colour stream. -/
noncomputable def toFiniteRunWalk : FiniteRunWalk D where
  lastIndex := S.runs.length - 1
  vertex := S.vertex
  run i := S.projectedRun (S.runIndex i)
  vertex_injective_on := by
    intro i j hi hj h
    rw [S.final_projectedRun_last] at hi hj
    exact S.vertex_injective_on hi hj h
  starts_zero := by
    rw [S.projectedRun_first, S.runIndex_val, runLower_zero]
  consecutive := by
    intro i
    rw [S.projectedRun_last, S.projectedRun_first,
      S.runIndex_val, S.runIndex_val]
    rfl
  ordered := by
    intro i j hij
    rw [S.projectedRun_last, S.projectedRun_first,
      S.runIndex_val, S.runIndex_val]
    apply runLower_mono S.runs
    omega
  directions_alternate := by
    intro i
    rw [S.projectedRun_direction, S.projectedRun_direction]
    have hl : S.runIndex i.castSucc =
        (⟨i.1, by have := S.runs_length_pos; omega⟩ : Fin S.runs.length) :=
      Fin.ext rfl
    have hr : S.runIndex i.succ =
        (⟨i.1 + 1, by have := S.runs_length_pos; omega⟩ : Fin S.runs.length) :=
      Fin.ext rfl
    rw [hl, hr]
    simpa only [runDirection, runs] using
      finiteColourRuns_head_ne_head S.colours i

@[simp] theorem toFiniteRunWalk_run_first
    (i : Fin (S.runs.length - 1 + 1)) :
    ((S.toFiniteRunWalk).run i).first = runLower S.runs i := by
  exact S.projectedRun_first (S.runIndex i)

@[simp] theorem toFiniteRunWalk_run_last
    (i : Fin (S.runs.length - 1 + 1)) :
    ((S.toFiniteRunWalk).run i).last = runLower S.runs (i.1 + 1) := by
  exact S.projectedRun_last (S.runIndex i)

@[simp] theorem toFiniteRunWalk_run_direction
    (i : Fin (S.runs.length - 1 + 1)) :
    ((S.toFiniteRunWalk).run i).link.direction = S.runDirection (S.runIndex i) :=
  S.projectedRun_direction (S.runIndex i)

theorem toFiniteRunWalk_run_support
    (i : Fin (S.runs.length - 1 + 1)) :
    ((S.toFiniteRunWalk).run i).link.path.support =
      S.vertex '' Set.Icc (runLower S.runs i) (runLower S.runs (i.1 + 1)) :=
  S.projectedRun_support (S.runIndex i)

@[simp] theorem toFiniteRunWalk_final_last :
    ((S.toFiniteRunWalk).run (S.toFiniteRunWalk.lastRunIndex)).last =
      S.lastEdge :=
  S.final_projectedRun_last

/-- Compression neither creates nor loses edges: the finite alternating
trace has exactly the explicit direction-oriented raw run edge set. -/
theorem toFiniteTrace_edgeSet :
    S.toFiniteRunWalk.toFiniteTrace.edgeSet = S.orientedEdgeSet := by
  classical
  ext e
  simp only [FiniteTrace.edgeSet, Set.mem_iUnion, orientedEdgeSet]
  constructor
  · rintro ⟨j, he⟩
    let i : Fin S.runs.length := S.runIndex j
    refine ⟨i, ?_⟩
    by_cases hd : S.runDirection i = .forward
    · rw [if_pos hd]
      rw [← S.projectedRun_edgeSet_eq_forward i hd]
      exact he
    · have hb : S.runDirection i = .backward := by
        cases h : S.runDirection i
        · exact (hd h).elim
        · rfl
      rw [if_neg hd]
      rw [← S.projectedRun_edgeSet_eq_backward i hb]
      exact he
  · rintro ⟨i, he⟩
    let j : Fin (S.runs.length - 1 + 1) := Fin.cast S.runCount_eq.symm i
    refine ⟨j, ?_⟩
    have hji : S.runIndex j = i := Fin.ext rfl
    change e ∈ (S.projectedRun (S.runIndex j)).link.path.edgeSet
    rw [hji]
    by_cases hd : S.runDirection i = .forward
    · rw [if_pos hd] at he
      rw [S.projectedRun_edgeSet_eq_forward i hd]
      exact he
    · have hb : S.runDirection i = .backward := by
        cases h : S.runDirection i
        · exact (hd h).elim
        · rfl
      rw [if_neg hd] at he
      rw [S.projectedRun_edgeSet_eq_backward i hb]
      exact he

end FiniteInput

end RunCompressor
end Erdos599.Alternating
