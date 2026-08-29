/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayFiniteInputCoordinateInterval

/-!
# Coordinate intervals and suffixes of an infinite compressor input

The constructions in this file retain the literal coordinate order of an
`InfiniteInput`.  A bounded interval is a genuine `FiniteInput`; a suffix is
a genuine shifted `InfiniteInput`.  Their compressed traces have exact
vertex and directed-edge descriptions in terms of the original stream.
-/

noncomputable section

open Set

namespace Erdos599.Alternating.RunCompressor.InfiniteInput

universe u

variable {V : Type u} {D : Digraph V}

/-- The literal direction-oriented edge at raw coordinate `n`. -/
def rawEdge (S : InfiniteInput D) (n : Nat) : V × V :=
  match S.colour n with
  | .forward => (S.vertex n, S.vertex (n + 1))
  | .backward => (S.vertex (n + 1), S.vertex n)

private theorem runBoundary_id_le (S : InfiniteInput D)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n) :
    ∀ i, i ≤ runBoundary S.colour hchange i := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
      exact Nat.succ_le_of_lt
        (ih.trans_lt (runBoundary_lt_succ S.colour hchange i))

/-- Every raw coordinate lies in a unique-enough compressed run interval.
Only existence is needed for exact trace coverage. -/
theorem exists_runInterval (S : InfiniteInput D)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (n : Nat) :
    ∃ i, runBoundary S.colour hchange i ≤ n ∧
      n < runBoundary S.colour hchange (i + 1) := by
  have hexists : ∃ i, n < runBoundary S.colour hchange (i + 1) := by
    refine ⟨n, ?_⟩
    exact (Nat.lt_succ_self n).trans_le (runBoundary_id_le S hchange (n + 1))
  let i := Nat.find hexists
  refine ⟨i, ?_, Nat.find_spec hexists⟩
  cases hi : i with
  | zero => simp
  | succ j =>
      have hminimal : ¬ n < runBoundary S.colour hchange (j + 1) := by
        have hjlt : j < Nat.find hexists := by
          rw [show Nat.find hexists = i from rfl, hi]
          exact Nat.lt_succ_self j
        exact Nat.find_min hexists hjlt
      simpa [hi] using Nat.le_of_not_gt hminimal

/-- A chosen maximal infinite run containing raw coordinate `n`. -/
noncomputable def runIndexAt (S : InfiniteInput D)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (n : Nat) : Nat :=
  Classical.choose (S.exists_runInterval hchange n)

theorem runBoundary_runIndexAt_le (S : InfiniteInput D)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (n : Nat) :
    runBoundary S.colour hchange (S.runIndexAt hchange n) ≤ n :=
  (Classical.choose_spec (S.exists_runInterval hchange n)).1

theorem runIndexAt_lt_nextBoundary (S : InfiniteInput D)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (n : Nat) :
    n < runBoundary S.colour hchange (S.runIndexAt hchange n + 1) :=
  (Classical.choose_spec (S.exists_runInterval hchange n)).2

/-- The chosen locator agrees with any maximal run interval containing the
coordinate. -/
theorem runIndexAt_eq_of_mem_interval (S : InfiniteInput D)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (n i : Nat)
    (hlo : runBoundary S.colour hchange i ≤ n)
    (hhi : n < runBoundary S.colour hchange (i + 1)) :
    S.runIndexAt hchange n = i := by
  let j := S.runIndexAt hchange n
  have hjlo := S.runBoundary_runIndexAt_le hchange n
  have hjhi := S.runIndexAt_lt_nextBoundary hchange n
  by_contra hne
  rcases lt_or_gt_of_ne hne with hji | hij
  · have hmono := (runBoundary_strictMono S.colour hchange).monotone
        (show j + 1 ≤ i by omega)
    exact (Nat.not_lt_of_ge (hmono.trans hlo)) hjhi
  · have hmono := (runBoundary_strictMono S.colour hchange).monotone
        (show i + 1 ≤ j by omega)
    exact (Nat.not_lt_of_ge (hmono.trans hjlo)) hhi

/-- Every raw edge occurs literally in the infinite compressed trace. -/
theorem rawEdge_mem_toInfiniteTrace (S : InfiniteInput D)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (n : Nat) :
    S.rawEdge n ∈ (S.toInfiniteRunWalk hchange).toInfiniteTrace.edgeSet := by
  obtain ⟨i, hlo, hhi⟩ := S.exists_runInterval hchange n
  have hcolour := colour_eq_on_run S.colour hchange hlo hhi
  simp only [InfiniteTrace.edgeSet, Set.mem_iUnion]
  refine ⟨i, ?_⟩
  cases hdir : S.colour (runBoundary S.colour hchange i) with
  | forward =>
      change S.rawEdge n ∈ (S.projectedRun hchange i).link.path.edgeSet
      rw [S.projectedRun_edgeSet_eq_forward hchange i hdir]
      refine ⟨n, hlo, hhi, ?_⟩
      simp [rawEdge, hcolour.trans hdir]
  | backward =>
      change S.rawEdge n ∈ (S.projectedRun hchange i).link.path.edgeSet
      rw [S.projectedRun_edgeSet_eq_backward hchange i hdir]
      refine ⟨n, hlo, hhi, ?_⟩
      simp [rawEdge, hcolour.trans hdir]

/-- Exact raw-edge description of the infinite compressed trace. -/
theorem mem_toInfiniteTrace_edgeSet_iff (S : InfiniteInput D)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    {e : V × V} :
    e ∈ (S.toInfiniteRunWalk hchange).toInfiniteTrace.edgeSet ↔
      ∃ n, e = S.rawEdge n := by
  constructor
  · simp only [InfiniteTrace.edgeSet, Set.mem_iUnion]
    rintro ⟨i, he⟩
    cases hdir : S.colour (runBoundary S.colour hchange i) with
    | forward =>
        change e ∈ (S.projectedRun hchange i).link.path.edgeSet at he
        rw [S.projectedRun_edgeSet_eq_forward hchange i hdir] at he
        obtain ⟨n, hlo, hhi, rfl⟩ := he
        refine ⟨n, ?_⟩
        have hc := colour_eq_on_run S.colour hchange hlo hhi
        simp [rawEdge, hc.trans hdir]
    | backward =>
        change e ∈ (S.projectedRun hchange i).link.path.edgeSet at he
        rw [S.projectedRun_edgeSet_eq_backward hchange i hdir] at he
        obtain ⟨n, hlo, hhi, rfl⟩ := he
        refine ⟨n, ?_⟩
        have hc := colour_eq_on_run S.colour hchange hlo hhi
        simp [rawEdge, hc.trans hdir]
  · rintro ⟨n, rfl⟩
    exact S.rawEdge_mem_toInfiniteTrace hchange n

/-- Exact vertex carrier of the infinite compressed trace. -/
theorem toInfiniteTrace_vertexSet (S : InfiniteInput D)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n) :
    (S.toInfiniteRunWalk hchange).toInfiniteTrace.vertexSet =
      Set.range S.vertex := by
  apply Set.Subset.antisymm
  · rintro x hx
    simp only [InfiniteTrace.vertexSet, Set.mem_iUnion] at hx
    obtain ⟨i, hxi⟩ := hx
    change x ∈ (S.projectedRun hchange i).link.path.support at hxi
    rw [S.projectedRun_support hchange i] at hxi
    obtain ⟨n, _hn, rfl⟩ := hxi
    exact ⟨n, rfl⟩
  · rintro x ⟨n, rfl⟩
    obtain ⟨i, hlo, hhi⟩ := S.exists_runInterval hchange n
    simp only [InfiniteTrace.vertexSet, Set.mem_iUnion]
    refine ⟨i, ?_⟩
    change S.vertex n ∈ (S.projectedRun hchange i).link.path.support
    rw [S.projectedRun_support hchange i]
    exact ⟨n, ⟨hlo, hhi.le⟩, rfl⟩

/-! ## Bounded coordinate intervals -/

/-- The literal finite compressor input on raw coordinates `[a,b]`. -/
def coordinateInterval (S : InfiniteInput D)
    (a b : Nat) (hab : a < b) : FiniteInput D where
  lastEdge := b - a
  lastEdge_pos := Nat.sub_pos_of_lt hab
  vertex n := S.vertex (a + n)
  vertex_injective_on := by
    intro i j _hi _hj hij
    exact Nat.add_left_cancel (S.vertex_injective hij)
  colour k := S.colour (a + k.1)
  forward_adj := by
    intro n hn
    simpa only [Nat.add_assoc] using S.forward_adj (a + n.1) hn
  backward_adj := by
    intro n hn
    simpa only [Nat.add_assoc] using S.backward_adj (a + n.1) hn

@[simp] theorem coordinateInterval_vertex (S : InfiniteInput D)
    (a b : Nat) (hab : a < b) (n : Nat) :
    (S.coordinateInterval a b hab).vertex n = S.vertex (a + n) := rfl

@[simp] theorem coordinateInterval_lastEdge (S : InfiniteInput D)
    (a b : Nat) (hab : a < b) :
    (S.coordinateInterval a b hab).lastEdge = b - a := rfl

theorem coordinateInterval_rawEdge (S : InfiniteInput D)
    (a b : Nat) (hab : a < b)
    (k : Fin (S.coordinateInterval a b hab).lastEdge) :
    (S.coordinateInterval a b hab).rawEdge k = S.rawEdge (a + k.1) := by
  cases hcolour : S.colour (a + k.1) <;>
    simp [FiniteInput.rawEdge, rawEdge, coordinateInterval, hcolour,
      Nat.add_assoc]

@[simp] theorem coordinateInterval_trace_initial (S : InfiniteInput D)
    (a b : Nat) (hab : a < b) :
    (S.coordinateInterval a b hab).toFiniteRunWalk.toFiniteTrace.initial =
      S.vertex a := by
  rw [(S.coordinateInterval a b hab).toFiniteRunWalk.toFiniteTrace_initial]
  rfl

@[simp] theorem coordinateInterval_trace_terminal (S : InfiniteInput D)
    (a b : Nat) (hab : a < b) :
    (S.coordinateInterval a b hab).toFiniteRunWalk.toFiniteTrace.terminal =
      S.vertex b := by
  rw [(S.coordinateInterval a b hab).toFiniteRunWalk.toFiniteTrace_terminal,
    (S.coordinateInterval a b hab).toFiniteRunWalk_final_last]
  change S.vertex (a + (b - a)) = S.vertex b
  rw [Nat.add_sub_of_le hab.le]

theorem coordinateInterval_trace_vertexSet (S : InfiniteInput D)
    (a b : Nat) (hab : a < b) :
    (S.coordinateInterval a b hab).toFiniteRunWalk.toFiniteTrace.vertexSet =
      S.vertex '' Set.Icc a b := by
  rw [(S.coordinateInterval a b hab).toFiniteTrace_vertexSet]
  ext x
  constructor
  · rintro ⟨n, hn, rfl⟩
    rcases hn with ⟨_hn0, hnb⟩
    exact ⟨a + n, ⟨Nat.le_add_right _ _, by
      change n ≤ b - a at hnb
      omega⟩, rfl⟩
  · rintro ⟨n, hn, rfl⟩
    refine ⟨n - a, ⟨Nat.zero_le _, ?_⟩, ?_⟩
    · change n - a ≤ b - a
      exact Nat.sub_le_sub_right hn.2 a
    · simp only [coordinateInterval_vertex]
      rw [Nat.add_sub_of_le hn.1]

theorem coordinateInterval_trace_edgeSet (S : InfiniteInput D)
    (a b : Nat) (hab : a < b) :
    (S.coordinateInterval a b hab).toFiniteRunWalk.toFiniteTrace.edgeSet =
      {e | ∃ n, a ≤ n ∧ n < b ∧ e = S.rawEdge n} := by
  ext e
  constructor
  · intro he
    rw [(S.coordinateInterval a b hab).mem_toFiniteTrace_edgeSet_iff] at he
    obtain ⟨k, rfl⟩ := he
    rw [S.coordinateInterval_rawEdge a b hab k]
    exact ⟨a + k.1, Nat.le_add_right _ _, by
      have hk : k.1 < b - a := by simpa using k.2
      omega, rfl⟩
  · rintro ⟨n, han, hnb, rfl⟩
    rw [(S.coordinateInterval a b hab).mem_toFiniteTrace_edgeSet_iff]
    let k : Fin (S.coordinateInterval a b hab).lastEdge :=
      ⟨n - a, by
        change n - a < b - a
        omega⟩
    refine ⟨k, ?_⟩
    rw [S.coordinateInterval_rawEdge a b hab k]
    change S.rawEdge n = S.rawEdge (a + (n - a))
    rw [Nat.add_sub_of_le han]

/-! ## Infinite suffixes -/

/-- The literal infinite compressor input beginning at raw coordinate `a`. -/
def shift (S : InfiniteInput D) (a : Nat) : InfiniteInput D where
  vertex n := S.vertex (a + n)
  vertex_injective := fun _ _ h ↦ Nat.add_left_cancel (S.vertex_injective h)
  colour n := S.colour (a + n)
  forward_adj := by
    intro n hn
    simpa only [Nat.add_assoc] using S.forward_adj (a + n) hn
  backward_adj := by
    intro n hn
    simpa only [Nat.add_assoc] using S.backward_adj (a + n) hn

@[simp] theorem shift_vertex (S : InfiniteInput D) (a n : Nat) :
    (S.shift a).vertex n = S.vertex (a + n) := rfl

@[simp] theorem shift_colour (S : InfiniteInput D) (a n : Nat) :
    (S.shift a).colour n = S.colour (a + n) := rfl

/-- Unbounded colour change is inherited by every shifted suffix. -/
theorem shift_changes (S : InfiniteInput D)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (a : Nat) :
    ∀ n, ∃ m, n < m ∧ (S.shift a).colour m ≠ (S.shift a).colour n := by
  intro n
  obtain ⟨m, hnm, hcolour⟩ := hchange (a + n)
  refine ⟨m - a, by omega, ?_⟩
  change S.colour (a + (m - a)) ≠ S.colour (a + n)
  rw [Nat.add_sub_of_le (by omega)]
  exact hcolour

theorem shift_rawEdge (S : InfiniteInput D) (a n : Nat) :
    (S.shift a).rawEdge n = S.rawEdge (a + n) := by
  cases hcolour : S.colour (a + n) <;>
    simp [rawEdge, shift, hcolour, Nat.add_assoc]

@[simp] theorem shift_trace_initial (S : InfiniteInput D)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (a : Nat) :
    ((S.shift a).toInfiniteRunWalk (S.shift_changes hchange a)).toInfiniteTrace.initial =
      S.vertex a := by
  rw [(S.shift a).toInfiniteRunWalk
    (S.shift_changes hchange a) |>.toInfiniteTrace_initial]
  rfl

theorem shift_trace_vertexSet (S : InfiniteInput D)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (a : Nat) :
    ((S.shift a).toInfiniteRunWalk
      (S.shift_changes hchange a)).toInfiniteTrace.vertexSet =
      S.vertex '' Set.Ici a := by
  rw [(S.shift a).toInfiniteTrace_vertexSet (S.shift_changes hchange a)]
  ext x
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨a + n, Nat.le_add_right _ _, rfl⟩
  · rintro ⟨n, han, rfl⟩
    exact ⟨n - a, by rw [shift_vertex, Nat.add_sub_of_le han]⟩

theorem shift_trace_edgeSet (S : InfiniteInput D)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (a : Nat) :
    ((S.shift a).toInfiniteRunWalk
      (S.shift_changes hchange a)).toInfiniteTrace.edgeSet =
      {e | ∃ n, a ≤ n ∧ e = S.rawEdge n} := by
  ext e
  rw [(S.shift a).mem_toInfiniteTrace_edgeSet_iff
    (S.shift_changes hchange a)]
  constructor
  · rintro ⟨n, rfl⟩
    rw [S.shift_rawEdge a n]
    exact ⟨a + n, Nat.le_add_right _ _, rfl⟩
  · rintro ⟨n, han, rfl⟩
    refine ⟨n - a, ?_⟩
    rw [S.shift_rawEdge a (n - a), Nat.add_sub_of_le han]

#print axioms exists_runInterval
#print axioms mem_toInfiniteTrace_edgeSet_iff
#print axioms coordinateInterval_trace_vertexSet
#print axioms coordinateInterval_trace_edgeSet
#print axioms shift_trace_vertexSet
#print axioms shift_trace_edgeSet

end Erdos599.Alternating.RunCompressor.InfiniteInput
