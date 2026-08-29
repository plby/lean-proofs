/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayInfiniteSuffixRunEmbedding
import Mathlib.Data.Nat.Nth

/-!
# Consecutive cut contacts on an actual infinite compressor input

The coordinates at which an injective infinite compressor stream meets a set
`X` are either finite or infinite.  In the finite case they are enumerated by
a finite strictly increasing tuple and the remaining raw stream is a genuine
shifted `InfiniteInput`.  In the infinite case `Nat.nth` gives a strictly
increasing omega-sequence.  In both cases every raw vertex and directed edge
is covered exactly by the consecutive coordinate intervals (and, in the
finite case, by the final suffix).
-/

noncomputable section

open Set

namespace Erdos599.Alternating.RunCompressor.InfiniteInput

universe u

variable {V : Type u} {D : Digraph V}

def contactCoordinates (S : InfiniteInput D) (X : Set V) : Set Nat :=
  {n | S.vertex n ∈ X}

private theorem nat_le_of_strictMono_zero {f : Nat → Nat}
    (hf : StrictMono f) (hzero : f 0 = 0) : ∀ n, n ≤ f n := by
  intro n
  induction n with
  | zero => simp [hzero]
  | succ n ih => exact Nat.succ_le_of_lt (ih.trans_lt (hf (Nat.lt_succ_self n)))

private theorem exists_nat_interval {f : Nat → Nat}
    (hf : StrictMono f) (hzero : f 0 = 0) (n : Nat) :
    ∃ i, f i ≤ n ∧ n < f (i + 1) := by
  have hexists : ∃ i, n < f (i + 1) := by
    refine ⟨n, ?_⟩
    exact (Nat.lt_succ_self n).trans_le
      (nat_le_of_strictMono_zero hf hzero (n + 1))
  let i := Nat.find hexists
  refine ⟨i, ?_, Nat.find_spec hexists⟩
  cases hi : i with
  | zero => simp [hzero]
  | succ j =>
      have hjlt : j < Nat.find hexists := by
        rw [show Nat.find hexists = i from rfl, hi]
        exact Nat.lt_succ_self j
      have hminimal : ¬ n < f (j + 1) := Nat.find_min hexists hjlt
      simpa [hi] using Nat.le_of_not_gt hminimal

private theorem exists_fin_interval {count : Nat}
    {f : Fin (count + 1) → Nat}
    (hf : StrictMono f) (hzero : f ⟨0, Nat.zero_lt_succ _⟩ = 0)
    {n : Nat} (hn : n < f ⟨count, Nat.lt_succ_self _⟩) :
    ∃ i : Fin count, f i.castSucc ≤ n ∧ n < f i.succ := by
  have hexists : ∃ j : Nat, ∃ hj : j < count + 1,
      n < f ⟨j, hj⟩ :=
    ⟨count, Nat.lt_succ_self _, hn⟩
  let j := Nat.find hexists
  have hjSpec := Nat.find_spec hexists
  obtain ⟨hjBound, hjUpper⟩ := hjSpec
  have hjPos : 0 < j := by
    by_contra hj0
    have hjzero : j = 0 := Nat.eq_zero_of_not_pos hj0
    have hjUpper0 : n < f ⟨0, Nat.zero_lt_succ _⟩ := by
      have hfin : (⟨0, Nat.zero_lt_succ _⟩ : Fin (count + 1)) =
          ⟨Nat.find hexists, hjBound⟩ := by
        apply Fin.ext
        change 0 = Nat.find hexists
        exact hjzero.symm
      rw [hfin]
      exact hjUpper
    rw [hzero] at hjUpper0
    exact (Nat.not_lt_zero n) hjUpper0
  let i : Fin count := ⟨j - 1, by omega⟩
  refine ⟨i, ?_, ?_⟩
  · have hnot : ¬ n < f ⟨j - 1, by omega⟩ := by
      intro hbad
      have hsmall : j - 1 < Nat.find hexists := by
        change j - 1 < j
        omega
      exact Nat.find_min hexists hsmall ⟨by omega, hbad⟩
    exact Nat.le_of_not_gt hnot
  · have heq : i.succ = ⟨j, hjBound⟩ := by
      apply Fin.ext
      simp [i]
      omega
    rw [heq]
    exact hjUpper

structure EventualContactCoordinates (S : InfiniteInput D) (X : Set V) where
  count : Nat
  coord : Fin (count + 1) → Nat
  coord_zero : coord ⟨0, Nat.zero_lt_succ _⟩ = 0
  strictMono_coord : StrictMono coord
  coord_mem : ∀ i, S.vertex (coord i) ∈ X
  complete : ∀ {n}, S.vertex n ∈ X → n ∈ Set.range coord

structure OmegaContactCoordinates (S : InfiniteInput D) (X : Set V) where
  coord : Nat → Nat
  coord_zero : coord 0 = 0
  strictMono_coord : StrictMono coord
  coord_mem : ∀ i, S.vertex (coord i) ∈ X
  complete : ∀ {n}, S.vertex n ∈ X → n ∈ Set.range coord

inductive InfiniteContactCoordinates (S : InfiniteInput D) (X : Set V)
  | eventual (data : EventualContactCoordinates S X)
  | omega (data : OmegaContactCoordinates S X)

namespace EventualContactCoordinates

variable {S : InfiniteInput D} {X : Set V}

def last (E : EventualContactCoordinates S X) : Nat :=
  E.coord ⟨E.count, Nat.lt_succ_self _⟩

theorem no_contact_after_last (E : EventualContactCoordinates S X)
    {n : Nat} (hn : E.last < n) : S.vertex n ∉ X := by
  intro hnX
  obtain ⟨i, hi⟩ := E.complete hnX
  rw [← hi] at hn
  exact (Nat.not_lt_of_ge (E.strictMono_coord.monotone (Fin.le_last i))) hn

theorem exists_interval (E : EventualContactCoordinates S X)
    {n : Nat} (hn : n < E.last) :
    ∃ i : Fin E.count,
      E.coord i.castSucc ≤ n ∧ n < E.coord i.succ :=
  exists_fin_interval E.strictMono_coord E.coord_zero hn

def interval (E : EventualContactCoordinates S X) (i : Fin E.count) :
    FiniteInput D :=
  S.coordinateInterval (E.coord i.castSucc) (E.coord i.succ)
    (E.strictMono_coord Fin.castSucc_lt_succ)

def suffix (E : EventualContactCoordinates S X) : InfiniteInput D :=
  S.shift E.last

def suffixChanges (E : EventualContactCoordinates S X)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n) :
    ∀ n, ∃ m, n < m ∧ E.suffix.colour m ≠ E.suffix.colour n :=
  S.shift_changes hchange E.last

theorem trace_vertexSet_exact (E : EventualContactCoordinates S X)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n) :
    (S.toInfiniteRunWalk hchange).toInfiniteTrace.vertexSet =
      (⋃ i : Fin E.count,
        (E.interval i).toFiniteRunWalk.toFiniteTrace.vertexSet) ∪
      ((S.shift E.last).toInfiniteRunWalk
        (S.shift_changes hchange E.last)).toInfiniteTrace.vertexSet := by
  rw [S.toInfiniteTrace_vertexSet hchange,
    S.shift_trace_vertexSet hchange E.last]
  apply Set.Subset.antisymm
  · rintro x ⟨n, rfl⟩
    by_cases hn : E.last ≤ n
    · right
      exact ⟨n, hn, rfl⟩
    · obtain ⟨i, hlo, hhi⟩ := E.exists_interval (Nat.lt_of_not_ge hn)
      left
      simp only [Set.mem_iUnion]
      refine ⟨i, ?_⟩
      rw [EventualContactCoordinates.interval,
        S.coordinateInterval_trace_vertexSet]
      exact ⟨n, ⟨hlo, hhi.le⟩, rfl⟩
  · rintro x (hx | hx)
    · simp only [Set.mem_iUnion] at hx
      obtain ⟨i, hxi⟩ := hx
      rw [EventualContactCoordinates.interval,
        S.coordinateInterval_trace_vertexSet] at hxi
      obtain ⟨n, _hn, rfl⟩ := hxi
      exact ⟨n, rfl⟩
    · obtain ⟨n, _hn, rfl⟩ := hx
      exact ⟨n, rfl⟩

theorem trace_edgeSet_exact (E : EventualContactCoordinates S X)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n) :
    (S.toInfiniteRunWalk hchange).toInfiniteTrace.edgeSet =
      (⋃ i : Fin E.count,
        (E.interval i).toFiniteRunWalk.toFiniteTrace.edgeSet) ∪
      ((S.shift E.last).toInfiniteRunWalk
        (S.shift_changes hchange E.last)).toInfiniteTrace.edgeSet := by
  ext e
  rw [S.mem_toInfiniteTrace_edgeSet_iff hchange]
  constructor
  · rintro ⟨n, rfl⟩
    by_cases hn : E.last ≤ n
    · right
      rw [S.shift_trace_edgeSet hchange E.last]
      exact ⟨n, hn, rfl⟩
    · obtain ⟨i, hlo, hhi⟩ := E.exists_interval (Nat.lt_of_not_ge hn)
      left
      simp only [Set.mem_iUnion]
      refine ⟨i, ?_⟩
      rw [EventualContactCoordinates.interval,
        S.coordinateInterval_trace_edgeSet]
      exact ⟨n, hlo, hhi, rfl⟩
  · rintro (he | he)
    · simp only [Set.mem_iUnion] at he
      obtain ⟨i, hei⟩ := he
      rw [EventualContactCoordinates.interval,
        S.coordinateInterval_trace_edgeSet] at hei
      obtain ⟨n, _hlo, _hhi, rfl⟩ := hei
      exact ⟨n, rfl⟩
    · rw [S.shift_trace_edgeSet hchange E.last] at he
      obtain ⟨n, _hn, rfl⟩ := he
      exact ⟨n, rfl⟩

end EventualContactCoordinates

namespace OmegaContactCoordinates

variable {S : InfiniteInput D} {X : Set V}

theorem exists_interval (E : OmegaContactCoordinates S X) (n : Nat) :
    ∃ i, E.coord i ≤ n ∧ n < E.coord (i + 1) :=
  exists_nat_interval E.strictMono_coord E.coord_zero n

def interval (E : OmegaContactCoordinates S X) (i : Nat) : FiniteInput D :=
  S.coordinateInterval (E.coord i) (E.coord (i + 1))
    (E.strictMono_coord (Nat.lt_succ_self i))

theorem trace_vertexSet_exact (E : OmegaContactCoordinates S X)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n) :
    (S.toInfiniteRunWalk hchange).toInfiniteTrace.vertexSet =
      ⋃ i : Nat, (E.interval i).toFiniteRunWalk.toFiniteTrace.vertexSet := by
  rw [S.toInfiniteTrace_vertexSet hchange]
  apply Set.Subset.antisymm
  · rintro x ⟨n, rfl⟩
    obtain ⟨i, hlo, hhi⟩ := E.exists_interval n
    simp only [Set.mem_iUnion]
    refine ⟨i, ?_⟩
    rw [OmegaContactCoordinates.interval,
      S.coordinateInterval_trace_vertexSet]
    exact ⟨n, ⟨hlo, hhi.le⟩, rfl⟩
  · rintro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨i, hxi⟩ := hx
    rw [OmegaContactCoordinates.interval,
      S.coordinateInterval_trace_vertexSet] at hxi
    obtain ⟨n, _hn, rfl⟩ := hxi
    exact ⟨n, rfl⟩

theorem trace_edgeSet_exact (E : OmegaContactCoordinates S X)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n) :
    (S.toInfiniteRunWalk hchange).toInfiniteTrace.edgeSet =
      ⋃ i : Nat, (E.interval i).toFiniteRunWalk.toFiniteTrace.edgeSet := by
  ext e
  rw [S.mem_toInfiniteTrace_edgeSet_iff hchange]
  constructor
  · rintro ⟨n, rfl⟩
    obtain ⟨i, hlo, hhi⟩ := E.exists_interval n
    simp only [Set.mem_iUnion]
    refine ⟨i, ?_⟩
    rw [OmegaContactCoordinates.interval,
      S.coordinateInterval_trace_edgeSet]
    exact ⟨n, hlo, hhi, rfl⟩
  · intro he
    simp only [Set.mem_iUnion] at he
    obtain ⟨i, hei⟩ := he
    rw [OmegaContactCoordinates.interval,
      S.coordinateInterval_trace_edgeSet] at hei
    obtain ⟨n, _hlo, _hhi, rfl⟩ := hei
    exact ⟨n, rfl⟩

end OmegaContactCoordinates

/-- Enumerate all cut contacts, with a genuine infinite suffix exactly when
only finitely many contacts occur. -/
noncomputable def contactDichotomy (S : InfiniteInput D) (X : Set V)
    (hzero : S.vertex 0 ∈ X) : InfiniteContactCoordinates S X := by
  let A := S.contactCoordinates X
  by_cases hfinite : A.Finite
  · let F := hfinite.toFinset
    have hFpos : 0 < F.card := by
      rw [Finset.card_pos]
      refine ⟨0, ?_⟩
      simpa [F, A, contactCoordinates] using hzero
    let count := F.card - 1
    have hcard : F.card = count + 1 := by
      dsimp [count]
      omega
    let e : Fin (count + 1) ≃o ↑F := Finset.orderIsoOfFin F hcard
    let coord : Fin (count + 1) → Nat := fun i ↦ (e i).1
    apply InfiniteContactCoordinates.eventual
    refine ⟨count, coord, ?_, ?_, ?_, ?_⟩
    · let z : ↑F := ⟨0, by
        simpa [F, A, contactCoordinates] using hzero⟩
      let j := e.symm z
      have hle : e ⟨0, Nat.zero_lt_succ _⟩ ≤ z := by
        simpa [j] using e.monotone (Fin.zero_le j)
      exact Nat.eq_zero_of_le_zero hle
    · intro i j hij
      exact e.strictMono hij
    · intro i
      have hi : (e i).1 ∈ A := by
        simpa only [F, Set.Finite.mem_toFinset] using (e i).2
      change S.vertex (e i).1 ∈ X at hi
      change S.vertex (coord i) ∈ X
      exact hi
    · intro n hn
      let z : ↑F := ⟨n, by
        simpa [F, A, contactCoordinates] using hn⟩
      exact ⟨e.symm z, by
        change (e (e.symm z)).1 = n
        rw [e.apply_symm_apply]⟩
  · have hinfinite : A.Infinite := hfinite
    apply InfiniteContactCoordinates.omega
    refine ⟨Nat.nth (fun n ↦ S.vertex n ∈ X), ?_, ?_, ?_, ?_⟩
    · exact Nat.nth_zero_of_zero hzero
    · exact Nat.nth_strictMono hinfinite
    · exact Nat.nth_mem_of_infinite hinfinite
    · intro n hn
      rw [Nat.range_nth_of_infinite hinfinite]
      exact hn

#print axioms contactDichotomy
#print axioms EventualContactCoordinates.trace_vertexSet_exact
#print axioms EventualContactCoordinates.trace_edgeSet_exact
#print axioms OmegaContactCoordinates.trace_vertexSet_exact
#print axioms OmegaContactCoordinates.trace_edgeSet_exact

end Erdos599.Alternating.RunCompressor.InfiniteInput
