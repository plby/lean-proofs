/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The finite lexicographic minimal-counterexample package used in the
Thomas--Wollan massed-pair argument.
-/

import ErdosProblems.Erdos717.TerminalCompletion

open Function Set
open SimpleGraph

namespace Erdos717
namespace ThomasWollanMassed

/-- A counterexample to the eight-massed linkage theorem, including the
finite and decidability data needed to count its edges. -/
structure MassedCounterexample (k : ℕ) where
  V : Type
  fintypeV : Fintype V
  decEqV : DecidableEq V
  G : SimpleGraph V
  decAdj : DecidableRel G.Adj
  X : Finset V
  card_le : X.card ≤ 2 * k
  massed : @IsEightKMassed V fintypeV decEqV G decAdj X k
  not_linked : ¬ Erdos718.IsLinkedSet G (X : Set V)

attribute [instance] MassedCounterexample.fintypeV
  MassedCounterexample.decEqV MassedCounterexample.decAdj

namespace MassedCounterexample

variable {k : ℕ}

def vertexCount (C : MassedCounterexample k) : ℕ := Fintype.card C.V

def outsideEdges (C : MassedCounterexample k) : ℕ :=
  incidentEdges C.G (Finset.univ \ C.X)

def insideEdges (C : MassedCounterexample k) : ℕ :=
  Erdos718.MaderPrototype.edgesOn C.G C.X

lemma insideEdges_le_vertexCount_sq (C : MassedCounterexample k) :
    C.insideEdges ≤ C.vertexCount ^ 2 := by
  unfold insideEdges vertexCount
  calc
    Erdos718.MaderPrototype.edgesOn C.G C.X ≤ C.X.card ^ 2 :=
      Erdos718.MaderPrototype.edgesOn_le_square C.G C.X
    _ ≤ Fintype.card C.V ^ 2 := by
      exact Nat.pow_le_pow_left (Finset.card_le_univ C.X) 2

/-- The three clauses of Thomas--Wollan minimality: minimize the number of
vertices, then the number of edges incident with the outside, and finally
maximize the number of edges internal to the distinguished set. -/
def IsLexMinimal (C : MassedCounterexample k) : Prop :=
  ∀ D : MassedCounterexample k,
    C.vertexCount ≤ D.vertexCount ∧
    (C.vertexCount = D.vertexCount → C.outsideEdges ≤ D.outsideEdges) ∧
    (C.vertexCount = D.vertexCount → C.outsideEdges = D.outsideEdges →
      D.insideEdges ≤ C.insideEdges)

/-- A nonempty collection of counterexamples has a Thomas--Wollan
lexicographically minimal member.  This is a genuine finite-measure
selection, even though the represented vertex types may differ. -/
theorem exists_lexMinimal (hbad : Nonempty (MassedCounterexample k)) :
    ∃ C : MassedCounterexample k, C.IsLexMinimal := by
  classical
  let Pn : ℕ → Prop := fun n =>
    ∃ C : MassedCounterexample k, C.vertexCount = n
  have hn : ∃ n, Pn n := by
    obtain ⟨C⟩ := hbad
    exact ⟨C.vertexCount, C, rfl⟩
  let n0 := Nat.find hn
  obtain ⟨Cn, hCn⟩ := Nat.find_spec hn
  let Pm : ℕ → Prop := fun m =>
    ∃ C : MassedCounterexample k,
      C.vertexCount = n0 ∧ C.outsideEdges = m
  have hm : ∃ m, Pm m := ⟨Cn.outsideEdges, Cn, hCn, rfl⟩
  let m0 := Nat.find hm
  obtain ⟨Cm, hCmn, hCmm⟩ := Nat.find_spec hm
  let Pq : ℕ → Prop := fun q =>
    ∃ C : MassedCounterexample k,
      C.vertexCount = n0 ∧ C.outsideEdges = m0 ∧ C.insideEdges = q
  have hqbound : Cm.insideEdges ≤ n0 ^ 2 := by
    rw [← hCmn]
    exact Cm.insideEdges_le_vertexCount_sq
  have hq : Pq Cm.insideEdges := ⟨Cm, hCmn, hCmm, rfl⟩
  let q0 := Nat.findGreatest Pq (n0 ^ 2)
  obtain ⟨C, hCn0, hCm0, hCq0⟩ :=
    Nat.findGreatest_spec (P := Pq) hqbound hq
  refine ⟨C, ?_⟩
  intro D
  have hnle : n0 ≤ D.vertexCount :=
    Nat.find_min' hn ⟨D, rfl⟩
  have hvertex : C.vertexCount ≤ D.vertexCount := by
    rw [hCn0]
    exact hnle
  refine ⟨hvertex, ?_, ?_⟩
  · intro heq
    have hDn : D.vertexCount = n0 := heq.symm.trans hCn0
    have hmle : m0 ≤ D.outsideEdges :=
      Nat.find_min' hm ⟨D, hDn, rfl⟩
    rwa [hCm0]
  · intro heqV heqM
    have hDn : D.vertexCount = n0 := heqV.symm.trans hCn0
    have hDm : D.outsideEdges = m0 := heqM.symm.trans hCm0
    have hDqBound : D.insideEdges ≤ n0 ^ 2 := by
      rw [← hDn]
      exact D.insideEdges_le_vertexCount_sq
    have hDq : Pq D.insideEdges := ⟨D, hDn, hDm, rfl⟩
    have := Nat.le_findGreatest (P := Pq) hDqBound hDq
    rwa [hCq0]

/-- A concrete pairing which witnesses failure of linkedness. -/
structure FailedPairing (C : MassedCounterexample k) where
  ι : Type
  fintypeι : Fintype ι
  terminal : Sum ι ι ↪ C.V
  range_subset : Set.range terminal ⊆ (C.X : Set C.V)
  no_linkage : ¬Nonempty
    (Erdos718.PairLinkage C.G (C.X : Set C.V) terminal)

attribute [instance] FailedPairing.fintypeι

theorem exists_failedPairing (C : MassedCounterexample k) :
    Nonempty (FailedPairing C) := by
  classical
  have hnot := C.not_linked
  unfold Erdos718.IsLinkedSet at hnot
  push Not at hnot
  obtain ⟨ι, inst, terminal, hsubset, hfail⟩ := hnot
  let : Fintype ι := inst
  exact ⟨{
    ι := ι
    fintypeι := inst
    terminal := terminal
    range_subset := hsubset
    no_linkage := fun ⟨L⟩ => hfail.false L
  }⟩

lemma FailedPairing.terminalFinset_subset (C : MassedCounterexample k)
    (F : FailedPairing C) : terminalFinset F.terminal ⊆ C.X := by
  intro x hx
  exact F.range_subset (mem_terminalFinset.mp hx)

/-- The last (edge-maximizing) clause of minimality makes every harmless
pair of terminals adjacent for a fixed failed pairing. -/
theorem adjacent_of_lexMinimal_of_terminal_notPaired
    (C : MassedCounterexample k) (hmin : C.IsLexMinimal)
    (F : FailedPairing C) {u v : C.V}
    (hu : u ∈ C.X) (hv : v ∈ C.X)
    (hne : u ≠ v) (hnotPaired : ¬ArePaired F.terminal u v) :
    C.G.Adj u v := by
  classical
  by_contra hnotAdj
  let H : SimpleGraph C.V := setCompletion C.G (C.X : Set C.V) F.terminal
  let : DecidableRel H.Adj := Classical.decRel H.Adj
  have hmassedH : IsEightKMassed H C.X k := by
    exact isEightKMassed_setCompletion C.G C.X F.terminal k C.massed
  have hnotLinkedH : ¬Erdos718.IsLinkedSet H (C.X : Set C.V) := by
    intro hlinked
    have hLH : Nonempty
        (Erdos718.PairLinkage H (C.X : Set C.V) F.terminal) :=
      hlinked F.ι F.terminal F.range_subset
    have hLG : Nonempty
        (Erdos718.PairLinkage C.G (C.X : Set C.V) F.terminal) := by
      exact hLH.map (fun L =>
        Erdos717.ThomasWollanMassed.Erdos718.PairLinkage.ofSetCompletion L)
    exact F.no_linkage hLG
  let D : MassedCounterexample k := {
    V := C.V
    fintypeV := C.fintypeV
    decEqV := C.decEqV
    G := H
    decAdj := inferInstance
    X := C.X
    card_le := C.card_le
    massed := hmassedH
    not_linked := hnotLinkedH
  }
  have houtEq : C.outsideEdges = D.outsideEdges := by
    unfold outsideEdges
    dsimp only [D]
    exact (incidentEdges_setCompletion C.G C.X (Finset.univ \ C.X)
      F.terminal Finset.sdiff_disjoint).symm
  have hinsideLt : C.insideEdges < D.insideEdges := by
    unfold insideEdges
    dsimp only [D]
    exact edgesOn_lt_setCompletion C.G C.X F.terminal hu hv hne
      hnotPaired hnotAdj
  have hmax := (hmin D).2.2 (by rfl) houtEq
  exact (Nat.not_lt_of_ge hmax) hinsideLt

end MassedCounterexample

end ThomasWollanMassed
end Erdos717
