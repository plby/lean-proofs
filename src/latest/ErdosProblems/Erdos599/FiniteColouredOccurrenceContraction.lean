/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FiniteColouredOccurrenceWord
import Mathlib.Data.Finset.Sort

/-!
# Literal connector deletion in a finite coloured occurrence word

The retained indices are precisely the steps with different projected
endpoints.  Ordered enumeration contracts the intervening constant stretches.
When proper edges have unique lifts within each colour, no coloured edge is
repeated after projection.  This construction neither loop-erases vertices
nor asserts preservation of the separate interval-safeness conditions.
-/

noncomputable section

namespace Erdos599.Alternating.FiniteColouredOccurrenceWord

open Set DirectedPath

universe u v

namespace ConnectorDeletion

variable {U : Type u} {V : Type v} {n : ℕ}

/-- Exactly the chronological indices which do not contract to a vertex. -/
def properSteps (q : Fin (n + 1) → U) (π : U → V) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i ↦ π (q i.castSucc) ≠ π (q i.succ)

@[simp] theorem mem_properSteps (q : Fin (n + 1) → U) (π : U → V)
    (i : Fin n) :
    i ∈ properSteps q π ↔ π (q i.castSucc) ≠ π (q i.succ) := by
  classical
  simp [properSteps]

/-- The old index of each retained step, in its original order. -/
def properIndex (q : Fin (n + 1) → U) (π : U → V) :
    Fin (properSteps q π).card ↪o Fin n :=
  (properSteps q π).orderEmbOfFin rfl

theorem properIndex_mem (q : Fin (n + 1) → U) (π : U → V)
    (j : Fin (properSteps q π).card) :
    properIndex q π j ∈ properSteps q π :=
  Finset.orderEmbOfFin_mem _ _ _

theorem exists_properIndex (q : Fin (n + 1) → U) (π : U → V)
    {i : Fin n} (hi : i ∈ properSteps q π) :
    ∃ j, properIndex q π j = i := by
  have hr := Finset.range_orderEmbOfFin (properSteps q π) rfl
  change i ∈ Set.range ((properSteps q π).orderEmbOfFin rfl)
  rw [hr]
  exact hi

theorem projected_eq_of_no_proper_between
    (q : Fin (n + 1) → U) (π : U → V)
    (a b : Fin (n + 1)) (hab : a ≤ b)
    (hgap : ∀ i : Fin n, a.val ≤ i.val → i.val < b.val →
      i ∉ properSteps q π) :
    π (q a) = π (q b) := by
  induction b using Fin.induction with
  | zero =>
      have ha : a = 0 := by
        apply Fin.ext
        change a.val ≤ 0 at hab
        change a.val = 0
        omega
      rw [ha]
  | succ b ih =>
      by_cases hab' : a ≤ b.castSucc
      · have hpre := ih hab' (fun i hai hib ↦ hgap i hai (by
          change i.val < b.val at hib
          change i.val < b.val + 1
          omega))
        have hnot : b ∉ properSteps q π := hgap b (by exact hab') (by simp)
        have heq : π (q b.castSucc) = π (q b.succ) := by
          simpa only [mem_properSteps, not_not] using hnot
        exact hpre.trans heq
      · have ha : a = b.succ := by
          apply Fin.ext
          change a.val ≤ b.val + 1 at hab
          change ¬ a.val ≤ b.val at hab'
          change a.val = b.val + 1
          omega
        rw [ha]

/-- Contracted vertices, keeping the projected final vertex even when all
steps contract. -/
def vertex (q : Fin (n + 1) → U) (π : U → V)
    (j : Fin ((properSteps q π).card + 1)) : V :=
  if h : j.val < (properSteps q π).card then
    π (q (properIndex q π ⟨j.val, h⟩).castSucc)
  else π (q (Fin.last n))

@[simp] theorem vertex_last (q : Fin (n + 1) → U) (π : U → V) :
    vertex q π (Fin.last (properSteps q π).card) = π (q (Fin.last n)) := by
  simp [vertex]

@[simp] theorem vertex_castSucc (q : Fin (n + 1) → U) (π : U → V)
    (j : Fin (properSteps q π).card) :
    vertex q π j.castSucc = π (q (properIndex q π j).castSucc) := by
  simp [vertex, j.isLt]

theorem vertex_first (q : Fin (n + 1) → U) (π : U → V) :
    vertex q π 0 = π (q 0) := by
  by_cases hm : 0 < (properSteps q π).card
  · let j : Fin (properSteps q π).card := ⟨0, hm⟩
    have hgap : ∀ i : Fin n, 0 ≤ i.val →
        i.val < (properIndex q π j).val → i ∉ properSteps q π := by
      intro i _ hi himem
      obtain ⟨k, hk⟩ := exists_properIndex q π himem
      have hkj : k < j := (properIndex q π).lt_iff_lt.mp (by
        rw [hk]
        exact hi)
      have : k.val < 0 := hkj
      omega
    have h := projected_eq_of_no_proper_between q π 0
      (properIndex q π j).castSucc (Fin.zero_le _) hgap
    simpa [vertex, hm, j] using h.symm
  · have hgap : ∀ i : Fin n, 0 ≤ i.val → i.val < n →
        i ∉ properSteps q π := by
      intro i _ _ himem
      obtain ⟨j, _⟩ := exists_properIndex q π himem
      exact hm (Nat.zero_lt_of_lt j.isLt)
    have h := projected_eq_of_no_proper_between q π 0 (Fin.last n)
      (Fin.zero_le _) hgap
    simpa [vertex, hm] using h.symm

theorem vertex_succ (q : Fin (n + 1) → U) (π : U → V)
    (j : Fin (properSteps q π).card) :
    vertex q π j.succ = π (q (properIndex q π j).succ) := by
  by_cases hj : j.val + 1 < (properSteps q π).card
  · let k : Fin (properSteps q π).card := ⟨j.val + 1, hj⟩
    have hjk : j < k := by exact Nat.lt_succ_self j.val
    have hindices : properIndex q π j < properIndex q π k :=
      (properIndex q π).strictMono hjk
    have hgap : ∀ i : Fin n,
        (properIndex q π j).val + 1 ≤ i.val →
        i.val < (properIndex q π k).val → i ∉ properSteps q π := by
      intro i hlo hhi himem
      obtain ⟨l, hl⟩ := exists_properIndex q π himem
      have hjl : j < l := (properIndex q π).lt_iff_lt.mp (by rw [hl]; exact hlo)
      have hlk : l < k := (properIndex q π).lt_iff_lt.mp (by rw [hl]; exact hhi)
      simp only [Fin.lt_def] at hjl hlk
      change l.val < j.val + 1 at hlk
      omega
    have h := projected_eq_of_no_proper_between q π
      (properIndex q π j).succ (properIndex q π k).castSucc
      (by exact hindices) hgap
    simpa [vertex, hj, k] using h.symm
  · have hgap : ∀ i : Fin n,
        (properIndex q π j).val + 1 ≤ i.val → i.val < n →
        i ∉ properSteps q π := by
      intro i hlo _ himem
      obtain ⟨l, hl⟩ := exists_properIndex q π himem
      have hjl : j < l := (properIndex q π).lt_iff_lt.mp (by rw [hl]; exact hlo)
      have hl := l.isLt
      simp only [Fin.lt_def] at hjl
      omega
    have h := projected_eq_of_no_proper_between q π
      (properIndex q π j).succ (Fin.last n) (Fin.le_last _) hgap
    simpa [vertex, hj] using h.symm

theorem vertex_mem_image (q : Fin (n + 1) → U) (π : U → V)
    (j : Fin ((properSteps q π).card + 1)) :
    vertex q π j ∈ π '' Set.range q := by
  unfold vertex
  split
  · exact ⟨_, ⟨_, rfl⟩, rfl⟩
  · exact ⟨_, ⟨_, rfl⟩, rfl⟩

end ConnectorDeletion

variable {U : Type u} {V : Type v} {Delta : DWeb U} {Gamma : DWeb V}
variable {Wup Yup : Set Delta.DPath} {W Y : Set Gamma.DPath}

/-- Projection of an edge in its graph orientation. -/
def mapEdge (π : U → V) (e : U × U) : V × V := (π e.1, π e.2)

private theorem actualEdge_projects_proper
    (Q : FiniteColouredOccurrenceWord Wup Yup) (π : U → V)
    {i : Fin Q.length} (hi : i ∈ ConnectorDeletion.properSteps Q.vertex π) :
    π (Q.actualEdge i).1 ≠ π (Q.actualEdge i).2 := by
  have hne := (ConnectorDeletion.mem_properSteps Q.vertex π i).mp hi
  cases hdir : Q.direction i with
  | forward => simpa [actualEdge, hdir] using hne
  | backward => simpa [actualEdge, hdir] using hne.symm

private theorem projected_actualEdge_eq
    (Q : FiniteColouredOccurrenceWord Wup Yup) (π : U → V)
    (j : Fin (ConnectorDeletion.properSteps Q.vertex π).card) :
    (match Q.direction (ConnectorDeletion.properIndex Q.vertex π j) with
    | .forward => (ConnectorDeletion.vertex Q.vertex π j.castSucc,
        ConnectorDeletion.vertex Q.vertex π j.succ)
    | .backward => (ConnectorDeletion.vertex Q.vertex π j.succ,
        ConnectorDeletion.vertex Q.vertex π j.castSucc)) =
      mapEdge π (Q.actualEdge (ConnectorDeletion.properIndex Q.vertex π j)) := by
  rw [ConnectorDeletion.vertex_castSucc, ConnectorDeletion.vertex_succ]
  cases hdir : Q.direction (ConnectorDeletion.properIndex Q.vertex π j) <;>
    simp [actualEdge, hdir, mapEdge]

/-- Delete exactly the connector occurrences. Proper-edge projection must
be faithful in each colour; no claim about interval safeness is assumed. -/
def contract (Q : FiniteColouredOccurrenceWord Wup Yup) (π : U → V)
    (hforward : ∀ e ∈ familyEdges Wup, π e.1 ≠ π e.2 → mapEdge π e ∈ familyEdges W)
    (hbackward : ∀ e ∈ familyEdges Yup, π e.1 ≠ π e.2 → mapEdge π e ∈ familyEdges Y)
    (hforwardUnique : Set.InjOn (mapEdge π)
      {e | e ∈ familyEdges Wup ∧ π e.1 ≠ π e.2})
    (hbackwardUnique : Set.InjOn (mapEdge π)
      {e | e ∈ familyEdges Yup ∧ π e.1 ≠ π e.2}) :
    FiniteColouredOccurrenceWord W Y where
  length := (ConnectorDeletion.properSteps Q.vertex π).card
  vertex := ConnectorDeletion.vertex Q.vertex π
  direction := fun j ↦ Q.direction (ConnectorDeletion.properIndex Q.vertex π j)
  actualEdge_spec := by
    intro j
    let i := ConnectorDeletion.properIndex Q.vertex π j
    have hi : π (Q.actualEdge i).1 ≠ π (Q.actualEdge i).2 :=
      actualEdge_projects_proper Q π (ConnectorDeletion.properIndex_mem Q.vertex π j)
    have hs := Q.actualEdge_spec i
    rw [ConnectorDeletion.vertex_castSucc, ConnectorDeletion.vertex_succ]
    change match Q.direction i with
      | .forward => _
      | .backward => _
    cases hdir : Q.direction i with
    | forward =>
        simpa only [actualEdge, hdir, mapEdge] using
          hforward (Q.actualEdge i) (by simpa [actualEdge, hdir] using hs) hi
    | backward =>
        simpa only [actualEdge, hdir, mapEdge] using
          hbackward (Q.actualEdge i) (by simpa [actualEdge, hdir] using hs) hi
  occurrence_injective := by
    intro j k hjk
    have hdir : Q.direction (ConnectorDeletion.properIndex Q.vertex π j) =
        Q.direction (ConnectorDeletion.properIndex Q.vertex π k) :=
      congrArg Prod.fst hjk
    have hedge := congrArg Prod.snd hjk
    dsimp only at hedge
    have hedge' := (projected_actualEdge_eq Q π j).symm.trans
      (hedge.trans (projected_actualEdge_eq Q π k))
    have hjProper := actualEdge_projects_proper Q π
      (ConnectorDeletion.properIndex_mem Q.vertex π j)
    have hkProper := actualEdge_projects_proper Q π
      (ConnectorDeletion.properIndex_mem Q.vertex π k)
    have hjSpec := Q.actualEdge_spec (ConnectorDeletion.properIndex Q.vertex π j)
    have hkSpec := Q.actualEdge_spec (ConnectorDeletion.properIndex Q.vertex π k)
    apply (ConnectorDeletion.properIndex Q.vertex π).injective
    apply Q.occurrence_injective
    apply Prod.ext hdir
    change Q.actualEdge (ConnectorDeletion.properIndex Q.vertex π j) =
      Q.actualEdge (ConnectorDeletion.properIndex Q.vertex π k)
    cases hjdir : Q.direction (ConnectorDeletion.properIndex Q.vertex π j) with
    | forward =>
        have hkdir := hdir.symm.trans hjdir
        exact hforwardUnique ⟨by simpa [actualEdge, hjdir] using hjSpec, hjProper⟩
          ⟨by simpa [actualEdge, hkdir] using hkSpec, hkProper⟩ hedge'
    | backward =>
        have hkdir := hdir.symm.trans hjdir
        exact hbackwardUnique ⟨by simpa [actualEdge, hjdir] using hjSpec, hjProper⟩
          ⟨by simpa [actualEdge, hkdir] using hkSpec, hkProper⟩ hedge'

section ContractProperties

variable (Q : FiniteColouredOccurrenceWord Wup Yup) (π : U → V)
    (hforward : ∀ e ∈ familyEdges Wup, π e.1 ≠ π e.2 → mapEdge π e ∈ familyEdges W)
    (hbackward : ∀ e ∈ familyEdges Yup, π e.1 ≠ π e.2 → mapEdge π e ∈ familyEdges Y)
    (hforwardUnique : Set.InjOn (mapEdge π)
      {e | e ∈ familyEdges Wup ∧ π e.1 ≠ π e.2})
    (hbackwardUnique : Set.InjOn (mapEdge π)
      {e | e ∈ familyEdges Yup ∧ π e.1 ≠ π e.2})

local notation "P" => Q.contract π hforward hbackward hforwardUnique hbackwardUnique

@[simp] theorem contract_first : (P).vertex 0 = π (Q.vertex 0) :=
  ConnectorDeletion.vertex_first Q.vertex π

@[simp] theorem contract_last :
    (P).vertex (Fin.last (P).length) = π (Q.vertex (Fin.last Q.length)) :=
  ConnectorDeletion.vertex_last Q.vertex π

theorem contract_actualEdge (j : Fin (P).length) :
    (P).actualEdge j =
      mapEdge π (Q.actualEdge (ConnectorDeletion.properIndex Q.vertex π j)) :=
  projected_actualEdge_eq Q π j

theorem contract_vertexSet_subset : (P).vertexSet ⊆ π '' Q.vertexSet := by
  rintro _ ⟨j, rfl⟩
  exact ConnectorDeletion.vertex_mem_image Q.vertex π j

theorem contract_forwardEdges :
    (P).forwardEdges = mapEdge π '' {e | e ∈ Q.forwardEdges ∧ π e.1 ≠ π e.2} := by
  ext e
  constructor
  · rintro ⟨j, rfl⟩
    let i := ConnectorDeletion.properIndex Q.vertex π j.1
    have hi : Q.direction i = .forward := j.2
    refine ⟨Q.actualEdge i, ⟨?_, ?_⟩, ?_⟩
    · exact ⟨⟨i, hi⟩, rfl⟩
    · exact actualEdge_projects_proper Q π
        (ConnectorDeletion.properIndex_mem Q.vertex π j.1)
    · exact (contract_actualEdge Q π hforward hbackward hforwardUnique hbackwardUnique
        j.1).symm
  · rintro ⟨e, ⟨⟨i, rfl⟩, hiProper⟩, rfl⟩
    have hi : i.1 ∈ ConnectorDeletion.properSteps Q.vertex π := by
      rw [ConnectorDeletion.mem_properSteps]
      simpa [forwardEdge, actualEdge, i.2] using hiProper
    obtain ⟨j, hj⟩ := ConnectorDeletion.exists_properIndex Q.vertex π hi
    have hjdir : (P).direction j = .forward := by
      change Q.direction (ConnectorDeletion.properIndex Q.vertex π j) = .forward
      rw [hj]
      exact i.2
    refine ⟨⟨j, hjdir⟩, ?_⟩
    change (P).actualEdge j = mapEdge π (Q.actualEdge i.1)
    exact (contract_actualEdge Q π hforward hbackward hforwardUnique hbackwardUnique
      j).trans (congrArg (fun i ↦ mapEdge π (Q.actualEdge i)) hj)

theorem contract_backwardEdges :
    (P).backwardEdges = mapEdge π '' {e | e ∈ Q.backwardEdges ∧ π e.1 ≠ π e.2} := by
  ext e
  constructor
  · rintro ⟨j, rfl⟩
    let i := ConnectorDeletion.properIndex Q.vertex π j.1
    have hi : Q.direction i ≠ .forward := j.2
    refine ⟨Q.actualEdge i, ⟨?_, ?_⟩, ?_⟩
    · exact ⟨⟨i, hi⟩, rfl⟩
    · exact actualEdge_projects_proper Q π
        (ConnectorDeletion.properIndex_mem Q.vertex π j.1)
    · exact (contract_actualEdge Q π hforward hbackward hforwardUnique hbackwardUnique
        j.1).symm
  · rintro ⟨e, ⟨⟨i, rfl⟩, hiProper⟩, rfl⟩
    have hi : i.1 ∈ ConnectorDeletion.properSteps Q.vertex π := by
      rw [ConnectorDeletion.mem_properSteps]
      have hdir := Q.backwardIndex_direction i
      have hne : π (Q.vertex i.1.succ) ≠ π (Q.vertex i.1.castSucc) := by
        simpa [backwardEdge, actualEdge, hdir] using hiProper
      exact hne.symm
    obtain ⟨j, hj⟩ := ConnectorDeletion.exists_properIndex Q.vertex π hi
    have hjdir : (P).direction j ≠ .forward := by
      change Q.direction (ConnectorDeletion.properIndex Q.vertex π j) ≠ .forward
      rw [hj]
      exact i.2
    refine ⟨⟨j, hjdir⟩, ?_⟩
    change (P).actualEdge j = mapEdge π (Q.actualEdge i.1)
    exact (contract_actualEdge Q π hforward hbackward hforwardUnique hbackwardUnique
      j).trans (congrArg (fun i ↦ mapEdge π (Q.actualEdge i)) hj)

end ContractProperties

#print axioms ConnectorDeletion.vertex_first
#print axioms ConnectorDeletion.vertex_succ
#print axioms contract
#print axioms contract_forwardEdges
#print axioms contract_backwardEdges

end Erdos599.Alternating.FiniteColouredOccurrenceWord
