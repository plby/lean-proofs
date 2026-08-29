/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FiniteColouredOccurrenceContraction
import ErdosProblems.Erdos599.InfiniteColouredOccurrenceBalance
import Mathlib.Data.Nat.Nth
import Mathlib.Order.Interval.Set.Infinite

/-!
# Infinite connector deletion

Finite projection fibres and occurrence freshness rule out an eventual
connector-only tail. Increasing enumeration of the remaining steps gives an
actual infinite word, preserving colours and the exact projected relations.
Interval safeness is a separate geometric transport obligation.
-/

noncomputable section

namespace Erdos599.Alternating.InfiniteColouredOccurrenceWord

open Set DirectedPath
open FiniteColouredOccurrenceWord (mapEdge)

universe u v

variable {U : Type u} {V : Type v} {Delta : DWeb U} {Gamma : DWeb V}
variable {Wup Yup : Set Delta.DPath} {W Y : Set Gamma.DPath}

/-- Indices of transitions which do not collapse under projection. -/
def ProperStep (Q : InfiniteColouredOccurrenceWord Wup Yup) (π : U → V)
    (n : ℕ) : Prop := π (Q.vertex n) ≠ π (Q.vertex (n + 1))

theorem projected_vertex_preimage_finite
    (Q : InfiniteColouredOccurrenceWord Wup Yup) (π : U → V)
    (hW : Delta.IsWarp Wup) (hY : Delta.IsWarp Yup)
    (hfibre : ∀ x : V, (π ⁻¹' {x}).Finite) (x : V) :
    {n : ℕ | π (Q.vertex n) = x}.Finite := by
  have h := (hfibre x).biUnion fun y _ ↦ Q.vertex_preimage_finite hW hY y
  apply h.subset
  intro n hn
  exact Set.mem_iUnion.mpr ⟨Q.vertex n,
    Set.mem_iUnion.mpr ⟨hn, rfl⟩⟩

private theorem projected_eq_of_no_proper_between
    (Q : InfiniteColouredOccurrenceWord Wup Yup) (π : U → V)
    {a b : ℕ} (hab : a ≤ b)
    (hgap : ∀ i, a ≤ i → i < b → ¬ Q.ProperStep π i) :
    π (Q.vertex a) = π (Q.vertex b) := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
      have hpre := ih (fun i hai hib ↦ hgap i hai (by omega))
      have heq : π (Q.vertex b) = π (Q.vertex (b + 1)) :=
        not_not.mp (hgap b hab (by omega))
      exact hpre.trans heq

/-- An infinite word cannot become eventually constant under a finite-fibre
projection. Consequently there are infinitely many retained transitions. -/
theorem properSteps_infinite
    (Q : InfiniteColouredOccurrenceWord Wup Yup) (π : U → V)
    (hW : Delta.IsWarp Wup) (hY : Delta.IsWarp Yup)
    (hfibre : ∀ x : V, (π ⁻¹' {x}).Finite) :
    {n | Q.ProperStep π n}.Infinite := by
  intro hfinite
  obtain ⟨N, hN⟩ := hfinite.bddAbove
  have hconst : ∀ n, N + 1 ≤ n →
      π (Q.vertex (N + 1)) = π (Q.vertex n) := by
    intro n hn
    apply projected_eq_of_no_proper_between Q π hn
    intro i hi _ hproper
    have hle : i ≤ N := hN hproper
    omega
  have hf := Q.projected_vertex_preimage_finite π hW hY hfibre
    (π (Q.vertex (N + 1)))
  exact (Set.Ici_infinite (N + 1)) (hf.subset fun n hn ↦ (hconst n hn).symm)

/-- Increasing enumeration of all actual nonconnector occurrences. -/
def properIndex (Q : InfiniteColouredOccurrenceWord Wup Yup) (π : U → V) : ℕ → ℕ :=
  Nat.nth (Q.ProperStep π)

theorem properIndex_mem
    (Q : InfiniteColouredOccurrenceWord Wup Yup) (π : U → V)
    (hproper : {n | Q.ProperStep π n}.Infinite) (j : ℕ) :
    Q.ProperStep π (Q.properIndex π j) :=
  Nat.nth_mem_of_infinite hproper j

theorem properIndex_strictMono
    (Q : InfiniteColouredOccurrenceWord Wup Yup) (π : U → V)
    (hproper : {n | Q.ProperStep π n}.Infinite) : StrictMono (Q.properIndex π) :=
  Nat.nth_strictMono hproper

theorem exists_properIndex
    (Q : InfiniteColouredOccurrenceWord Wup Yup) (π : U → V)
    {i : ℕ} (hi : Q.ProperStep π i) : ∃ j, Q.properIndex π j = i :=
  Nat.subset_range_nth hi

theorem projected_properIndex_zero
    (Q : InfiniteColouredOccurrenceWord Wup Yup) (π : U → V)
    (hproper : {n | Q.ProperStep π n}.Infinite) :
    π (Q.vertex (Q.properIndex π 0)) = π (Q.vertex 0) := by
  symm
  apply projected_eq_of_no_proper_between Q π (Nat.zero_le _)
  intro i _ hi hmem
  obtain ⟨j, hj⟩ := Q.exists_properIndex π hmem
  have hlt : j < 0 := (Q.properIndex_strictMono π hproper).lt_iff_lt.mp (by
    rw [hj]
    exact hi)
  omega

theorem projected_properIndex_succ
    (Q : InfiniteColouredOccurrenceWord Wup Yup) (π : U → V)
    (hproper : {n | Q.ProperStep π n}.Infinite) (j : ℕ) :
    π (Q.vertex (Q.properIndex π (j + 1))) =
      π (Q.vertex (Q.properIndex π j + 1)) := by
  symm
  have hmono := Q.properIndex_strictMono π hproper
  apply projected_eq_of_no_proper_between Q π (hmono (Nat.lt_succ_self j))
  intro i hlo hhi hmem
  obtain ⟨k, hk⟩ := Q.exists_properIndex π hmem
  have hjk : j < k := hmono.lt_iff_lt.mp (by rw [hk]; exact hlo)
  have hkj : k < j + 1 := hmono.lt_iff_lt.mp (by rw [hk]; exact hhi)
  omega

private theorem actualEdge_projects_proper
    (Q : InfiniteColouredOccurrenceWord Wup Yup) (π : U → V)
    {i : ℕ} (hi : Q.ProperStep π i) :
    π (Q.actualEdge i).1 ≠ π (Q.actualEdge i).2 := by
  change π (Q.vertex i) ≠ π (Q.vertex (i + 1)) at hi
  cases hdir : Q.direction i with
  | forward => simpa [actualEdge, hdir] using hi
  | backward => simpa [actualEdge, hdir] using hi.symm

private theorem projected_actualEdge_eq
    (Q : InfiniteColouredOccurrenceWord Wup Yup) (π : U → V)
    (hproper : {n | Q.ProperStep π n}.Infinite) (j : ℕ) :
    (match Q.direction (Q.properIndex π j) with
    | .forward => (π (Q.vertex (Q.properIndex π j)),
        π (Q.vertex (Q.properIndex π (j + 1))))
    | .backward => (π (Q.vertex (Q.properIndex π (j + 1))),
        π (Q.vertex (Q.properIndex π j)))) =
      mapEdge π (Q.actualEdge (Q.properIndex π j)) := by
  rw [Q.projected_properIndex_succ π hproper]
  cases hdir : Q.direction (Q.properIndex π j) <;>
    simp [actualEdge, hdir, mapEdge]

/-- Infinite chronological connector contraction. The infinitude premise is
proved by `properSteps_infinite` for finite-fibre projections of warp words. -/
def contract (Q : InfiniteColouredOccurrenceWord Wup Yup) (π : U → V)
    (hproper : {n | Q.ProperStep π n}.Infinite)
    (hforward : ∀ e ∈ familyEdges Wup, π e.1 ≠ π e.2 → mapEdge π e ∈ familyEdges W)
    (hbackward : ∀ e ∈ familyEdges Yup, π e.1 ≠ π e.2 → mapEdge π e ∈ familyEdges Y)
    (hforwardUnique : Set.InjOn (mapEdge π)
      {e | e ∈ familyEdges Wup ∧ π e.1 ≠ π e.2})
    (hbackwardUnique : Set.InjOn (mapEdge π)
      {e | e ∈ familyEdges Yup ∧ π e.1 ≠ π e.2}) :
    InfiniteColouredOccurrenceWord W Y where
  vertex := fun j ↦ π (Q.vertex (Q.properIndex π j))
  direction := fun j ↦ Q.direction (Q.properIndex π j)
  actualEdge_spec := by
    intro j
    rw [Q.projected_properIndex_succ π hproper]
    have hi := actualEdge_projects_proper Q π (Q.properIndex_mem π hproper j)
    have hs := Q.actualEdge_spec (Q.properIndex π j)
    cases hdir : Q.direction (Q.properIndex π j) with
    | forward =>
        simpa only [actualEdge, hdir, mapEdge] using
          hforward (Q.actualEdge (Q.properIndex π j))
            (by simpa [actualEdge, hdir] using hs) hi
    | backward =>
        simpa only [actualEdge, hdir, mapEdge] using
          hbackward (Q.actualEdge (Q.properIndex π j))
            (by simpa [actualEdge, hdir] using hs) hi
  occurrence_injective := by
    intro j k hjk
    have hdir : Q.direction (Q.properIndex π j) = Q.direction (Q.properIndex π k) :=
      congrArg Prod.fst hjk
    have hedge := congrArg Prod.snd hjk
    dsimp only at hedge
    have hedge' := (projected_actualEdge_eq Q π hproper j).symm.trans
      (hedge.trans (projected_actualEdge_eq Q π hproper k))
    have hjProper := actualEdge_projects_proper Q π (Q.properIndex_mem π hproper j)
    have hkProper := actualEdge_projects_proper Q π (Q.properIndex_mem π hproper k)
    have hjSpec := Q.actualEdge_spec (Q.properIndex π j)
    have hkSpec := Q.actualEdge_spec (Q.properIndex π k)
    apply (Q.properIndex_strictMono π hproper).injective
    apply Q.occurrence_injective
    apply Prod.ext hdir
    change Q.actualEdge (Q.properIndex π j) = Q.actualEdge (Q.properIndex π k)
    cases hjdir : Q.direction (Q.properIndex π j) with
    | forward =>
        have hkdir := hdir.symm.trans hjdir
        exact hforwardUnique ⟨by simpa [actualEdge, hjdir] using hjSpec, hjProper⟩
          ⟨by simpa [actualEdge, hkdir] using hkSpec, hkProper⟩ hedge'
    | backward =>
        have hkdir := hdir.symm.trans hjdir
        exact hbackwardUnique ⟨by simpa [actualEdge, hjdir] using hjSpec, hjProper⟩
          ⟨by simpa [actualEdge, hkdir] using hkSpec, hkProper⟩ hedge'

section ContractProperties

variable (Q : InfiniteColouredOccurrenceWord Wup Yup) (π : U → V)
    (hproper : {n | Q.ProperStep π n}.Infinite)
    (hforward : ∀ e ∈ familyEdges Wup, π e.1 ≠ π e.2 → mapEdge π e ∈ familyEdges W)
    (hbackward : ∀ e ∈ familyEdges Yup, π e.1 ≠ π e.2 → mapEdge π e ∈ familyEdges Y)
    (hforwardUnique : Set.InjOn (mapEdge π)
      {e | e ∈ familyEdges Wup ∧ π e.1 ≠ π e.2})
    (hbackwardUnique : Set.InjOn (mapEdge π)
      {e | e ∈ familyEdges Yup ∧ π e.1 ≠ π e.2})

local notation "P" => Q.contract π hproper hforward hbackward hforwardUnique hbackwardUnique

@[simp] theorem contract_first : (P).vertex 0 = π (Q.vertex 0) :=
  Q.projected_properIndex_zero π hproper

theorem contract_actualEdge (j : ℕ) :
    (P).actualEdge j = mapEdge π (Q.actualEdge (Q.properIndex π j)) :=
  projected_actualEdge_eq Q π hproper j

theorem contract_vertexSet_subset : (P).vertexSet ⊆ π '' Q.vertexSet := by
  rintro _ ⟨j, rfl⟩
  exact ⟨Q.vertex (Q.properIndex π j), ⟨_, rfl⟩, rfl⟩

theorem contract_forwardEdges :
    (P).forwardEdges = mapEdge π '' {e | e ∈ Q.forwardEdges ∧ π e.1 ≠ π e.2} := by
  ext e
  constructor
  · rintro ⟨j, rfl⟩
    let i := Q.properIndex π j.1
    have hi : Q.direction i = .forward := j.2
    refine ⟨Q.actualEdge i, ⟨?_, ?_⟩, ?_⟩
    · exact ⟨⟨i, hi⟩, rfl⟩
    · exact actualEdge_projects_proper Q π (Q.properIndex_mem π hproper j.1)
    · exact (contract_actualEdge Q π hproper hforward hbackward
        hforwardUnique hbackwardUnique j.1).symm
  · rintro ⟨e, ⟨⟨i, rfl⟩, hiProper⟩, rfl⟩
    have hi : Q.ProperStep π i.1 := by
      simpa [ProperStep, forwardEdge, actualEdge, i.2] using hiProper
    obtain ⟨j, hj⟩ := Q.exists_properIndex π hi
    have hjdir : (P).direction j = .forward := by
      change Q.direction (Q.properIndex π j) = .forward
      rw [hj]
      exact i.2
    refine ⟨⟨j, hjdir⟩, ?_⟩
    change (P).actualEdge j = mapEdge π (Q.actualEdge i.1)
    exact (contract_actualEdge Q π hproper hforward hbackward
      hforwardUnique hbackwardUnique j).trans
        (congrArg (fun i ↦ mapEdge π (Q.actualEdge i)) hj)

theorem contract_backwardEdges :
    (P).backwardEdges = mapEdge π '' {e | e ∈ Q.backwardEdges ∧ π e.1 ≠ π e.2} := by
  ext e
  constructor
  · rintro ⟨j, rfl⟩
    let i := Q.properIndex π j.1
    have hi : Q.direction i ≠ .forward := j.2
    refine ⟨Q.actualEdge i, ⟨?_, ?_⟩, ?_⟩
    · exact ⟨⟨i, hi⟩, rfl⟩
    · exact actualEdge_projects_proper Q π (Q.properIndex_mem π hproper j.1)
    · exact (contract_actualEdge Q π hproper hforward hbackward
        hforwardUnique hbackwardUnique j.1).symm
  · rintro ⟨e, ⟨⟨i, rfl⟩, hiProper⟩, rfl⟩
    have hi : Q.ProperStep π i.1 := by
      have hdir := Q.backwardIndex_direction i
      have hne : π (Q.vertex (i.1 + 1)) ≠ π (Q.vertex i.1) := by
        simpa [backwardEdge, actualEdge, hdir] using hiProper
      exact hne.symm
    obtain ⟨j, hj⟩ := Q.exists_properIndex π hi
    have hjdir : (P).direction j ≠ .forward := by
      change Q.direction (Q.properIndex π j) ≠ .forward
      rw [hj]
      exact i.2
    refine ⟨⟨j, hjdir⟩, ?_⟩
    change (P).actualEdge j = mapEdge π (Q.actualEdge i.1)
    exact (contract_actualEdge Q π hproper hforward hbackward
      hforwardUnique hbackwardUnique j).trans
        (congrArg (fun i ↦ mapEdge π (Q.actualEdge i)) hj)

end ContractProperties

#print axioms projected_vertex_preimage_finite
#print axioms properSteps_infinite
#print axioms projected_properIndex_succ
#print axioms contract
#print axioms contract_forwardEdges
#print axioms contract_backwardEdges

end Erdos599.Alternating.InfiniteColouredOccurrenceWord
