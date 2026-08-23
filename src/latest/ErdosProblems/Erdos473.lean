/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 473.
https://www.erdosproblems.com/forum/thread/473

Informal authors:
- A. M. Odlyzko

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos473.md
-/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos387.UniformAnalyticInputs
import ErdosProblems.Erdos473.ClusterGadget

/-!
# Erdős Problem 473

Does there exist a permutation `a` of the positive integers such that
`a n + a (n + 1)` is prime for every `n`?

The proof is split into two parts.  The first is a general graph-theoretic
construction: a countable graph in which every finite simple path can be
extended so as to contain any prescribed vertex has a spanning one-way ray.
The second verifies that extension property for the prime-sum graph.
-/

namespace Erdos473

open Function

/-! ## A spanning ray from finite path extensions -/

/-- If finite duplicate-free `R`-chains can always be extended, as prefixes,
to contain any prescribed vertex, then any enumeration of the vertex type can
be reordered into a spanning one-way `R`-chain. -/
theorem exists_equiv_nat_of_chain_prefix_extension
    {α : Type*} (enum : ℕ ≃ α) (R : α → α → Prop)
    (extend : ∀ (l : List α), l.Nodup → l.IsChain R → ∀ x : α,
      ∃ l' : List α, l <+: l' ∧ l'.Nodup ∧ l'.IsChain R ∧ x ∈ l') :
    ∃ e : ℕ ≃ α, ∀ n : ℕ, R (e n) (e (n + 1)) := by
  classical
  let State := {l : List α // l.Nodup ∧ l.IsChain R}
  let initial : State := ⟨[], by simp⟩
  let step (n : ℕ) (s : State) : State :=
    ⟨(extend s.1 s.2.1 s.2.2 (enum n)).choose,
      (extend s.1 s.2.1 s.2.2 (enum n)).choose_spec.2.1,
      (extend s.1 s.2.1 s.2.2 (enum n)).choose_spec.2.2.1⟩
  have step_prefix (n : ℕ) (s : State) :
      s.1 <+: (step n s).1 := by
    dsimp [step]
    exact (extend s.1 s.2.1 s.2.2 (enum n)).choose_spec.1
  have step_mem (n : ℕ) (s : State) :
      enum n ∈ (step n s).1 := by
    dsimp [step]
    exact (extend s.1 s.2.1 s.2.2 (enum n)).choose_spec.2.2.2
  let stages : ℕ → State :=
    fun n => Nat.rec initial (fun k s => step k s) n
  have stages_succ (n : ℕ) : stages (n + 1) = step n (stages n) := by
    simp [stages]
  have prefix_succ (n : ℕ) :
      (stages n).1 <+: (stages (n + 1)).1 := by
    rw [stages_succ]
    exact step_prefix n (stages n)
  have enum_mem_succ (n : ℕ) : enum n ∈ (stages (n + 1)).1 := by
    rw [stages_succ]
    exact step_mem n (stages n)
  have stages_prefix : ∀ {m n : ℕ}, m ≤ n →
      (stages m).1 <+: (stages n).1 := by
    intro m n hmn
    induction n with
    | zero =>
        have hm : m = 0 := Nat.eq_zero_of_le_zero hmn
        subst m
        exact List.prefix_rfl
    | succ n ih =>
        rcases hmn.eq_or_lt with hEq | hLt
        · subst m
          exact List.prefix_rfl
        · exact (ih (Nat.lt_succ_iff.mp hLt)).trans (by
            simpa [Nat.succ_eq_add_one] using prefix_succ n)
  have enum_mem_stage {i n : ℕ} (hin : i < n) :
      enum i ∈ (stages n).1 := by
    exact (stages_prefix (Nat.succ_le_iff.mpr hin)).subset (enum_mem_succ i)
  have stage_length (n : ℕ) : n ≤ (stages n).1.length := by
    let first : Finset α := Finset.univ.image (fun i : Fin n => enum i.1)
    have hfun : Function.Injective (fun i : Fin n => enum i.1) :=
      enum.injective.comp Fin.val_injective
    have hcard : first.card = n := by
      dsimp [first]
      rw [Finset.card_image_of_injective _ hfun, Finset.card_univ, Fintype.card_fin]
    have hsub : first ⊆ (stages n).1.toFinset := by
      intro x hx
      simp only [first, Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨i, rfl⟩ := hx
      exact List.mem_toFinset.mpr (enum_mem_stage i.2)
    calc
      n = first.card := hcard.symm
      _ ≤ (stages n).1.toFinset.card := Finset.card_le_card hsub
      _ = (stages n).1.length := List.toFinset_card_of_nodup (stages n).2.1
  have diagonal_lt (n : ℕ) : n < (stages (n + 1)).1.length := by
    have := stage_length (n + 1)
    omega
  let seq (n : ℕ) : α := (stages (n + 1)).1[n]'(diagonal_lt n)
  have diagonal_lt_of_le {n m : ℕ} (h : n + 1 ≤ m) :
      n < (stages m).1.length :=
    lt_of_lt_of_le (diagonal_lt n) (stages_prefix h).length_le
  have seq_eq_getElem {n m : ℕ} (h : n + 1 ≤ m) :
      seq n = (stages m).1[n]'(diagonal_lt_of_le h) := by
    dsimp [seq]
    simpa using (stages_prefix h).getElem (diagonal_lt n)
  have seq_chain (n : ℕ) : R (seq n) (seq (n + 1)) := by
    have hbound : n + 1 < (stages (n + 2)).1.length := by
      have := stage_length (n + 2)
      omega
    have hrel := (stages (n + 2)).2.2.getElem n hbound
    rw [← seq_eq_getElem (show n + 1 ≤ n + 2 by omega)] at hrel
    rw [← seq_eq_getElem (show n + 1 + 1 ≤ n + 2 by omega)] at hrel
    exact hrel
  have seq_injective : Function.Injective seq := by
    intro i j hij
    let m := max (i + 1) (j + 1)
    have hi : i + 1 ≤ m := Nat.le_max_left _ _
    have hj : j + 1 ≤ m := Nat.le_max_right _ _
    have hget :
        (stages m).1[i]'(diagonal_lt_of_le hi) =
          (stages m).1[j]'(diagonal_lt_of_le hj) := by
      rw [← seq_eq_getElem hi, ← seq_eq_getElem hj, hij]
    exact ((stages m).2.1.getElem_inj_iff).mp hget
  have seq_surjective : Function.Surjective seq := by
    intro x
    let k : ℕ := enum.symm x
    have hx : x ∈ (stages (k + 1)).1 := by
      have hk := enum_mem_succ k
      simpa [k] using hk
    obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hx
    let m := max (i + 1) (k + 1)
    have hi_m : i + 1 ≤ m := Nat.le_max_left _ _
    have hk_m : k + 1 ≤ m := Nat.le_max_right _ _
    have hprefix := stages_prefix hk_m
    have hmget : (stages m).1[i]'(diagonal_lt_of_le hi_m) = x := by
      rw [← hprefix.getElem hi]
      exact hix
    exact ⟨i, (seq_eq_getElem hi_m).trans hmget⟩
  exact ⟨Equiv.ofBijective seq ⟨seq_injective, seq_surjective⟩, seq_chain⟩

/-! ## Finite-deletion connectivity implies the extension property -/

/-- Finite-deletion connectivity lets us extend a finite simple path at its
last vertex while retaining the old path as an initial segment. -/
theorem chain_prefix_extension_of_finitely_avoidably_connected
    {α : Type*} {R : α → α → Prop}
    (hR : FinitelyAvoidablyConnected R) (l : List α)
    (hl : l.Nodup) (hlR : l.IsChain R) (target : α) :
    ∃ l' : List α, l <+: l' ∧ l'.Nodup ∧ l'.IsChain R ∧ target ∈ l' := by
  classical
  by_cases htarget : target ∈ l
  · exact ⟨l, List.prefix_rfl, hl, hlR, htarget⟩
  by_cases hnil : l = []
  · subst l
    exact ⟨[target], by simp, by simp, by simp, by simp⟩
  let endpoint := l.getLast hnil
  let forbidden := l.toFinset.erase endpoint
  have hendpoint_mem : endpoint ∈ l := List.getLast_mem hnil
  have hendpoint_not_forbidden : endpoint ∉ forbidden := by
    simp [forbidden]
  have htarget_not_forbidden : target ∉ forbidden := by
    intro ht
    exact htarget (List.mem_toFinset.mp (Finset.mem_of_mem_erase ht))
  obtain ⟨tail, hnodup, hchain, hlast, havoid⟩ :=
    hR forbidden endpoint target hendpoint_not_forbidden htarget_not_forbidden
  have hendpoint_not_tail : endpoint ∉ tail := (List.nodup_cons.mp hnodup).1
  have htail_disjoint : List.Disjoint l tail := by
    rw [List.disjoint_iff_ne]
    intro a ha b hb hab
    subst b
    by_cases hbe : a = endpoint
    · exact hendpoint_not_tail (hbe ▸ hb)
    · have haf : a ∈ forbidden := by
        simp [forbidden, ha, hbe]
      exact (havoid a hb) haf
  have htail_nodup : tail.Nodup := (List.nodup_cons.mp hnodup).2
  have happend_nodup : (l ++ tail).Nodup := hl.append htail_nodup htail_disjoint
  have htail_chain : tail.IsChain R := hchain.tail
  have hboundary :
      ∀ a ∈ l.getLast?, ∀ b ∈ tail.head?, R a b := by
    intro a ha b hb
    have hae : a = endpoint := by
      rw [List.getLast?_eq_some_getLast hnil] at ha
      exact Option.some.inj ha.symm
    subst a
    exact hchain.rel_head? hb
  have happend_chain : (l ++ tail).IsChain R :=
    hlR.append htail_chain hboundary
  have htarget_tail : target ∈ tail := by
    have hmem : target ∈ endpoint :: tail := List.mem_of_mem_getLast? (by simpa using hlast)
    have hne : target ≠ endpoint := by
      intro hEq
      exact htarget (by simpa [hEq] using hendpoint_mem)
    exact (List.mem_cons.mp hmem).resolve_left hne
  exact ⟨l ++ tail, List.prefix_append _ _, happend_nodup, happend_chain,
    List.mem_append_right _ htarget_tail⟩

/-- A countable finitely-deletion-connected relation has a spanning one-way
ray. -/
theorem exists_equiv_nat_of_finitely_avoidably_connected
    {α : Type*} (enum : ℕ ≃ α) (R : α → α → Prop)
    (hR : FinitelyAvoidablyConnected R) :
    ∃ e : ℕ ≃ α, ∀ n : ℕ, R (e n) (e (n + 1)) := by
  apply exists_equiv_nat_of_chain_prefix_extension enum R
  intro l hl hlR target
  exact chain_prefix_extension_of_finitely_avoidably_connected hR l hl hlR target

/-! ## The prime-sum graph -/

theorem erdos473_of_finitely_avoidably_connected
    (h : FinitelyAvoidablyConnected PrimeAdjacent) :
    ∃ a : ℕ ≃ ℕ+, ∀ n : ℕ,
      Nat.Prime ((a n : ℕ) + (a (n + 1) : ℕ)) := by
  simpa only [PrimeAdjacent] using
    exists_equiv_nat_of_finitely_avoidably_connected
      Equiv.pnatEquivNat.symm PrimeAdjacent h

/-- Erdős Problem 473: the positive integers admit a permutation in which
every two consecutive terms have prime sum. -/
theorem erdos473 :
    ∃ a : ℕ ≃ ℕ+, ∀ n : ℕ,
      Nat.Prime ((a n : ℕ) + (a (n + 1) : ℕ)) := by
  apply erdos473_of_finitely_avoidably_connected
  exact finitelyAvoidablyConnected_of_clusters
    (fun H ↦ primeCluster_nonempty Erdos387.shiftedSiegelWalfiszLower H)

end Erdos473

#print axioms Erdos473.erdos473
