/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CoupledBitUpdate
import ErdosProblems.Erdos207.FiniteKernelConcentration

/-! # A proposal envelope with exact marginals through adaptive updates -/

namespace Erdos207.FiniteLaw

open Finset

noncomputable section

theorem map_evolveKernels
    {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ] [DecidableEq Ξ]
    (K : ℕ → Ω → FiniteLaw Ω) (H : ℕ → Ξ → FiniteLaw Ξ)
    (f : Ω → Ξ) (h : ∀ t x, map f (K t x) = H t (f x))
    (t : ℕ) (L : FiniteLaw Ω) :
    map f (evolveKernels K t L) = evolveKernels H t (map f L) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [evolveKernels_succ, evolveKernels_succ, map_bind, ← ih, bind_map]
      congr 1
      funext x
      exact h t x

def proposalUnionKernel
    {I : Type*} [Fintype I] [DecidableEq I]
    (Q : FiniteLaw (Finset I)) (R : Finset I) : FiniteLaw (Finset I) :=
  map (fun B ↦ R ∪ B) Q

def coupledEnvelopeKernel
    {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]
    (C : S → FiniteLaw (Finset I × S)) (z : Finset I × S) :
    FiniteLaw (Finset I × S) :=
  map (fun w ↦ (z.1 ∪ w.1, w.2)) (C z.2)

def coupledEnvelopeProcess
    {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]
    (C : ℕ → S → FiniteLaw (Finset I × S)) (t : ℕ) (L : FiniteLaw S) :
    FiniteLaw (Finset I × S) :=
  evolveKernels (fun n ↦ coupledEnvelopeKernel (C n)) t (map (fun s ↦ (∅, s)) L)

theorem coupledEnvelopeKernel_proposal
    {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]
    (C : S → FiniteLaw (Finset I × S)) (Q : FiniteLaw (Finset I))
    (hQ : ∀ s, map Prod.fst (C s) = Q) (z : Finset I × S) :
    map Prod.fst (coupledEnvelopeKernel C z) = proposalUnionKernel Q z.1 := by
  unfold coupledEnvelopeKernel proposalUnionKernel
  rw [map_comp, ← hQ z.2, map_comp]
  rfl

theorem coupledEnvelopeKernel_actual
    {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]
    (C : S → FiniteLaw (Finset I × S)) (K : S → FiniteLaw S)
    (hK : ∀ s, map Prod.snd (C s) = K s) (z : Finset I × S) :
    map Prod.snd (coupledEnvelopeKernel C z) = K z.2 := by
  unfold coupledEnvelopeKernel
  rw [map_comp]
  exact hK z.2

theorem coupledEnvelopeProcess_proposal
    {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]
    (C : ℕ → S → FiniteLaw (Finset I × S)) (Q : ℕ → FiniteLaw (Finset I))
    (hQ : ∀ n s, map Prod.fst (C n s) = Q n) (t : ℕ) (L : FiniteLaw S) :
    map Prod.fst (coupledEnvelopeProcess C t L) =
      evolveKernels (fun n ↦ proposalUnionKernel (Q n)) t (pure ∅) := by
  unfold coupledEnvelopeProcess
  rw [map_evolveKernels _ _ _ (fun n ↦ coupledEnvelopeKernel_proposal (C n) (Q n) (hQ n))]
  rw [map_comp]
  change evolveKernels _ t (map (fun _ : S ↦ (∅ : Finset I)) L) = _
  rw [map_const]

theorem coupledEnvelopeProcess_actual
    {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]
    (C : ℕ → S → FiniteLaw (Finset I × S)) (K : ℕ → S → FiniteLaw S)
    (hK : ∀ n s, map Prod.snd (C n s) = K n s) (t : ℕ) (L : FiniteLaw S) :
    map Prod.snd (coupledEnvelopeProcess C t L) = evolveKernels K t L := by
  unfold coupledEnvelopeProcess
  rw [map_evolveKernels _ _ _ (fun n ↦ coupledEnvelopeKernel_actual (C n) (K n) (hK n))]
  rw [map_comp]
  change evolveKernels _ t (map id L) = _
  rw [map_id]

theorem coupledEnvelopeProcess_supported
    {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]
    (C : ℕ → S → FiniteLaw (Finset I × S)) (accepted : S → Finset I)
    (hC : ∀ n s, (C n s).SupportedOn (fun w ↦ accepted w.2 ⊆ accepted s ∪ w.1))
    (t : ℕ) (L : FiniteLaw S) (hL : L.SupportedOn (fun s ↦ accepted s = ∅)) :
    (coupledEnvelopeProcess C t L).SupportedOn (fun z ↦ accepted z.2 ⊆ z.1) := by
  induction t with
  | zero =>
      change (map (fun s : S ↦ ((∅ : Finset I), s)) L).SupportedOn _
      apply hL.map (Q := fun z ↦ accepted z.2 ⊆ z.1) (fun s ↦ ((∅ : Finset I), s))
      intro s hs
      simp [hs]
  | succ t ih =>
      change (bind (coupledEnvelopeProcess C t L) (coupledEnvelopeKernel (C t))).SupportedOn _
      apply ih.bind (Q := fun z ↦ accepted z.2 ⊆ z.1) (coupledEnvelopeKernel (C t))
      intro z hz
      unfold coupledEnvelopeKernel
      apply (hC t z.2).map (Q := fun z ↦ accepted z.2 ⊆ z.1)
        (fun w ↦ (z.1 ∪ w.1, w.2))
      intro w hw
      exact hw.trans (union_subset_union hz Subset.rfl)

theorem coupledEnvelopeProcess_independent_of_initial_data
    {D I S : Type*} [Fintype D] [DecidableEq D] [Fintype I] [DecidableEq I]
    [Fintype S] [DecidableEq S]
    (P : FiniteLaw D) (L : D → FiniteLaw S)
    (C : D → ℕ → S → FiniteLaw (Finset I × S)) (Q : ℕ → FiniteLaw (Finset I))
    (hQ : ∀ d n s, map Prod.fst (C d n s) = Q n) (t : ℕ) :
    map (fun z ↦ (z.1, z.2.1)) (P.jointBind (fun d ↦ coupledEnvelopeProcess (C d) t (L d))) =
      P.jointBind (fun _ ↦ evolveKernels (fun n ↦ proposalUnionKernel (Q n)) t (pure ∅)) := by
  have h := map_jointBind_independent P (fun d ↦ coupledEnvelopeProcess (C d) t (L d))
    id Prod.fst _ (fun d ↦ coupledEnvelopeProcess_proposal (C d) Q (hQ d) t (L d))
  rw [map_id] at h
  exact h

end

end Erdos207.FiniteLaw
