/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.IndependentSeedConditioning

/-! # Independent envelopes when the auxiliary state type varies with prior data -/

namespace Erdos207.FiniteLaw

noncomputable section

variable {D R Z : Type*} [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R]
  [Fintype Z] [DecidableEq Z] {S : D → Type*} [∀ d, Fintype (S d)] [∀ d, DecidableEq (S d)]

def encodedEnvelopeJointLaw
    (P : FiniteLaw D) (K : (d : D) → FiniteLaw (R × S d)) (encode : (d : D) → S d → Z) :
    FiniteLaw (D × (R × Z)) :=
  P.jointBind (fun d ↦ map (fun w ↦ (w.1, encode d w.2)) (K d))

theorem encodedEnvelopeJointLaw_data_seed
    (P : FiniteLaw D) (K : (d : D) → FiniteLaw (R × S d)) (encode : (d : D) → S d → Z)
    (Q : FiniteLaw R) (hQ : ∀ d, map Prod.fst (K d) = Q) :
    map (fun z ↦ (z.1, z.2.1)) (encodedEnvelopeJointLaw P K encode) =
      P.jointBind (fun _ ↦ Q) := by
  have h := map_jointBind_independent P
    (fun d ↦ map (fun w ↦ (w.1, encode d w.2)) (K d)) id Prod.fst Q (fun d ↦ by
      rw [map_comp]
      exact hQ d)
  rw [map_id] at h
  exact h

theorem encodedEnvelopeJointLaw_data_state
    (P : FiniteLaw D) (K : (d : D) → FiniteLaw (R × S d)) (encode : (d : D) → S d → Z) :
    map (fun z ↦ (z.1, z.2.2)) (encodedEnvelopeJointLaw P K encode) =
      P.jointBind (fun d ↦ map (encode d) (map Prod.snd (K d))) := by
  have h := map_jointBind_coordinates P
    (fun d ↦ map (fun w ↦ (w.1, encode d w.2)) (K d)) id Prod.snd
    (fun d ↦ map (encode d) (map Prod.snd (K d))) (fun d ↦ by
      rw [map_comp, map_comp]
      rfl)
  rw [map_id] at h
  exact h

theorem encodedEnvelopeJointLaw_supported
    (P : FiniteLaw D) (K : (d : D) → FiniteLaw (R × S d)) (encode : (d : D) → S d → Z)
    (Good : D → R → Z → Prop)
    (hK : ∀ d, (K d).SupportedOn (fun w ↦ Good d w.1 (encode d w.2))) :
    (encodedEnvelopeJointLaw P K encode).SupportedOn (fun z ↦ Good z.1 z.2.1 z.2.2) := by
  unfold encodedEnvelopeJointLaw jointBind
  apply SupportedOn.bind (L := P) (P := fun _ ↦ True) (Q := fun z ↦ Good z.1 z.2.1 z.2.2)
    (fun _ _ ↦ True.intro)
    (fun d ↦ map (fun w ↦ (d, w)) (map (fun w ↦ (w.1, encode d w.2)) (K d)))
  intro d _
  rw [map_comp]
  exact (hK d).map (Q := fun z ↦ Good z.1 z.2.1 z.2.2)
    (fun w ↦ (d, (w.1, encode d w.2))) (fun w hw ↦ hw)

end

end Erdos207.FiniteLaw
