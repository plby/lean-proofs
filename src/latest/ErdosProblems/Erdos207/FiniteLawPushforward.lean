/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FiniteJointBind

/-! # Exact pushforward identities for finite coupling marginals -/

namespace Erdos207.FiniteLaw

open Finset

noncomputable section

theorem probability_eq_mass
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (L : FiniteLaw Ω) (x : Ω) :
    L.probability (fun y ↦ y = x) = L.mass x := by
  classical
  unfold probability
  rw [sum_eq_single x]
  · simp
  · intro y _ hy
    simp [hy]
  · simp

theorem ext_probability
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {L K : FiniteLaw Ω}
    (h : ∀ P : Ω → Prop, L.probability P = K.probability P) : L = K := by
  apply FiniteLaw.ext
  intro x
  simpa only [probability_eq_mass] using h (fun y ↦ y = x)

theorem map_comp
    {Ω Ξ Z : Type*} [Fintype Ω] [Fintype Ξ] [DecidableEq Ξ] [Fintype Z] [DecidableEq Z]
    (L : FiniteLaw Ω) (f : Ω → Ξ) (g : Ξ → Z) :
    map g (map f L) = map (g ∘ f) L := by
  apply ext_probability
  intro P
  simp only [probability_map, Function.comp_apply]

theorem map_id
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (L : FiniteLaw Ω) : map id L = L := by
  apply ext_probability
  intro P
  simp only [probability_map, id_eq]

theorem map_bind
    {Ω Ξ Z : Type*} [Fintype Ω] [Fintype Ξ] [Fintype Z] [DecidableEq Z]
    (L : FiniteLaw Ω) (K : Ω → FiniteLaw Ξ) (f : Ξ → Z) :
    map f (L.bind K) = L.bind (fun x ↦ map f (K x)) := by
  apply ext_probability
  intro P
  simp only [probability_map, probability_bind]

theorem map_jointBind_fst
    {Ω Ξ : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Ξ] [DecidableEq Ξ]
    (L : FiniteLaw Ω) (K : Ω → FiniteLaw Ξ) : map Prod.fst (L.jointBind K) = L := by
  apply ext_probability
  intro P
  rw [probability_map, probability_jointBind_fst]

end

end Erdos207.FiniteLaw
