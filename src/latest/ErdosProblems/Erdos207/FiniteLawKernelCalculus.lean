/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FiniteLawPushforward

/-! # Finite kernel calculus for state-independent proposal marginals -/

namespace Erdos207.FiniteLaw

open Finset

noncomputable section

theorem bind_map
    {Ω Ξ Z : Type*} [Fintype Ω] [Fintype Ξ] [DecidableEq Ξ] [Fintype Z]
    (L : FiniteLaw Ω) (f : Ω → Ξ) (K : Ξ → FiniteLaw Z) :
    (map f L).bind K = L.bind (fun x ↦ K (f x)) := by
  classical
  apply FiniteLaw.ext
  intro z
  change (∑ y, (∑ x, if f x = y then L.mass x else 0) * (K y).mass z) =
    ∑ x, L.mass x * (K (f x)).mass z
  simp_rw [sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  rw [sum_eq_single (f x)]
  · simp
  · intro y _ hy
    simp [Ne.symm hy]
  · simp

theorem bind_const
    {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (L : FiniteLaw Ω) (K : FiniteLaw Ξ) : L.bind (fun _ ↦ K) = K := by
  apply FiniteLaw.ext
  intro y
  change (∑ x, L.mass x * K.mass y) = K.mass y
  rw [← sum_mul, L.sum_mass, one_mul]

theorem bind_pure_right
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (L : FiniteLaw Ω) :
    L.bind pure = L := by
  classical
  apply FiniteLaw.ext
  intro y
  change (∑ x, L.mass x * (if y = x then 1 else 0)) = L.mass y
  rw [sum_eq_single y]
  · simp
  · intro x _ hx
    simp [Ne.symm hx]
  · simp

theorem map_const
    {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ] [DecidableEq Ξ]
    (L : FiniteLaw Ω) (y : Ξ) : map (fun _ ↦ y) L = pure y := by
  classical
  apply ext_probability
  intro P
  rw [probability_map, probability_pure]
  by_cases h : P y
  · simp only [h, probability_true, if_true]
  · simp only [h, probability_false, if_false]

theorem map_jointBind_snd
    {Ω Ξ : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Ξ] [DecidableEq Ξ]
    (L : FiniteLaw Ω) (K : Ω → FiniteLaw Ξ) :
    map Prod.snd (L.jointBind K) = L.bind K := by
  unfold jointBind
  rw [map_bind]
  congr 1
  funext x
  rw [map_comp]
  exact map_id (K x)

theorem map_jointBind_coordinates
    {Ω Ξ A B : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Ξ] [DecidableEq Ξ]
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (L : FiniteLaw Ω) (K : Ω → FiniteLaw Ξ) (f : Ω → A) (g : Ξ → B)
    (Q : A → FiniteLaw B) (hQ : ∀ x, map g (K x) = Q (f x)) :
    map (fun z ↦ (f z.1, g z.2)) (L.jointBind K) = (map f L).jointBind Q := by
  unfold jointBind
  rw [map_bind, bind_map]
  congr 1
  funext x
  rw [map_comp, ← hQ x, map_comp]
  rfl

theorem map_jointBind_independent
    {Ω Ξ A B : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Ξ] [DecidableEq Ξ]
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (L : FiniteLaw Ω) (K : Ω → FiniteLaw Ξ) (f : Ω → A) (g : Ξ → B)
    (Q : FiniteLaw B) (hQ : ∀ x, map g (K x) = Q) :
    map (fun z ↦ (f z.1, g z.2)) (L.jointBind K) =
      (map f L).jointBind (fun _ ↦ Q) :=
  map_jointBind_coordinates L K f g (fun _ ↦ Q) hQ

end

end Erdos207.FiniteLaw
