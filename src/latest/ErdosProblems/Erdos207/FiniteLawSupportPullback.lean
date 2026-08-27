/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FiniteLawPushforward

/-! # Pulling support properties back from an exact marginal -/

namespace Erdos207.FiniteLaw

open Finset

noncomputable section

theorem mass_le_map_mass
    {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ] [DecidableEq Ξ]
    (L : FiniteLaw Ω) (f : Ω → Ξ) (x : Ω) : L.mass x ≤ (map f L).mass (f x) := by
  classical
  change L.mass x ≤ ∑ y, if f y = f x then L.mass y else 0
  have h := single_le_sum (s := univ) (a := x)
    (f := fun y ↦ if f y = f x then L.mass y else 0) (fun _ _ ↦ zero_le) (mem_univ x)
  simpa using h

theorem SupportedOn.of_map
    {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ] [DecidableEq Ξ]
    {L : FiniteLaw Ω} {f : Ω → Ξ} {P : Ξ → Prop}
    (h : (FiniteLaw.map f L).SupportedOn P) : L.SupportedOn (fun x ↦ P (f x)) := by
  intro x hx
  exact h (f x) (hx.trans_le (mass_le_map_mass L f x))

end

end Erdos207.FiniteLaw
