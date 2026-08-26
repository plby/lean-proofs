/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Finite height boxes on the affine sextic surface.
Formal author: Codex.
-/

import Mathlib

namespace Erdos477.Counting

noncomputable def sexticBox (c : ℤ) (B : ℝ) : Finset (Fin 3 → ℤ) := by
  classical
  exact (Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-(⌈B⌉₊ : ℤ)) ⌈B⌉₊)).filter
    (fun z => z 0 ^ 6 + z 1 ^ 6 - z 2 ^ 6 = c ∧ ∀ k, |(z k : ℝ)| ≤ B)

lemma mem_sexticBox (c : ℤ) (B : ℝ) (z : Fin 3 → ℤ) :
    z ∈ sexticBox c B ↔
      z 0 ^ 6 + z 1 ^ 6 - z 2 ^ 6 = c ∧ ∀ k, |(z k : ℝ)| ≤ B := by
  classical
  rw [sexticBox, Finset.mem_filter]
  constructor
  · exact And.right
  · intro hz
    refine ⟨Fintype.mem_piFinset.mpr (fun k => ?_), hz⟩
    apply Finset.mem_Icc.mpr
    apply abs_le.mp
    have h := (hz.2 k).trans (Nat.le_ceil B)
    exact_mod_cast h

end Erdos477.Counting
