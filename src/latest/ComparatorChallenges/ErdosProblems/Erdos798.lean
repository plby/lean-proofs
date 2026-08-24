/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Finset Real Filter

namespace Erdos798

variable {d : ℕ} [d.AtLeastTwo] {v : Fin d → ℤ}

noncomputable def cube (d n : ℕ) : Finset (Fin d → ℤ) := Fintype.piFinset fun _ ↦ Icc 1 n

def Covers (a b c : Fin d → ℤ) : Prop :=
  ∃ t q : ℤ, q ≠ 0 ∧ (q - t) • a + t • b = q • c

def IsCubeCover (n : ℕ) (S : Finset (Fin d → ℤ)) : Prop :=
  S ⊆ cube d n ∧ ∀ x ∈ cube d n, ∃ y z, y ∈ S ∧ z ∈ S ∧ Covers y z x

variable (d) in
open scoped Classical in
noncomputable def minCoverSize (n : ℕ) : ℕ :=
  {c ∈ Finset.range (n ^ d + 1) | ∃ S : Finset (Fin d → ℤ), #S = c ∧ IsCubeCover n S}.min'
  ⟨n ^ d, by
    simp_rw [mem_filter, mem_range_succ_iff, le_rfl, true_and]
    exact ⟨cube d n, by simp [cube], subset_rfl,
      fun a ma ↦ ⟨_, _, ma, ma, ⟨0, 1, by simp, by simp⟩⟩⟩⟩

theorem erdos_798 : (fun n ↦ (minCoverSize 2 n : ℝ)) =O[atTop] fun n ↦ n ^ (2 / 3 : ℝ) * log n := by
  sorry

end Erdos798
