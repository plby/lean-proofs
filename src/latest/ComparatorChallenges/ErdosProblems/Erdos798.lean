import Mathlib

namespace Erdos798

noncomputable section

open Finset Int Real Filter Topology

variable {d : ℕ} [d.AtLeastTwo] {v : Fin d → ℤ}

def cube (d n : ℕ) : Finset (Fin d → ℤ) := Fintype.piFinset fun _ ↦ Icc 1 n
section MaxAbs

end MaxAbs

def Covers (a b c : Fin d → ℤ) : Prop :=
  ∃ t q : ℤ, q ≠ 0 ∧ (q - t) • a + t • b = q • c

def IsCubeCover (n : ℕ) (S : Finset (Fin d → ℤ)) : Prop :=
  S ⊆ cube d n ∧ ∀ x ∈ cube d n, ∃ y z, y ∈ S ∧ z ∈ S ∧ Covers y z x

variable (d) in
open scoped Classical in
def minCoverSize (n : ℕ) : ℕ :=
  {c ∈ Finset.range (n ^ d + 1) | ∃ S : Finset (Fin d → ℤ), #S = c ∧ IsCubeCover n S}.min'
  ⟨n ^ d, by
    simp_rw [mem_filter, mem_range_succ_iff, le_rfl, true_and]
    exact ⟨cube d n, by simp [cube], subset_rfl,
      fun a ma ↦ ⟨_, _, ma, ma, ⟨0, 1, by simp, by simp⟩⟩⟩⟩
end

end Erdos798


open Finset Int Real Filter Topology

namespace Erdos798

open scoped Classical in
theorem erdos798 : (fun n ↦ (minCoverSize 2 n : ℝ)) =O[atTop] fun n ↦ n ^ (2 / 3 : ℝ) * log n := by
  sorry

end Erdos798
