/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter
open scoped SimpleGraph

namespace Erdos578

abbrev CubeVertex (d : ℕ) := Fin d → ZMod 2

local instance twoNeZero : NeZero (2 : ℕ) := Nat.instNeZeroSucc

abbrev cubeGraph (d : ℕ) : SimpleGraph (CubeVertex d) where
  Adj x y := hammingDist x y = 1
  symm := ⟨fun x y h ↦ by simpa [hammingDist_comm] using h⟩
  loopless := ⟨fun x h ↦ by simp [hammingDist] at h⟩

noncomputable def successCount (d : ℕ) : ℕ := by
  classical
  exact ((Finset.univ : Finset (SimpleGraph (CubeVertex d))).filter
    fun G ↦ cubeGraph d ⊑ G).card

noncomputable def successProbability (d : ℕ) : ℝ :=
  (successCount d : ℝ) / (Fintype.card (SimpleGraph (CubeVertex d)) : ℝ)

theorem erdos_578 : Tendsto successProbability atTop (nhds 1) := by
  sorry

end Erdos578
