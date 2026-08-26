/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The last two coordinates distinguish sextic points with nonnegative first coordinate.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.IntegerBox

namespace Erdos477.Geometry

variable {K : Type*} [Field K] [CharZero K]

def integerPlaneProjection (z : Fin 3 → ℤ) : K × K := (z 1, z 2)

lemma integerPlaneProjection_injOn (c : ℤ) (S : Finset (Fin 3 → ℤ))
    (hS : ∀ z ∈ S, 0 ≤ z 0 ∧ z 0 ^ 6 + z 1 ^ 6 - z 2 ^ 6 = c) :
    Set.InjOn (integerPlaneProjection (K := K)) S := by
  intro z hz w hw hproj
  have h1 : z 1 = w 1 := Int.cast_injective (congrArg Prod.fst hproj)
  have h2 : z 2 = w 2 := Int.cast_injective (congrArg Prod.snd hproj)
  have hpow : z 0 ^ 6 = w 0 ^ 6 := by
    have hz' := (hS z hz).2
    have hw' := (hS w hw).2
    rw [h1, h2] at hz'
    omega
  have h0 : z 0 = w 0 :=
    (pow_left_inj₀ (hS z hz).1 (hS w hw).1 (by decide : 6 ≠ 0)).mp hpow
  ext k
  fin_cases k
  · exact h0
  · exact h1
  · exact h2

#print axioms integerPlaneProjection_injOn
-- 'Erdos477.Geometry.integerPlaneProjection_injOn' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
