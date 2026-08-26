/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.B5SingularEnergy
import ErdosProblems.Erdos822.ShiftedCoefficient

/-!
# Symmetric orientation of the collision scale

The primitive parameterization is asymmetric: its denominator is the
shifted coefficient of the second cofactor.  Collision fibers themselves
are symmetric, so before summing we orient every pair with the larger
cofactor second.  In that orientation the quotient scale is bounded by the
expected gcd-over-product weight.
-/

namespace Erdos822

/-- The scale in the primitive collision-fiber parameterization. -/
def reducedScale (x m m' : ℕ) : ℕ :=
  max (x / m) (x / m') / reducedCollisionRight m m' + 1

/-- Orient the primitive scale so that the larger cofactor is second. -/
def symmetricReducedScale (x m m' : ℕ) : ℕ :=
  if m ≤ m' then reducedScale x m m' else reducedScale x m' m

theorem reducedTotientDet_comm (m m' : ℕ) :
    reducedTotientDet m m' = reducedTotientDet m' m := by
  unfold reducedTotientDet
  rw [shiftedCoefficientGcd_comm]
  congr 1
  rw [← Int.natAbs_neg]
  congr
  ring

/-- Swapping the two outer primes is a bijection between the two ordered
cofactor fibers. -/
theorem outerCollisionPairs_card_comm (x m m' : ℕ) :
    (outerCollisionPairs x m m').card =
      (outerCollisionPairs x m' m).card := by
  classical
  apply Finset.card_bij
      (fun t _ => (t.2, t.1))
  · intro t ht
    rw [mem_outerCollisionPairs_iff] at ht ⊢
    exact ⟨ht.2.1, ht.1, ht.2.2.symm⟩
  · intro a ha b hb hab
    rcases a with ⟨a₁, a₂⟩
    rcases b with ⟨b₁, b₂⟩
    simp only [Prod.mk.injEq] at hab ⊢
    exact ⟨hab.2, hab.1⟩
  · intro b hb
    refine ⟨(b.2, b.1), ?_, ?_⟩
    · rw [mem_outerCollisionPairs_iff] at hb ⊢
      exact ⟨hb.2.1, hb.1, hb.2.2.symm⟩
    · cases b
      rfl

/-- With the larger cofactor second, the quotient part of the primitive
scale is at most x times the shifted-coefficient gcd divided by m*m'. -/
theorem reducedScale_sub_one_mul_le_of_le
    {x m m' : ℕ} (hm : 0 < m) (hm' : 0 < m') (hmm' : m ≤ m') :
    (reducedScale x m m' - 1) * (m * m') ≤
      x * shiftedCoefficientGcd m m' := by
  let B := reducedCollisionRight m m'
  let g := shiftedCoefficientGcd m m'
  let U := max (x / m) (x / m')
  have hBg : B * g = shiftedTotient m' := by
    dsimp [B, g, reducedCollisionRight, shiftedCoefficientGcd]
    exact Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)
  have hm'leBg : m' ≤ B * g := by
    rw [hBg]
    exact Nat.le_add_right m' (Nat.totient m')
  have hU : U = x / m := by
    dsimp [U]
    rw [max_eq_left]
    exact Nat.div_le_div_left hmm' hm
  have hdivmul : (U / B) * B ≤ U := Nat.div_mul_le_self U B
  have hUm : U * m ≤ x := by
    rw [hU]
    exact Nat.div_mul_le_self x m
  have htbm : (U / B) * B * m ≤ x := by
    exact (Nat.mul_le_mul_right m hdivmul).trans hUm
  calc
    (reducedScale x m m' - 1) * (m * m') =
        (U / B) * (m * m') := by
      simp [reducedScale, U, B]
    _ ≤ (U / B) * (m * (B * g)) := by
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left m hm'leBg)
    _ = ((U / B) * B * m) * g := by ring
    _ ≤ x * g := Nat.mul_le_mul_right g htbm
    _ = x * shiftedCoefficientGcd m m' := rfl

/-- Real-valued form of the sorted scale estimate. -/
theorem reducedScale_cast_le_one_add_gcdWeight_of_le
    {x m m' : ℕ} (hm : 0 < m) (hm' : 0 < m') (hmm' : m ≤ m') :
    (reducedScale x m m' : ℝ) ≤
      1 + ((x * shiftedCoefficientGcd m m' : ℕ) : ℝ) /
        ((m * m' : ℕ) : ℝ) := by
  have hmul := reducedScale_sub_one_mul_le_of_le (x := x) hm hm' hmm'
  have hden : (0 : ℝ) < ((m * m' : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos hm hm'
  have hmulR :
      ((reducedScale x m m' - 1 : ℕ) : ℝ) *
          ((m * m' : ℕ) : ℝ) ≤
        ((x * shiftedCoefficientGcd m m' : ℕ) : ℝ) := by
    exact_mod_cast hmul
  have hquot :
      ((reducedScale x m m' - 1 : ℕ) : ℝ) ≤
        ((x * shiftedCoefficientGcd m m' : ℕ) : ℝ) /
          ((m * m' : ℕ) : ℝ) :=
    (le_div_iff₀ hden).2 hmulR
  have hscalePos : 0 < reducedScale x m m' := by
    unfold reducedScale
    exact Nat.zero_lt_succ _
  have hsplit : (reducedScale x m m' : ℝ) =
      1 + ((reducedScale x m m' - 1 : ℕ) : ℝ) := by
    have hnat : reducedScale x m m' = 1 + (reducedScale x m m' - 1) := by
      omega
    exact_mod_cast hnat
  rw [hsplit]
  gcongr

/-- The symmetric orientation always satisfies the gcd-over-product
majorant. -/
theorem symmetricReducedScale_cast_le_one_add_gcdWeight
    {x m m' : ℕ} (hm : 0 < m) (hm' : 0 < m') :
    (symmetricReducedScale x m m' : ℝ) ≤
      1 + ((x * shiftedCoefficientGcd m m' : ℕ) : ℝ) /
        ((m * m' : ℕ) : ℝ) := by
  by_cases hle : m ≤ m'
  · rw [symmetricReducedScale, if_pos hle]
    exact reducedScale_cast_le_one_add_gcdWeight_of_le hm hm' hle
  · have hrev : m' ≤ m := by omega
    rw [symmetricReducedScale, if_neg hle]
    have h :=
      reducedScale_cast_le_one_add_gcdWeight_of_le (x := x) hm' hm hrev
    simpa [shiftedCoefficientGcd_comm, Nat.mul_comm] using h

end Erdos822
