import ErdosProblems.Erdos394.GeneralEulerInterval

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# A polynomial lower bound for the Euler density at a geometric endpoint
-/

open Nat Finset Filter

namespace Erdos394

lemma primeEulerProduct_pos (N : ℕ) :
    0 < localEulerProduct N.primesLE (fun p : ℕ ↦ 1 / (p : ℝ)) := by
  unfold localEulerProduct
  apply Finset.prod_pos
  intro p hp
  have hpprime := (Nat.mem_primesLE.mp hp).2
  have hpR : (1 : ℝ) < p := by exact_mod_cast hpprime.one_lt
  exact sub_pos.mpr ((div_lt_one (show (0 : ℝ) < p by positivity)).2 hpR)

/-- From one fixed geometric endpoint onward, the full prime Euler density has
a fixed positive constant times `exp(-24(1+log J))` as a lower bound. -/
theorem exists_geometric_endpoint_primeEuler_lower :
    ∃ J0 : ℕ, ∃ c : ℝ, 0 < J0 ∧ 0 < c ∧
      ∀ J : ℕ, J0 ≤ J →
        c * Real.exp (-24 * (1 + Real.log J)) ≤
          localEulerProduct (16 ^ J).primesLE (fun p : ℕ ↦ 1 / (p : ℝ)) := by
  obtain ⟨J0, hJ0, hinterval⟩ := exists_geometric_localEulerProduct_lower
  let c := localEulerProduct (16 ^ J0).primesLE (fun p : ℕ ↦ 1 / (p : ℝ))
  refine ⟨J0, c, hJ0, ?_, ?_⟩
  · dsimp [c]
    exact primeEulerProduct_pos (16 ^ J0)
  · intro J hJ
    have hpow : 16 ^ J0 ≤ 16 ^ J := Nat.pow_le_pow_right (by omega) hJ
    have hsplit := localEulerProduct_mul_sdiff
      (16 ^ J).primesLE (16 ^ J0).primesLE (Nat.primesLE_mono hpow)
      (fun p : ℕ ↦ 1 / (p : ℝ))
    have hlow := hinterval J hJ
    have hc0 : 0 ≤ c := (primeEulerProduct_pos (16 ^ J0)).le
    have hmul := mul_le_mul_of_nonneg_left hlow hc0
    dsimp [c] at hmul ⊢
    rw [← hsplit]
    exact hmul

/-- The exponential expression in the preceding endpoint bound is exactly a
constant times the reciprocal twenty-fourth power. -/
theorem exp_neg_twentyfour_one_add_log_eq (x : ℝ) (hx : 0 < x) :
    Real.exp (-24 * (1 + Real.log x)) =
      Real.exp (-24) / x ^ (24 : ℕ) := by
  have hden : Real.exp ((24 : ℝ) * Real.log x) = x ^ (24 : ℕ) := by
    calc
      Real.exp ((24 : ℝ) * Real.log x) =
          (Real.exp (Real.log x)) ^ (24 : ℕ) := by
        simpa using Real.exp_nat_mul (Real.log x) 24
      _ = x ^ (24 : ℕ) := by rw [Real.exp_log hx]
  rw [show -24 * (1 + Real.log x) =
      (-24 : ℝ) - (24 : ℝ) * Real.log x by ring,
    Real.exp_sub, hden]

end Erdos394
