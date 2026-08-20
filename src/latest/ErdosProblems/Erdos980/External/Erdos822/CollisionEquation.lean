/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos980.External.Erdos822.CofactorLayers
import ErdosProblems.Erdos980.External.Erdos822.SmoothPart

/-!
# Collision equations for Erdős Problem 822

After an outer prime is attached, `n + φ(n)` is a linear form in that
prime.  The GIL energy estimate starts by equating two such linear forms.
This file records the exact integer equation and the first divisibility
consequence, independently of the later sieve bounds.
-/

namespace Erdos822

/-- Integer-valued version of the outer linear form.  Working in `ℤ` avoids
truncated subtraction when the two sides of a collision are rearranged. -/
theorem shiftedTotient_outer_linear_int {x m p : ℕ}
    (hp : p ∈ outerPrimes x m) (hmpos : 0 < m) (hmp : m < p) :
    (shiftedTotient (m * p) : ℤ) =
      (shiftedTotient m : ℤ) * p - Nat.totient m := by
  have hpprime : p.Prime := (mem_outerPrimes_iff.mp hp).2.2
  have hple : 1 ≤ p := hpprime.one_le
  have hsub : Nat.totient m ≤ (m + Nat.totient m) * p := by
    calc
      Nat.totient m ≤ m + Nat.totient m := Nat.le_add_left _ _
      _ = (m + Nat.totient m) * 1 := by simp
      _ ≤ (m + Nat.totient m) * p := Nat.mul_le_mul_left _ hple
  rw [shiftedTotient_outer_linear hp hmpos hmp, Nat.cast_sub hsub]
  simp [shiftedTotient]

/-- Equation (5.2) of GIL, in its clean integer form. -/
theorem outer_collision_linear_eq_int {x m m' p p' : ℕ}
    (hp : p ∈ outerPrimes x m) (hp' : p' ∈ outerPrimes x m')
    (hmpos : 0 < m) (hm'pos : 0 < m')
    (hmp : m < p) (hm'p' : m' < p')
    (hcollision : shiftedTotient (m * p) = shiftedTotient (m' * p')) :
    (shiftedTotient m : ℤ) * p - Nat.totient m =
      (shiftedTotient m' : ℤ) * p' - Nat.totient m' := by
  rw [← shiftedTotient_outer_linear_int hp hmpos hmp,
    ← shiftedTotient_outer_linear_int hp' hm'pos hm'p']
  exact_mod_cast hcollision

/-- If a common modulus divides both cofactor coefficients in a collision,
then it divides the difference of the two totients.  This is the divisibility
condition immediately preceding equation (5.4) in GIL. -/
theorem int_dvd_totient_sub_of_outer_collision {x m m' p p' d : ℕ}
    (hp : p ∈ outerPrimes x m) (hp' : p' ∈ outerPrimes x m')
    (hmpos : 0 < m) (hm'pos : 0 < m')
    (hmp : m < p) (hm'p' : m' < p')
    (hdm : d ∣ shiftedTotient m) (hdm' : d ∣ shiftedTotient m')
    (hcollision : shiftedTotient (m * p) = shiftedTotient (m' * p')) :
    (d : ℤ) ∣ (Nat.totient m : ℤ) - Nat.totient m' := by
  obtain ⟨u, hu⟩ := hdm
  obtain ⟨u', hu'⟩ := hdm'
  have hlin := outer_collision_linear_eq_int hp hp' hmpos hm'pos hmp hm'p' hcollision
  have huZ : (shiftedTotient m : ℤ) = d * u := by exact_mod_cast hu
  have hu'Z : (shiftedTotient m' : ℤ) = d * u' := by exact_mod_cast hu'
  refine ⟨(u : ℤ) * p - (u' : ℤ) * p', ?_⟩
  rw [huZ, hu'Z] at hlin
  linarith

/-- Under the preliminary prime-power divisibility condition, a collision
can only occur between cofactors in the same smooth-part class.  This is the
formal partition step just before GIL defines `B_d`. -/
theorem smoothPart_eq_of_outer_collision {x m m' p p' y : ℕ}
    (hp : p ∈ outerPrimes x m) (hp' : p' ∈ outerPrimes x m')
    (hmpos : 0 < m) (hm'pos : 0 < m')
    (hmp : m < p) (hm'p' : m' < p')
    (hyp : y < p) (hyp' : y < p')
    (hφ : ∀ q : ℕ, q.Prime → q ≤ y →
      ∀ a : ℕ, a ≤ m.factorization q + 1 → q ^ a ∣ Nat.totient m)
    (hφ' : ∀ q : ℕ, q.Prime → q ≤ y →
      ∀ a : ℕ, a ≤ m'.factorization q + 1 → q ^ a ∣ Nat.totient m')
    (hcollision : shiftedTotient (m * p) = shiftedTotient (m' * p')) :
    smoothPart m y = smoothPart m' y := by
  have hpprime : p.Prime := (mem_outerPrimes_iff.mp hp).2.2
  have hp'prime : p'.Prime := (mem_outerPrimes_iff.mp hp').2.2
  have h := congrArg (fun n => smoothPart n y) hcollision
  rw [smoothPart_shiftedTotient_mul_prime_eq hmpos hpprime hmp hyp hφ,
    smoothPart_shiftedTotient_mul_prime_eq hm'pos hp'prime hm'p' hyp' hφ'] at h
  exact h

end Erdos822
