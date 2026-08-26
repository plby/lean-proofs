import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The two-residue lower construction when the weak order is divisible by three

For `h=3u`, Plagne's extremal cyclic construction uses modulus
`g=3u²+4u+1` and residues `{1, x}`, where `x=3u+3`.  This file verifies the
entire finite covering calculation: every residue modulo `g` is a positive
sum of at most `3u` copies of `1` and `x`.
-/

namespace Erdos336.Problem336

/-- Modulus in the `h=3u` lower construction. -/
def lowerModulus (u : ℕ) : ℕ := 3 * u ^ 2 + 4 * u + 1

/-- The second residue in the `h=3u` lower construction. -/
def lowerStep (u : ℕ) : ℕ := 3 * u + 3

lemma lower_modulus_identity (u : ℕ) :
    lowerModulus u + (2 * u + 2) = (u + 1) * lowerStep u := by
  simp [lowerModulus, lowerStep]
  ring

/-- Every standard residue modulo `g` has a representative of the form
`Q*x+R`, using between one and `3u` summands.  The representative is either
`n` itself or `n+g`, so this is an exact, readily checkable modular cover. -/
theorem lower_cyclic_cover_multiple_three
    (u n : ℕ) (hu : 1 ≤ u) (hn : n < lowerModulus u) :
    ∃ Q R : ℕ,
      1 ≤ Q + R ∧ Q + R ≤ 3 * u ∧
      (Q * lowerStep u + R = n ∨
        Q * lowerStep u + R = n + lowerModulus u) := by
  by_cases hn0 : n = 0
  · subst n
    refine ⟨u, u + 1, by omega, by omega, Or.inr ?_⟩
    simp [lowerModulus, lowerStep]
    ring
  let x := lowerStep u
  let q := n / x
  let r := n % x
  have hxpos : 0 < x := by simp [x, lowerStep]
  have hrx : r < x := Nat.mod_lt n hxpos
  have hnqr : n = q * x + r := by
    dsimp [q, r]
    simpa [Nat.mul_comm] using (Nat.div_add_mod n x).symm
  have hqx : q ≤ u := by
    by_contra hnot
    have huq : u + 1 ≤ q := by omega
    have hmul : (u + 1) * x ≤ q * x :=
      Nat.mul_le_mul_right x huq
    have hgap : lowerModulus u < (u + 1) * x := by
      dsimp [x]
      simp [lowerModulus, lowerStep]
      nlinarith
    omega
  have hsumpos : 0 < q + r := by
    by_contra hz
    have hzero : q + r = 0 := Nat.eq_zero_of_not_pos hz
    obtain ⟨hq0, hr0⟩ := Nat.add_eq_zero.mp hzero
    rw [hq0, hr0] at hnqr
    simp at hnqr
    exact hn0 hnqr
  by_cases hqu : q = u
  · have hn_expand : n = u * x + r := by simpa [hqu] using hnqr
    have hg_split : lowerModulus u = u * x + (u + 1) := by
      dsimp [x]
      simp [lowerModulus, lowerStep]
      ring
    have hru : r ≤ u := by omega
    refine ⟨q, r, hsumpos, by omega, Or.inl ?_⟩
    · simpa [x] using hnqr.symm
  · have hq_lt : q < u := lt_of_le_of_ne hqx hqu
    by_cases hshort : q + r ≤ 3 * u
    · refine ⟨q, r, hsumpos, hshort, Or.inl ?_⟩
      · simpa [x] using hnqr.symm
    · have hrlarge : 2 * u + 2 ≤ r := by omega
      have hr_upper : r ≤ 3 * u + 2 := by
        dsimp [x, lowerStep] at hrx
        omega
      let Q := q + u + 1
      let R := r - (2 * u + 2)
      have hr_split : R + (2 * u + 2) = r := by
        dsimp [R]
        omega
      have hRle : R ≤ r := by exact Nat.sub_le r (2 * u + 2)
      refine ⟨Q, R, by omega, ?_, Or.inr ?_⟩
      · dsimp [Q]
        omega
      · change Q * x + R = n + lowerModulus u
        have hQx : Q * x = q * x + (u + 1) * x := by
          dsimp [Q]
          ring
        have hid : (u + 1) * x = lowerModulus u + (2 * u + 2) := by
          simpa [x] using (lower_modulus_identity u).symm
        rw [hQx, hid]
        omega

/-- The difference between the two residues is invertible modulo the
construction modulus. -/
theorem lower_step_sub_one_coprime (u : ℕ) :
    (lowerStep u - 1).Coprime (lowerModulus u) := by
  have hid :
      (lowerStep u - 1) * (lowerStep u - 1) =
        lowerModulus u * 3 + 1 := by
    simp [lowerStep, lowerModulus]
    ring
  show Nat.gcd (lowerStep u - 1) (lowerModulus u) = 1
  apply Nat.dvd_one.mp
  have hleft : Nat.gcd (lowerStep u - 1) (lowerModulus u) ∣
      (lowerStep u - 1) * (lowerStep u - 1) :=
    dvd_mul_of_dvd_left (Nat.gcd_dvd_left _ _) _
  have hright : Nat.gcd (lowerStep u - 1) (lowerModulus u) ∣
      lowerModulus u * 3 := dvd_mul_of_dvd_left (Nat.gcd_dvd_right _ _) _
  rw [hid] at hleft
  exact (Nat.dvd_add_iff_right hright).mpr hleft

/-- Multiples of the residue difference run through every residue modulo the
construction modulus.  This is the exact-exponent half of the two-residue
construction. -/
theorem lower_difference_hits_every_residue
    (u n : ℕ) (hu : 1 ≤ u) :
    ∃ j : ℕ, j < lowerModulus u ∧
      (lowerStep u - 1) * j % lowerModulus u = n % lowerModulus u := by
  have hg : lowerModulus u ≠ 0 := by
    simp [lowerModulus]
  exact Nat.exists_mul_mod_eq_of_coprime n
    (lower_step_sub_one_coprime u) hg

end Erdos336.Problem336
