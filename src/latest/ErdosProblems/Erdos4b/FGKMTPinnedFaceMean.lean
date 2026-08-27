/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPinnedFaceCost

/-!
# Uniform harmonic approximation of an actual profile slice

The face-majorant error remains valid when the principal face integral
is zero. The absolute constant precedes the dimension, modulus, radius,
denominator choice, and all remaining coordinates.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

theorem exists_sieveProfile_face_smooth_error :
    ∃ C : ℝ, 0 < C ∧ ∀ {m M R : ℕ}, 1 ≤ m → 10000 ≤ Real.log (m + 1 : ℕ) →
      0 < M → 1 < R →
      (∀ p : ℕ, p.Prime → p ≤ 2 * (m + 1) ^ 2 → p ∣ M) → ∀ pinned : Bool,
      ∀ t : Fin m → ℝ, (∀ i, 0 ≤ t i) →
        |(∑ a ∈ Finset.Icc 0 R,
            sieveProfile (m + 1) (m + 1) (Fin.cons (Real.log a / Real.log R) t) *
              roughSieveWeight M (actualSieveDenominator pinned (m + 1)) a) -
          sieveMainConstant M (actualSieveDenominator pinned (m + 1)) * Real.log R *
            (∫ x in (0 : ℝ)..1, sieveProfile (m + 1) (m + 1) (Fin.cons x t))| ≤
          C * sieveMainConstant M (actualSieveDenominator pinned (m + 1)) *
            modulusLogScale M ^ 3 * sieveProfileScale (m + 1) *
            majorantFaceValue (m + 1) m t := by
  obtain ⟨C₁, hC₁, hmean⟩ := exists_roughSieveWeight_smooth_error_logScale
  obtain ⟨C₂, hC₂, hderiv⟩ := exists_sieveProfile_face_deriv_bound
  refine ⟨C₁ * C₂, mul_pos hC₁ hC₂, ?_⟩
  intro m M R hm hlog hM hR hsmall pinned t ht
  let g := actualSieveDenominator pinned (m + 1)
  let G := fun x => sieveProfile (m + 1) (m + 1) (Fin.cons x t)
  have hchain := actualSieveDenominator_chain (by omega : 2 ≤ m + 1)
    (by omega : 1 ≤ m + 1) hsmall pinned
  have hg (p : ℕ) (hp : p.Prime) (hpM : ¬p ∣ M) :
      (p : ℝ) / 2 ≤ g p ∧ |g p - p| ≤ 2 * (m + 1 : ℕ) ∧ g p ≤ p - 1 := by
    simpa only [g, Nat.cast_zero, add_zero] using hchain 0 (by omega) p hp hpM
  have hG : ContDiff ℝ 1 G := by
    apply (sieveProfile_contDiff (m + 1) (m + 1)).comp
    apply contDiff_pi.mpr
    intro i
    refine Fin.cases ?_ (fun q => ?_) i
    · simp only [Fin.cons_zero]
      exact contDiff_id
    · simp only [Fin.cons_succ]
      exact contDiff_const
  have hG1 : G 1 = 0 := sieveProfile_cons_zero_of_one_le (m + 1) m t ht le_rfl
  have h := hmean (Nat.succ_pos m) hM hR
    (fun p hp hpk => hsmall p hp (by
      change p ≤ (m + 1) ^ 2 at hpk
      omega)) g
    (fun p hp hpM => (hg p hp hpM).1) (fun p hp hpM => (hg p hp hpM).2.1)
    (fun p hp hpM => (hg p hp hpM).2.2) hG
    (V := C₂ * sieveProfileScale (m + 1) * majorantFaceValue (m + 1) m t)
    (fun x hx => hderiv hm hlog t ht x hx.1)
  rw [hG1, abs_zero, zero_add] at h
  convert h using 1
  ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.exists_sieveProfile_face_smooth_error
