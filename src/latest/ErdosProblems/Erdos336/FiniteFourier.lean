import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Elementary finite Fourier identities for cyclic groups
-/

namespace Erdos336

open scoped BigOperators ComplexConjugate
open Finset

noncomputable def cyclicFinsetFourier {N : ℕ} [NeZero N]
    (A : Finset (ZMod N)) (k : ZMod N) : ℂ :=
  ∑ a ∈ A, ZMod.stdAddChar (-(a * k))

@[simp] lemma cyclicFinsetFourier_zero {N : ℕ} [NeZero N]
    (A : Finset (ZMod N)) :
    cyclicFinsetFourier A 0 = A.card := by
  simp [cyclicFinsetFourier]

lemma cyclic_character_orthogonality {N : ℕ} [NeZero N] (x : ZMod N) :
    (∑ k : ZMod N, ZMod.stdAddChar (x * k)) =
      if x = 0 then (N : ℂ) else 0 := by
  simpa [mul_comm] using
    AddChar.sum_mulShift x (ZMod.isPrimitive_stdAddChar N)

/-- Parseval for the unnormalized Fourier transform of a finite-set
indicator. -/
theorem sum_fourier_mul_conj {N : ℕ} [NeZero N]
    (A : Finset (ZMod N)) :
    (∑ k : ZMod N,
      cyclicFinsetFourier A k * conj (cyclicFinsetFourier A k)) =
      (N : ℂ) * A.card := by
  classical
  simp only [cyclicFinsetFourier, map_sum, Finset.sum_mul_sum]
  have hconj (y : ZMod N) :
      conj (ZMod.stdAddChar (-y)) = ZMod.stdAddChar y := by
    rw [AddChar.map_neg_eq_conj, Complex.conj_conj]
  simp_rw [hconj]
  simp_rw [← AddChar.map_add_eq_mul]
  have harg (i j k : ZMod N) : -(i * k) + j * k = (j - i) * k := by ring
  simp_rw [harg]
  rw [Finset.sum_comm]
  calc
    _ = ∑ y ∈ A, (N : ℂ) := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [Finset.sum_comm]
      simp_rw [cyclic_character_orthogonality]
      rw [Finset.sum_eq_single y]
      · simp
      · intro b hb hby
        simp only [if_neg (sub_ne_zero.mpr hby)]
      · exact fun h => (h hy).elim
    _ = (N : ℂ) * A.card := by
      rw [Finset.sum_const]
      simp [mul_comm]

/-- Real-valued Parseval form. -/
theorem sum_norm_sq_cyclicFinsetFourier {N : ℕ} [NeZero N]
    (A : Finset (ZMod N)) :
    (∑ k : ZMod N, ‖cyclicFinsetFourier A k‖ ^ 2) =
      (N : ℝ) * A.card := by
  have hc := sum_fourier_mul_conj A
  have h := congrArg Complex.re hc
  have hre (z : ℂ) : (z * conj z).re = Complex.normSq z := by
    rw [Complex.mul_conj]
    simp
  rw [Complex.re_sum] at h
  simp_rw [hre] at h
  simpa [Complex.normSq_eq_norm_sq] using h

/-- Frequencies where the unnormalized Fourier coefficient has norm at least
`τ`. -/
noncomputable def cyclicLargeSpectrum {N : ℕ} [NeZero N]
    (A : Finset (ZMod N)) (τ : ℝ) : Finset (ZMod N) :=
  Finset.univ.filter fun k => τ ≤ ‖cyclicFinsetFourier A k‖

/-- Parseval bounds the cardinality of the large spectrum. -/
theorem card_cyclicLargeSpectrum_mul_sq_le {N : ℕ} [NeZero N]
    (A : Finset (ZMod N)) {τ : ℝ} (hτ : 0 ≤ τ) :
    ((cyclicLargeSpectrum A τ).card : ℝ) * τ ^ 2 ≤
      (N : ℝ) * A.card := by
  classical
  let Γ := cyclicLargeSpectrum A τ
  have hpoint : ∀ k ∈ Γ, τ ^ 2 ≤ ‖cyclicFinsetFourier A k‖ ^ 2 := by
    intro k hk
    have hk' : τ ≤ ‖cyclicFinsetFourier A k‖ := by
      simpa [Γ, cyclicLargeSpectrum] using hk
    nlinarith [norm_nonneg (cyclicFinsetFourier A k)]
  have hlower := Finset.card_nsmul_le_sum Γ
    (fun k => ‖cyclicFinsetFourier A k‖ ^ 2) (τ ^ 2) hpoint
  have hupper :
      (∑ k ∈ Γ, ‖cyclicFinsetFourier A k‖ ^ 2) ≤
        ∑ k : ZMod N, ‖cyclicFinsetFourier A k‖ ^ 2 := by
    exact Finset.sum_le_univ_sum_of_nonneg fun k => sq_nonneg _
  rw [sum_norm_sq_cyclicFinsetFourier A] at hupper
  simpa [nsmul_eq_mul] using le_trans hlower hupper

end Erdos336
