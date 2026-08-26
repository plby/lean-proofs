import ErdosProblems.Erdos67b.PrimeGraph
import ErdosProblems.Erdos67b.PrimeFourier

/-!
# Exact finite Fourier expansion of the prime graph mean

The transform is unnormalised and the frequency average has the factor
`1/T`. Every equality uses literal integer offsets; a no-wrap hypothesis
is checked before applying character orthogonality.
-/

open scoped BigOperators ComplexConjugate
open Finset
open Erdos438.Fourier

namespace Erdos67b

noncomputable section

/-- Unnormalised Fourier transform of a block, indexed from zero. -/
def blockFourier {H : ℕ} (T : ℕ) (b : Fin H → ℂ) (t : ℤ) : ℂ :=
  ∑ j : Fin H, b j * phase T t j.1

/-- The Fourier multiplier for the reciprocal-prime graph. -/
def primeGraphMultiplier (T h : ℕ) (s : Finset ℕ) (t : ℤ) : ℂ :=
  ∑ p ∈ s, (p : ℂ)⁻¹ * phase T t (p * h : ℕ)

theorem norm_blockFourier_le {H : ℕ} (T : ℕ) (b : Fin H → ℂ) (t : ℤ)
    {B : ℝ} (hb : ∀ j, ‖b j‖ ≤ B) :
    ‖blockFourier T b t‖ ≤ H * B := by
  calc
    _ ≤ ∑ j : Fin H, ‖b j * phase T t j.1‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin H, B := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [norm_mul, norm_phase, mul_one] using hb j
    _ = H * B := by simp

/-- Expand a squared Fourier coefficient with one additional shift. -/
theorem blockFourier_norm_sq_mul_phase {H : ℕ} (T : ℕ) (b : Fin H → ℂ)
    (t : ℤ) (a : ℕ) :
    (‖blockFourier T b t‖ : ℂ) ^ 2 * phase T t a =
      ∑ j : Fin H, ∑ k : Fin H,
        (b j * conj (b k)) * phase T t ((j.1 : ℤ) + a - k.1) := by
  rw [← Complex.mul_conj']
  simp only [blockFourier, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [conj_phase]
  calc
    (b j * phase T t j.1) * (conj (b k) * phase T t (-(k.1 : ℤ))) * phase T t a =
        (b j * conj (b k)) *
          (phase T t j.1 * phase T t a * phase T t (-(k.1 : ℤ))) := by ring
    _ = _ := by
      rw [← phase_add_right, ← phase_add_right]
      congr 2

/-- Orthogonality detects the actual edge equation, since both endpoints
are strictly smaller than the frequency modulus. -/
theorem sum_phase_block_shift {H T : ℕ} [NeZero T] (a : ℕ)
    (hT : H + a ≤ T) (j k : Fin H) :
    (∑ t ∈ Finset.range T, phase T (t : ℤ) ((j.1 : ℤ) + a - k.1)) =
      if j.1 + a = k.1 then (T : ℂ) else 0 := by
  rw [phase_orthogonality]
  have hcond : (((j.1 : ℤ) + a - k.1 : ℤ) : ZMod T) = 0 ↔ j.1 + a = k.1 := by
    simp only [Int.cast_sub, Int.cast_natCast, sub_eq_zero, ← Nat.cast_add]
    rw [ZMod.natCast_eq_natCast_iff]
    constructor
    · intro hmod
      exact hmod.eq_of_lt_of_lt (by omega) (by omega)
    · intro heq
      rw [heq]
  simp only [hcond]

/-- Exact shifted correlation identity for a block without cyclic edges. -/
theorem sum_blockFourier_norm_sq_mul_phase {H T : ℕ} [NeZero T]
    (b : Fin H → ℂ) (p h : ℕ) (hT : H + p * h ≤ T) :
    (∑ t ∈ Finset.range T,
      (‖blockFourier T b (t : ℤ)‖ : ℂ) ^ 2 * phase T (t : ℤ) (p * h : ℕ)) =
        (T : ℂ) * ∑ j : Fin H, primeGraphEdge b p h j := by
  classical
  simp_rw [blockFourier_norm_sq_mul_phase]
  rw [Finset.sum_comm]
  calc
    _ = ∑ j : Fin H, ∑ k : Fin H,
        (b j * conj (b k)) *
          ∑ t ∈ Finset.range T, phase T (t : ℤ) ((j.1 : ℤ) + (p * h : ℕ) - k.1) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
    _ = ∑ j : Fin H, ∑ k : Fin H,
        if j.1 + p * h = k.1 then (T : ℂ) * (b j * conj (b k)) else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      rw [sum_phase_block_shift (p * h) hT]
      split_ifs <;> ring
    _ = (T : ℂ) * ∑ j : Fin H, primeGraphEdge b p h j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j.1 + p * h < H
      · let k₀ : Fin H := ⟨j.1 + p * h, hj⟩
        have hcond (k : Fin H) : j.1 + p * h = k.1 ↔ k = k₀ := by
          constructor
          · intro hk
            exact Fin.ext hk.symm
          · intro hk
            rw [hk]
        simp_rw [hcond]
        simp [primeGraphEdge, hj, k₀]
      · have hcond (k : Fin H) : ¬ j.1 + p * h = k.1 := by omega
        simp [hcond, primeGraphEdge, hj]

/-- Parseval with the same transform normalization as the graph identity. -/
theorem sum_blockFourier_norm_sq {H T : ℕ} [NeZero T]
    (b : Fin H → ℂ) (hT : H ≤ T) :
    (∑ t ∈ Finset.range T, ‖blockFourier T b (t : ℤ)‖ ^ 2 : ℝ) =
      T * ∑ j : Fin H, ‖b j‖ ^ 2 := by
  have h := sum_blockFourier_norm_sq_mul_phase b 0 0 (by simpa using hT)
  simp only [Nat.zero_mul, Nat.cast_zero, phase_zero_right, mul_one] at h
  have hedge (j : Fin H) : primeGraphEdge b 0 0 j = (‖b j‖ : ℂ) ^ 2 := by
    simp only [primeGraphEdge, Nat.zero_mul, Nat.add_zero, j.isLt, dif_pos]
    exact Complex.mul_conj' (b j)
  simp_rw [hedge] at h
  exact_mod_cast h

theorem sum_blockFourier_norm_sq_le {H T : ℕ} [NeZero T]
    (b : Fin H → ℂ) (hT : H ≤ T) (hb : ∀ j, ‖b j‖ ≤ 1) :
    (∑ t ∈ Finset.range T, ‖blockFourier T b (t : ℤ)‖ ^ 2 : ℝ) ≤ T * H := by
  rw [sum_blockFourier_norm_sq b hT]
  have hsum : (∑ j : Fin H, ‖b j‖ ^ 2 : ℝ) ≤ H := by
    calc
      _ ≤ ∑ _j : Fin H, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        nlinarith [hb j, norm_nonneg (b j)]
      _ = H := by simp
  exact mul_le_mul_of_nonneg_left hsum (by positivity)

/-- When the active primes lie in the ambient index set, the mean is
the ordinary reciprocal-prime sum. -/
theorem primeGraphMean_eq_sum {H : ℕ} (b : Fin H → ℂ) (h : ℕ) (s : Finset ℕ)
    (hs : s ⊆ Nat.primesLE H) :
    primeGraphMean b h s = ∑ p ∈ s, (p : ℂ)⁻¹ * ∑ j : Fin H, primeGraphEdge b p h j := by
  classical
  calc
    _ = ∑ p ∈ Nat.primesLE H, if p ∈ s then
        (p : ℝ)⁻¹ • ∑ j : Fin H, primeGraphEdge b p h j else 0 :=
      Finset.sum_coe_sort (Nat.primesLE H) _
    _ = ∑ p ∈ s, (p : ℝ)⁻¹ • ∑ j : Fin H, primeGraphEdge b p h j := by
      rw [← Finset.sum_filter]
      congr 1
      ext p
      simp only [Finset.mem_filter]
      exact ⟨fun hp ↦ hp.2, fun hp ↦ ⟨hs hp, hp⟩⟩
    _ = _ := by simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast]

/-- The graph mean is exactly the Fourier multiplier pairing. -/
theorem primeGraphMean_eq_fourier {H T : ℕ} [NeZero T]
    (b : Fin H → ℂ) (h : ℕ) (s : Finset ℕ) (hs : s ⊆ Nat.primesLE H)
    (hT : ∀ p ∈ s, H + p * h ≤ T) :
    primeGraphMean b h s = (T : ℂ)⁻¹ * ∑ t ∈ Finset.range T,
      (‖blockFourier T b (t : ℤ)‖ : ℂ) ^ 2 * primeGraphMultiplier T h s (t : ℤ) := by
  classical
  have hT0 : (T : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne T)
  have hsum : (∑ t ∈ Finset.range T,
      (‖blockFourier T b (t : ℤ)‖ : ℂ) ^ 2 * primeGraphMultiplier T h s (t : ℤ)) =
        (T : ℂ) * primeGraphMean b h s := by
    simp only [primeGraphMultiplier, Finset.mul_sum]
    rw [Finset.sum_comm, primeGraphMean_eq_sum b h s hs, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    calc
      _ = (p : ℂ)⁻¹ * ∑ t ∈ Finset.range T,
          (‖blockFourier T b (t : ℤ)‖ : ℂ) ^ 2 * phase T (t : ℤ) (p * h : ℕ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t _
        ring
      _ = _ := by rw [sum_blockFourier_norm_sq_mul_phase b p h (hT p hp)]; ring
  rw [hsum, ← mul_assoc, inv_mul_cancel₀ hT0, one_mul]

end

end Erdos67b
