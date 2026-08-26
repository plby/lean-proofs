import ErdosProblems.Erdos941.PrimeSquareLifting
import ErdosProblems.Erdos941.PlaneWords

/-! # From projective conic and plane certificates to prime-square targets -/

namespace Erdos941

open PairLocal

theorem heightLinear_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (a b c : R) (v : R × R × R) :
    φ (heightLinear a b c v) = heightLinear (φ a) (φ b) (φ c) (mapCoeffs φ v) := by
  simp [heightLinear, mapCoeffs]

theorem targetLine_eq_smul {R : Type*} [CommRing R] {r s : R} {v : R × R × R}
    (h : OnTargetLine r s v) : v = v.2.1 • (r, 1, s) := by
  apply Prod.ext
  · simpa only [Prod.smul_fst, smul_eq_mul, mul_comm] using h.1
  · apply Prod.ext
    · simp
    · simpa only [Prod.smul_snd, smul_eq_mul, mul_comm] using h.2

theorem exists_primeSquare_smul_of_reduction_zero {p : ℕ}
    (v : ZMod (p ^ 2) × ZMod (p ^ 2) × ZMod (p ^ 2))
    (hv : mapCoeffs (primeSquareReduce p) v = 0) :
    ∃ z : ZMod (p ^ 2) × ZMod (p ^ 2) × ZMod (p ^ 2), v = (p : ZMod (p ^ 2)) • z := by
  obtain ⟨x, hx⟩ := (primeSquare_reduce_zero_iff v.1).mp (congrArg Prod.fst hv)
  obtain ⟨y, hy⟩ := (primeSquare_reduce_zero_iff v.2.1).mp (congrArg (fun u => u.2.1) hv)
  obtain ⟨z, hz⟩ := (primeSquare_reduce_zero_iff v.2.2).mp (congrArg (fun u => u.2.2) hv)
  exact ⟨(x, y, z), Prod.ext hx (Prod.ext hy hz)⟩

theorem kernelLinear_prime_reduction {p : ℕ} (u : ZMod (p ^ 2))
    (v : ZMod (p ^ 2) × ZMod (p ^ 2) × ZMod (p ^ 2)) :
    mapCoeffs (primeSquareReduce p) (kernelLinear (p : ZMod (p ^ 2)) u v) =
      mapCoeffs (primeSquareReduce p) v := by
  ext <;> simp [mapCoeffs, kernelLinear]

theorem exists_word_primeSquare_target {p : ℕ} [Fact p.Prime]
    (t u r s a b c : ZMod (p ^ 2)) (ht : 3 * t = 1)
    (w₀ : List Axis) (hw₀ : linearWord t w₀ = kernelLinear (p : ZMod (p ^ 2)) u)
    (hline : primeSquareReduce p (a * r + b + c * s) = 0)
    (hderiv : primeSquareReduce p (u * ((a - b) * s + c * (1 - r))) ≠ 0)
    (hconic : ∀ z : ZMod p × ZMod p × ZMod p, normThree z = 0 →
      ∃ w : List Axis, OnTargetLine (primeSquareReduce p r) (primeSquareReduce p s)
        (linearWord (primeSquareReduce p t) w z))
    (hplane : ∀ z : ZMod p × ZMod p × ZMod p, ∃ w : List Axis,
      heightLinear (primeSquareReduce p a) (primeSquareReduce p b) (primeSquareReduce p c)
        (linearWord (primeSquareReduce p t) w z) = 0)
    (v : ZMod (p ^ 2) × ZMod (p ^ 2) × ZMod (p ^ 2))
    (hv : normThree (mapCoeffs (primeSquareReduce p) v) = 0) :
    ∃ w : List Axis,
      OnTargetLine (primeSquareReduce p r) (primeSquareReduce p s)
        (mapCoeffs (primeSquareReduce p) (linearWord t w v)) ∧
      heightLinear a b c (linearWord t w v) = 0 := by
  let ρ := primeSquareReduce p
  by_cases hz : mapCoeffs ρ v = 0
  · obtain ⟨z, hzv⟩ := exists_primeSquare_smul_of_reduction_zero v hz
    obtain ⟨w, hw⟩ := hplane (mapCoeffs ρ z)
    refine ⟨w, ?_, ?_⟩
    · rw [linearWord_map, hz, map_zero]
      simp [OnTargetLine]
    · rw [hzv, map_smul, map_smul]
      change (p : ZMod (p ^ 2)) * heightLinear a b c (linearWord t w z) = 0
      apply primeSquare_mul_zero
      rw [heightLinear_map, linearWord_map]
      exact hw
  · obtain ⟨w, hw⟩ := hconic (mapCoeffs ρ v) hv
    let z := linearWord t w v
    have hzmap : mapCoeffs ρ z = linearWord (ρ t) w (mapCoeffs ρ v) := linearWord_map ρ t w v
    have hztarget : OnTargetLine (ρ r) (ρ s) (mapCoeffs ρ z) := hzmap.symm ▸ hw
    have hzt : mapCoeffs ρ z ≠ 0 := by
      intro heq
      apply hz
      have ht' : 3 * ρ t = 1 := by
        have h := congrArg ρ ht
        simpa only [map_mul, map_ofNat, map_one] using h
      apply linearWord_injective ht' w
      rw [← hzmap, heq, map_zero]
    have hzB : ρ z.2.1 ≠ 0 := by
      intro hB
      apply hzt
      rw [targetLine_eq_smul hztarget]
      change (ρ z.2.1) • _ = 0
      rw [hB, zero_smul]
    have hheight : ρ (heightLinear a b c z) = 0 := by
      rw [heightLinear_map, targetLine_eq_smul hztarget, map_smul]
      change ρ z.2.1 * (ρ a * ρ r + ρ b * 1 + ρ c * ρ s) = 0
      have hh : ρ a * ρ r + ρ b + ρ c * ρ s = 0 := by
        simpa only [map_add, map_mul] using hline
      rw [mul_one, hh, mul_zero]
    have hdiff : ρ (u * ((a - b) * z.2.2 + c * (z.2.1 - z.1))) ≠ 0 := by
      have hA := hztarget.1
      have hC := hztarget.2
      change ρ z.1 = ρ r * ρ z.2.1 at hA
      change ρ z.2.2 = ρ s * ρ z.2.1 at hC
      have he : ρ (u * ((a - b) * z.2.2 + c * (z.2.1 - z.1))) =
          ρ (u * ((a - b) * s + c * (1 - r))) * ρ z.2.1 := by
        simp only [map_mul, map_add, map_sub, map_one, hA, hC]
        ring
      rw [he]
      exact mul_ne_zero hderiv hzB
    obtain ⟨j, hj⟩ := exists_kernel_word_kill_height t u a b c w₀ hw₀ z hheight hdiff
    refine ⟨w ++ (List.replicate j w₀).flatten, ?_, ?_⟩
    · rw [linearWord_append]
      change OnTargetLine (ρ r) (ρ s)
        (mapCoeffs ρ (linearWord t (List.replicate j w₀).flatten z))
      rw [linearWord_replicate_kernel (primeSquare_square_zero p) w₀ hw₀,
        kernelLinear_prime_reduction]
      exact hztarget
    · rw [linearWord_append]
      exact hj

end Erdos941
