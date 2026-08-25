import ErdosProblems.Erdos964.ScalarAffineScaleBounds
import ErdosProblems.Erdos964.SemiprimeIntervals

/-!
# A common prime support for translated affine intervals

Use parameter intervals `[t²,2t²)`, distribution scale `L = K*t`, and
smaller primes below `t/(K+1)`. The larger prime then exceeds `L`.
-/

namespace Erdos964

open BoundedGaps.Maynard

noncomputable def scalarSmallPrimeSupport (η : ℝ) (K t : ℕ) : Finset ℕ := by
  classical
  exact (t / (K + 1)).primesLE.filter (fun p => Real.rpow (K * t : ℕ) η < p)

theorem scalarSmallPrimeSupport_spec (η : ℝ) (K t p : ℕ)
    (hp : p ∈ scalarSmallPrimeSupport η K t) :
    p.Prime ∧ p ≤ t / (K + 1) ∧ Real.rpow (K * t : ℕ) η < p := by
  have hp' := Finset.mem_filter.mp hp
  have hp'' := Nat.mem_primesLE.mp hp'.1
  exact ⟨hp''.2, hp''.1, hp'.2⟩

theorem scalarSmallPrimeSupport_le_scale (η : ℝ) (K t p : ℕ) (hK : 1 ≤ K)
    (hp : p ∈ scalarSmallPrimeSupport η K t) : p ≤ K * t := by
  exact (scalarSmallPrimeSupport_spec η K t p hp).2.1.trans
    ((Nat.div_le_self t (K + 1)).trans (Nat.le_mul_of_pos_left t hK))

theorem scalarSmallPrimeSupport_mul_scale_le_square (η : ℝ) (K t p : ℕ)
    (hp : p ∈ scalarSmallPrimeSupport η K t) : p * (K * t) ≤ t ^ 2 := by
  have hpmul := (Nat.le_div_iff_mul_le (Nat.succ_pos K)).mp
    (scalarSmallPrimeSupport_spec η K t p hp).2.1
  have hpk : p * K ≤ t := (Nat.mul_le_mul_left p (Nat.le_succ K)).trans hpmul
  simpa only [Nat.mul_assoc, pow_two] using Nat.mul_le_mul_right t hpk

theorem scalar_affine_interval_bounds (m c K t : ℕ) (hm : 1 ≤ m) (hc : 1 ≤ c)
    (ht : 2 ≤ t) (hK : 2 * m + c ≤ K ^ 2) :
    t ^ 2 ≤ m * t ^ 2 + c - 1 ∧
      m * t ^ 2 + c - 1 ≤ m * (2 * t ^ 2) + c - 1 ∧
      m * (2 * t ^ 2) + c - 1 ≤ (K * t) ^ 2 := by
  have htpos : 0 < t ^ 2 := by positivity
  have hmt : t ^ 2 ≤ m * t ^ 2 := Nat.le_mul_of_pos_left _ hm
  have hm2t : m * t ^ 2 ≤ m * (2 * t ^ 2) := Nat.mul_le_mul_left m (by omega)
  have hct : c ≤ c * t ^ 2 := Nat.le_mul_of_pos_right c htpos
  have hcap : m * (2 * t ^ 2) + c ≤ (K * t) ^ 2 := by
    calc
      _ ≤ (2 * m + c) * t ^ 2 := by nlinarith
      _ ≤ K ^ 2 * t ^ 2 := Nat.mul_le_mul_right _ hK
      _ = _ := by ring
  omega

theorem semiprimeScaleInterval_subset_Ioc (P : Finset ℕ) (L x z : ℕ) (hxz : x ≤ z) :
    semiprimeScaleInterval P L x z ⊆ Finset.Ioc x z := by
  intro n hn
  rw [semiprimeScaleInterval_eq_filter P L x z hxz] at hn
  have hn' := Finset.mem_filter.mp hn
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hn'.1
  exact Finset.mem_Ioc.mpr ⟨hn'.2, (Finset.mem_filter.mp hr).2⟩

theorem semiprimeScaleInterval_subset_exact_range (P : Finset ℕ) (L a b : ℕ)
    (ha : 0 < a) (hab : a ≤ b) :
    semiprimeScaleInterval P L (a - 1) (b - 1) ⊆ Finset.Ico a b := by
  intro n hn
  have h := Finset.mem_Ioc.mp
    (semiprimeScaleInterval_subset_Ioc P L (a - 1) (b - 1) (Nat.sub_le_sub_right hab 1) hn)
  exact Finset.mem_Ico.mpr (by omega)

theorem exists_scalarSmallPrimeSupport_coprime (m : ℕ) (hm : 0 < m)
    (η : ℝ) (hη : 0 < η) :
    ∃ t₀ : ℕ, 4 ≤ t₀ ∧ ∀ t : ℕ, t₀ ≤ t → ∀ K : ℕ, 1 ≤ K →
      ∀ p ∈ scalarSmallPrimeSupport η K t, p.Coprime m := by
  obtain ⟨t₀, ht₀, hmul⟩ := exists_mul_modulusCutoff_le m hm 0 η hη
  refine ⟨t₀, ht₀, ?_⟩
  intro t ht K hK p hp
  have htL : t ≤ K * t := Nat.le_mul_of_pos_left t hK
  have h := hmul (K * t) (ht.trans htL)
  have hzero : modulusCutoff 0 (K * t) = 1 := by
    simp only [modulusCutoff, Real.rpow_eq_pow, Real.rpow_zero, Nat.floor_one]
  rw [hzero, mul_one] at h
  have hmR : (m : ℝ) ≤ Real.rpow (K * t : ℕ) η :=
    (show (m : ℝ) ≤ (modulusCutoff η (K * t) : ℝ) by exact_mod_cast h).trans
      (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) η))
  have hp' := scalarSmallPrimeSupport_spec η K t p hp
  apply hp'.1.coprime_iff_not_dvd.mpr
  intro hpm
  have hpmR : (p : ℝ) ≤ m := by exact_mod_cast Nat.le_of_dvd hm hpm
  exact (not_le_of_gt hp'.2.2) (hpmR.trans hmR)

theorem exists_scalar_affine_sieve_ranges (m c K : ℕ) (hm : 1 ≤ m) (hc : 1 ≤ c)
    (hK : 1 ≤ K) (hKsize : 2 * m + c ≤ K ^ 2)
    (β η θβ θp : ℝ) (hβ : 0 < β) (hη : 0 < η) (hβθβ : 2 * β ≤ θβ)
    (hβθp : β < θp) (hθphalf : θp < 1 / 2) :
    ∃ t₀ : ℕ, 4 ≤ t₀ ∧ ∀ t : ℕ, t₀ ≤ t →
      let R := modulusCutoff β t
      let L := K * t
      let P := scalarSmallPrimeSupport η K t
      let x := m * t ^ 2 + c - 1
      let z := m * (2 * t ^ 2) + c - 1
      1 ≤ R ∧ R ≤ L ∧ m * R ^ 2 ≤ L ∧ R ^ 2 ≤ modulusCutoff θβ L ∧
        x ∈ Finset.Icc 1 (L ^ 2) ∧ z ∈ Finset.Icc 1 (L ^ 2) ∧ x ≤ z ∧
        (∀ p ∈ P, p.Prime ∧ p ≤ L ∧ Real.rpow (L : ℝ) η < p ∧ p.Coprime m ∧
          p * L ≤ x ∧ R ^ 2 / p ≤ modulusCutoff θp (x / p)) ∧
        semiprimeScaleInterval P L x z ⊆ Finset.Ico (m * t ^ 2 + c) (m * (2 * t ^ 2) + c) := by
  have hβhalf : β < 1 / 2 := hβθp.trans hθphalf
  obtain ⟨tM, htM, hM⟩ := exists_scalar_radius_square_le_scale m hm β hβhalf
  obtain ⟨tP, htP, hPrime⟩ := exists_scalar_radius_prime_cutoff β θp hβθp
    (hβ.trans hβθp).le (by linarith)
  obtain ⟨tC, htC, hC⟩ := exists_scalarSmallPrimeSupport_coprime m hm η hη
  refine ⟨max tM (max tP tC), htM.trans (le_max_left _ _), ?_⟩
  intro t ht
  have hMt : tM ≤ t := (le_max_left _ _).trans ht
  have hPt : tP ≤ t := (le_max_left _ _).trans ((le_max_right _ _).trans ht)
  have hCt : tC ≤ t := (le_max_right _ _).trans ((le_max_right _ _).trans ht)
  have ht4 : 4 ≤ t := htM.trans hMt
  have htL : t ≤ K * t := Nat.le_mul_of_pos_left t hK
  have hR := scalar_radius_bounds t K (by omega) hK β hβ.le (by linarith)
  have hends := scalar_affine_interval_bounds m c K t hm hc (by omega) hKsize
  refine ⟨hR.1, hR.2, (hM t hMt).trans htL,
    scalar_radius_semiprime_cutoff t (K * t) (by omega) htL β θβ hβ.le hβθβ,
    Finset.mem_Icc.mpr ⟨?_, hends.2.1.trans hends.2.2⟩,
    Finset.mem_Icc.mpr ⟨?_, hends.2.2⟩, hends.2.1, ?_, ?_⟩
  · have ht2 : 1 ≤ t ^ 2 := by nlinarith
    exact ht2.trans hends.1
  · have ht2 : 1 ≤ t ^ 2 := by nlinarith
    exact (ht2.trans hends.1).trans hends.2.1
  · intro p hp
    have hp' := scalarSmallPrimeSupport_spec η K t p hp
    have hpt : p ≤ t := hp'.2.1.trans (Nat.div_le_self t (K + 1))
    have hpx : p ≤ m * t ^ 2 + c - 1 :=
      (hpt.trans (by nlinarith : t ≤ t ^ 2)).trans hends.1
    exact ⟨hp'.1, scalarSmallPrimeSupport_le_scale η K t p hK hp, hp'.2.2,
      hC t hCt K hK p hp,
      (scalarSmallPrimeSupport_mul_scale_le_square η K t p hp).trans hends.1,
      hPrime t hPt _ hends.1 p hp'.1.pos hpx⟩
  · apply semiprimeScaleInterval_subset_exact_range
    · omega
    · exact Nat.add_le_add_right (Nat.mul_le_mul_left m (by omega)) c

end Erdos964
