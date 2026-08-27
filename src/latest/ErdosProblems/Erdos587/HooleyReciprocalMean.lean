import ErdosProblems.Erdos587.HooleyReciprocalPowerMean
import ErdosProblems.Erdos587.HooleySmoothQuadratic

/-!
# The smooth reciprocal quadratic mean

The congruence for the inverse coefficient is explicit, so the theorem
applies to any chosen integer lifts. The weight and linear phase may
vary independently with the index.
-/

open scoped BigOperators FourierTransform SchwartzMap

namespace Erdos587

theorem exists_delta_smooth_reciprocal_sum_majorant {W : Set 𝓢(ℝ, ℂ)}
    (hW : Bornology.IsVonNBounded ℝ W) :
    ∃ C : ℝ, 0 < C ∧ ∀ f ∈ W, ∀ (c : ℕ) (A : ℕ → ℤ) (x : DeltaApproximant),
      0 < x.denominator → IsUnit (x.numerator : ZMod x.denominator) →
      ∀ K θ : ℝ, 0 < K → (x.denominator : ℝ) ≤ K →
      |deltaReciprocalFrequencyError c A x| ≤ 2 / ((x.denominator : ℝ) * K) →
      ‖deltaSmoothQuadraticSum f K ((A x.index : ℝ) / (c * x.index : ℕ)) θ‖ ^ 2 ≤
        C * deltaReciprocalMajorant K c A x := by
  obtain ⟨C, hC, hbound⟩ := exists_delta_family_smooth_major_arc_sq_bound hW
  refine ⟨C, hC, ?_⟩
  intro f hf c A x hb hunit K θ hK hbK herror
  have h := hbound f hf x.denominator hb x.numerator hunit K
    (deltaReciprocalFrequencyError c A x) θ hK hbK herror
  have hα : (x.numerator : ℝ) / x.denominator + deltaReciprocalFrequencyError c A x =
      (A x.index : ℝ) / (c * x.index : ℕ) := by dsimp only [deltaReciprocalFrequencyError]; ring
  rw [hα] at h
  exact h.trans_eq (by dsimp only [deltaReciprocalMajorant]; ring)

theorem exists_delta_smooth_reciprocal_mean {W : Set 𝓢(ℝ, ℂ)}
    (hW : Bornology.IsVonNBounded ℝ W) (a c : ℕ) (ha : 0 < a) (hc : 0 < c)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ q v X : ℕ, 0 < q → q.Coprime v → 2 ≤ X → q ≤ X →
      ∀ (A : ℕ → ℤ) (K R : ℝ), 1 ≤ K → 0 < R → 2 * K ≤ X →
      (a : ℝ) * K < q → (a : ℝ) * v * K + 16 * c * q * R ≤ X → K * (X : ℝ) ^ κ ≤ R →
      ∀ I : Finset ℕ, (∀ m ∈ I, R < m ∧ (m : ℝ) ≤ 2 * R) →
      (∀ m ∈ I, ((c * m : ℕ) : ℤ) ∣ (q : ℤ) * A m - (a : ℤ) * v) →
      ∀ (f : ℕ → 𝓢(ℝ, ℂ)) (θ : ℕ → ℝ), (∀ m ∈ I, f m ∈ W) →
      (∑ m ∈ I, ‖deltaSmoothQuadraticSum (f m) K ((A m : ℝ) / (c * m : ℕ)) (θ m)‖ ^ 2) ≤
        C * R * K * (max 1 (Real.log (Real.log (X : ℝ)))) ^ 7 := by
  classical
  obtain ⟨r, hrlarge⟩ := exists_nat_gt (3 / κ)
  have hrR : (0 : ℝ) < r := lt_trans (by positivity : 0 < 3 / κ) hrlarge
  have hr : 0 < r := by exact_mod_cast hrR
  have hexponent : 3 / (r : ℝ) ≤ κ := by
    apply (div_le_iff₀ hrR).mpr
    have h := (div_lt_iff₀ hκ).mp hrlarge
    nlinarith
  obtain ⟨C₀, hC₀, hpoint⟩ := exists_delta_smooth_reciprocal_sum_majorant hW
  obtain ⟨C₁, hC₁, hmean⟩ := exists_delta_reciprocal_majorant_power_mean a c r ha hc hr
  refine ⟨C₀ * C₁, by positivity, ?_⟩
  intro q v X hq hcop hX hqX A K R hK hR hKX hqa hvalue hsep I hI hrel f θ hf
  obtain ⟨D, hKD, hDK⟩ := exists_delta_dyadic_scale hK
  have hDX : 2 ^ D ≤ X := by exact_mod_cast hDK.trans hKX
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hsep' : K * (X : ℝ) ^ (3 / (r : ℝ)) ≤ R :=
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hX1 hexponent)
      (by linarith : 0 ≤ K)).trans hsep
  obtain ⟨x, hx⟩ := exists_delta_reciprocal_approximant_family c A hK
  have hindex (m : ℕ) : (x m).index = m := (hx m).1
  have hinj : Function.Injective x := by
    intro m n heq
    simpa only [hindex] using congrArg DeltaApproximant.index heq
  let S := I.image x
  have hlow (y : DeltaApproximant) (hy : y ∈ S) : R < y.index := by
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hy
    simpa only [hindex] using (hI m hm).1
  have hupp (y : DeltaApproximant) (hy : y ∈ S) : (y.index : ℝ) ≤ 2 * R := by
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hy
    simpa only [hindex] using (hI m hm).2
  have hden (y : DeltaApproximant) (hy : y ∈ S) :
      0 < y.denominator ∧ (y.denominator : ℝ) ≤ K := by
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hy
    exact ⟨(hx m).2.1, (hx m).2.2.1⟩
  have hrelations (y : DeltaApproximant) (hy : y ∈ S) :
      ((c * y.index : ℕ) : ℤ) ∣ (q : ℤ) * A y.index - (a : ℤ) * v := by
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hy
    simpa only [hindex] using hrel m hm
  have herror (y : DeltaApproximant) (hy : y ∈ S) :
      |deltaReciprocalFrequencyError c A y| ≤ 2 / ((y.denominator : ℝ) * K) := by
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hy
    exact (hx m).2.2.2.2
  have h := hmean q v X D hq hcop hX hqX hDX A K R hK hR hKD hDK hqa hvalue hsep'
    S hlow hupp hden hrelations herror
  calc
    _ ≤ ∑ m ∈ I, C₀ * deltaReciprocalMajorant K c A (x m) := by
      apply Finset.sum_le_sum
      intro m hm
      have hp := hpoint (f m) (hf m hm) c A (x m) (hx m).2.1 (hx m).2.2.2.1
        K (θ m) (by linarith) (hx m).2.2.1 (hx m).2.2.2.2
      simpa only [hindex] using hp
    _ = C₀ * ∑ y ∈ S, deltaReciprocalMajorant K c A y := by
      rw [Finset.mul_sum, Finset.sum_image hinj.injOn]
    _ ≤ C₀ * (C₁ * R * K * (max 1 (Real.log (Real.log (X : ℝ)))) ^ 7) :=
      mul_le_mul_of_nonneg_left h hC₀.le
    _ = _ := by ring

end Erdos587
