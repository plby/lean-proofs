import ErdosProblems.Erdos587.UniformNearby

/-! Signed frequencies and conjugation of the nearby remainder. -/

open MeasureTheory
open scoped BigOperators SchwartzMap ComplexConjugate

namespace Erdos587

noncomputable def conjugateSchwartz (f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  f.postcompCLM (Complex.conjCLE : ℂ →L[ℝ] ℂ)

lemma conjugateSchwartz_apply (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    conjugateSchwartz f x = conj (f x) := rfl

lemma conjugateSchwartz_conjugate (f : 𝓢(ℝ, ℂ)) :
    conjugateSchwartz (conjugateSchwartz f) = f := by
  ext x
  simp only [conjugateSchwartz_apply, Complex.conj_conj]

noncomputable def signedNearbyQuadraticRemainder (f : 𝓢(ℝ, ℂ))
    (q : ℕ) (m : ℤ) (v : ℕ) (b : ℤ) (L : ℝ) : ℂ :=
  (∑' z : ℤ, quadraticResiduePhase q (m * b) z *
      (phase (((m : ℝ) / (q * v)) * (z : ℝ) ^ 2) * f (L⁻¹ * z))) -
    (q : ℂ)⁻¹ * completeQuadraticGaussSum q (m * b) 0 *
      (∫ x : ℝ, phase (((m : ℝ) / (q * v)) * x ^ 2) * f (L⁻¹ * x))

lemma signedNearbyQuadraticRemainder_nat (f : 𝓢(ℝ, ℂ))
    (q m v : ℕ) (b : ℤ) (L : ℝ) :
    signedNearbyQuadraticRemainder f q (m : ℤ) v b L = nearbyQuadraticRemainder f q m v b L := by
  simp only [signedNearbyQuadraticRemainder, nearbyQuadraticRemainder, Int.cast_natCast]

lemma conj_quadraticResiduePhase (q : ℕ) (a z : ℤ) :
    conj (quadraticResiduePhase q a z) = quadraticResiduePhase q (-a) z := by
  unfold quadraticResiduePhase
  rw [← phase_neg]
  congr 1
  push_cast
  ring

lemma conj_chirp_weight (f : 𝓢(ℝ, ℂ)) (L A x : ℝ) :
    conj (phase (A * x ^ 2) * f (L⁻¹ * x)) =
      phase ((-A) * x ^ 2) * conjugateSchwartz f (L⁻¹ * x) := by
  rw [map_mul, ← phase_neg, conjugateSchwartz_apply]
  congr 1
  congr 1
  ring

lemma signedNearbyQuadraticRemainder_conj (f : 𝓢(ℝ, ℂ))
    {q : ℕ} (hq : 0 < q) (m : ℤ) (v : ℕ) (b : ℤ) (L : ℝ) :
    conj (signedNearbyQuadraticRemainder f q m v b L) =
      signedNearbyQuadraticRemainder (conjugateSchwartz f) q (-m) v b L := by
  unfold signedNearbyQuadraticRemainder
  rw [map_sub, Complex.conj_tsum, map_mul, map_mul, map_inv₀, map_natCast]
  rw [← completeQuadraticGaussSum_neg_zero hq (m * b), ← integral_conj]
  simp only [neg_mul, Int.cast_neg, neg_div]
  congr 1
  · apply tsum_congr
    intro z
    rw [map_mul, conj_quadraticResiduePhase, conj_chirp_weight]
    simp only [neg_mul]
  · congr 1
    apply integral_congr_ae
    filter_upwards [] with x
    simpa only [neg_mul] using conj_chirp_weight f L ((m : ℝ) / (q * v)) x

lemma signedNearbyQuadraticRemainder_neg_nat (f : 𝓢(ℝ, ℂ))
    {q : ℕ} (hq : 0 < q) (m v : ℕ) (b : ℤ) (L : ℝ) :
    signedNearbyQuadraticRemainder f q (-(m : ℤ)) v b L =
      conj (nearbyQuadraticRemainder (conjugateSchwartz f) q m v b L) := by
  have hh := signedNearbyQuadraticRemainder_conj (conjugateSchwartz f) hq (m : ℤ) v b L
  rw [conjugateSchwartz_conjugate, signedNearbyQuadraticRemainder_nat] at hh
  exact hh.symm

noncomputable def reflectedSchwartz (g : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  dilateSchwartz g (-1) (by norm_num)

lemma reflectedSchwartz_apply (g : 𝓢(ℝ, ℂ)) (x : ℝ) : reflectedSchwartz g x = g (-x) := by
  simp only [reflectedSchwartz, dilateSchwartz_apply, neg_one_mul]

lemma norm_negative_nearby_weighted_term (f g : 𝓢(ℝ, ℂ)) {q : ℕ} (hq : 0 < q)
    (m v : ℕ) (b : ℤ) (L σ : ℝ) :
    ‖((σ : ℂ) * g (σ * ((-(m : ℤ)) : ℝ))) *
      signedNearbyQuadraticRemainder f q (-(m : ℤ)) v b L‖ =
    ‖((σ : ℂ) * reflectedSchwartz g (σ * m)) *
      nearbyQuadraticRemainder (conjugateSchwartz f) q m v b L‖ := by
  rw [signedNearbyQuadraticRemainder_neg_nat f hq]
  simp only [norm_mul, Complex.norm_conj, reflectedSchwartz_apply, Int.cast_neg,
    Int.cast_natCast, mul_neg]

lemma summable_int_of_positive_negative {f : ℤ → ℝ} (hzero : f 0 = 0)
    (hpos : Summable (fun n : ℕ => f ((n + 1 : ℕ) : ℤ)))
    (hneg : Summable (fun n : ℕ => f (-((n + 1 : ℕ) : ℤ)))) :
    Summable f ∧ (∑' n : ℤ, f n) =
      (∑' n : ℕ, f ((n + 1 : ℕ) : ℤ)) + ∑' n : ℕ, f (-((n + 1 : ℕ) : ℤ)) := by
  have hp : Summable (fun n : ℕ => f (n : ℤ)) := (summable_nat_add_iff 1).mp hpos
  have hn : Summable (fun n : ℕ => f (-(n : ℤ))) := (summable_nat_add_iff 1).mp hneg
  refine ⟨hp.of_nat_of_neg hn, ?_⟩
  have hh := hp.tsum_of_nat_of_neg hn
  rw [hp.tsum_eq_zero_add, hn.tsum_eq_zero_add] at hh
  simpa only [Nat.cast_zero, neg_zero, hzero, zero_add, sub_zero] using hh

end Erdos587
