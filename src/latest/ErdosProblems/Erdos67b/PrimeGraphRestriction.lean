import ErdosProblems.Erdos67b.PrimeGraphFourier
import ErdosProblems.Erdos67b.MRTFourPrimeBound

/-!
# The prime graph multiplier restriction estimate

The sharp logarithmic saving comes from the proved four-prime sieve
bound. Positive dilation preserves additive equations exactly, so the
edge multiplier `h` introduces no additional additive-energy loss.
-/

open scoped BigOperators ComplexConjugate
open Finset Filter

namespace Erdos67b

noncomputable section

/-- Positive integer dilation preserves ordered additive quadruples. -/
theorem card_additiveQuadruples_image_mul (s : Finset ℕ) {h : ℕ} (hh : 0 < h) :
    (additiveQuadruples (s.image fun p ↦ p * h)).card = (additiveQuadruples s).card := by
  classical
  symm
  apply Finset.card_bij (fun x _ ↦ ((x.1.1 * h, x.1.2 * h), (x.2.1 * h, x.2.2 * h)))
  · intro x hx
    obtain ⟨ha, hb, hc, hd, heq⟩ := mem_additiveQuadruples.mp hx
    apply mem_additiveQuadruples.mpr
    refine ⟨Finset.mem_image.mpr ⟨_, ha, rfl⟩, Finset.mem_image.mpr ⟨_, hb, rfl⟩,
      Finset.mem_image.mpr ⟨_, hc, rfl⟩, Finset.mem_image.mpr ⟨_, hd, rfl⟩, ?_⟩
    dsimp
    rw [← Nat.add_mul, ← Nat.add_mul, heq]
  · intro x hx y hy hxy
    have ha := congrArg (fun z : (ℕ × ℕ) × (ℕ × ℕ) ↦ z.1.1) hxy
    have hb := congrArg (fun z : (ℕ × ℕ) × (ℕ × ℕ) ↦ z.1.2) hxy
    have hc := congrArg (fun z : (ℕ × ℕ) × (ℕ × ℕ) ↦ z.2.1) hxy
    have hd := congrArg (fun z : (ℕ × ℕ) × (ℕ × ℕ) ↦ z.2.2) hxy
    exact Prod.ext (Prod.ext (Nat.eq_of_mul_eq_mul_right hh ha) (Nat.eq_of_mul_eq_mul_right hh hb))
      (Prod.ext (Nat.eq_of_mul_eq_mul_right hh hc) (Nat.eq_of_mul_eq_mul_right hh hd))
  · intro x hx
    obtain ⟨ha, hb, hc, hd, heq⟩ := mem_additiveQuadruples.mp hx
    obtain ⟨a, ha, haeq⟩ := Finset.mem_image.mp ha
    obtain ⟨b, hb, hbeq⟩ := Finset.mem_image.mp hb
    obtain ⟨c, hc, hceq⟩ := Finset.mem_image.mp hc
    obtain ⟨d, hd, hdeq⟩ := Finset.mem_image.mp hd
    refine ⟨((a, b), (c, d)), mem_additiveQuadruples.mpr ⟨ha, hb, hc, hd, ?_⟩, ?_⟩
    · apply Nat.eq_of_mul_eq_mul_right hh
      rw [Nat.add_mul, Nat.add_mul, haeq, hbeq, hceq, hdeq]
      exact heq
    · exact Prod.ext (Prod.ext haeq hbeq) (Prod.ext hceq hdeq)

/-- The multiplier is a weighted exponential sum on the dilated support. -/
theorem primeGraphMultiplier_eq_weightedExponentialSum
    (T : ℕ) {h : ℕ} (hh : 0 < h) (s : Finset ℕ) (t : ℤ) :
    primeGraphMultiplier T h s t =
      weightedExponentialSum T (s.image fun p ↦ p * h)
        (fun m ↦ ((m / h : ℕ) : ℂ)⁻¹) t := by
  classical
  rw [weightedExponentialSum, Finset.sum_image]
  · simp only [Nat.mul_div_left _ hh]
    rfl
  · intro p hp q hq heq
    exact Nat.eq_of_mul_eq_mul_right hh heq

/-- An exact finite multiplier fourth-moment bound in terms of the
undilated support's additive energy. -/
theorem fourth_moment_primeGraphMultiplier_le_energy
    (T X : ℕ) [NeZero T] {h : ℕ} (hh : 0 < h) (s : Finset ℕ)
    {B : ℝ} (hB : 0 ≤ B) (hweight : ∀ p ∈ s, (p : ℝ)⁻¹ ≤ B)
    (hs : ∀ p ∈ s, p ≤ X) (hT : 2 * (X * h) < T) :
    ∑ t ∈ Finset.range T, ‖primeGraphMultiplier T h s (t : ℤ)‖ ^ 4 ≤
      T * (additiveQuadruples s).card * B ^ 4 := by
  simp_rw [primeGraphMultiplier_eq_weightedExponentialSum T hh s]
  have hbound := fourth_moment_weightedExponentialSum_le_energy T (X * h)
    (s.image fun p ↦ p * h) (fun m ↦ ((m / h : ℕ) : ℂ)⁻¹) B hB (by
      intro m hm
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hm
      simpa only [Nat.mul_div_left _ hh, norm_inv, Complex.norm_natCast] using hweight p hp)
    (by
      intro m hm
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hm
      exact Nat.mul_le_mul_right h (hs p hp)) hT
  simpa only [card_additiveQuadruples_image_mul s hh] using hbound

/-- The dyadic multiplier inherits the sharp fourth-moment saving from
the already proved four-prime upper-bound sieve. -/
theorem exists_dyadic_primeGraphMultiplier_fourth_moment_bound :
    ∃ A : ℝ, 0 < A ∧ ∃ P₀ : ℕ, 2 ≤ P₀ ∧ ∀ P ≥ P₀,
      ∀ T h : ℕ, 0 < h → 4 * P * h < T →
      ∑ t ∈ Finset.range T,
        ‖primeGraphMultiplier T h (PrimeEstimates.dyadicPrimes P) (t : ℤ)‖ ^ 4 ≤
          A * T / ((P : ℝ) * Real.log P ^ 4) := by
  obtain ⟨A, hA, henergy⟩ := exists_primesLE_additiveQuadruples_bound
  obtain ⟨P₀, hP₀⟩ := Filter.eventually_atTop.mp henergy
  refine ⟨A, hA, max P₀ 2, le_max_right _ _, ?_⟩
  intro P hP T h hh hT
  have hP2 : 2 ≤ P := (le_max_right _ _).trans hP
  have hPr : (0 : ℝ) < P := by positivity
  have hlog : 0 < Real.log (P : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < P))
  have hTpos : 0 < T := by omega
  let : NeZero T := ⟨hTpos.ne'⟩
  have hs : PrimeEstimates.dyadicPrimes P ⊆ Nat.primesLE (2 * P) := by
    intro p hp
    have hp' := PrimeEstimates.mem_primesInInterval.mp hp
    exact Nat.mem_primesLE.mpr ⟨hp'.2.1, hp'.2.2⟩
  have hcard : (additiveQuadruples (PrimeEstimates.dyadicPrimes P)).card ≤
      (additiveQuadruples (Nat.primesLE (2 * P))).card := by
    rw [card_additiveQuadruples, card_additiveQuadruples]
    exact Finset.addEnergy_mono hs hs
  have he := hP₀ P ((le_max_left _ _).trans hP)
  have hbound := fourth_moment_primeGraphMultiplier_le_energy T (2 * P) hh
    (PrimeEstimates.dyadicPrimes P) (B := (P : ℝ)⁻¹) (by positivity) (by
      intro p hp
      exact inv_anti₀ hPr (by exact_mod_cast (PrimeEstimates.mem_primesInInterval.mp hp).1.le))
    (fun p hp ↦ (PrimeEstimates.mem_primesInInterval.mp hp).2.1) (by nlinarith)
  calc
    _ ≤ T * (additiveQuadruples (PrimeEstimates.dyadicPrimes P)).card * ((P : ℝ)⁻¹) ^ 4 := hbound
    _ ≤ T * (A * (P : ℝ) ^ 3 / Real.log P ^ 4) * ((P : ℝ)⁻¹) ^ 4 := by
      gcongr
      exact (show ((additiveQuadruples (PrimeEstimates.dyadicPrimes P)).card : ℝ) ≤
        (additiveQuadruples (Nat.primesLE (2 * P))).card by exact_mod_cast hcard).trans he
    _ = A * T / ((P : ℝ) * Real.log P ^ 4) := by field_simp

end

end Erdos67b
