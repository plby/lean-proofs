/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralCollisionMatrixBound

/-!
# Rough-prime estimates for the collision Euler product

The generic reciprocal-square contribution and the exceptional reciprocal
contribution are bounded separately.  The latter is retained explicitly;
it is not treated as a reciprocal-square error.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

noncomputable local instance (p : Prop) : Decidable p :=
  Classical.propDecidable p

theorem roughPrimeSupport_eq_filter_primesLE (w Q : ℕ) :
    BoundedGaps.Maynard.roughPrimeSupport w Q =
      (Nat.primesLE Q).filter fun p ↦ w < p := by
  ext p
  simp only [BoundedGaps.Maynard.roughPrimeSupport, Finset.mem_filter,
    Finset.mem_Icc, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hwp, hpQ⟩, hp⟩
    exact ⟨⟨hpQ, hp⟩, by omega⟩
  · rintro ⟨⟨hpQ, hp⟩, hwp⟩
    exact ⟨⟨by omega, hpQ⟩, hp⟩

noncomputable def crossMatrixRoughEulerProduct
    (H : Finset ℕ) (w Q m q : ℕ) : ℝ :=
  ∏ p ∈ BoundedGaps.Maynard.roughPrimeSupport w Q,
    ∏ ba : H × H, (1 + crossMatrixPrimeWeight m q p ba)

noncomputable def roughCrossExceptionalTotientMass
    (H : Finset ℕ) (w Q m q : ℕ) : ℝ :=
  ∑ p ∈ (BoundedGaps.Maynard.roughPrimeSupport w Q).filter
      (fun p ↦ p ∣ crossExceptionalModulus H m q),
    (1 : ℝ) / Nat.totient p

theorem roughCrossExceptionalTotientMass_nonneg
    (H : Finset ℕ) (w Q m q : ℕ) :
    0 ≤ roughCrossExceptionalTotientMass H w Q m q := by
  unfold roughCrossExceptionalTotientMass
  exact Finset.sum_nonneg fun p hp ↦ by positivity

theorem crossMatrixSievedPrimeWeight_le
    {H : Finset ℕ} (WD WE m q p : ℕ) (ba : H × H) :
    crossMatrixSievedPrimeWeight WD WE m q p ba ≤
      crossMatrixPrimeWeight m q p ba := by
  unfold crossMatrixSievedPrimeWeight
  split
  · exact crossMatrixPrimeWeight_nonneg m q p ba
  · exact le_rfl

/-- A primorial in the first pre-sieve modulus deletes all factors through
its cutoff.  Additional exclusions can only decrease the majorant. -/
theorem sievedCrossMatrixEulerProduct_le_rough
    {H : Finset ℕ} {WD WE w Q m q : ℕ}
    (hWD : primorial w ∣ WD) :
    (∏ x ∈ crossAuxiliaryPrimeEdgeUniverse H Q,
      (1 + crossMatrixSievedPrimeWeight WD WE m q x.1 x.2)) ≤
      crossMatrixRoughEulerProduct H w Q m q := by
  unfold crossAuxiliaryPrimeEdgeUniverse crossMatrixRoughEulerProduct
  rw [Finset.prod_product, roughPrimeSupport_eq_filter_primesLE,
    Finset.prod_filter]
  apply Finset.prod_le_prod
  · intro p hp
    exact Finset.prod_nonneg fun ba hba ↦
      add_nonneg zero_le_one
        (crossMatrixSievedPrimeWeight_nonneg WD WE m q p ba)
  · intro p hp
    by_cases hwp : w < p
    · rw [if_pos hwp]
      apply Finset.prod_le_prod
      · intro ba hba
        exact add_nonneg zero_le_one
          (crossMatrixSievedPrimeWeight_nonneg WD WE m q p ba)
      · intro ba hba
        exact add_le_add le_rfl
          (crossMatrixSievedPrimeWeight_le WD WE m q p ba)
    · rw [if_neg hwp]
      have hpPrime := (Nat.mem_primesLE.mp hp).2
      have hpWD : p ∣ WD :=
        (hpPrime.dvd_primorial_iff.mpr (by omega)).trans hWD
      simp [crossMatrixSievedPrimeWeight, hpWD]

theorem crossMatrixPrimeWeight_eq_generic
    {H : Finset ℕ} (m q p : ℕ) (ba : H × H)
    (hnot : ¬(p : ℤ) ∣ crossAffineDifference m q ba) :
    crossMatrixPrimeWeight m q p ba =
      (fixedLcmPrimeCost H : ℝ) ^ 2 *
        BoundedGaps.Maynard.primeTotientSquareWeight p := by
  unfold crossMatrixPrimeWeight BoundedGaps.Maynard.primeTotientSquareWeight
  rw [if_neg hnot]
  ring

theorem crossMatrixPrimeWeight_eq_exceptional
    {H : Finset ℕ} (m q : ℕ) {p : ℕ} (hp : p.Prime) (ba : H × H)
    (hcollision : (p : ℤ) ∣ crossAffineDifference m q ba) :
    crossMatrixPrimeWeight m q p ba =
      (fixedLcmPrimeCost H : ℝ) ^ 2 * ((1 : ℝ) / Nat.totient p) := by
  have hphi : (Nat.totient p : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hp.pos).ne'
  unfold crossMatrixPrimeWeight
  rw [if_pos hcollision]
  field_simp [hphi]

theorem crossMatrixPrimeWeight_le_generic_add_exceptional
    {H : Finset ℕ} (m q : ℕ) {p : ℕ} (hp : p.Prime) (ba : H × H) :
    crossMatrixPrimeWeight m q p ba ≤
      (fixedLcmPrimeCost H : ℝ) ^ 2 *
        (BoundedGaps.Maynard.primeTotientSquareWeight p +
          if p ∣ crossExceptionalModulus H m q then
            (1 : ℝ) / Nat.totient p else 0) := by
  by_cases hcollision : (p : ℤ) ∣ crossAffineDifference m q ba
  · have hpDelta : p ∣ crossExceptionalModulus H m q :=
      (Int.natCast_dvd.mp hcollision).trans
        (Finset.dvd_prod_of_mem _ (Finset.mem_univ ba))
    rw [crossMatrixPrimeWeight_eq_exceptional m q hp ba hcollision,
      if_pos hpDelta, mul_add]
    exact le_add_of_nonneg_left
      (mul_nonneg (sq_nonneg _)
        (BoundedGaps.Maynard.primeTotientSquareWeight_nonneg p))
  · rw [crossMatrixPrimeWeight_eq_generic m q p ba hcollision, mul_add]
    apply le_add_of_nonneg_right
    apply mul_nonneg (sq_nonneg _)
    split <;> positivity

/-- The sum of all prime/edge factors separates into the convergent
generic tail and the finite exceptional-prime mass. -/
theorem sum_crossMatrixPrimeWeight_le
    (H : Finset ℕ) (w Q m q : ℕ) :
    (∑ p ∈ BoundedGaps.Maynard.roughPrimeSupport w Q,
      ∑ ba : H × H, crossMatrixPrimeWeight m q p ba) ≤
      (Fintype.card (H × H) : ℝ) * (fixedLcmPrimeCost H : ℝ) ^ 2 *
        ((∑ p ∈ BoundedGaps.Maynard.roughPrimeSupport w Q,
            BoundedGaps.Maynard.primeTotientSquareWeight p) +
          roughCrossExceptionalTotientMass H w Q m q) := by
  let P := BoundedGaps.Maynard.roughPrimeSupport w Q
  calc
    _ ≤ ∑ p ∈ P, ∑ _ba : H × H,
        (fixedLcmPrimeCost H : ℝ) ^ 2 *
          (BoundedGaps.Maynard.primeTotientSquareWeight p +
            if p ∣ crossExceptionalModulus H m q then
              (1 : ℝ) / Nat.totient p else 0) := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro ba hba
      exact crossMatrixPrimeWeight_le_generic_add_exceptional m q
        (Finset.mem_filter.mp hp).2 ba
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      simp_rw [← mul_assoc, ← Finset.mul_sum]
      rw [Finset.sum_add_distrib]
      congr 2
      unfold roughCrossExceptionalTotientMass
      rw [Finset.sum_filter]

theorem sum_crossMatrixPrimeWeight_le_eight_div
    {H : Finset ℕ} {w : ℕ} (hw : 0 < w) (Q m q : ℕ) :
    (∑ p ∈ BoundedGaps.Maynard.roughPrimeSupport w Q,
      ∑ ba : H × H, crossMatrixPrimeWeight m q p ba) ≤
      (Fintype.card (H × H) : ℝ) * (fixedLcmPrimeCost H : ℝ) ^ 2 *
        (8 / (w : ℝ) + roughCrossExceptionalTotientMass H w Q m q) := by
  apply (sum_crossMatrixPrimeWeight_le H w Q m q).trans
  apply mul_le_mul_of_nonneg_left
    (add_le_add (BoundedGaps.Maynard.roughPrimeWeightSum_le hw) le_rfl)
  positivity

theorem crossMatrixRoughEulerProduct_le_exp
    {H : Finset ℕ} {w : ℕ} (hw : 0 < w) (Q m q : ℕ) :
    crossMatrixRoughEulerProduct H w Q m q ≤
      Real.exp ((Fintype.card (H × H) : ℝ) *
        (fixedLcmPrimeCost H : ℝ) ^ 2 *
        (8 / (w : ℝ) + roughCrossExceptionalTotientMass H w Q m q)) := by
  unfold crossMatrixRoughEulerProduct
  calc
    _ ≤ ∏ p ∈ BoundedGaps.Maynard.roughPrimeSupport w Q,
        Real.exp (∑ ba : H × H, crossMatrixPrimeWeight m q p ba) := by
      apply Finset.prod_le_prod
      · intro p hp
        exact Finset.prod_nonneg fun ba hba ↦
          add_nonneg zero_le_one (crossMatrixPrimeWeight_nonneg m q p ba)
      · intro p hp
        exact Real.prod_one_add_le_exp_sum _
          (crossMatrixPrimeWeight_nonneg m q p)
    _ = Real.exp (∑ p ∈ BoundedGaps.Maynard.roughPrimeSupport w Q,
        ∑ ba : H × H, crossMatrixPrimeWeight m q p ba) := by
      rw [Real.exp_sum]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      exact sum_crossMatrixPrimeWeight_le_eight_div hw Q m q

theorem abs_doubledSelbergCrossYTail_le_roughEulerProduct
    {H : Finset ℕ} {RD RE WD WE w m q : ℕ}
    {yD yE : (H → ℕ) → ℝ} {BD BE : ℝ}
    (hRD : 0 < RD) (hWD : primorial w ∣ WD)
    (hBD : 0 ≤ BD) (hBE : 0 ≤ BE)
    (hyD : BoundedGaps.Maynard.IsSupportedMaynardY H RD WD yD)
    (hyE : BoundedGaps.Maynard.IsSupportedMaynardY H RE WE yE)
    (hyDBound : ∀ r, |yD r| ≤ BD) (hyEBound : ∀ r, |yE r| ≤ BE) :
    |doubledSelbergCrossYTail H RD RE yD yE m q| ≤
      ((BD ^ 2 * crossBaseEulerProduct H RD) *
        (BE ^ 2 * crossBaseEulerProduct H RE)) *
      (crossMatrixRoughEulerProduct H w (RD * RD) m q - 1) := by
  apply (abs_doubledSelbergCrossYTail_le_sievedEulerProduct
    hRD hBD hBE hyD hyE hyDBound hyEBound).trans
  apply mul_le_mul_of_nonneg_left
    (sub_le_sub (sievedCrossMatrixEulerProduct_le_rough hWD) le_rfl)
  exact mul_nonneg
    (mul_nonneg (sq_nonneg BD) (crossBaseEulerProduct_nonneg H RD))
    (mul_nonneg (sq_nonneg BE) (crossBaseEulerProduct_nonneg H RE))

/-- Quantitative bound for the actual coefficient-summed collision tail.
The exceptional-prime term remains in the exponent. -/
theorem abs_doubledSelbergCrossYTail_le_exp
    {H : Finset ℕ} {RD RE WD WE w m q : ℕ}
    {yD yE : (H → ℕ) → ℝ} {BD BE : ℝ}
    (hRD : 0 < RD) (hw : 0 < w) (hWD : primorial w ∣ WD)
    (hBD : 0 ≤ BD) (hBE : 0 ≤ BE)
    (hyD : BoundedGaps.Maynard.IsSupportedMaynardY H RD WD yD)
    (hyE : BoundedGaps.Maynard.IsSupportedMaynardY H RE WE yE)
    (hyDBound : ∀ r, |yD r| ≤ BD) (hyEBound : ∀ r, |yE r| ≤ BE) :
    |doubledSelbergCrossYTail H RD RE yD yE m q| ≤
      ((BD ^ 2 * crossBaseEulerProduct H RD) *
        (BE ^ 2 * crossBaseEulerProduct H RE)) *
      (Real.exp ((Fintype.card (H × H) : ℝ) *
        (fixedLcmPrimeCost H : ℝ) ^ 2 *
        (8 / (w : ℝ) + roughCrossExceptionalTotientMass H w (RD * RD) m q)) - 1) := by
  apply (abs_doubledSelbergCrossYTail_le_roughEulerProduct
    hRD hWD hBD hBE hyD hyE hyDBound hyEBound).trans
  apply mul_le_mul_of_nonneg_left
    (sub_le_sub (crossMatrixRoughEulerProduct_le_exp hw (RD * RD) m q) le_rfl)
  exact mul_nonneg
    (mul_nonneg (sq_nonneg BD) (crossBaseEulerProduct_nonneg H RD))
    (mul_nonneg (sq_nonneg BE) (crossBaseEulerProduct_nonneg H RE))

theorem roughCrossExceptionalTotientMass_eq_zero_of_no_exceptional
    {H : Finset ℕ} {w Q m q : ℕ}
    (hno : ∀ p ∈ BoundedGaps.Maynard.roughPrimeSupport w Q,
      ¬p ∣ crossExceptionalModulus H m q) :
    roughCrossExceptionalTotientMass H w Q m q = 0 := by
  unfold roughCrossExceptionalTotientMass
  apply Finset.sum_eq_zero
  intro p hp
  have hdata := Finset.mem_filter.mp hp
  exact (hno p hdata.1 hdata.2).elim

theorem crossMatrixRoughEulerProduct_le_exp_of_no_exceptional
    {H : Finset ℕ} {w Q m q : ℕ} (hw : 0 < w)
    (hno : ∀ p ∈ BoundedGaps.Maynard.roughPrimeSupport w Q,
      ¬p ∣ crossExceptionalModulus H m q) :
    crossMatrixRoughEulerProduct H w Q m q ≤
      Real.exp ((Fintype.card (H × H) : ℝ) *
        (fixedLcmPrimeCost H : ℝ) ^ 2 * (8 / (w : ℝ))) := by
  simpa only [roughCrossExceptionalTotientMass_eq_zero_of_no_exceptional hno,
    add_zero] using crossMatrixRoughEulerProduct_le_exp (H := H) hw Q m q

theorem one_div_totient_prime_le_two_div {p : ℕ} (hp : p.Prime) :
    (1 : ℝ) / Nat.totient p ≤ 2 / (p : ℝ) := by
  have hpTwo : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  rw [Nat.totient_prime hp, Nat.cast_sub hp.one_le, Nat.cast_one]
  apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
  nlinarith

/-- Exceptional reciprocal-totient mass is controlled by the logarithmic
prime-divisor mass already used in the uniform affine-modulus estimates. -/
theorem roughCrossExceptionalTotientMass_le_logMass
    {H : Finset ℕ} {w m q : ℕ} (hw : 0 < w)
    (hDelta : 0 < crossExceptionalModulus H m q) (Q : ℕ) :
    roughCrossExceptionalTotientMass H w Q m q ≤
      (2 / Real.log (w + 1 : ℕ)) *
        roughPrimeLogDivisorMass (crossExceptionalModulus H m q) w := by
  let P := crossExceptionalModulus H m q
  let S := (BoundedGaps.Maynard.roughPrimeSupport w Q).filter
    fun p ↦ p ∣ P
  let T := P.primeFactors.filter fun p ↦ w < p
  have hlog : 0 < Real.log (w + 1 : ℕ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < w + 1 by omega)
  have hcoef : 0 ≤ 2 / Real.log (w + 1 : ℕ) := by positivity
  have hsubset : S ⊆ T := by
    intro p hp
    have hpData := Finset.mem_filter.mp hp
    have hpRough := Finset.mem_filter.mp hpData.1
    exact Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr
      ⟨hpRough.2, hpData.2, hDelta.ne'⟩,
      by have := (Finset.mem_Icc.mp hpRough.1).1; omega⟩
  have hpoint : ∀ p ∈ S,
      (1 : ℝ) / Nat.totient p ≤
        (2 / Real.log (w + 1 : ℕ)) * (Real.log p / (p : ℝ)) := by
    intro p hp
    have hpData := Finset.mem_filter.mp (Finset.mem_filter.mp hp).1
    have hpPrime := hpData.2
    have hpPos : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
    have hlogs : Real.log (w + 1 : ℕ) ≤ Real.log p := by
      apply Real.log_le_log
      · positivity
      · exact_mod_cast (Finset.mem_Icc.mp hpData.1).1
    calc
      (1 : ℝ) / Nat.totient p ≤ 2 / (p : ℝ) :=
        one_div_totient_prime_le_two_div hpPrime
      _ = (2 / Real.log (w + 1 : ℕ)) *
          (Real.log (w + 1 : ℕ) / (p : ℝ)) := by
        field_simp [hlog.ne', hpPos.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hlogs hpPos.le) hcoef
  change (∑ p ∈ S, (1 : ℝ) / Nat.totient p) ≤ _
  calc
    _ ≤ ∑ p ∈ S,
        (2 / Real.log (w + 1 : ℕ)) * (Real.log p / (p : ℝ)) :=
      Finset.sum_le_sum hpoint
    _ = (2 / Real.log (w + 1 : ℕ)) *
        ∑ p ∈ S, Real.log p / (p : ℝ) := by rw [Finset.mul_sum]
    _ ≤ (2 / Real.log (w + 1 : ℕ)) *
        ∑ p ∈ T, Real.log p / (p : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ hcoef
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro p hp hpnot
      exact div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
    _ = _ := by rfl

theorem tendsto_crossMatrixGenericError_zero (H : Finset ℕ) :
    Filter.Tendsto
      (fun w : ℕ ↦ Real.exp ((Fintype.card (H × H) : ℝ) *
        (fixedLcmPrimeCost H : ℝ) ^ 2 * (8 / (w : ℝ))) - 1)
      Filter.atTop (nhds 0) := by
  have hinv : Filter.Tendsto (fun w : ℕ ↦ (w : ℝ)⁻¹)
      Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hdiv : Filter.Tendsto (fun w : ℕ ↦ (8 : ℝ) / w)
      Filter.atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds (x := (8 : ℝ))).mul hinv
  have harg : Filter.Tendsto
      (fun w : ℕ ↦ (Fintype.card (H × H) : ℝ) *
        (fixedLcmPrimeCost H : ℝ) ^ 2 * (8 / (w : ℝ)))
      Filter.atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hdiv
  have hexp := (Real.continuous_exp.tendsto 0).comp harg
  simpa using hexp.sub (tendsto_const_nhds (x := (1 : ℝ)))

end

end Erdos4b
