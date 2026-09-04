import ErdosProblems.Erdos140.BohrEstimates
import ErdosProblems.Erdos140.GroupCount

/-!
# The rank-regular Hölder approximation

This file isolates the last boundary calculation in the local Hölder step.
The function is written explicitly, rather than through the final assembly
alias, so that this module can be imported by that assembly without a cycle.
-/

open Finset Fintype Function
open scoped BigOperators NNReal mu

namespace Erdos140.HolderApproximation

noncomputable section

variable {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
  [MeasurableSpace G] [DiscreteMeasurableSpace G]

private lemma normalizedIndicator_neg_eq (K : BohrData G) (x : G) :
    normalizedIndicator K.carrier (-x) = normalizedIndicator K.carrier x := by
  by_cases hx : x ∈ K.carrier
  · have hnx : -x ∈ K.carrier := BohrData.neg_mem_carrier.mpr hx
    simp [normalizedIndicator_apply_mem hx, normalizedIndicator_apply_mem hnx]
  · have hnx : -x ∉ K.carrier := by
      intro h
      exact hx (BohrData.neg_mem_carrier.mp h)
    simp [normalizedIndicator_apply_not_mem hx,
      normalizedIndicator_apply_not_mem hnx]

/-- A point of a small Bohr dilate sees the mixed `A*K` convolution as the
constant density `1/|K|`, with the rank-regular boundary error amplified only
by `1/|A|`. -/
theorem abs_normalizedConvolution_subset_carrier_sub_inv_le
    {K : BohrData G} (hreg : K.IsRankRegular) {κ : ℝ≥0}
    (hκ : κ ≤ 1 / (100 * (max K.rank 1 : ℕ) : ℝ≥0))
    {A : Finset G} (hA : A.Nonempty) (hAK : A ⊆ K.carrier)
    {t : G} (ht : t ∈ (K.dilate κ).carrier) :
    |normalizedConvolution (normalizedIndicator A)
        (normalizedIndicator K.carrier) t - (K.carrier.card : ℝ)⁻¹| ≤
      (A.card : ℝ)⁻¹ *
        (200 * ((max K.rank 1 : ℕ) : ℝ) * (κ : ℝ)) := by
  let E : ℝ := 200 * ((max K.rank 1 : ℕ) : ℝ) * (κ : ℝ)
  have hAcard : (A.card : ℝ) ≠ 0 := by exact_mod_cast hA.card_ne_zero
  have hsumA : ∑ x : G, normalizedIndicator A x = 1 :=
    sum_normalizedIndicator hA
  have hbase :
      ∑ x : G, normalizedIndicator A x * (K.carrier.card : ℝ)⁻¹ =
        (K.carrier.card : ℝ)⁻¹ := by
    rw [← Finset.sum_mul, hsumA, one_mul]
  have hsumDiff :
      ∑ x : G,
          |normalizedIndicator K.carrier (t - x) -
            normalizedIndicator K.carrier (-x)| ≤ E := by
    have hneg : -t ∈ (K.dilate κ).carrier :=
      BohrData.neg_mem_carrier.mpr ht
    have htranslate :=
      BohrData.sum_abs_normalizedIndicator_translate_le_of_rankRegular
        hreg hκ hneg
    calc
      ∑ x : G,
          |normalizedIndicator K.carrier (t - x) -
            normalizedIndicator K.carrier (-x)| =
          ∑ x : G,
            |normalizedIndicator K.carrier (x - -t) -
              normalizedIndicator K.carrier x| := by
        refine Fintype.sum_equiv (Equiv.neg G) _ _ ?_
        intro x
        simp only [Equiv.neg_apply]
        congr 2 <;> abel_nf
      _ ≤ E := htranslate
  have hweighted :
      ∑ x : G, normalizedIndicator A x *
          |normalizedIndicator K.carrier (t - x) -
            normalizedIndicator K.carrier (-x)| ≤
        (A.card : ℝ)⁻¹ * E := by
    calc
      ∑ x : G, normalizedIndicator A x *
          |normalizedIndicator K.carrier (t - x) -
            normalizedIndicator K.carrier (-x)| =
          (A.card : ℝ)⁻¹ * ∑ x ∈ A,
            |normalizedIndicator K.carrier (t - x) -
              normalizedIndicator K.carrier (-x)| := by
        change (∑ x : G, (if x ∈ A then (A.card : ℝ)⁻¹ else 0) *
            |normalizedIndicator K.carrier (t - x) -
              normalizedIndicator K.carrier (-x)|) = _
        simp only [ite_mul, zero_mul]
        rw [← Finset.sum_filter]
        have hfilter : (Finset.univ : Finset G).filter (fun x ↦ x ∈ A) = A := by
          ext x
          simp
        rw [hfilter, Finset.mul_sum]
      _ ≤ (A.card : ℝ)⁻¹ * ∑ x : G,
            |normalizedIndicator K.carrier (t - x) -
              normalizedIndicator K.carrier (-x)| := by
        apply mul_le_mul_of_nonneg_left
        · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
            (fun _ _ _ ↦ abs_nonneg _)
        · positivity
      _ ≤ (A.card : ℝ)⁻¹ * E :=
        mul_le_mul_of_nonneg_left hsumDiff (by positivity)
  rw [normalizedConvolution, ← hbase, ← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  calc
    |∑ x : G, normalizedIndicator A x *
        (normalizedIndicator K.carrier (t - x) -
          (K.carrier.card : ℝ)⁻¹)| =
        |∑ x : G, normalizedIndicator A x *
          (normalizedIndicator K.carrier (t - x) -
            normalizedIndicator K.carrier (-x))| := by
      apply congrArg abs
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x ∈ A
      · rw [normalizedIndicator_neg_eq K x,
          normalizedIndicator_apply_mem (hAK hx)]
      · simp [normalizedIndicator_apply_not_mem hx]
    _ ≤ ∑ x : G, |normalizedIndicator A x *
          (normalizedIndicator K.carrier (t - x) -
            normalizedIndicator K.carrier (-x))| :=
      abs_sum_le_sum_abs _ _
    _ = ∑ x : G, normalizedIndicator A x *
          |normalizedIndicator K.carrier (t - x) -
            normalizedIndicator K.carrier (-x)| := by
      apply Finset.sum_congr rfl
      intro x _
      rw [abs_mul, abs_of_nonneg (normalizedIndicator_nonneg A x)]
    _ ≤ (A.card : ℝ)⁻¹ * E := hweighted

private lemma localAverage_sub_const
    {C : Finset G} (hC : C.Nonempty) (f : G → ℝ) (c : ℝ) :
    HolderLifting.localAverage C f - c =
      HolderLifting.localAverage C (fun x ↦ f x - c) := by
  unfold HolderLifting.localAverage
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hCcard : (C.card : ℝ) ≠ 0 := by exact_mod_cast hC.card_ne_zero
  field_simp

private lemma localAverage_const
    {C : Finset G} (hC : C.Nonempty) (c : ℝ) :
    HolderLifting.localAverage C (fun _ ↦ c) = c := by
  unfold HolderLifting.localAverage
  simp [hC.card_ne_zero]

/-- Averaging the preceding pointwise estimate over a nonempty set of small
translations preserves its right-hand side. -/
theorem abs_localAverage_normalizedConvolution_subset_carrier_sub_inv_le
    {K : BohrData G} (hreg : K.IsRankRegular) {κ : ℝ≥0}
    (hκ : κ ≤ 1 / (100 * (max K.rank 1 : ℕ) : ℝ≥0))
    {A C : Finset G} (hA : A.Nonempty) (hAK : A ⊆ K.carrier)
    (hC : C.Nonempty) (hCsmall : C ⊆ (K.dilate κ).carrier) :
    |HolderLifting.localAverage C
        (normalizedConvolution (normalizedIndicator A)
          (normalizedIndicator K.carrier)) - (K.carrier.card : ℝ)⁻¹| ≤
      (A.card : ℝ)⁻¹ *
        (200 * ((max K.rank 1 : ℕ) : ℝ) * (κ : ℝ)) := by
  let M : ℝ := (A.card : ℝ)⁻¹ *
    (200 * ((max K.rank 1 : ℕ) : ℝ) * (κ : ℝ))
  rw [localAverage_sub_const hC]
  calc
    |HolderLifting.localAverage C (fun x ↦
        normalizedConvolution (normalizedIndicator A)
          (normalizedIndicator K.carrier) x - (K.carrier.card : ℝ)⁻¹)| ≤
      HolderLifting.localAverage C (fun x ↦
        |normalizedConvolution (normalizedIndicator A)
          (normalizedIndicator K.carrier) x - (K.carrier.card : ℝ)⁻¹|) :=
      HolderLifting.abs_localAverage_le_localAverage_abs _
    _ ≤ HolderLifting.localAverage C (fun _ ↦ M) := by
      unfold HolderLifting.localAverage
      apply div_le_div_of_nonneg_right
      · apply Finset.sum_le_sum
        intro x hx
        exact abs_normalizedConvolution_subset_carrier_sub_inv_le
          hreg hκ hA hAK (hCsmall hx)
      · positivity
    _ = M := localAverage_const hC M

private lemma normalizedConvolution_sub_sub_apply
    (a k : G → ℝ) (x : G) :
    normalizedConvolution (a - k) (a - k) x =
      normalizedConvolution a a x - normalizedConvolution a k x -
        normalizedConvolution k a x + normalizedConvolution k k x := by
  unfold normalizedConvolution
  simp only [Pi.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]
  ring

private lemma localAverage_add
    {C : Finset G} (f g : G → ℝ) :
    HolderLifting.localAverage C (fun x ↦ f x + g x) =
      HolderLifting.localAverage C f + HolderLifting.localAverage C g := by
  unfold HolderLifting.localAverage
  rw [Finset.sum_add_distrib, add_div]

private lemma localAverage_sub
    {C : Finset G} (f g : G → ℝ) :
    HolderLifting.localAverage C (fun x ↦ f x - g x) =
      HolderLifting.localAverage C f - HolderLifting.localAverage C g := by
  unfold HolderLifting.localAverage
  rw [Finset.sum_sub_distrib, sub_div]

private lemma localAverage_mul_const_left
    {C : Finset G} (c : ℝ) (f : G → ℝ) :
    HolderLifting.localAverage C (fun x ↦ c * f x) =
      c * HolderLifting.localAverage C f := by
  unfold HolderLifting.localAverage
  rw [← Finset.mul_sum]
  ring

/-- The concrete three-term Holder approximation.  `C` is the doubled
middle-term set in the endpoint application; the statement is kept at this
level so it can be reused without importing the final assembly namespace. -/
theorem normalizedMixedProgression_scaledBalanced_approximation
    {K : BohrData G} (hreg : K.IsRankRegular) {κ : ℝ≥0}
    (hκ : κ ≤ 1 / (100 * (max K.rank 1 : ℕ) : ℝ≥0))
    {A A'' : Finset G} (hA : A.Nonempty) (hAK : A ⊆ K.carrier)
    (hA'' : A''.Nonempty)
    (hCsmall : GroupCount.doubledFinset A'' ⊆ (K.dilate κ).carrier)
    (hwidth :
      2 * ((A.card : ℝ)⁻¹ *
          (200 * ((max K.rank 1 : ℕ) : ℝ) * (κ : ℝ))) +
        (K.carrier.card : ℝ)⁻¹ *
          (200 * ((max K.rank 1 : ℕ) : ℝ) * (κ : ℝ)) ≤
        ((K.carrier.card : ℝ)⁻¹) / 8) :
    |(GroupCount.normalizedMixedProgression A A'' -
        (Fintype.card G : ℝ) / (#K.carrier : ℝ)) -
        HolderLifting.pairing
          ((Fintype.card G : ℝ) •
            normalizedConvolution
              (normalizedIndicator A - normalizedIndicator K.carrier)
              (normalizedIndicator A - normalizedIndicator K.carrier))
          (GroupCount.doubledFinset A'')| ≤
      ((Fintype.card G : ℝ) / (#K.carrier : ℝ)) / 8 := by
  let C := GroupCount.doubledFinset A''
  let gAA := normalizedConvolution (normalizedIndicator A) (normalizedIndicator A)
  let gAK := normalizedConvolution (normalizedIndicator A) (normalizedIndicator K.carrier)
  let gKA := normalizedConvolution (normalizedIndicator K.carrier) (normalizedIndicator A)
  let gKK := normalizedConvolution (normalizedIndicator K.carrier) (normalizedIndicator K.carrier)
  let invK : ℝ := (K.carrier.card : ℝ)⁻¹
  let E : ℝ := 200 * ((max K.rank 1 : ℕ) : ℝ) * (κ : ℝ)
  have hC : C.Nonempty := GroupCount.doubledFinset_nonempty hA''
  have hAKavg : |HolderLifting.localAverage C gAK - invK| ≤
      (A.card : ℝ)⁻¹ * E := by
    simpa [C, gAK, invK, E] using
      abs_localAverage_normalizedConvolution_subset_carrier_sub_inv_le
        hreg hκ hA hAK hC hCsmall
  have hKAavg : |HolderLifting.localAverage C gKA - invK| ≤
      (A.card : ℝ)⁻¹ * E := by
    rw [show gKA = gAK by
      dsimp [gKA, gAK]
      exact normalizedConvolution_comm _ _]
    exact hAKavg
  have hKKavg : |HolderLifting.localAverage C gKK - invK| ≤ invK * E := by
    simpa [C, gKK, invK, E] using
      abs_localAverage_normalizedConvolution_subset_carrier_sub_inv_le
        hreg hκ K.carrier_nonempty (Finset.Subset.rfl) hC hCsmall
  have hsum :
      |(HolderLifting.localAverage C gAK - invK) +
          (HolderLifting.localAverage C gKA - invK) -
          (HolderLifting.localAverage C gKK - invK)| ≤
        2 * ((A.card : ℝ)⁻¹ * E) + invK * E := by
    calc
      |(HolderLifting.localAverage C gAK - invK) +
          (HolderLifting.localAverage C gKA - invK) -
          (HolderLifting.localAverage C gKK - invK)| ≤
        |HolderLifting.localAverage C gAK - invK| +
          |HolderLifting.localAverage C gKA - invK| +
          |HolderLifting.localAverage C gKK - invK| := by
        calc
          |_ - _| ≤ |(HolderLifting.localAverage C gAK - invK) +
              (HolderLifting.localAverage C gKA - invK)| +
              |HolderLifting.localAverage C gKK - invK| := by
            simpa [abs_sub_comm] using (abs_sub_le
              ((HolderLifting.localAverage C gAK - invK) +
                (HolderLifting.localAverage C gKA - invK))
              (0 : ℝ) (HolderLifting.localAverage C gKK - invK))
          _ ≤ (|HolderLifting.localAverage C gAK - invK| +
              |HolderLifting.localAverage C gKA - invK|) +
              |HolderLifting.localAverage C gKK - invK| := by
            gcongr
            exact abs_add_le _ _
      _ ≤ 2 * ((A.card : ℝ)⁻¹ * E) + invK * E := by
        nlinarith
  have hmain : (Fintype.card G : ℝ) / (#K.carrier : ℝ) =
      (Fintype.card G : ℝ) * invK := by
    simp [invK, div_eq_mul_inv]
  have hprog : GroupCount.normalizedMixedProgression A A'' =
      (Fintype.card G : ℝ) * HolderLifting.localAverage C gAA := by
    rw [GroupCount.normalizedMixedProgression_eq_localAverage hA'']
    change HolderLifting.localAverage C
        (fun x ↦ (Fintype.card G : ℝ) * gAA x) = _
    rw [localAverage_mul_const_left]
  have hpair :
      HolderLifting.pairing
          ((Fintype.card G : ℝ) •
            normalizedConvolution
              (normalizedIndicator A - normalizedIndicator K.carrier)
              (normalizedIndicator A - normalizedIndicator K.carrier)) C =
        (Fintype.card G : ℝ) *
          (HolderLifting.localAverage C gAA - HolderLifting.localAverage C gAK -
            HolderLifting.localAverage C gKA + HolderLifting.localAverage C gKK) := by
    rw [HolderLifting.pairing_eq_localAverage hC]
    change HolderLifting.localAverage C (fun x ↦ (Fintype.card G : ℝ) *
      normalizedConvolution
        (normalizedIndicator A - normalizedIndicator K.carrier)
        (normalizedIndicator A - normalizedIndicator K.carrier) x) = _
    rw [localAverage_mul_const_left]
    congr 1
    rw [show normalizedConvolution
        (normalizedIndicator A - normalizedIndicator K.carrier)
        (normalizedIndicator A - normalizedIndicator K.carrier) =
        (fun x ↦ gAA x - gAK x - gKA x + gKK x) by
      funext x
      simpa [gAA, gAK, gKA, gKK] using
        normalizedConvolution_sub_sub_apply (normalizedIndicator A)
          (normalizedIndicator K.carrier) x]
    rw [localAverage_add, localAverage_sub, localAverage_sub]
  rw [hprog, hmain, hpair]
  have hcardG : 0 ≤ (Fintype.card G : ℝ) := by positivity
  calc
    |((Fintype.card G : ℝ) * HolderLifting.localAverage C gAA -
        (Fintype.card G : ℝ) * invK) -
        (Fintype.card G : ℝ) *
          (HolderLifting.localAverage C gAA - HolderLifting.localAverage C gAK -
            HolderLifting.localAverage C gKA + HolderLifting.localAverage C gKK)| =
      (Fintype.card G : ℝ) *
        |(HolderLifting.localAverage C gAK - invK) +
          (HolderLifting.localAverage C gKA - invK) -
          (HolderLifting.localAverage C gKK - invK)| := by
      have heq :
          (Fintype.card G : ℝ) * HolderLifting.localAverage C gAA -
              (Fintype.card G : ℝ) * invK -
              (Fintype.card G : ℝ) *
                (HolderLifting.localAverage C gAA - HolderLifting.localAverage C gAK -
                  HolderLifting.localAverage C gKA + HolderLifting.localAverage C gKK) =
            (Fintype.card G : ℝ) *
              ((HolderLifting.localAverage C gAK - invK) +
                (HolderLifting.localAverage C gKA - invK) -
                (HolderLifting.localAverage C gKK - invK)) := by ring
      rw [heq, abs_mul, abs_of_nonneg hcardG]
    _ ≤ (Fintype.card G : ℝ) *
        (2 * ((A.card : ℝ)⁻¹ * E) + invK * E) :=
      mul_le_mul_of_nonneg_left hsum hcardG
    _ ≤ (Fintype.card G : ℝ) * (invK / 8) := by
      apply mul_le_mul_of_nonneg_left
      · simpa [E, invK] using hwidth
      · exact hcardG
    _ = ((Fintype.card G : ℝ) / (#K.carrier : ℝ)) / 8 := by
      rw [hmain]
      ring

/-- Endpoint-shaped form of the approximation.  This is the version consumed
by `RawTwoBohrEndpointPackage`: its stored boundary budget is the stronger
`(1/8)/8` budget, and APAP's `μ` notation is used for the balanced function. -/
theorem normalizedMixedProgression_scaledBalanced_approximation_of_boundaryWidth
    {K : BohrData G} (hreg : K.IsRankRegular) {κ : ℝ≥0}
    (hκ : κ ≤ 1 / (100 * (max K.rank 1 : ℕ) : ℝ≥0))
    {A A'' : Finset G} (hA : A.Nonempty) (hAK : A ⊆ K.carrier)
    (hA'' : A''.Nonempty)
    (hCsmall : GroupCount.doubledFinset A'' ⊆ (K.dilate κ).carrier)
    (hwidth :
      2 * ((A.card : ℝ)⁻¹ *
          (200 * ((max K.rank 1 : ℕ) : ℝ) * (κ : ℝ))) +
        (K.carrier.card : ℝ)⁻¹ *
          (200 * ((max K.rank 1 : ℕ) : ℝ) * (κ : ℝ)) ≤
        (1 / 8 : ℝ) / 8 * (K.carrier.card : ℝ)⁻¹) :
    |(GroupCount.normalizedMixedProgression A A'' -
        (Fintype.card G : ℝ) / (#K.carrier : ℝ)) -
        HolderLifting.pairing
          ((Fintype.card G : ℝ) •
            normalizedConvolution
              (μ_[ℝ] A - μ K.carrier)
              (μ A - μ K.carrier))
          (GroupCount.doubledFinset A'')| ≤
      ((Fintype.card G : ℝ) / (#K.carrier : ℝ)) / 8 := by
  have hKinv : 0 ≤ (K.carrier.card : ℝ)⁻¹ := by positivity
  have hwidth' :
      2 * ((A.card : ℝ)⁻¹ *
          (200 * ((max K.rank 1 : ℕ) : ℝ) * (κ : ℝ))) +
        (K.carrier.card : ℝ)⁻¹ *
          (200 * ((max K.rank 1 : ℕ) : ℝ) * (κ : ℝ)) ≤
        ((K.carrier.card : ℝ)⁻¹) / 8 := by
    apply hwidth.trans
    nlinarith
  have hmuA : μ_[ℝ] A = normalizedIndicator A :=
    LocalizedUnbalancing.mu_eq_normalizedIndicator A
  have hmuK : μ_[ℝ] K.carrier = normalizedIndicator K.carrier :=
    LocalizedUnbalancing.mu_eq_normalizedIndicator K.carrier
  simpa only [hmuA, hmuK] using
    normalizedMixedProgression_scaledBalanced_approximation hreg hκ hA hAK
      hA'' hCsmall hwidth'

end
end Erdos140.HolderApproximation

#print axioms Erdos140.HolderApproximation.abs_normalizedConvolution_subset_carrier_sub_inv_le
#print axioms Erdos140.HolderApproximation.normalizedMixedProgression_scaledBalanced_approximation
#print axioms Erdos140.HolderApproximation.normalizedMixedProgression_scaledBalanced_approximation_of_boundaryWidth
