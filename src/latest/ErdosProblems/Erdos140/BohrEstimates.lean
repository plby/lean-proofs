import ErdosProblems.Erdos140.RegularBohr

/-!
# Elementary estimates on regular finite Bohr sets

This file proves the three normalization-sensitive Bohr estimates used in the
Kelley--Meka density-increment argument.

* On an exact regular plateau, convolution by a nonnegative measure supported
  on the small Bohr carrier does not move the normalized carrier measure.  In
  particular the corresponding counting-measure `L¹` error is zero (and hence
  is stronger than the usual `O (rho * rank)` estimate).
* Coarse regularity of one shell gives the pointwise factor-two Bohr
  majorization inequality.
* Exact plateau invariance gives a two-scale Bourgain narrowing alternative.

All convolutions and indicators below use counting-measure probability
normalization from `FiniteConvolution.lean`; consequently there are no hidden
factors of `|G|`.
-/

open Finset
open scoped BigOperators NNReal

namespace Erdos140

noncomputable section

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-! ## Translation invariance and convolution -/

/-- Convolution by a measure supported on the small carrier is exactly
translation-invariant on a plateau-regular Bohr carrier. -/
theorem normalizedConvolution_normalizedIndicator_eq_of_plateauRegular
    {B : BohrData G} {rho eta : ℝ≥0}
    (hreg : B.IsPlateauRegularAt rho eta)
    (ν : G → ℝ)
    (hνsupp : ∀ t, ν t ≠ 0 → t ∈ (B.dilate eta).carrier) :
    normalizedConvolution (normalizedIndicator (B.dilate rho).carrier) ν =
      fun x ↦ (∑ t : G, ν t) * normalizedIndicator (B.dilate rho).carrier x := by
  funext x
  rw [normalizedConvolution_comm]
  simp only [normalizedConvolution]
  calc
    ∑ t : G, ν t * normalizedIndicator (B.dilate rho).carrier (x - t) =
        ∑ t : G, ν t * normalizedIndicator (B.dilate rho).carrier x := by
      apply Finset.sum_congr rfl
      intro t _
      by_cases ht : ν t = 0
      · simp [ht]
      · rw [BohrData.normalizedIndicator_sub_eq_of_plateauRegular hreg (hνsupp t ht)]
    _ = (∑ t : G, ν t) * normalizedIndicator (B.dilate rho).carrier x := by
      rw [Finset.sum_mul]

/-- Probability-mass specialization of exact convolution invariance. -/
theorem normalizedConvolution_normalizedIndicator_eq_self_of_plateauRegular
    {B : BohrData G} {rho eta : ℝ≥0}
    (hreg : B.IsPlateauRegularAt rho eta)
    (ν : G → ℝ)
    (hνmass : ∑ t : G, ν t = 1)
    (hνsupp : ∀ t, ν t ≠ 0 → t ∈ (B.dilate eta).carrier) :
    normalizedConvolution (normalizedIndicator (B.dilate rho).carrier) ν =
      normalizedIndicator (B.dilate rho).carrier := by
  rw [normalizedConvolution_normalizedIndicator_eq_of_plateauRegular hreg ν hνsupp,
    hνmass]
  simp

/-- The normalized-convolution translation error has counting-measure `L¹`
norm zero on an exact regular plateau.  This is the finite, zero-boundary
version of the usual regular-Bohr `O (rho * rank)` estimate. -/
theorem sum_abs_normalizedConvolution_error_eq_zero_of_plateauRegular
    {B : BohrData G} {rho eta : ℝ≥0}
    (hreg : B.IsPlateauRegularAt rho eta)
    (ν : G → ℝ)
    (hνsupp : ∀ t, ν t ≠ 0 → t ∈ (B.dilate eta).carrier) :
    ∑ x : G,
        |normalizedConvolution (normalizedIndicator (B.dilate rho).carrier) ν x -
          (∑ t : G, ν t) * normalizedIndicator (B.dilate rho).carrier x| = 0 := by
  rw [normalizedConvolution_normalizedIndicator_eq_of_plateauRegular hreg ν hνsupp]
  simp

/-- The standard rank-linear regular-Bohr convolution estimate, with the
fully explicit constant inherited from `RegularBohr.lean`. -/
theorem sum_abs_normalizedConvolution_error_le_of_rankRegular
    {B : BohrData G} (hreg : B.IsRankRegular) {κ : ℝ≥0}
    (hκ : κ ≤ 1 / (100 * (max B.rank 1 : ℕ) : ℝ≥0))
    (ν : G → ℝ) (hνnonneg : ∀ t, 0 ≤ ν t)
    (hνsupp : ∀ t, ν t ≠ 0 → t ∈ (B.dilate κ).carrier) :
    ∑ x : G,
        |normalizedConvolution (normalizedIndicator B.carrier) ν x -
          (∑ t : G, ν t) * normalizedIndicator B.carrier x| ≤
      200 * ((max B.rank 1 : ℕ) : ℝ) * (κ : ℝ) * ∑ t : G, ν t := by
  let E : ℝ := 200 * ((max B.rank 1 : ℕ) : ℝ) * (κ : ℝ)
  have hpoint (x : G) :
      |normalizedConvolution (normalizedIndicator B.carrier) ν x -
          (∑ t : G, ν t) * normalizedIndicator B.carrier x| ≤
        ∑ t : G, ν t *
          |normalizedIndicator B.carrier (x - t) - normalizedIndicator B.carrier x| := by
    rw [normalizedConvolution_comm]
    simp only [normalizedConvolution]
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    simp_rw [← mul_sub]
    calc
      |∑ t : G, ν t *
          (normalizedIndicator B.carrier (x - t) - normalizedIndicator B.carrier x)| ≤
          ∑ t : G, |ν t *
            (normalizedIndicator B.carrier (x - t) - normalizedIndicator B.carrier x)| :=
        abs_sum_le_sum_abs _ _
      _ = ∑ t : G, ν t *
          |normalizedIndicator B.carrier (x - t) - normalizedIndicator B.carrier x| := by
        apply Finset.sum_congr rfl
        intro t _
        rw [abs_mul, abs_of_nonneg (hνnonneg t)]
  calc
    ∑ x : G,
        |normalizedConvolution (normalizedIndicator B.carrier) ν x -
          (∑ t : G, ν t) * normalizedIndicator B.carrier x| ≤
        ∑ x : G, ∑ t : G, ν t *
          |normalizedIndicator B.carrier (x - t) - normalizedIndicator B.carrier x| := by
      exact Finset.sum_le_sum fun x _ ↦ hpoint x
    _ = ∑ t : G, ν t * ∑ x : G,
          |normalizedIndicator B.carrier (x - t) - normalizedIndicator B.carrier x| := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t _
      rw [Finset.mul_sum]
    _ ≤ ∑ t : G, ν t * E := by
      apply Finset.sum_le_sum
      intro t _
      by_cases ht : ν t = 0
      · simp [ht]
      · exact mul_le_mul_of_nonneg_left
          (BohrData.sum_abs_normalizedIndicator_translate_le_of_rankRegular
            hreg hκ (hνsupp t ht)) (hνnonneg t)
    _ = (∑ t : G, ν t) * E := by rw [Finset.sum_mul]
    _ = E * ∑ t : G, ν t := by ring
    _ = 200 * ((max B.rank 1 : ℕ) : ℝ) * (κ : ℝ) * ∑ t : G, ν t := rfl

/-! ## Bohr majorization -/

/-- A coarsely regular shell majorizes its central Bohr measure after
smoothing by any probability measure supported on the small carrier.

The factor `2` is exactly the factor in `IsCoarselyRegularAt`; no asymptotic
notation is used. -/
theorem normalizedIndicator_le_two_mul_convolution_of_coarselyRegular
    {B : BohrData G} {rho eta : ℝ≥0}
    (hreg : B.IsCoarselyRegularAt rho eta)
    (ν : G → ℝ)
    (hνnonneg : ∀ t, 0 ≤ ν t)
    (hνmass : ∑ t : G, ν t = 1)
    (hνsupp : ∀ t, ν t ≠ 0 → t ∈ (B.dilate eta).carrier)
    (x : G) :
    normalizedIndicator (B.dilate rho).carrier x ≤
      2 * normalizedConvolution
        (normalizedIndicator (B.dilate (rho + eta)).carrier) ν x := by
  let Kminus := (B.dilate (rho - eta)).carrier
  let K := (B.dilate rho).carrier
  let Kplus := (B.dilate (rho + eta)).carrier
  have hinner : Kminus.card ≤ K.card := by
    apply Finset.card_le_card
    exact BohrData.carrier_dilate_mono (tsub_le_self : rho - eta ≤ rho)
  have hcard : Kplus.card ≤ 2 * K.card :=
    hreg.2.2.trans (Nat.mul_le_mul_left 2 hinner)
  have hKpos : (0 : ℝ) < K.card := by
    exact_mod_cast (B.dilate rho).carrier_nonempty.card_pos
  have hKpluspos : (0 : ℝ) < Kplus.card := by
    exact_mod_cast (B.dilate (rho + eta)).carrier_nonempty.card_pos
  have hconv (hx : x ∈ K) :
      normalizedConvolution (normalizedIndicator Kplus) ν x =
        (Kplus.card : ℝ)⁻¹ := by
    rw [normalizedConvolution_comm]
    simp only [normalizedConvolution]
    calc
      ∑ t : G, ν t * normalizedIndicator Kplus (x - t) =
          ∑ t : G, ν t * (Kplus.card : ℝ)⁻¹ := by
        apply Finset.sum_congr rfl
        intro t _
        by_cases ht : ν t = 0
        · simp [ht]
        · have hxt : x - t ∈ Kplus :=
            BohrData.sub_mem_dilate hx (hνsupp t ht)
          rw [normalizedIndicator_apply_mem hxt]
      _ = (∑ t : G, ν t) * (Kplus.card : ℝ)⁻¹ := by
        rw [Finset.sum_mul]
      _ = (Kplus.card : ℝ)⁻¹ := by rw [hνmass, one_mul]
  by_cases hx : x ∈ K
  · rw [show (B.dilate rho).carrier = K by rfl,
      normalizedIndicator_apply_mem hx, hconv hx]
    calc
      (K.card : ℝ)⁻¹ = 1 / (K.card : ℝ) := by rw [one_div]
      _ ≤ 2 / (Kplus.card : ℝ) := by
        rw [div_le_div_iff₀ hKpos hKpluspos]
        simpa only [one_mul] using (show (Kplus.card : ℝ) ≤ 2 * K.card by
          exact_mod_cast hcard)
      _ = 2 * (Kplus.card : ℝ)⁻¹ := by rw [div_eq_mul_inv]
  · rw [show (B.dilate rho).carrier = K by rfl,
      normalizedIndicator_apply_not_mem hx]
    exact mul_nonneg (by norm_num)
      (normalizedConvolution_nonneg
        (normalizedIndicator_nonneg Kplus) hνnonneg x)

/-- Rank-regular specialization of Bohr majorization.  The explicit
`1/(400 d)` scale ensures the outer shell is at most twice the inner shell,
so the preceding factor-two estimate applies. -/
theorem normalizedIndicator_le_two_mul_convolution_of_rankRegular
    {B : BohrData G} (hreg : B.IsRankRegular) {κ : ℝ≥0} (hκpos : 0 < κ)
    (hκ : κ ≤ 1 / (400 * (max B.rank 1 : ℕ) : ℝ≥0))
    (ν : G → ℝ) (hνnonneg : ∀ t, 0 ≤ ν t)
    (hνmass : ∑ t : G, ν t = 1)
    (hνsupp : ∀ t, ν t ≠ 0 → t ∈ (B.dilate κ).carrier)
    (x : G) :
    normalizedIndicator B.carrier x ≤
      2 * normalizedConvolution
        (normalizedIndicator (B.dilate (1 + κ)).carrier) ν x := by
  let d : ℕ := max B.rank 1
  have hd : 0 < d := by simp [d]
  have hκd : κ ≤ 1 / (400 * (d : ℝ≥0)) := by simpa [d] using hκ
  have hκreg : κ ≤ 1 / (100 * (d : ℝ≥0)) := by
    apply hκd.trans
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_right (by norm_num : (100 : ℝ≥0) ≤ 400) (by positivity)
  have hκone : κ ≤ 1 := by
    apply hκreg.trans
    rw [div_le_one]
    · exact_mod_cast (show 1 ≤ 100 * d by omega)
    · positivity
  have hcards := hreg κ (by simpa [d] using hκreg)
  have hquarter : (100 : ℝ) * d * (κ : ℝ) ≤ 1 / 4 := by
    have hκreal : (κ : ℝ) ≤ 1 / (400 * (d : ℝ)) := by
      exact_mod_cast hκd
    have hdreal : (0 : ℝ) < d := by exact_mod_cast hd
    calc
      (100 : ℝ) * d * (κ : ℝ) ≤ 100 * d * (1 / (400 * (d : ℝ))) := by gcongr
      _ = 1 / 4 := by field_simp; ring
  have hcardreal :
      ((B.dilate (1 + κ)).carrier.card : ℝ) ≤
        2 * ((B.dilate (1 - κ)).carrier.card : ℝ) := by
    nlinarith [hcards.1, hcards.2,
      show (0 : ℝ) < B.carrier.card by exact_mod_cast B.carrier_nonempty.card_pos]
  have hcard :
      (B.dilate (1 + κ)).carrier.card ≤
        2 * (B.dilate (1 - κ)).carrier.card := by
    exact_mod_cast hcardreal
  have hcoarse : B.IsCoarselyRegularAt 1 κ := ⟨hκpos, hκone, hcard⟩
  simpa only [BohrData.dilate_one] using
    normalizedIndicator_le_two_mul_convolution_of_coarselyRegular
      hcoarse ν hνnonneg hνmass hνsupp x

/-! ## A finite two-scale narrowing alternative -/

/-- The `{0,1}`-valued indicator used for local relative densities. -/
def finsetIndicator (A : Finset G) (x : G) : ℝ :=
  if x ∈ A then 1 else 0

@[simp] theorem finsetIndicator_apply_mem {A : Finset G} {x : G} (hx : x ∈ A) :
    finsetIndicator A x = 1 := by simp [finsetIndicator, hx]

@[simp] theorem finsetIndicator_apply_not_mem {A : Finset G} {x : G} (hx : x ∉ A) :
    finsetIndicator A x = 0 := by simp [finsetIndicator, hx]

/-- Relative density of `A` in a nonempty ambient finite set. -/
def relativeDensityOn (A K : Finset G) : ℝ :=
  (A.card : ℝ) / K.card

/-- The density of `A` on the translate `x - C`, normalized by `|C|`. -/
def localDensity (A C : Finset G) (x : G) : ℝ :=
  normalizedConvolution (finsetIndicator A) (normalizedIndicator C) x

/-- Summing an indicator over an ambient set containing it gives its
cardinality. -/
theorem sum_finsetIndicator_of_subset {A K : Finset G} (hAK : A ⊆ K) :
    ∑ x ∈ K, finsetIndicator A x = A.card := by
  have hsum :
      ∑ x ∈ A, finsetIndicator A x = ∑ x ∈ K, finsetIndicator A x := by
    apply Finset.sum_subset hAK
    intro x hxK hxA
    simp [finsetIndicator, hxA]
  rw [← hsum]
  simp [finsetIndicator]

/-- Pairing a subset indicator with the probability measure of its ambient
set gives the relative density. -/
theorem sum_finsetIndicator_mul_normalizedIndicator
    {A K : Finset G} (hAK : A ⊆ K) (hK : K.Nonempty) :
    ∑ x : G, finsetIndicator A x * normalizedIndicator K x =
      relativeDensityOn A K := by
  have hsum :
      ∑ x ∈ A, finsetIndicator A x * normalizedIndicator K x =
        ∑ x : G, finsetIndicator A x * normalizedIndicator K x := by
    apply Finset.sum_subset (Finset.subset_univ A)
    intro x _ hxA
    simp [finsetIndicator, hxA]
  rw [← hsum]
  calc
    ∑ x ∈ A, finsetIndicator A x * normalizedIndicator K x =
        ∑ _x ∈ A, (K.card : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [finsetIndicator_apply_mem hx,
        normalizedIndicator_apply_mem (hAK hx), one_mul]
    _ = relativeDensityOn A K := by
      simp [relativeDensityOn, div_eq_mul_inv, hK.card_ne_zero]

/-- The normalized average of a local-density function differs from the
ambient relative density only by the regular-Bohr boundary error. -/
theorem abs_sum_normalizedIndicator_mul_localDensity_sub_le_of_rankRegular
    {B : BohrData G} (hreg : B.IsRankRegular) {κ : ℝ≥0}
    (hκ : κ ≤ 1 / (100 * (max B.rank 1 : ℕ) : ℝ≥0))
    {A C : Finset G} (hAK : A ⊆ B.carrier) (hC : C.Nonempty)
    (hCsmall : C ⊆ (B.dilate κ).carrier) :
    |(∑ x : G, normalizedIndicator B.carrier x * localDensity A C x) -
        relativeDensityOn A B.carrier| ≤
      200 * ((max B.rank 1 : ℕ) : ℝ) * (κ : ℝ) := by
  let ν : G → ℝ := fun t ↦ normalizedIndicator C (-t)
  have hνnonneg : ∀ t, 0 ≤ ν t := fun t ↦ normalizedIndicator_nonneg C (-t)
  have hνmass : ∑ t : G, ν t = 1 := by
    calc
      ∑ t : G, ν t = ∑ t : G, normalizedIndicator C t := by
        exact Fintype.sum_equiv (Equiv.neg G) _ _ (fun _ ↦ rfl)
      _ = 1 := sum_normalizedIndicator hC
  have hνsupp : ∀ t, ν t ≠ 0 → t ∈ (B.dilate κ).carrier := by
    intro t ht
    have hneg : -t ∈ C := (normalizedIndicator_ne_zero_iff hC (-t)).mp ht
    exact BohrData.neg_mem_carrier.mp (hCsmall hneg)
  have hconv :
      ∑ y : G,
          |normalizedConvolution (normalizedIndicator B.carrier) ν y -
            normalizedIndicator B.carrier y| ≤
        200 * ((max B.rank 1 : ℕ) : ℝ) * (κ : ℝ) := by
    simpa [hνmass] using
      sum_abs_normalizedConvolution_error_le_of_rankRegular
        hreg hκ ν hνnonneg hνsupp
  have havg :
      ∑ x : G, normalizedIndicator B.carrier x * localDensity A C x =
        ∑ y : G, finsetIndicator A y *
          normalizedConvolution (normalizedIndicator B.carrier) ν y := by
    simp only [localDensity, normalizedConvolution, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro x _
    dsimp [ν]
    rw [neg_sub]
    ring
  have hbase :
      ∑ y : G, finsetIndicator A y * normalizedIndicator B.carrier y =
        relativeDensityOn A B.carrier :=
    sum_finsetIndicator_mul_normalizedIndicator hAK B.carrier_nonempty
  rw [havg, ← hbase, ← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  calc
    |∑ y : G, finsetIndicator A y *
        (normalizedConvolution (normalizedIndicator B.carrier) ν y -
          normalizedIndicator B.carrier y)| ≤
        ∑ y : G, |finsetIndicator A y *
          (normalizedConvolution (normalizedIndicator B.carrier) ν y -
            normalizedIndicator B.carrier y)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ y : G,
        |normalizedConvolution (normalizedIndicator B.carrier) ν y -
          normalizedIndicator B.carrier y| := by
      apply Finset.sum_le_sum
      intro y _
      by_cases hy : y ∈ A <;> simp [finsetIndicator, hy]
    _ ≤ 200 * ((max B.rank 1 : ℕ) : ℝ) * (κ : ℝ) := hconv

/-- On a plateau, translating the summation carrier by a small Bohr element
does not change the total mass of a subset indicator. -/
theorem sum_finsetIndicator_sub_eq_card_of_plateauRegular
    {B : BohrData G} {rho eta : ℝ≥0}
    (hreg : B.IsPlateauRegularAt rho eta)
    {A : Finset G} (hAK : A ⊆ (B.dilate rho).carrier)
    {t : G} (ht : t ∈ (B.dilate eta).carrier) :
    ∑ x ∈ (B.dilate rho).carrier, finsetIndicator A (x - t) = A.card := by
  let K := (B.dilate rho).carrier
  have hmem : ∀ x : G, x ∈ K ↔ x - t ∈ K := by
    intro x
    rw [← BohrData.mem_translateFinset]
    rw [BohrData.translate_carrier_eq_of_plateauRegular hreg ht]
  calc
    ∑ x ∈ (B.dilate rho).carrier, finsetIndicator A (x - t) =
        ∑ x ∈ K, finsetIndicator A x := by
      exact Finset.sum_equiv (Equiv.subRight t) hmem (by simp)
    _ = A.card := sum_finsetIndicator_of_subset hAK

/-- The exact local-density averaging identity behind Bourgain narrowing. -/
theorem sum_localDensity_on_plateau
    {B : BohrData G} {rho eta : ℝ≥0}
    (hreg : B.IsPlateauRegularAt rho eta)
    {A C : Finset G}
    (hAK : A ⊆ (B.dilate rho).carrier)
    (hC : C.Nonempty)
    (hCsmall : C ⊆ (B.dilate eta).carrier) :
    ∑ x ∈ (B.dilate rho).carrier, localDensity A C x = A.card := by
  have hcomm : localDensity A C =
      normalizedConvolution (normalizedIndicator C) (finsetIndicator A) :=
    normalizedConvolution_comm _ _
  rw [hcomm]
  simp only [normalizedConvolution]
  rw [Finset.sum_comm]
  calc
    ∑ t : G, ∑ x ∈ (B.dilate rho).carrier,
        normalizedIndicator C t * finsetIndicator A (x - t) =
        ∑ t : G, normalizedIndicator C t * A.card := by
      apply Finset.sum_congr rfl
      intro t _
      rw [← Finset.mul_sum]
      by_cases ht : t ∈ C
      · rw [sum_finsetIndicator_sub_eq_card_of_plateauRegular hreg hAK (hCsmall ht)]
      · simp [normalizedIndicator_apply_not_mem ht]
    _ = (∑ t : G, normalizedIndicator C t) * A.card := by
      rw [Finset.sum_mul]
    _ = A.card := by rw [sum_normalizedIndicator hC, one_mul]

/-- **Bourgain two-scale narrowing alternative.**  Let `A` lie in a
plateau-regular carrier `K`, and let `C₁,C₂` be nonempty subsets of the
small carrier.  For every positive `epsilon`, either one translate has at
least `(1-epsilon)` times the ambient density on both scales, or one of the
two local-density functions has a point at least
`(1+epsilon/2)` times the ambient density.

The proof is the two-scale averaging argument with no boundary error. -/
theorem bohr_narrowing_alternative
    {B : BohrData G} {rho eta : ℝ≥0}
    (hreg : B.IsPlateauRegularAt rho eta)
    {A C₁ C₂ : Finset G}
    (hA : A.Nonempty)
    (hAK : A ⊆ (B.dilate rho).carrier)
    (hC₁ : C₁.Nonempty) (hC₂ : C₂.Nonempty)
    (hC₁small : C₁ ⊆ (B.dilate eta).carrier)
    (hC₂small : C₂ ⊆ (B.dilate eta).carrier)
    {ε : ℝ} (hε : 0 < ε) :
    (∃ x ∈ (B.dilate rho).carrier,
        (1 - ε) * relativeDensityOn A (B.dilate rho).carrier ≤ localDensity A C₁ x ∧
        (1 - ε) * relativeDensityOn A (B.dilate rho).carrier ≤ localDensity A C₂ x) ∨
      (∃ x : G,
        (1 + ε / 2) * relativeDensityOn A (B.dilate rho).carrier ≤
          localDensity A C₁ x) ∨
      (∃ x : G,
        (1 + ε / 2) * relativeDensityOn A (B.dilate rho).carrier ≤
          localDensity A C₂ x) := by
  let K := (B.dilate rho).carrier
  let α : ℝ := relativeDensityOn A K
  have hK : K.Nonempty := (B.dilate rho).carrier_nonempty
  have hα : 0 < α := by
    dsimp [α, relativeDensityOn]
    exact div_pos (by exact_mod_cast hA.card_pos) (by exact_mod_cast hK.card_pos)
  by_cases hgood :
      ∃ x ∈ K,
        (1 - ε) * α ≤ localDensity A C₁ x ∧
        (1 - ε) * α ≤ localDensity A C₂ x
  · exact Or.inl hgood
  by_cases hinc₁ : ∃ x : G, (1 + ε / 2) * α ≤ localDensity A C₁ x
  · exact Or.inr (Or.inl hinc₁)
  by_cases hinc₂ : ∃ x : G, (1 + ε / 2) * α ≤ localDensity A C₂ x
  · exact Or.inr (Or.inr hinc₂)
  exfalso
  have hpoint : ∀ x ∈ K,
      localDensity A C₁ x + localDensity A C₂ x < 2 * α := by
    intro x hx
    have hu₁ : localDensity A C₁ x < (1 + ε / 2) * α := by
      exact lt_of_not_ge (fun h ↦ hinc₁ ⟨x, h⟩)
    have hu₂ : localDensity A C₂ x < (1 + ε / 2) * α := by
      exact lt_of_not_ge (fun h ↦ hinc₂ ⟨x, h⟩)
    have hlow :
        localDensity A C₁ x < (1 - ε) * α ∨
          localDensity A C₂ x < (1 - ε) * α := by
      by_cases h₁ : (1 - ε) * α ≤ localDensity A C₁ x
      · right
        exact lt_of_not_ge (fun h₂ ↦ hgood ⟨x, hx, h₁, h₂⟩)
      · left
        exact lt_of_not_ge h₁
    rcases hlow with hlow₁ | hlow₂
    · calc
        localDensity A C₁ x + localDensity A C₂ x <
            (1 - ε) * α + (1 + ε / 2) * α := add_lt_add hlow₁ hu₂
        _ < 2 * α := by nlinarith
    · calc
        localDensity A C₁ x + localDensity A C₂ x <
            (1 + ε / 2) * α + (1 - ε) * α := add_lt_add hu₁ hlow₂
        _ < 2 * α := by nlinarith
  have hsumlt :
      ∑ x ∈ K, (localDensity A C₁ x + localDensity A C₂ x) <
        ∑ x ∈ K, 2 * α :=
    Finset.sum_lt_sum_of_nonempty hK hpoint
  have hsum₁ : ∑ x ∈ K, localDensity A C₁ x = A.card :=
    sum_localDensity_on_plateau hreg hAK hC₁ hC₁small
  have hsum₂ : ∑ x ∈ K, localDensity A C₂ x = A.card :=
    sum_localDensity_on_plateau hreg hAK hC₂ hC₂small
  have hleft :
      ∑ x ∈ K, (localDensity A C₁ x + localDensity A C₂ x) =
        2 * (A.card : ℝ) := by
    rw [Finset.sum_add_distrib, hsum₁, hsum₂]
    ring
  have hright : ∑ _x ∈ K, 2 * α = 2 * (A.card : ℝ) := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    dsimp [α, relativeDensityOn]
    field_simp [hK.card_ne_zero]
  rw [hleft, hright] at hsumlt
  exact (lt_irrefl _ hsumlt)

/-- The quantitative rank-regular Bourgain narrowing alternative.  The last
hypothesis is the explicit version of `kappa ≪ alpha * epsilon / rank`; with
the constants in this development it absorbs both boundary errors. -/
theorem bohr_narrowing_alternative_of_rankRegular
    {B : BohrData G} (hreg : B.IsRankRegular) {κ : ℝ≥0}
    (hκ : κ ≤ 1 / (100 * (max B.rank 1 : ℕ) : ℝ≥0))
    {A C₁ C₂ : Finset G}
    (hA : A.Nonempty) (hAK : A ⊆ B.carrier)
    (hC₁ : C₁.Nonempty) (hC₂ : C₂.Nonempty)
    (hC₁small : C₁ ⊆ (B.dilate κ).carrier)
    (hC₂small : C₂ ⊆ (B.dilate κ).carrier)
    {ε : ℝ} (hε : 0 < ε)
    (hsmall :
      400 * ((max B.rank 1 : ℕ) : ℝ) * (κ : ℝ) ≤
        ε * relativeDensityOn A B.carrier / 4) :
    (∃ x ∈ B.carrier,
        (1 - ε) * relativeDensityOn A B.carrier ≤ localDensity A C₁ x ∧
        (1 - ε) * relativeDensityOn A B.carrier ≤ localDensity A C₂ x) ∨
      (∃ x : G,
        (1 + ε / 2) * relativeDensityOn A B.carrier ≤ localDensity A C₁ x) ∨
      (∃ x : G,
        (1 + ε / 2) * relativeDensityOn A B.carrier ≤ localDensity A C₂ x) := by
  let K := B.carrier
  let α : ℝ := relativeDensityOn A K
  let E : ℝ := 200 * ((max B.rank 1 : ℕ) : ℝ) * (κ : ℝ)
  let M₁ : ℝ := ∑ x : G, normalizedIndicator K x * localDensity A C₁ x
  let M₂ : ℝ := ∑ x : G, normalizedIndicator K x * localDensity A C₂ x
  have hK : K.Nonempty := B.carrier_nonempty
  have hα : 0 < α := by
    dsimp [α, K, relativeDensityOn]
    exact div_pos (by exact_mod_cast hA.card_pos) (by exact_mod_cast hK.card_pos)
  have havg₁ : |M₁ - α| ≤ E := by
    simpa [M₁, α, E, K] using
      abs_sum_normalizedIndicator_mul_localDensity_sub_le_of_rankRegular
        hreg hκ hAK hC₁ hC₁small
  have havg₂ : |M₂ - α| ≤ E := by
    simpa [M₂, α, E, K] using
      abs_sum_normalizedIndicator_mul_localDensity_sub_le_of_rankRegular
        hreg hκ hAK hC₂ hC₂small
  have hM₁ : α - E ≤ M₁ := by
    have := (abs_le.mp havg₁).1
    linarith
  have hM₂ : α - E ≤ M₂ := by
    have := (abs_le.mp havg₂).1
    linarith
  have hsmallE : 2 * E ≤ ε * α / 4 := by
    calc
      2 * E = 400 * ((max B.rank 1 : ℕ) : ℝ) * (κ : ℝ) := by
        dsimp [E]
        ring
      _ ≤ ε * relativeDensityOn A B.carrier / 4 := hsmall
      _ = ε * α / 4 := by rfl
  by_cases hgood :
      ∃ x ∈ K,
        (1 - ε) * α ≤ localDensity A C₁ x ∧
        (1 - ε) * α ≤ localDensity A C₂ x
  · exact Or.inl hgood
  by_cases hinc₁ : ∃ x : G, (1 + ε / 2) * α ≤ localDensity A C₁ x
  · exact Or.inr (Or.inl hinc₁)
  by_cases hinc₂ : ∃ x : G, (1 + ε / 2) * α ≤ localDensity A C₂ x
  · exact Or.inr (Or.inr hinc₂)
  exfalso
  let T : ℝ := 2 * α - ε * α / 2
  have hpoint : ∀ x ∈ K,
      localDensity A C₁ x + localDensity A C₂ x < T := by
    intro x hx
    have hu₁ : localDensity A C₁ x < (1 + ε / 2) * α :=
      lt_of_not_ge (fun h ↦ hinc₁ ⟨x, h⟩)
    have hu₂ : localDensity A C₂ x < (1 + ε / 2) * α :=
      lt_of_not_ge (fun h ↦ hinc₂ ⟨x, h⟩)
    have hlow :
        localDensity A C₁ x < (1 - ε) * α ∨
          localDensity A C₂ x < (1 - ε) * α := by
      by_cases h₁ : (1 - ε) * α ≤ localDensity A C₁ x
      · right
        exact lt_of_not_ge (fun h₂ ↦ hgood ⟨x, hx, h₁, h₂⟩)
      · left
        exact lt_of_not_ge h₁
    rcases hlow with hlow₁ | hlow₂
    · dsimp [T]
      nlinarith
    · dsimp [T]
      nlinarith
  have hweighted :
      ∑ x : G, normalizedIndicator K x *
          (localDensity A C₁ x + localDensity A C₂ x) <
        ∑ x : G, normalizedIndicator K x * T := by
    apply Finset.sum_lt_sum
    · intro x _
      by_cases hx : x ∈ K
      · exact mul_le_mul_of_nonneg_left (hpoint x hx).le
          (normalizedIndicator_nonneg K x)
      · simp [normalizedIndicator_apply_not_mem hx]
    · refine ⟨0, Finset.mem_univ 0, ?_⟩
      have hz : 0 ∈ K := B.zero_mem_carrier
      exact mul_lt_mul_of_pos_left (hpoint 0 hz)
        ((normalizedIndicator_pos_iff hK 0).2 hz)
  have hweighted' : M₁ + M₂ < T := by
    calc
      M₁ + M₂ = ∑ x : G, normalizedIndicator K x *
          (localDensity A C₁ x + localDensity A C₂ x) := by
        dsimp [M₁, M₂]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ < ∑ x : G, normalizedIndicator K x * T := hweighted
      _ = (∑ x : G, normalizedIndicator K x) * T := by rw [Finset.sum_mul]
      _ = T := by rw [sum_normalizedIndicator hK, one_mul]
  dsimp [T] at hweighted'
  nlinarith

end

end Erdos140

#print axioms Erdos140.sum_abs_normalizedConvolution_error_eq_zero_of_plateauRegular
#print axioms Erdos140.sum_abs_normalizedConvolution_error_le_of_rankRegular
#print axioms Erdos140.normalizedIndicator_le_two_mul_convolution_of_coarselyRegular
#print axioms Erdos140.normalizedIndicator_le_two_mul_convolution_of_rankRegular
#print axioms Erdos140.abs_sum_normalizedIndicator_mul_localDensity_sub_le_of_rankRegular
#print axioms Erdos140.bohr_narrowing_alternative
#print axioms Erdos140.bohr_narrowing_alternative_of_rankRegular
