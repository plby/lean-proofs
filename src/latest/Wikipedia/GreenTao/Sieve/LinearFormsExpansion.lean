import Wikipedia.GreenTao.LinearForms.Geometry
import Wikipedia.GreenTao.Sieve.CongruenceAverage
import Wikipedia.GreenTao.Sieve.LocalEulerFactors
import Wikipedia.GreenTao.Sieve.SmoothMajorant

/-!
# Exact finite expansion of Selberg weights along linear forms

This file performs the algebraic expansion that precedes the analytic
Goldston--Yıldırım estimate.  For a finite family of positive
natural-valued forms, the mean of a product of smooth Selberg squares is
written exactly as a finite sum over two bounded divisor choices per form.
Each term splits into

* a product of smooth Möbius-cutoff coefficients; and
* the exact density of the simultaneous divisibility congruences.

The least common multiple of the chosen divisors is bounded by
`R ^ (2 * card κ)`, using `CongruenceAverage`.  The final section
specializes the identity to the full CFZ family evaluated through
`apLinearForm` and the natural W-tricked lift.

There are no asymptotic estimates here.  Factoring the composite-modulus
congruence density into prime local factors, controlling the exceptional
primes, and bounding the resulting Euler product remain separate analytic
steps.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Bounded divisor choices and congruence densities -/

/-- Positive divisor choices allowed by a cutoff at `R`. -/
def smoothDivisorChoices (R : ℕ) : Finset ℕ :=
  Finset.Icc 1 R

/-- The pair of divisor choices created by one Selberg square. -/
def smoothDivisorPairChoices (R : ℕ) :
    Finset (ℕ × ℕ) :=
  (smoothDivisorChoices R).product
    (smoothDivisorChoices R)

/-- A simultaneous pair of divisor choices for every member of a finite
family. -/
def smoothDivisorFamilyChoices
    (κ : Type*) [Fintype κ] [DecidableEq κ]
    (R : ℕ) :
    Finset (κ → ℕ × ℕ) :=
  Fintype.piFinset fun _ : κ =>
    smoothDivisorPairChoices R

/-- Real-valued indicator of the natural divisibility relation. -/
def natDivisibilityIndicator (d n : ℕ) : ℝ :=
  if d ∣ n then 1 else 0

/-- The smooth Möbius coefficient attached to a family of paired divisor
choices. -/
noncomputable def smoothDivisorFamilyCoefficient
    {κ : Type*} [Fintype κ]
    (χ : ℝ → ℝ) (R : ℕ)
    (z : κ → ℕ × ℕ) : ℝ :=
  ∏ q,
    smoothDivisorSummand χ R (z q).1 *
      smoothDivisorSummand χ R (z q).2

/-- Indicator of all paired divisor conditions in one expansion term. -/
def pairedDivisibilityIndicator
    {κ X : Type*} [Fintype κ]
    (values : κ → X → ℕ)
    (z : κ → ℕ × ℕ) (x : X) : ℝ :=
  ∏ q,
    natDivisibilityIndicator (z q).1 (values q x) *
      natDivisibilityIndicator (z q).2 (values q x)

/-- Exact finite density of the simultaneous paired divisor
congruences. -/
noncomputable def pairedDivisibilityDensity
    {κ X : Type*} [Fintype κ] [Fintype X]
    (values : κ → X → ℕ)
    (z : κ → ℕ × ℕ) : ℝ :=
  mean (pairedDivisibilityIndicator values z)

/-- LCM of the `2 * card κ` moduli in one divisor-choice term. -/
def pairedDivisorLcm
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (z : κ → ℕ × ℕ) : ℕ :=
  Finset.univ.lcm
    (Sum.elim (fun q => (z q).1)
      (fun q => (z q).2))

theorem pairedDivisorLcm_pos
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {R : ℕ} {z : κ → ℕ × ℕ}
    (hz : z ∈ smoothDivisorFamilyChoices κ R) :
    0 < pairedDivisorLcm z := by
  apply Nat.pos_of_ne_zero
  rw [pairedDivisorLcm, Finset.lcm_ne_zero_iff]
  intro q _hq
  have hzq :=
    Fintype.mem_piFinset.mp hz
  cases q with
  | inl q =>
      exact Nat.ne_of_gt
        (Finset.mem_Icc.mp
          (Finset.mem_product.mp (hzq q)).1).1
  | inr q =>
      exact Nat.ne_of_gt
        (Finset.mem_Icc.mp
          (Finset.mem_product.mp (hzq q)).2).1

/-- Every term produced by `card κ` Selberg squares has period modulus at
most `R ^ (2 * card κ)`. -/
theorem pairedDivisorLcm_le_pow
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {R : ℕ} {z : κ → ℕ × ℕ}
    (hz : z ∈ smoothDivisorFamilyChoices κ R) :
    pairedDivisorLcm z ≤
      R ^ (2 * Fintype.card κ) := by
  have hzq :=
    Fintype.mem_piFinset.mp hz
  have hle :
      ∀ q : Sum κ κ,
        Sum.elim (fun i => (z i).1)
            (fun i => (z i).2) q ≤ R := by
    intro q
    cases q with
    | inl q =>
        exact
          (Finset.mem_Icc.mp
            (Finset.mem_product.mp (hzq q)).1).2
    | inr q =>
        exact
          (Finset.mem_Icc.mp
            (Finset.mem_product.mp (hzq q)).2).2
  unfold pairedDivisorLcm
  simpa [Fintype.card_sum, two_mul] using
    finset_lcm_le_pow_of_le
      (Finset.univ : Finset (Sum κ κ))
      (Sum.elim (fun i => (z i).1)
        (fun i => (z i).2))
      R (fun q _ => hle q)

/-! ## One Selberg square -/

/-- For a positive integer, filtered divisors up to `R` are exactly the
positive choices up to `R` which divide that integer. -/
theorem filtered_divisors_eq_smoothDivisorChoices
    {R n : ℕ} (hn : 0 < n) :
    n.divisors.filter (fun d => d ≤ R) =
      (smoothDivisorChoices R).filter
        (fun d => d ∣ n) := by
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors,
    smoothDivisorChoices, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hdvd, _hn0⟩, hdR⟩
    exact
      ⟨⟨Nat.pos_of_dvd_of_pos hdvd hn, hdR⟩, hdvd⟩
  · rintro ⟨⟨_hdpos, hdR⟩, hdvd⟩
    exact ⟨⟨hdvd, hn.ne'⟩, hdR⟩

/-- A support-filtered divisor sum reindexed over the fixed interval
`[1,R]`, with divisibility recorded by a zero--one factor. -/
theorem smoothTruncatedDivisorSum_eq_choice_sum
    (χ : ℝ → ℝ) {R n : ℕ}
    (hR : 1 < R)
    (hχ : ∀ x : ℝ, 1 ≤ x → χ x = 0)
    (hn : 0 < n) :
    smoothTruncatedDivisorSum χ R n =
      Real.log R *
        ∑ d ∈ smoothDivisorChoices R,
          smoothDivisorSummand χ R d *
            natDivisibilityIndicator d n := by
  rw [smoothTruncatedDivisorSum_eq_filtered_divisors
    χ hR hχ n]
  rw [filtered_divisors_eq_smoothDivisorChoices hn]
  apply congrArg (fun t : ℝ => Real.log R * t)
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d _hd
  by_cases hdn : d ∣ n <;>
    simp [natDivisibilityIndicator, hdn]

/-- Exact bounded paired-divisor expansion of one smooth Selberg square. -/
theorem smoothSelbergWeight_eq_pair_choice_sum
    (χ : ℝ → ℝ) {R n : ℕ}
    (hR : 1 < R)
    (hχ : ∀ x : ℝ, 1 ≤ x → χ x = 0)
    (hn : 0 < n) :
    smoothSelbergWeight χ R n =
      Real.log R ^ 2 *
        ∑ z ∈ smoothDivisorPairChoices R,
          (smoothDivisorSummand χ R z.1 *
              smoothDivisorSummand χ R z.2) *
            (natDivisibilityIndicator z.1 n *
              natDivisibilityIndicator z.2 n) := by
  rw [smoothSelbergWeight,
    smoothTruncatedDivisorSum_eq_choice_sum
      χ hR hχ hn]
  calc
    (Real.log R *
        ∑ d ∈ smoothDivisorChoices R,
          smoothDivisorSummand χ R d *
            natDivisibilityIndicator d n) ^ 2 =
        Real.log R ^ 2 *
          ((∑ d ∈ smoothDivisorChoices R,
              smoothDivisorSummand χ R d *
                natDivisibilityIndicator d n) *
            ∑ e ∈ smoothDivisorChoices R,
              smoothDivisorSummand χ R e *
                natDivisibilityIndicator e n) := by
      ring
    _ =
        Real.log R ^ 2 *
          ∑ d ∈ smoothDivisorChoices R,
            ∑ e ∈ smoothDivisorChoices R,
              (smoothDivisorSummand χ R d *
                  natDivisibilityIndicator d n) *
                (smoothDivisorSummand χ R e *
                  natDivisibilityIndicator e n) := by
      rw [Finset.sum_mul_sum]
    _ =
        Real.log R ^ 2 *
          ∑ d ∈ smoothDivisorChoices R,
            ∑ e ∈ smoothDivisorChoices R,
              (smoothDivisorSummand χ R d *
                  smoothDivisorSummand χ R e) *
                (natDivisibilityIndicator d n *
                  natDivisibilityIndicator e n) := by
      apply congrArg (fun t : ℝ => Real.log R ^ 2 * t)
      apply Finset.sum_congr rfl
      intro d _hd
      apply Finset.sum_congr rfl
      intro e _he
      ring
    _ =
        Real.log R ^ 2 *
          ∑ z ∈ smoothDivisorPairChoices R,
            (smoothDivisorSummand χ R z.1 *
                smoothDivisorSummand χ R z.2) *
              (natDivisibilityIndicator z.1 n *
                natDivisibilityIndicator z.2 n) := by
      unfold smoothDivisorPairChoices
      apply congrArg (fun t : ℝ => Real.log R ^ 2 * t)
      exact
        (Finset.sum_product
          (s := smoothDivisorChoices R)
          (t := smoothDivisorChoices R)
          (f := fun z : ℕ × ℕ =>
            (smoothDivisorSummand χ R z.1 *
                smoothDivisorSummand χ R z.2) *
              (natDivisibilityIndicator z.1 n *
                natDivisibilityIndicator z.2 n))).symm

/-! ## A finite family of Selberg squares -/

/-- Pointwise product expansion for a finite family of positive
natural-valued forms. -/
theorem prod_smoothSelbergWeight_eq_divisorExpansion
    {κ X : Type*} [Fintype κ] [DecidableEq κ]
    (χ : ℝ → ℝ) {R : ℕ}
    (hR : 1 < R)
    (hχ : ∀ x : ℝ, 1 ≤ x → χ x = 0)
    (values : κ → X → ℕ)
    (hvalues : ∀ q x, 0 < values q x)
    (x : X) :
    (∏ q, smoothSelbergWeight χ R (values q x)) =
      (Real.log R ^ 2) ^ Fintype.card κ *
        ∑ z ∈ smoothDivisorFamilyChoices κ R,
          smoothDivisorFamilyCoefficient χ R z *
            pairedDivisibilityIndicator values z x := by
  calc
    (∏ q, smoothSelbergWeight χ R (values q x)) =
        ∏ q,
          (Real.log R ^ 2 *
            ∑ z ∈ smoothDivisorPairChoices R,
              (smoothDivisorSummand χ R z.1 *
                  smoothDivisorSummand χ R z.2) *
                (natDivisibilityIndicator z.1
                    (values q x) *
                  natDivisibilityIndicator z.2
                    (values q x))) := by
      apply Finset.prod_congr rfl
      intro q _hq
      exact smoothSelbergWeight_eq_pair_choice_sum
        χ hR hχ (hvalues q x)
    _ =
        (Real.log R ^ 2) ^ Fintype.card κ *
          ∏ q,
            ∑ z ∈ smoothDivisorPairChoices R,
              (smoothDivisorSummand χ R z.1 *
                  smoothDivisorSummand χ R z.2) *
                (natDivisibilityIndicator z.1
                    (values q x) *
                  natDivisibilityIndicator z.2
                    (values q x)) := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ]
    _ =
        (Real.log R ^ 2) ^ Fintype.card κ *
          ∑ z ∈ smoothDivisorFamilyChoices κ R,
            ∏ q,
              ((smoothDivisorSummand χ R (z q).1 *
                  smoothDivisorSummand χ R (z q).2) *
                (natDivisibilityIndicator (z q).1
                    (values q x) *
                  natDivisibilityIndicator (z q).2
                    (values q x))) := by
      unfold smoothDivisorFamilyChoices
      rw [Finset.prod_univ_sum]
    _ =
        (Real.log R ^ 2) ^ Fintype.card κ *
          ∑ z ∈ smoothDivisorFamilyChoices κ R,
            smoothDivisorFamilyCoefficient χ R z *
              pairedDivisibilityIndicator values z x := by
      apply congrArg
        (fun t : ℝ =>
          (Real.log R ^ 2) ^ Fintype.card κ * t)
      apply Finset.sum_congr rfl
      intro z _hz
      unfold smoothDivisorFamilyCoefficient
        pairedDivisibilityIndicator
      rw [← Finset.prod_mul_distrib]

/-- **Exact finite linear-forms expansion.**  Averaging the pointwise
identity separates every term into its smooth coefficient and its exact
simultaneous divisibility density. -/
theorem mean_prod_smoothSelbergWeight_eq_divisorExpansion
    {κ X : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype X]
    (χ : ℝ → ℝ) {R : ℕ}
    (hR : 1 < R)
    (hχ : ∀ x : ℝ, 1 ≤ x → χ x = 0)
    (values : κ → X → ℕ)
    (hvalues : ∀ q x, 0 < values q x) :
    mean (fun x =>
        ∏ q, smoothSelbergWeight χ R (values q x)) =
      (Real.log R ^ 2) ^ Fintype.card κ *
        ∑ z ∈ smoothDivisorFamilyChoices κ R,
          smoothDivisorFamilyCoefficient χ R z *
            pairedDivisibilityDensity values z := by
  rw [show
      (fun x =>
        ∏ q, smoothSelbergWeight χ R (values q x)) =
      fun x =>
        (Real.log R ^ 2) ^ Fintype.card κ *
          ∑ z ∈ smoothDivisorFamilyChoices κ R,
            smoothDivisorFamilyCoefficient χ R z *
              pairedDivisibilityIndicator values z x by
    funext x
    exact prod_smoothSelbergWeight_eq_divisorExpansion
      χ hR hχ values hvalues x]
  rw [mean_smul]
  have hmean :
      mean (fun x =>
          ∑ z ∈ smoothDivisorFamilyChoices κ R,
            smoothDivisorFamilyCoefficient χ R z *
              pairedDivisibilityIndicator values z x) =
        ∑ z ∈ smoothDivisorFamilyChoices κ R,
          mean (fun x =>
            smoothDivisorFamilyCoefficient χ R z *
              pairedDivisibilityIndicator values z x) := by
    simpa [mean] using
      (Finset.expect_sum_comm
        (Finset.univ : Finset X)
        (smoothDivisorFamilyChoices κ R)
        (fun x z =>
          smoothDivisorFamilyCoefficient χ R z *
            pairedDivisibilityIndicator values z x))
  rw [hmean]
  apply congrArg
    (fun t : ℝ =>
      (Real.log R ^ 2) ^ Fintype.card κ * t)
  apply Finset.sum_congr rfl
  intro z _hz
  rw [mean_smul]
  rfl

/-! ## Normalized Selberg majorants -/

/-- Scalar relating the normalized Selberg majorant to its unnormalized
square. -/
noncomputable def normalizedSelbergScale
    (cχ : ℝ) (R W : ℕ) : ℝ :=
  ((W.totient : ℝ) / W) /
    (cχ * Real.log R)

theorem normalizedSelbergMajorant_eq_scale_mul
    (χ : ℝ → ℝ) (cχ : ℝ) (R W n : ℕ) :
    normalizedSelbergMajorant χ cχ R W n =
      normalizedSelbergScale cχ R W *
        smoothSelbergWeight χ R n := by
  unfold normalizedSelbergMajorant
    normalizedSelbergScale
  ring

/-- Exact expansion for a product of normalized Selberg majorants. -/
theorem mean_prod_normalizedSelbergMajorant_eq_divisorExpansion
    {κ X : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype X]
    (χ : ℝ → ℝ) (cχ : ℝ) {R W : ℕ}
    (hR : 1 < R)
    (hχ : ∀ x : ℝ, 1 ≤ x → χ x = 0)
    (values : κ → X → ℕ)
    (hvalues : ∀ q x, 0 < values q x) :
    mean (fun x =>
        ∏ q,
          normalizedSelbergMajorant
            χ cχ R W (values q x)) =
      normalizedSelbergScale cχ R W ^
          Fintype.card κ *
        ((Real.log R ^ 2) ^ Fintype.card κ *
          ∑ z ∈ smoothDivisorFamilyChoices κ R,
            smoothDivisorFamilyCoefficient χ R z *
              pairedDivisibilityDensity values z) := by
  rw [show
      (fun x =>
        ∏ q,
          normalizedSelbergMajorant
            χ cχ R W (values q x)) =
      fun x =>
        normalizedSelbergScale cχ R W ^
            Fintype.card κ *
          ∏ q, smoothSelbergWeight χ R (values q x) by
    funext x
    simp_rw [normalizedSelbergMajorant_eq_scale_mul]
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_const, Finset.card_univ]]
  rw [mean_smul,
    mean_prod_smoothSelbergWeight_eq_divisorExpansion
      χ hR hχ values hvalues]

/-! ## CFZ specialization -/

/-- The positive natural W-tricked lift of one CFZ residue-valued linear
form. -/
def cfzWTrickedLinearValue
    {k N : ℕ} [NeZero N]
    (W b : ℕ) (q : CFZFormIndex k)
    (x : CubePoint k N) : ℕ :=
  wTrickedValue W b
    (apLinearForm k N q.1 q.2 x)

theorem cfzWTrickedLinearValue_pos
    {k N : ℕ} [NeZero N]
    (W : ℕ) {b : ℕ} (hb : 0 < b)
    (q : CFZFormIndex k)
    (x : CubePoint k N) :
    0 < cfzWTrickedLinearValue W b q x := by
  unfold cfzWTrickedLinearValue wTrickedValue
  omega

/-- Exact full-CFZ-family expansion for the normalized W-tricked Selberg
majorant.  This is the finite algebraic identity immediately preceding the
local-factor analysis. -/
theorem mean_prod_normalizedSelbergMajorant_cfz_eq_divisorExpansion
    {k N : ℕ} [NeZero N]
    (χ : ℝ → ℝ) (cχ : ℝ)
    {R W b : ℕ} (hR : 1 < R) (hb : 0 < b)
    (hχ : ∀ x : ℝ, 1 ≤ x → χ x = 0) :
    mean (fun x : CubePoint k N =>
        ∏ q : CFZFormIndex k,
          normalizedSelbergMajorant χ cχ R W
            (cfzWTrickedLinearValue W b q x)) =
      normalizedSelbergScale cχ R W ^
          Fintype.card (CFZFormIndex k) *
        ((Real.log R ^ 2) ^
            Fintype.card (CFZFormIndex k) *
          ∑ z ∈ smoothDivisorFamilyChoices
              (CFZFormIndex k) R,
            smoothDivisorFamilyCoefficient χ R z *
              pairedDivisibilityDensity
                (cfzWTrickedLinearValue
                  (k := k) (N := N) W b) z) := by
  exact
    mean_prod_normalizedSelbergMajorant_eq_divisorExpansion
      χ cχ hR hχ
      (cfzWTrickedLinearValue
        (k := k) (N := N) W b)
      (fun q x =>
        cfzWTrickedLinearValue_pos W hb q x)

/-- Structured-cutoff version of the full CFZ expansion. -/
theorem SmoothSieveCutoff.mean_prod_majorant_cfz_eq_divisorExpansion
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    {R W b : ℕ} (hR : 1 < R) (hb : 0 < b) :
    mean (fun x : CubePoint k N =>
        ∏ q : CFZFormIndex k,
          χ.majorant R W
            (cfzWTrickedLinearValue W b q x)) =
      normalizedSelbergScale χ.normalizer R W ^
          Fintype.card (CFZFormIndex k) *
        ((Real.log R ^ 2) ^
            Fintype.card (CFZFormIndex k) *
          ∑ z ∈ smoothDivisorFamilyChoices
              (CFZFormIndex k) R,
            smoothDivisorFamilyCoefficient χ.toFun R z *
              pairedDivisibilityDensity
                (cfzWTrickedLinearValue
                  (k := k) (N := N) W b) z) := by
  simpa [SmoothSieveCutoff.majorant] using
    mean_prod_normalizedSelbergMajorant_cfz_eq_divisorExpansion
      χ.toFun χ.normalizer hR hb χ.zero_of_one_le

end Wikipedia.SzemeredisTheorem
