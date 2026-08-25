import ErdosProblems.Erdos67.Section3

/-!
# Tao's Section 4: two-scale probability bookkeeping

This file contains no new analytic input.  It applies the measurable good-set
theorem from Section 3 at the two geometric scales `Y` and `Y ^ D`, intersects
the events, and keeps both pretentious approximations attached to the same
compact character.  The final frequency comparison is exposed as the precise
deterministic conclusion to be supplied by the twist-separation argument.
-/

open scoped ENNReal
open MeasureTheory

namespace Erdos67

/-- One sample has bounded pretentious approximations at both `Y` and
`Y ^ D`. -/
def HasTwoScalePretentiousPair
    (A Y D : ℕ) (g : CompactCircleCharacter) : Prop :=
  HasBoundedPretentiousApproximation A (Y ^ D) g ∧
    HasBoundedPretentiousApproximation A Y g

/-- The same two approximations, with their witnesses displayed and with the
frequency difference smaller than the lower scale. -/
def HasNearbyTwoScalePretentiousPair
    (A Y D : ℕ) (g : CompactCircleCharacter) : Prop :=
  ∃ q : ℕ, 0 < q ∧ q ≤ A ∧
    ∃ χ : DirichletCharacter ℂ q, ∃ t : ℝ,
      |t| ≤ (A : ℝ) * (Y ^ D : ℕ) ∧
      pretentiousDistSqToTwist (compactCharacterNatValue g) χ t (Y ^ D) < A ∧
  ∃ q' : ℕ, 0 < q' ∧ q' ≤ A ∧
    ∃ χ' : DirichletCharacter ℂ q', ∃ t' : ℝ,
      |t'| ≤ (A : ℝ) * Y ∧
      pretentiousDistSqToTwist (compactCharacterNatValue g) χ' t' Y < A ∧
      |t' - t| < Y

/-- The exact deterministic twist-separation conclusion needed by the
probability assembly.  The Vinogradov--Korobov module is responsible only for
proving this predicate (under its analytic hypotheses); no probability or
measurable-selection issue remains there. -/
def TwoScaleTwistSeparationConclusion (A Y D : ℕ) : Prop :=
  ∀ (g : CompactCircleCharacter)
    (q : ℕ) (_hq : 0 < q) (_hqA : q ≤ A)
    (χ : DirichletCharacter ℂ q) (t : ℝ),
      |t| ≤ (A : ℝ) * (Y ^ D : ℕ) →
      pretentiousDistSqToTwist (compactCharacterNatValue g) χ t (Y ^ D) < A →
    ∀ (q' : ℕ) (_hq' : 0 < q') (_hq'A : q' ≤ A)
      (χ' : DirichletCharacter ℂ q') (t' : ℝ),
        |t'| ≤ (A : ℝ) * Y →
        pretentiousDistSqToTwist (compactCharacterNatValue g) χ' t' Y < A →
        |t' - t| < Y

theorem HasTwoScalePretentiousPair.nearby
    {A Y D : ℕ} {g : CompactCircleCharacter}
    (hpair : HasTwoScalePretentiousPair A Y D g)
    (hsep : TwoScaleTwistSeparationConclusion A Y D) :
    HasNearbyTwoScalePretentiousPair A Y D g := by
  rcases hpair.1 with ⟨q, hq, hqA, χ, t, ht, hdist⟩
  rcases hpair.2 with ⟨q', hq', hq'A, χ', t', ht', hdist'⟩
  refine ⟨q, hq, hqA, χ, t, ht, hdist,
    q', hq', hq'A, χ', t', ht', hdist', ?_⟩
  exact hsep g q hq hqA χ t ht hdist q' hq' hq'A χ' t' ht' hdist'

/-- Intersecting two measurable events doubles a common upper bound for the
measure of their complements. -/
theorem measure_compl_inter_le_two
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {G₁ G₂ : Set Ω}
    (δ : ℝ≥0∞) (h₁ : μ G₁ᶜ ≤ δ) (h₂ : μ G₂ᶜ ≤ δ) :
    μ (G₁ ∩ G₂)ᶜ ≤ 2 * δ := by
  rw [Set.compl_inter]
  calc
    μ (G₁ᶜ ∪ G₂ᶜ) ≤ μ G₁ᶜ + μ G₂ᶜ := measure_union_le _ _
    _ ≤ δ + δ := add_le_add h₁ h₂
    _ = 2 * δ := (two_mul δ).symm

/-- A set whose complement has probability strictly below one contains a
sample.  This is the final elementary step after the two-scale union bound. -/
theorem set_nonempty_of_probability_compl_lt_one
    {Ω : Type*} [MeasurableSpace Ω] (μ : ProbabilityMeasure Ω)
    {G : Set Ω} (hG : (μ : Measure Ω) Gᶜ < 1) : G.Nonempty := by
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty.mp hempty] at hG
  have hone : (μ : Measure Ω) Set.univ = 1 := measure_univ
  rw [Set.compl_empty, hone] at hG
  exact (lt_irrefl 1) hG

/-- Consumer form for an explicit exceptional-probability upper bound. -/
theorem set_nonempty_of_probability_compl_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : ProbabilityMeasure Ω)
    {G : Set Ω} {δ : ℝ≥0∞}
    (hG : (μ : Measure Ω) Gᶜ ≤ δ) (hδ : δ < 1) : G.Nonempty :=
  set_nonempty_of_probability_compl_lt_one μ (hG.trans_lt hδ)

/-- Section 3 applied at `Y = 4^K` and `Y^D = 4^(K*D)`.

The two exceptional-set bounds are combined by a union bound, giving the
exact loss `2 * ofReal (4*C^2/B)`.  Every character in the intersection has
both approximations simultaneously; the existential witnesses need not be
chosen measurably. -/
theorem NonasymptoticLogElliott.exists_highProbability_twoScalePretentiousSet
    (helliott : NonasymptoticLogElliott)
    (μ : ProbabilityMeasure CompactCircleCharacter) (C B η : ℝ) (H D : ℕ)
    (hBpos : 0 < B) (hH : 0 < H) (hBH : B < H) (hη : 0 < η)
    (hD : 0 < D)
    (hbound : ∀ m : ℕ, compactMeanSquarePartialSum μ m ≤ C ^ 2) :
    ∃ A₀ : ℕ, 2 ≤ A₀ ∧
      ∀ A K : ℕ, A₀ ≤ A → A ≤ 2 ^ K → 0 < K →
        η * Real.log ((2 ^ K : ℕ) : ℝ) <
          ((H : ℝ) - B) * dyadicCorrelationWeight K / (H : ℝ) ^ 2 →
        η * Real.log ((2 ^ (K * D) : ℕ) : ℝ) <
          ((H : ℝ) - B) * dyadicCorrelationWeight (K * D) / (H : ℝ) ^ 2 →
        ∃ G : Set CompactCircleCharacter,
          MeasurableSet G ∧
          (μ : Measure CompactCircleCharacter) Gᶜ ≤
            2 * ENNReal.ofReal (4 * C ^ 2 / B) ∧
          ∀ g ∈ G,
            HasTwoScalePretentiousPair A (4 ^ K) D g := by
  obtain ⟨A₀, hA₀, hgood⟩ :=
    helliott.exists_highProbability_pretentiousSet
      μ C B η H hBpos hH hBH hη hbound
  refine ⟨A₀, hA₀, ?_⟩
  intro A K hA hAK hK hsmall hlarge
  have hKD : 0 < K * D := Nat.mul_pos hK hD
  have hKleKD : K ≤ K * D := by
    have hDone : 1 ≤ D := hD
    nlinarith
  have hAKD : A ≤ 2 ^ (K * D) :=
    hAK.trans (Nat.pow_le_pow_right (by omega) hKleKD)
  obtain ⟨Glarge, hGlarge, hμlarge, hlargeWitness⟩ :=
    hgood A (K * D) hA hAKD hKD hlarge
  obtain ⟨Gsmall, hGsmall, hμsmall, hsmallWitness⟩ :=
    hgood A K hA hAK hK hsmall
  refine ⟨Glarge ∩ Gsmall, hGlarge.inter hGsmall,
    measure_compl_inter_le_two (μ : Measure CompactCircleCharacter)
      (ENNReal.ofReal (4 * C ^ 2 / B)) hμlarge hμsmall, ?_⟩
  intro g hg
  have hlarge' := hlargeWitness g hg.1
  have hsmall' := hsmallWitness g hg.2
  constructor
  · simpa only [pow_mul] using hlarge'
  · exact hsmall'

/-- The probability assembly with the analytic twist-separation conclusion
plugged in.  This theorem performs only deterministic witness unpacking after
the union bound. -/
theorem NonasymptoticLogElliott.exists_highProbability_nearbyTwoScaleSet
    (helliott : NonasymptoticLogElliott)
    (μ : ProbabilityMeasure CompactCircleCharacter) (C B η : ℝ) (H D : ℕ)
    (hBpos : 0 < B) (hH : 0 < H) (hBH : B < H) (hη : 0 < η)
    (hD : 0 < D)
    (hbound : ∀ m : ℕ, compactMeanSquarePartialSum μ m ≤ C ^ 2) :
    ∃ A₀ : ℕ, 2 ≤ A₀ ∧
      ∀ A K : ℕ, A₀ ≤ A → A ≤ 2 ^ K → 0 < K →
        η * Real.log ((2 ^ K : ℕ) : ℝ) <
          ((H : ℝ) - B) * dyadicCorrelationWeight K / (H : ℝ) ^ 2 →
        η * Real.log ((2 ^ (K * D) : ℕ) : ℝ) <
          ((H : ℝ) - B) * dyadicCorrelationWeight (K * D) / (H : ℝ) ^ 2 →
        TwoScaleTwistSeparationConclusion A (4 ^ K) D →
        ∃ G : Set CompactCircleCharacter,
          MeasurableSet G ∧
          (μ : Measure CompactCircleCharacter) Gᶜ ≤
            2 * ENNReal.ofReal (4 * C ^ 2 / B) ∧
          ∀ g ∈ G,
            HasNearbyTwoScalePretentiousPair A (4 ^ K) D g := by
  obtain ⟨A₀, hA₀, hgood⟩ :=
    helliott.exists_highProbability_twoScalePretentiousSet
      μ C B η H D hBpos hH hBH hη hD hbound
  refine ⟨A₀, hA₀, ?_⟩
  intro A K hA hAK hK hsmall hlarge hsep
  obtain ⟨G, hG, hμG, hpair⟩ :=
    hgood A K hA hAK hK hsmall hlarge
  exact ⟨G, hG, hμG, fun g hg ↦ (hpair g hg).nearby hsep⟩

end Erdos67
