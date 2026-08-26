import ErdosProblems.Erdos67b.ElliottComplete
import ErdosProblems.Erdos67b.LSeriesSublinear
import ErdosProblems.Erdos67b.Section4ConvolutionBridge

/-! # Unconditional selection with two pretentious events and weighted energy

The conductor cutoff precedes the BCC parameters. The finite weight window
is specified after the dyadic scale and before the sample is selected.
-/

open scoped ENNReal
open MeasureTheory

namespace Erdos67b

noncomputable section

theorem Section4Selection.fields_eq_of_params_heq
    {C B : ℝ} {A : ℕ} {S : Section4Selection C}
    {P : Section4BCCParameters A B}
    (hA : S.A = A) (hB : S.B = B) (hP : HEq S.params P) :
    S.H = P.H ∧ S.k = P.k ∧ S.D = P.D := by
  cases S
  dsimp only at hA hB hP ⊢
  subst A
  subst B
  cases eq_of_heq hP
  exact ⟨rfl, rfl, rfl⟩

theorem section4_threeExceptionalProbability_lt_one (C : ℝ) :
    2 * ENNReal.ofReal (4 * C ^ 2 / section4B C) +
      ENNReal.ofReal (4 * C ^ 2 / section4B C) < 1 := by
  rw [show 2 * ENNReal.ofReal (4 * C ^ 2 / section4B C) +
      ENNReal.ofReal (4 * C ^ 2 / section4B C) =
      3 * ENNReal.ofReal (4 * C ^ 2 / section4B C) by ring]
  rw [← ENNReal.ofReal_ofNat 3, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_lt_one]
  have hB := section4B_pos C
  rw [show (3 : ℝ) * (4 * C ^ 2 / section4B C) =
      12 * C ^ 2 / section4B C by ring, div_lt_one hB]
  unfold section4B
  nlinarith [sq_nonneg C]

theorem exists_final_weightedSection4Selection
    (μ : ProbabilityMeasure CompactCircleCharacter) (C : ℝ)
    (hbound : ∀ m : ℕ, compactMeanSquarePartialSum μ m ≤ C ^ 2) :
    ∃ A : ℕ, 2 ≤ A ∧
      ∀ Bcc : ℝ, ∀ P : Section4BCCParameters A Bcc,
        ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K →
          ∀ V : Section4WeightWindow P.H (4 ^ K),
            ∃ S : Section4Selection C,
              S.A = A ∧ S.K = K ∧ S.B = Bcc ∧ HEq S.params P ∧
              compactMediumWeightedLocalEnergy V.centers V.weight S.H S.sample <
                section4B C * V.mass := by
  obtain ⟨A, hA, hone⟩ := unitCircleLogElliott.exists_highProbability_pretentiousSet
    μ C (section4B C) (section4Eta C) (section4H C)
    (section4B_pos C) (section4H_pos C) (section4B_lt_section4H C)
    (section4Eta_pos C) hbound
  refine ⟨A, hA, ?_⟩
  intro Bcc P
  obtain ⟨Ksep, hsep⟩ := LSeriesSublinear.eventuallyTwoScaleTwistSeparation_unconditional
    A P.D hA P.D_pos
  let K₀ := max A Ksep
  refine ⟨K₀, ?_⟩
  intro K hK V
  have hAK : A ≤ K := (le_max_left _ _).trans hK
  have hsepK : Ksep ≤ K := (le_max_right _ _).trans hK
  have hKpos : 0 < K := by omega
  have hApow : A ≤ 2 ^ K := hAK.trans K.lt_two_pow_self.le
  have hKD : 0 < K * P.D := Nat.mul_pos hKpos P.D_pos
  have hKleKD : K ≤ K * P.D := by
    have hDone := P.D_pos
    nlinarith
  have hApowD : A ≤ 2 ^ (K * P.D) :=
    hApow.trans (Nat.pow_le_pow_right (by omega) hKleKD)
  obtain ⟨Glarge, hGlarge, hμlarge, hlarge⟩ :=
    hone A (K * P.D) le_rfl hApowD hKD (section4_threshold C hKD)
  obtain ⟨Gsmall, hGsmall, hμsmall, hsmall⟩ :=
    hone A K le_rfl hApow hKpos (section4_threshold C hKpos)
  let G := Glarge ∩ Gsmall
  have hG : (μ : Measure CompactCircleCharacter) Gᶜ ≤
      2 * ENNReal.ofReal (4 * C ^ 2 / section4B C) :=
    measure_compl_inter_le_two _ _ hμlarge hμsmall
  have hnear : ∀ g ∈ G, HasNearbyTwoScalePretentiousPair A (4 ^ K) P.D g := by
    intro g hg
    have hpair : HasTwoScalePretentiousPair A (4 ^ K) P.D g := by
      constructor
      · simpa only [pow_mul] using hlarge g hg.1
      · exact hsmall g hg.2
    exact hpair.nearby (hsep K hsepK)
  obtain ⟨S, hSA, hSK, hSB, hSP, _hg, henergy⟩ :=
    exists_weightedSection4Selection_of_nearbySet μ C hbound P hA hKpos hApow
      G _ hG hnear V (section4B C) (section4B_pos C)
      (section4_threeExceptionalProbability_lt_one C)
  exact ⟨S, hSA, hSK, hSB, hSP, henergy⟩

end

end Erdos67b
