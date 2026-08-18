/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section4DecayAlgebra
import ErdosProblems.Erdos186.CFP.Bilu.Section4RankOneInitializer
import ErdosProblems.Erdos186.CFP.Bilu.Section4RawDecaySourceAssembly
import ErdosProblems.Erdos186.CFP.Bilu.Section9PresentationReplacement

/-!
# Uniform assembly of the sharp Section 9 decay

This is the numeric terminal adapter for the remaining geometric theorem.
The input record says that an enlarged-injective presentation admits the
source Section 9 replacement with a rank-uniform loss.  The adapter chooses
all Proposition 8.3 parameters, performs rank repair, handles the branch in
which repair already gives the desired decay, and constructs the exact raw
Section 4 package.
-/

namespace Erdos186.CFP.Bilu.Section4SharpDecayAssembly

open MeasureTheory MinkowskiUpper
open CFP.BiluFreiman
open Section4DecayAlgebra Section4RankOneInitializer
open Section4RawDecaySourceAssembly Section4TerminalConstants
open Section4TerminalScaledRealization Section4ScaledDecay
open Section7BiasedNumerics Section8Synthesis
open Section8PresentationNormalization
open Section92PresentationDescent Section92UniformRankRepair
open Section92WeightedRankRepair

noncomputable section

set_option autoImplicit false

/-- A finite upper bound for every Proposition 8.3 threshold below the
chosen rank ceiling. -/
def uniformProposition83Threshold (rankBound : ℕ) (sigma : ℝ) : ℝ :=
  1 + ∑ m ∈ Finset.range (rankBound + 1),
    proposition83Threshold m (distortionRank sigma) sigma

theorem proposition83Threshold_lt_uniform
    {m rankBound : ℕ} (hm : m ≤ rankBound) (sigma : ℝ) :
    proposition83Threshold m (distortionRank sigma) sigma <
      uniformProposition83Threshold rankBound sigma := by
  have hterm : proposition83Threshold m (distortionRank sigma) sigma ≤
      ∑ i ∈ Finset.range (rankBound + 1),
        proposition83Threshold i (distortionRank sigma) sigma := by
    exact Finset.single_le_sum
      (s := Finset.range (rankBound + 1))
      (f := fun i ↦ proposition83Threshold i
        (distortionRank sigma) sigma)
      (fun i _hi ↦ by unfold proposition83Threshold; positivity)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))
  unfold uniformProposition83Threshold
  linarith

theorem one_le_uniformProposition83Threshold
    (rankBound : ℕ) (sigma : ℝ) :
    1 ≤ uniformProposition83Threshold rankBound sigma := by
  unfold uniformProposition83Threshold
  have hsum : 0 ≤ ∑ m ∈ Finset.range (rankBound + 1),
      proposition83Threshold m (distortionRank sigma) sigma := by
    apply Finset.sum_nonneg
    intro m _hm
    unfold proposition83Threshold
    positivity
  linarith

/-- The sole remaining geometric boundary.  The loss is independent of
the source set and current presentation; the replacement itself may depend
on all of them. -/
structure UniformSharpReplacement (s : ℕ) (sigma : ℝ) where
  rankBound : ℕ
  rankBound_pos : 1 ≤ rankBound
  sigma_one : 1 ≤ sigma
  loss : ℝ
  loss_pos : 0 < loss
  replace : ∀ {A : Finset ℤ} (X : RankedBodyPresentation A),
    A.Nonempty → 1 < A.card → X.1 ≤ rankBound →
    EnlargedInjective s X →
    ∀ epsilon : ℝ, 0 < epsilon →
      ((twoA A).card : ℝ) ≤ sigma * A.card →
      (((16 : ℝ) * X.1) ^ X.1) * epsilon * A.card ≤
        (4 : ℝ) ^ X.1 *
          volume.real (unitBall (normalizedMahlerSeminorm X)) →
      proposition83Threshold X.1 (distortionRank sigma) sigma < epsilon →
      ∃ Y : RankedBodyPresentation A,
        Y.1 ≤ rankBound ∧
        bodyVolume Y ≤ loss * bodyVolume X *
          (epsilon ^ proposition83Exponent X.1
            (distortionRank sigma))⁻¹

/-- The common positive natural denominator for all actual Proposition 8.3
exponents below the rank ceiling. -/
def uniformDecayExponent (rankBound : ℕ) (sigma : ℝ) : ℕ :=
  2 * (2 * rankBound + distortionRank sigma)

theorem uniformDecayExponent_pos
    {rankBound : ℕ} {sigma : ℝ} (hsigma : 1 ≤ sigma) :
    0 < uniformDecayExponent rankBound sigma := by
  unfold uniformDecayExponent
  have hr := distortionRank_pos hsigma
  omega

/-- The polar-volume coefficient used uniformly at every lower rank. -/
def uniformEpsilonCoefficient (rankBound : ℕ) : ℝ :=
  ((4 : ℝ) ^ rankBound)⁻¹

theorem uniformEpsilonCoefficient_pos (rankBound : ℕ) :
    0 < uniformEpsilonCoefficient rankBound := by
  unfold uniformEpsilonCoefficient
  positivity

/-- The fixed ordinary-volume cost of forgetting the rank weights after
canonical quotient repair. -/
def uniformRepairLoss (s rankBound : ℕ) : ℝ :=
  canonicalRankRepairFactor s rankBound ^ rankBound

theorem uniformRepairLoss_pos (s rankBound : ℕ) :
    0 < uniformRepairLoss s rankBound := by
  unfold uniformRepairLoss
  exact pow_pos (zero_lt_one.trans_le
    (one_le_canonicalRankRepairFactor s rankBound)) _

/-- One real constant simultaneously ensuring that epsilon clears the
Proposition 8.3 threshold and that the geometric replacement satisfies the
raw decay inequality. -/
def rawDecayRealConstant (s rankBound : ℕ) (sigma loss : ℝ) : ℝ :=
  let Q := uniformDecayExponent rankBound sigma
  let repair := uniformRepairLoss s rankBound
  let coefficient := uniformEpsilonCoefficient rankBound
  let threshold := uniformProposition83Threshold rankBound sigma
  1 +
    (2 : ℝ) ^ Q * repair ^ (Q - 1) * threshold / coefficient +
    (2 : ℝ) ^ Q * loss ^ Q * repair ^ (Q - 1) / coefficient

/-- Natural coefficient consumed by the source-facing Section 4 package. -/
def rawDecayConstant (s rankBound : ℕ) (sigma loss : ℝ) : ℕ :=
  Nat.ceil (rawDecayRealConstant s rankBound sigma loss)

theorem rawDecayRealConstant_le_cast
    (s rankBound : ℕ) (sigma loss : ℝ) :
    rawDecayRealConstant s rankBound sigma loss ≤
      (rawDecayConstant s rankBound sigma loss : ℝ) := by
  exact Nat.le_ceil _

/-- The exact raw decay field required by `RawBodyDecaySourcePackage`,
deduced from a uniform sharp replacement theorem. -/
theorem exists_rawBodyDecay_of_uniformSharpReplacement
    (s d : ℕ) (delta sigma : ℝ) (_hs : 0 < s)
    (hsourceSigma : Real.rpow 2 ((d : ℝ) + 1 - delta) ≤ sigma)
    (S : UniformSharpReplacement s sigma)
    (A : Finset ℤ) (hA : A.Nonempty)
    (hdouble : ((twoA A).card : ℝ) ≤
      Real.rpow 2 ((d : ℝ) + 1 - delta) * A.card)
    (hlargeCard : S.rankBound < A.card)
    (x : RankBoundedBodyPresentation A S.rankBound)
    (_hlargeVolume :
      ((terminalVolumeConstant s S.rankBound S.rankBound
          (rawDecayConstant s S.rankBound sigma S.loss) * A.card : ℕ) : ℝ) <
        uniformTerminalBodyVolume s S.rankBound x.1) :
    ∃ y : RankBoundedBodyPresentation A S.rankBound,
      (2 * bodyVolume y.1) ^ uniformDecayExponent S.rankBound sigma ≤
        (((rawDecayConstant s S.rankBound sigma S.loss * A.card : ℕ) : ℝ)) *
          bodyVolume x.1 ^ (uniformDecayExponent S.rankBound sigma - 1) := by
  let Q := uniformDecayExponent S.rankBound sigma
  let repairFactor := canonicalRankRepairFactor s S.rankBound
  let repairLoss := uniformRepairLoss s S.rankBound
  let coefficient := uniformEpsilonCoefficient S.rankBound
  let threshold := uniformProposition83Threshold S.rankBound sigma
  let rawConstant := rawDecayConstant s S.rankBound sigma S.loss
  have hQ : 0 < Q := uniformDecayExponent_pos S.sigma_one
  have hcardTwo : 1 < A.card := lt_of_le_of_lt S.rankBound_pos hlargeCard
  obtain ⟨Z, hZgood, hZrank, hZweighted⟩ :=
    exists_enlargedInjective_of_canonicalQuotient
      s S.rankBound hcardTwo x.1 x.2
  have hrepairFactor : 1 ≤ repairFactor := by
    exact one_le_canonicalRankRepairFactor s S.rankBound
  have hrepairLoss : 0 < repairLoss := uniformRepairLoss_pos s S.rankBound
  have hZle : bodyVolume Z ≤ repairLoss * bodyVolume x.1 := by
    exact bodyVolume_le_factor_pow_rankBound_of_weighted_le
      hrepairFactor x.1 Z x.2 hZweighted
  by_cases hdirect : (2 * bodyVolume Z) ^ Q ≤
      ((rawConstant : ℝ) * A.card) * bodyVolume x.1 ^ (Q - 1)
  · exact ⟨⟨Z, hZrank⟩, by
      simpa only [Nat.cast_mul] using hdirect⟩
  have hlinear : (rawConstant : ℝ) * A.card <
      2 ^ Q * repairLoss ^ (Q - 1) * bodyVolume Z :=
    linear_large_of_not_pow_decay hQ (bodyVolume_pos x.1)
      (bodyVolume_pos Z) hZle hdirect
  let epsilon : ℝ := coefficient * bodyVolume Z / A.card
  have hcardReal : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hcoefficient : 0 < coefficient :=
    uniformEpsilonCoefficient_pos S.rankBound
  have hepsilon : 0 < epsilon := by
    dsimp only [epsilon]
    exact div_pos (mul_pos hcoefficient (bodyVolume_pos Z)) hcardReal
  have hsum : ((twoA A).card : ℝ) ≤ sigma * A.card :=
    hdouble.trans (mul_le_mul_of_nonneg_right hsourceSigma (by positivity))
  have hrawCeil : rawDecayRealConstant s S.rankBound sigma S.loss ≤
      (rawConstant : ℝ) := by
    exact rawDecayRealConstant_le_cast s S.rankBound sigma S.loss
  have hthresholdConstant :
      (2 : ℝ) ^ Q * repairLoss ^ (Q - 1) * threshold / coefficient ≤
        (rawConstant : ℝ) := by
    apply le_trans ?_ hrawCeil
    dsimp only [rawDecayRealConstant, Q, repairLoss, coefficient, threshold]
    have hdecayTerm : 0 ≤
        (2 : ℝ) ^ uniformDecayExponent S.rankBound sigma *
          S.loss ^ uniformDecayExponent S.rankBound sigma *
          uniformRepairLoss s S.rankBound ^
            (uniformDecayExponent S.rankBound sigma - 1) /
          uniformEpsilonCoefficient S.rankBound := by
      exact div_nonneg
        (mul_nonneg
          (mul_nonneg (pow_nonneg (by norm_num) _)
            (pow_nonneg S.loss_pos.le _))
          (pow_nonneg (uniformRepairLoss_pos s S.rankBound).le _))
        (uniformEpsilonCoefficient_pos S.rankBound).le
    linarith
  have hthresholdLt : threshold < epsilon := by
    exact threshold_lt_coefficient_mul_div_of_linear_large
      hcoefficient hcardReal
      (by positivity : 0 < (2 : ℝ) ^ Q * repairLoss ^ (Q - 1))
      hthresholdConstant hlinear
  have hepsilonOne : 1 ≤ epsilon :=
    (one_le_uniformProposition83Threshold S.rankBound sigma).trans
      hthresholdLt.le
  have hepsilonActual :
      proposition83Threshold Z.1 (distortionRank sigma) sigma < epsilon :=
    (proposition83Threshold_lt_uniform hZrank sigma).trans hthresholdLt
  have hpolarNumeric := polar_large_numeric_of_rank_le hZrank
    (bodyVolume_pos Z) hcardReal
  have hpolar : (((16 : ℝ) * Z.1) ^ Z.1) * epsilon * A.card ≤
      (4 : ℝ) ^ Z.1 *
        volume.real (unitBall (normalizedMahlerSeminorm Z)) := by
    dsimp only [epsilon, coefficient] at hpolarNumeric ⊢
    rw [normalizedMahlerUnitBall_volumeReal]
    exact hpolarNumeric
  obtain ⟨Y, hYrank, hYvolume⟩ :=
    S.replace Z hA hcardTwo hZrank hZgood epsilon hepsilon hsum hpolar
      hepsilonActual
  have hexponent : ((Q : ℝ)⁻¹) ≤
      proposition83Exponent Z.1 (distortionRank sigma) := by
    dsimp only [Q, uniformDecayExponent]
    exact inv_uniformDenominator_le_proposition83Exponent hZrank
      (distortionRank_pos S.sigma_one)
  have hinvRpow :
      (epsilon ^ proposition83Exponent Z.1 (distortionRank sigma))⁻¹ ≤
        (epsilon ^ ((Q : ℝ)⁻¹))⁻¹ :=
    inv_rpow_le_inv_rpow_of_exponent_le hepsilonOne hexponent
  have hYuniform : bodyVolume Y ≤
      S.loss * bodyVolume Z * (epsilon ^ ((Q : ℝ)⁻¹))⁻¹ :=
    hYvolume.trans (mul_le_mul_of_nonneg_left hinvRpow
      (mul_nonneg S.loss_pos.le (bodyVolume_pos Z).le))
  have hdecayZ := pow_decay_of_replacement_bound hQ
    (bodyVolume_pos Z) (bodyVolume_pos Y).le hcardReal hcoefficient
    S.loss_pos.le hYuniform
  have hpowZ : bodyVolume Z ^ (Q - 1) ≤
      (repairLoss * bodyVolume x.1) ^ (Q - 1) :=
    pow_le_pow_left₀ (bodyVolume_pos Z).le hZle _
  have hdecayX : (2 * bodyVolume Y) ^ Q ≤
      ((2 ^ Q * S.loss ^ Q / coefficient) *
          repairLoss ^ (Q - 1)) * A.card *
        bodyVolume x.1 ^ (Q - 1) := by
    calc
      (2 * bodyVolume Y) ^ Q ≤
          (2 ^ Q * S.loss ^ Q / coefficient) * A.card *
            bodyVolume Z ^ (Q - 1) := hdecayZ
      _ ≤ (2 ^ Q * S.loss ^ Q / coefficient) * A.card *
            ((repairLoss * bodyVolume x.1) ^ (Q - 1)) := by
        exact mul_le_mul_of_nonneg_left hpowZ
          (mul_nonneg
            (div_nonneg
              (mul_nonneg (pow_nonneg (by norm_num) _)
                (pow_nonneg S.loss_pos.le _)) hcoefficient.le)
            (Nat.cast_nonneg A.card))
      _ = ((2 ^ Q * S.loss ^ Q / coefficient) *
          repairLoss ^ (Q - 1)) * A.card *
            bodyVolume x.1 ^ (Q - 1) := by
        rw [mul_pow]
        ring
  have hdecayConstant :
      (2 ^ Q * S.loss ^ Q / coefficient) * repairLoss ^ (Q - 1) ≤
        (rawConstant : ℝ) := by
    apply le_trans ?_ hrawCeil
    dsimp only [rawDecayRealConstant, Q, repairLoss, coefficient, threshold]
    have hthresholdTerm : 0 ≤
        (2 : ℝ) ^ uniformDecayExponent S.rankBound sigma *
          uniformRepairLoss s S.rankBound ^
            (uniformDecayExponent S.rankBound sigma - 1) *
          uniformProposition83Threshold S.rankBound sigma /
          uniformEpsilonCoefficient S.rankBound := by
      exact div_nonneg
        (mul_nonneg
          (mul_nonneg (pow_nonneg (by norm_num) _)
            (pow_nonneg (uniformRepairLoss_pos s S.rankBound).le _))
          (zero_le_one.trans
            (one_le_uniformProposition83Threshold S.rankBound sigma)))
        (uniformEpsilonCoefficient_pos S.rankBound).le
    ring_nf at hthresholdTerm ⊢
    linarith
  refine ⟨⟨Y, hYrank⟩, ?_⟩
  have hnonneg : 0 ≤ (A.card : ℝ) * bodyVolume x.1 ^ (Q - 1) := by
    exact mul_nonneg (Nat.cast_nonneg A.card)
      (pow_nonneg (bodyVolume_pos x.1).le _)
  calc
    (2 * bodyVolume Y) ^ Q ≤
        ((2 ^ Q * S.loss ^ Q / coefficient) *
          repairLoss ^ (Q - 1)) * A.card *
            bodyVolume x.1 ^ (Q - 1) := hdecayX
    _ ≤ (rawConstant : ℝ) * A.card * bodyVolume x.1 ^ (Q - 1) := by
      nlinarith
    _ = (((rawConstant * A.card : ℕ) : ℝ)) *
        bodyVolume x.1 ^ (Q - 1) := by norm_num [Nat.cast_mul]

/-- The source doubling coefficient, enlarged only to enter the
nondegenerate `sigma ≥ 1` range of Sections 6--8. -/
def sourceDoublingSigma (d : ℕ) (delta : ℝ) : ℝ :=
  max 1 (Real.rpow 2 ((d : ℝ) + 1 - delta))

theorem one_le_sourceDoublingSigma (d : ℕ) (delta : ℝ) :
    1 ≤ sourceDoublingSigma d delta := by
  exact le_max_left _ _

theorem sourceCoefficient_le_sourceDoublingSigma (d : ℕ) (delta : ℝ) :
    Real.rpow 2 ((d : ℝ) + 1 - delta) ≤
      sourceDoublingSigma d delta := by
  exact le_max_right _ _

/-- A sharp geometric replacement family gives the exact source package
consumed by the terminal Bilu--Freiman assembly. -/
def rawBodyDecaySourcePackageOfUniformSharpReplacement
    (s d : ℕ) (delta : ℝ) (hs : 0 < s)
    (S : UniformSharpReplacement s (sourceDoublingSigma d delta)) :
    RawBodyDecaySourcePackage s d delta :=
  rawBodyDecaySourcePackageOfLarge s d delta
    S.rankBound S.rankBound
    (rawDecayConstant s S.rankBound (sourceDoublingSigma d delta) S.loss)
    (uniformDecayExponent S.rankBound (sourceDoublingSigma d delta))
    S.rankBound_pos S.rankBound_pos le_rfl
    (uniformDecayExponent_pos S.sigma_one)
    (fun A _hA _hlarge ↦
      rankBoundedRankOneBodyPresentation S.rankBound S.rankBound_pos A)
    (fun A hA hdouble hlarge x hvolume ↦
      exists_rawBodyDecay_of_uniformSharpReplacement
        s d delta (sourceDoublingSigma d delta) hs
        (sourceCoefficient_le_sourceDoublingSigma d delta) S
        A hA hdouble hlarge x hvolume)

/-- This is the end-to-end conditional endpoint of the analytic source
work.  Supplying the sharp replacement record uniformly proves the public
`BiluFreimanStatement`; no further Section 4 or terminal premise remains. -/
theorem biluFreimanStatement_of_uniformSharpReplacement
    (hsharp : ∀ s d : ℕ, 0 < s → 0 < d →
      ∀ delta : ℝ, 0 < delta →
        Nonempty (UniformSharpReplacement s
          (sourceDoublingSigma d delta))) :
    BiluFreimanStatement := by
  apply biluFreimanStatement_of_rawBodyDecay
  intro s d hs hd delta hdelta
  obtain ⟨S⟩ := hsharp s d hs hd delta hdelta
  exact ⟨rawBodyDecaySourcePackageOfUniformSharpReplacement
    s d delta hs S⟩

end


end Erdos186.CFP.Bilu.Section4SharpDecayAssembly

#print axioms
  Erdos186.CFP.Bilu.Section4SharpDecayAssembly.proposition83Threshold_lt_uniform
#print axioms
  Erdos186.CFP.Bilu.Section4SharpDecayAssembly.exists_rawBodyDecay_of_uniformSharpReplacement
#print axioms
  Erdos186.CFP.Bilu.Section4SharpDecayAssembly.biluFreimanStatement_of_uniformSharpReplacement
