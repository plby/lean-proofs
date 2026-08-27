/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ReindexedInitialMasterLaw
import ErdosProblems.Erdos207.ReindexedPowerSource

/-! # A simultaneous initial-law certificate for every retained vortex -/

namespace Erdos207

open scoped NNReal

noncomputable section

def HasAbsorberSourcePrefixBounds
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (q : ℕ) (bank : TripleSystemOn V) (W : Vortex V ell) : Prop :=
  (∀ i : Fin ell, ∀ j : ℕ, 4 ≤ j → j ≤ q →
    SourceVortexWellSpread (W.prefix i.succ) j (absorberInducedConfigurationsOn q j bank)
      (((2 : ℝ≥0) ^ (12 * (q + 2) ^ 2) + 1) * exactBankVortexOrderCoefficient q (i.val + 1))
      (2 * (((2 : ℝ≥0) ^ (12 * (q + 2) ^ 2) + 1) * exactBankVortexOrderCoefficient q (i.val + 1)) +
        exactBankVortexCoefficient j (i.val + 1))) ∧
  ∀ j : ℕ, 4 ≤ j → j ≤ q →
    SourceVortexWellSpread (W.prefix 0) j (absorberInducedConfigurationsOn q j bank)
      (2 * exactBankVortexOrderCoefficient q 0)
      (2 * ((subsetsUpToCard bank q).card * (exactBankVortexOrderCoefficient q 0 : ℝ≥0)) +
        exactBankVortexCoefficient j 0)

def HasRetainedInitialLaw
    {q h n ell t rootPower step : ℕ}
    (P : InitialPowerVortexPackage q h n ell t rootPower step) (b B k : ℕ)
    (law : FiniteLaw (GreedyStateOn (Fin n))) : Prop :=
  ∀ length : ℕ, ∀ stage : Fin (length + 1) → Fin (ell + 1),
    ∀ hstage : StrictMono stage, ∀ hzero : stage 0 = 0,
      let W := P.W.reindex stage hstage.monotone hzero
      law.SupportedOn (IsInitialTypicalPatternOutcome q h b B k t P.H P.B W) ∧
        HasAbsorberSourcePrefixBounds q P.B W ∧
        (Admissible n → ∃ masterLaw, IsInitialResidualCompressedMasterLawWithError q h b t
          P.H P.B W (2 * ksssInitialGraphProductConstant q (initialErdosCoefficientBound q))
          (initialPatternGraphError q h ell n t) masterLaw)

theorem InitialPowerVortexPackage.retained_initial_law
    {q h n ell t rootPower step b B k R : ℕ}
    (P : InitialPowerVortexPackage q h n ell t rootPower step)
    (law : FiniteLaw (GreedyStateOn (Fin n)))
    (hlaw : IsInitialTypicalPatternLaw q h b B k t P.H P.B P.W law)
    (hb : 1 ≤ b) (ht : 2 ≤ t) (hh : h ≤ t) (hc : powerAbsorberCoefficient q ≤ t)
    (hlarge : 6 * t ^ initialSupportPower rootPower + 4 ≤ n)
    (hroot : b * h + h ^ 2 + 2 ≤ rootPower)
    (hexp : Real.exp (∑ d ∈ ksssOrders q, initialErdosCoefficientBound q d) ≤ t)
    (hell : 0 < ell) (hbankCoeff : powerBankSubsetCoefficient q ≤ t)
    (hsourceGap : powerBankSubsetExponent q rootPower + max rootPower (step * (ell - 1)) + 1 ≤ R)
    (hscale : t ^ R ≤ n) : HasRetainedInitialLaw P b B k law := by
  intro length stage hstage hzero
  dsimp only
  have hsupport : law.SupportedOn (IsInitialTypicalPatternOutcome q h b B k t P.H P.B
      (P.W.reindex stage hstage.monotone hzero)) := by
    intro S hS
    exact P.initial_pattern_outcome_typical_reindex stage hstage.monotone hzero b B k S
      (hlaw.1 S hS).1 hb (by omega) hh hc hlarge hroot hexp
  refine ⟨hsupport, ⟨?_, ?_⟩, ?_⟩
  · intro i j hj hjq
    exact P.reindexed_positive_prefix_sourceWellSpread stage hstage hzero ht hell hbankCoeff
      hsourceGap hscale i j hj hjq
  · intro j hj _hjq
    exact P.reindexed_zero_prefix_sourceWellSpread stage hstage.monotone hzero hbankCoeff
      (show powerBankSubsetExponent q rootPower ≤ R by omega) hscale j hj
  · intro hadmissible
    refine ⟨_, P.compressed_residual_master_of_initial_typical_support hadmissible law
      (P.W.reindex stage hstage.monotone hzero) hsupport ?_⟩
    simpa only [Fintype.card_fin] using hlaw.2

end

end Erdos207
