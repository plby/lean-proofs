import Arxiv.Arxiv2411_18291.SampledAbsorberProcessData

/-!
# The four sampled absorber stages, composed conditionally

All stages use their actual greedy trajectory laws. Roots for either
cancellation stage are fixed from the preceding output before that stage
is sampled. Successful outputs give a bounded absorber for every generated
leave, and the joint failure probability is below exp(-n^(1/10)) at n0.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem exists_sampled_absorber_process_paper_threshold
    {X W U : Type*} [Fintype X] [Fintype W] [Fintype U]
    [DecidableEq X] [DecidableEq W] [DecidableEq U] {q r n : ℕ}
    (F₀ : Block X (r + 1)) (hX : Fintype.card X = q + (r + 1))
    (S : ExchangeSystem W q (r + 1)) {A₀ : Finset (Block W q)}
    (hA₀ : IsExchangeFamily S A₀) (hlocal : IsPositiveFrameLocal S A₀)
    (hcross : IsCrossSimple (r + 1) S.positive S.negative)
    (T : ExchangeSystem U q (r + 1)) (N : Block U q) (e₀ : Block U (r + 1))
    (hpair : IsEliminationPair T N e₀) (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hwS : Fintype.card W ≤ (4 * q) ^ (2 * q))
    (hwT : Fintype.card U ≤ (4 * q) ^ (2 * q))
    (hS : S.graph.card ≤ absorberExchangeEdges q (r + 1))
    (hT : T.graph.card ≤ absorberExchangeEdges q (r + 1))
    (B : Hypergraph (Fin n) (r + 1)) (D₁ : Finset (Block (Fin n) q))
    (hB : IsGraphBounded B (2 * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 2))))
    (hDB : cliqueSupport (r + 1) D₁ ⊆ B)
    (hmult : ∀ e : Block (Fin n) (r + 1), (D₁.filter fun Q => e.val ⊆ Q.val).card ≤ 16)
    (d₀ : Block (Fin n) (r + 1)) (Q₀ : Block (Fin n) q) :
    SampledAbsorberProcessSuccess F₀ hX S T N B D₁ d₀ Q₀ := by
  classical
  let C := absorberCoefficientCap q (r + 1)
  let M := absorberGeneratorMultiplicity q (r + 1)
  let A := 2 * splittingFactor S C (absorberNormalizationFactor q (r + 1))
  let x := (n : ℝ) ^ (-(paperAlpha q (r + 1) / 2))
  let Decoder := LocalDecoderOutput B hX (2 * x)
  let D := fun O : Decoder => D₁ ∪ decoderFamilyOfPlacements hX O.embedding
  let B' := fun O : Decoder =>
    B ∪ cliqueSupport (r + 1) (decoderFamilyOfPlacements hX O.embedding)
  let Split := fun O : Decoder => SplittingFamily S (D O) (B' O) C (A * x)
  let First := fun (O : Decoder) (F : Split O) =>
    EliminationFamily T N F.graph F.pairPositive F.pairNegative
      (firstEliminationFactor T C M A * x)
  have hparam (O : Decoder) :=
    LocalDecoderOutput.normalized_augmentation hX hqr B D₁ hB hDB hmult O
  have hA : 1 ≤ A := by
    have hh := one_le_splittingFactor S C
      (by exact_mod_cast absorberNormalizationFactor_pos q (r + 1) :
        (1 : ℝ) ≤ absorberNormalizationFactor q (r + 1))
    dsimp only [A]
    linarith only [hh]
  have hA0 : 0 ≤ A := le_trans zero_le_one hA
  have hAb : A ≤ 2 * absorberSplittingConstant q (r + 1) :=
    mul_le_mul_of_nonneg_left (splittingFactor_le_absorberSplittingConstant S hS) (by norm_num)
  have hconstants := normalized_elimination_constant_bounds T hqr hT hA0 hAb
  have hc₀ := hconstants.1
  have hc₁ := hconstants.2.1
  have hfinal := hconstants.2.2
  have hα := paperAlpha_pos hqr
  have hαupper := (paperAlpha_le_rho hqr).trans (paperRho_le_one_div_36 hqr)
  have hρ : paperAlpha q (r + 1) / 3 ≤ paperAlpha q (r + 1) / 2 := by
    linarith only [hα]
  have hρhalf : paperAlpha q (r + 1) / 2 ≤ 1 / 2 := by linarith only [hαupper]
  have hTsmall := hT.trans (paper_exchange_graph_bound (Nat.succ_pos r) hqr)
  have hfirst (O : Decoder) (F : Split O) :=
    exists_first_elimination_output_law S hA₀ T N e₀ hpair hqr hn hwT hTsmall
      C M hA hc₀ hρ hρhalf (D O) (B' O) F (hparam O).2.2.2.2.2.1
  let Φ₁ := fun (O : Decoder) (F : Split O) => (hfirst O F).choose
  have hΦ₁ := fun (O : Decoder) (F : Split O) => (hfirst O F).choose_spec
  let L : ∀ (O : Decoder) (F : Split O) (E : First O F), FurtherEliminationPairs F E :=
    fun _ F E => Classical.choice (exists_further_elimination_pairs F hA₀ E hpair)
  have hsecond (O : Decoder) (F : Split O) (E : First O F) :=
    exists_second_elimination_output_law S hA₀ T N e₀ hpair hqr hn hwT hTsmall
      C (2 * C * M + 2) (one_le_firstEliminationFactor T C M hA) hc₁ hρ hρhalf
      (D O) (B' O) (A * x) F E (L O F E)
      (F.clique_multiplicity (hparam O).2.2.2.2.2.1)
  let Φ₂ := fun (O : Decoder) (F : Split O) (E : First O F) => (hsecond O F E).choose
  have hΦ₂ := fun (O : Decoder) (F : Split O) (E : First O F) => (hsecond O F E).choose_spec
  unfold SampledAbsorberProcessSuccess
  dsimp only
  refine ⟨Φ₁, L, Φ₂, ?_, ?_⟩
  · apply fourStageOutput_absorber_failure_lt hqr hn
    · exact (localDecoderOutputLaw_half_alpha_failure_lt F₀ hX hqr hn B d₀ hB).le
    · intro O
      exact (splittingFamilyOutputLaw_half_alpha_failure_lt S hqr hn hwS hS
        (D O) (B' O) (hparam O).2.2.1 (hparam O).2.2.2.1
        (hparam O).2.2.2.2.1 (hparam O).2.2.2.2.2.1 Q₀).le
    · intro O F
      exact (hΦ₁ O F).le
    · intro O F E
      exact (hΦ₂ O F E).le
  · intro O F E G
    refine ⟨⟨_, finalNegative_decomposition F E (L O F E) G hpair⟩,
      Disjoint.mono_right (hparam O).2.1
        (finalNegative_avoids_original F E (L O F E) G hpair), ?_, ?_⟩
    · apply (finalNegative_bounded F E (L O F E) G hpair).mono
      exact (mul_le_mul_of_nonneg_right hfinal (Real.rpow_nonneg (Nat.cast_nonneg n) _)).trans
        (absorber_final_density_paper_threshold (Nat.succ_pos r) hqr hn)
    · intro J hJB hgen
      obtain ⟨φ, hb, hs, hc⟩ := (hparam O).2.2.2.2.2.2 J hJB hgen
      exact two_stage_absorbs_bounded_representations F hA₀ hlocal hcross E (L O F E) G
        hpair hqr.le J (hJB.trans (hparam O).2.1) φ hc hs hb

end Arxiv2411_18291
