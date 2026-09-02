import ErdosProblems.Erdos327.Analytic.MixedEdges
import ErdosProblems.Erdos327.Analytic.Regularity
import ErdosProblems.Erdos327.AnalyticAssembly

/-!
# Reduction to the four canonical quantitative estimates

This theorem instantiates the abstract analytic assembly interface with
the actual rough regular source and regular odd host.  It leaves exactly
four numerical estimates: the two regularity tails, the centered source
conflict loss, and the mixed-edge count.
-/

namespace Erdos327

open Finset Real

/-- Exact finite rough density attached to the cutoff `L`. -/
noncomputable def roughDensity (L : ℕ) : ℝ :=
  ((Analytic.roughPrimeModulus L).totient : ℝ) /
    Analytic.roughPrimeModulus L

theorem roughDensity_pos {L : ℕ} (hL : 3 ≤ L) :
    0 < roughDensity L := by
  have hlower :=
    Analytic.mertensLowerConstant_div_log_le_roughDensity hL
  have hlog : 0 < log (L : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < L by omega))
  have hc : 0 < Analytic.mertensLowerConstant / log L :=
    div_pos Analytic.mertensLowerConstant_pos hlog
  unfold roughDensity
  exact hc.trans_le hlower

/-- The four analytic estimates, with their exact constants, imply the
full Erdős 327 conclusion.  The construction uses
`ρ = roughDensity L / 2`. -/
theorem erdos327Conclusion_of_canonical_estimates
    {L : ℕ} {Ab Kb Ao Ko : ℝ} (hL : 3 ≤ L)
    {N₀ : ℕ}
    (hmodulus :
      ∀ N ≥ N₀, 4 * Analytic.roughPrimeModulus L ≤ N)
    (hest :
      ∀ N ≥ N₀,
        ((Analytic.irregularRoughSource L Ab Kb N).card : ℝ) ≤
            (N : ℝ) * roughDensity L / 8 ∧
        ((rankBad (upto N)
          (Analytic.regularSource L Ab Kb N)
          ArithmeticFunction.cardFactors).card : ℝ) ≤
            (N : ℝ) * roughDensity L / 16 ∧
        ((Analytic.irregularOddHost L Ao Ko N).card : ℝ) ≤
            (N : ℝ) * roughDensity L / 64 ∧
        ((mixedEdges
          (Analytic.regularOddHost L Ao Ko N)
          (rankFilteredSource (upto N)
            (Analytic.regularSource L Ab Kb N)
            ArithmeticFunction.cardFactors)).card : ℝ) ≤
              (N : ℝ) * roughDensity L / 64) :
    Erdos327Conclusion := by
  have hρ : 0 < roughDensity L / 2 := by
    positivity [roughDensity_pos hL]
  refine erdos327Conclusion_of_analytic_sets (N₀ := N₀) hρ ?_
  intro N hN
  let S := Analytic.regularSource L Ab Kb N
  let O := Analytic.regularOddHost L Ao Ko N
  have hmod := hmodulus N hN
  have hN2 : 2 ≤ N := by
    have hmodPos := Analytic.roughPrimeModulus_pos L
    omega
  rcases hest N hN with
    ⟨hIrregularSource, hSourceBad, hIrregularHost, hMixedEdges⟩
  have hrough :=
    Analytic.roughSourceInterval_card_lower hmod
  have hsourceCardNat :=
    Analytic.card_regularSource_add_irregular L Ab Kb N
  have hsourceCardReal :
      ((S.card : ℕ) : ℝ) +
          ((Analytic.irregularRoughSource L Ab Kb N).card : ℝ) =
        ((Analytic.roughSourceInterval L N).card : ℝ) := by
    dsimp [S]
    exact_mod_cast hsourceCardNat
  have hrough' :
      (N : ℝ) / 4 * roughDensity L ≤
        ((Analytic.roughSourceInterval L N).card : ℝ) := by
    convert hrough using 1; unfold roughDensity; ring
  have hScard :
      (N : ℝ) * (roughDensity L / 2) / 4 ≤ (S.card : ℝ) := by
    nlinarith
  have hhostCardNat :=
    Analytic.card_regularOddHost_add_irregular L Ao Ko N
  have hhostCardReal :
      ((O.card : ℕ) : ℝ) +
          ((Analytic.irregularOddHost L Ao Ko N).card : ℝ) =
        (N : ℝ) := by
    dsimp [O]
    exact_mod_cast hhostCardNat
  have hOcard :
      (N : ℝ) - (N : ℝ) * (roughDensity L / 2) / 32 ≤
        (O.card : ℝ) := by
    nlinarith
  have hMixedBadNat :=
    card_mixedBad_le_card_mixedEdges O
      (rankFilteredSource (upto N) S
        ArithmeticFunction.cardFactors)
  have hMixedBadReal :
      ((mixedBad O
        (rankFilteredSource (upto N) S
          ArithmeticFunction.cardFactors)).card : ℝ) ≤
        ((mixedEdges O
          (rankFilteredSource (upto N) S
            ArithmeticFunction.cardFactors)).card : ℝ) := by
    exact_mod_cast hMixedBadNat
  refine ⟨S, O,
    Analytic.regularSource_subset_upto L Ab Kb N hN2,
    Analytic.regularOddHost_subset_upto L Ao Ko N,
    ?_, hScard, ?_, hOcard, ?_⟩
  · intro a ha
    exact Analytic.odd_of_mem_regularOddHost ha
  · dsimp [S]
    nlinarith
  · dsimp [S, O] at hMixedEdges hMixedBadReal ⊢
    nlinarith

/-- The source half of the canonical estimates already yields Sawin's
positive-density answer to the second question. -/
theorem erdos327SecondConclusion_of_canonical_estimates
    {L : ℕ} {Ab Kb : ℝ} (hL : 3 ≤ L)
    {N₀ : ℕ}
    (hmodulus :
      ∀ N ≥ N₀, 4 * Analytic.roughPrimeModulus L ≤ N)
    (hest :
      ∀ N ≥ N₀,
        ((Analytic.irregularRoughSource L Ab Kb N).card : ℝ) ≤
            (N : ℝ) * roughDensity L / 8 ∧
        ((rankBad (upto N)
          (Analytic.regularSource L Ab Kb N)
          ArithmeticFunction.cardFactors).card : ℝ) ≤
            (N : ℝ) * roughDensity L / 16) :
    Erdos327SecondConclusion := by
  have hρ : 0 < roughDensity L / 2 := by
    positivity [roughDensity_pos hL]
  refine erdos327SecondConclusion_of_analytic_source (N₀ := N₀) hρ ?_
  intro N hN
  let S := Analytic.regularSource L Ab Kb N
  have hmod := hmodulus N hN
  have hN2 : 2 ≤ N := by
    have hmodPos := Analytic.roughPrimeModulus_pos L
    omega
  rcases hest N hN with ⟨hIrregularSource, hSourceBad⟩
  have hrough :=
    Analytic.roughSourceInterval_card_lower hmod
  have hsourceCardNat :=
    Analytic.card_regularSource_add_irregular L Ab Kb N
  have hsourceCardReal :
      ((S.card : ℕ) : ℝ) +
          ((Analytic.irregularRoughSource L Ab Kb N).card : ℝ) =
        ((Analytic.roughSourceInterval L N).card : ℝ) := by
    dsimp [S]
    exact_mod_cast hsourceCardNat
  have hrough' :
      (N : ℝ) / 4 * roughDensity L ≤
        ((Analytic.roughSourceInterval L N).card : ℝ) := by
    convert hrough using 1; unfold roughDensity; ring
  have hScard :
      (N : ℝ) * (roughDensity L / 2) / 4 ≤ (S.card : ℝ) := by
    nlinarith
  refine ⟨S,
    Analytic.regularSource_subset_upto L Ab Kb N hN2,
    hScard, ?_⟩
  dsimp [S]
  convert hSourceBad using 1; ring

/-- All four canonical estimates prove both asymptotic conclusions of the
problem. -/
theorem erdos327FullConclusion_of_canonical_estimates
    {L : ℕ} {Ab Kb Ao Ko : ℝ} (hL : 3 ≤ L)
    {N₀ : ℕ}
    (hmodulus :
      ∀ N ≥ N₀, 4 * Analytic.roughPrimeModulus L ≤ N)
    (hest :
      ∀ N ≥ N₀,
        ((Analytic.irregularRoughSource L Ab Kb N).card : ℝ) ≤
            (N : ℝ) * roughDensity L / 8 ∧
        ((rankBad (upto N)
          (Analytic.regularSource L Ab Kb N)
          ArithmeticFunction.cardFactors).card : ℝ) ≤
            (N : ℝ) * roughDensity L / 16 ∧
        ((Analytic.irregularOddHost L Ao Ko N).card : ℝ) ≤
            (N : ℝ) * roughDensity L / 64 ∧
        ((mixedEdges
          (Analytic.regularOddHost L Ao Ko N)
          (rankFilteredSource (upto N)
            (Analytic.regularSource L Ab Kb N)
            ArithmeticFunction.cardFactors)).card : ℝ) ≤
              (N : ℝ) * roughDensity L / 64) :
    Erdos327FullConclusion := by
  refine ⟨erdos327Conclusion_of_canonical_estimates
    hL hmodulus hest, ?_⟩
  apply erdos327SecondConclusion_of_canonical_estimates
    (Ab := Ab) (Kb := Kb) hL hmodulus
  intro N hN
  rcases hest N hN with
    ⟨hIrregularSource, hSourceBad, _hIrregularHost, _hMixed⟩
  exact ⟨hIrregularSource, hSourceBad⟩

end Erdos327
