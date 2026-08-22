/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AsymmetricCoarseCompletionCode
import ErdosProblems.Erdos1165.AsymmetricActualFarPairData

/-!
# Eventual scale bounds for the coarse asymmetric completion

Every far-pair separation level lies at least one level below the selected
profile scale.  This discharges the extractor's `k + 1 ≤ scale` premise
uniformly at the final Proposition 1.3 scales.
-/

open Filter

namespace Erdos1165.AsymmetricCoarseCompletionScale

open AppendixPair AppendixPairMoment GaussianGeometricCutoff
open Proposition13Scales ThickPoint

noncomputable section

/-- The logarithmic padding is eventually nonzero, so the far cutoff is
strictly below the ambient profile scale. -/
theorem eventually_decorrelationCutoff_succ_le_scaleIndex
    {delta : ℝ} :
    ∀ᶠ N : ℕ in atTop,
      decorrelationCutoff (scaleIndex delta N) + 1 ≤ scaleIndex delta N := by
  have hscaleNat : Tendsto (scaleIndex delta) atTop atTop :=
    tendsto_natCast_atTop_iff.mp (tendsto_scaleIndex_atTop delta)
  have hpadding := hscaleNat.eventually
    eventually_geometricCutoff_le_decorrelationPadding
  have hscale1 := hscaleNat.eventually (eventually_ge_atTop 1)
  filter_upwards [hpadding, hscale1] with N hpadding hscale1
  have hpaddingPos : 1 ≤ decorrelationPadding (scaleIndex delta N) :=
    (show 1 ≤ 32 by omega).trans
      (geometricCutoff_ge_thirty_two.trans hpadding)
  unfold decorrelationCutoff
  omega

/-- Uniform hypotheses used by the source coarse-code constructor for every
far pair at an eventual selected scale. -/
theorem eventually_coarseSeparationLevel_bounds
    {delta : ℝ} :
    ∀ᶠ N : ℕ in atTop, 2 ≤ scaleIndex delta N ∧
      ∀ x y : Point,
        separationLevel (scaleIndex delta N) x y ≤
            decorrelationCutoff (scaleIndex delta N) →
          separationLevel (scaleIndex delta N) x y + 1 ≤
              scaleIndex delta N ∧
            separationLevel (scaleIndex delta N) x y ≤
              scaleIndex delta N := by
  have hscaleNat : Tendsto (scaleIndex delta) atTop atTop :=
    tendsto_natCast_atTop_iff.mp (tendsto_scaleIndex_atTop delta)
  have hscale2 := hscaleNat.eventually (eventually_ge_atTop 2)
  filter_upwards
      [hscale2, eventually_decorrelationCutoff_succ_le_scaleIndex]
      with N hscale hcutoff
  refine ⟨hscale, ?_⟩
  intro x y hlevel
  constructor
  · exact (Nat.add_le_add_right hlevel 1).trans hcutoff
  · omega

/-- If a separation level is in the far range and the padding is nonzero,
the level immediately below its padded prefix is a valid deeper coarse
split. -/
theorem paddedPredecessorSplit_bounds
    {q l : ℕ} (hl : l ≤ decorrelationCutoff q)
    (hpadding : 1 ≤ decorrelationPadding q)
    (hpadding_le : decorrelationPadding q ≤ q) :
    let k := pairPrefixScale q l - 1
    l ≤ k ∧ k + 1 = pairPrefixScale q l ∧
      k + 1 ≤ q ∧ k ≤ q := by
  have hadd : l + decorrelationPadding q ≤ q := by
    unfold decorrelationCutoff at hl
    exact Nat.add_le_of_le_sub hpadding_le hl
  have hpref : pairPrefixScale q l = l + decorrelationPadding q :=
    pairPrefixScale_eq_of_add_le hadd
  dsimp only
  rw [hpref]
  omega

/-- At the selected final scales the preceding padded-split bounds hold
uniformly for every far separation level. -/
theorem eventually_paddedPredecessorSplit_bounds
    {delta : ℝ} :
    ∀ᶠ N : ℕ in atTop,
      ∀ l ≤ decorrelationCutoff (scaleIndex delta N),
        let k := pairPrefixScale (scaleIndex delta N) l - 1
        l ≤ k ∧ k + 1 = pairPrefixScale (scaleIndex delta N) l ∧
          k + 1 ≤ scaleIndex delta N ∧ k ≤ scaleIndex delta N := by
  have hscaleNat : Tendsto (scaleIndex delta) atTop atTop :=
    tendsto_natCast_atTop_iff.mp (tendsto_scaleIndex_atTop delta)
  have hpadding := hscaleNat.eventually
    eventually_geometricCutoff_le_decorrelationPadding
  have hpaddingLt := hscaleNat.eventually eventually_decorrelationPadding_lt
  filter_upwards [hpadding, hpaddingLt] with N hpadding hpaddingLt
  intro l hl
  apply paddedPredecessorSplit_bounds hl
  exact (show 1 ≤ 32 by omega).trans
    (geometricCutoff_ge_thirty_two.trans hpadding)
  exact hpaddingLt.le

end

end Erdos1165.AsymmetricCoarseCompletionScale
