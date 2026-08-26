/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Each central-bin root count agrees with its capped window statistic outside a fourth-power error.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.FineGridCoarseErrors
import ErdosProblems.Erdos521.FineGridWindowError
import ErdosProblems.Erdos521.FineGridCapping
import ErdosProblems.Erdos521.DisagreementProbability

namespace Erdos521

open MeasureTheory Filter

theorem eventually_bin_capped_disagreement :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ j : ℕ in atTop, ∀ k ∈ mainBinSet j,
      sequenceLaw.real {ε | intervalRootCount ε (2 ^ j) (dyadicPoint k) (dyadicPoint (k + 1)) ≠
        min (windowGridSignChanges ε (dyadicCoefficientWindow (2 ^ j) k (windowWidthScale j))
          (dyadicFineGrid j k) (fineGridLength j)) (windowCapScale j)} ≤ C * (j : ℝ) ^ (-4 : ℝ) := by
  obtain ⟨B, hB, hcap⟩ := eventually_fineGrid_capping_probability
  let C := (3 * fineGridSmallBallConstant + 97) + (2 * fineGridSmallBallConstant + 16) + B
  have hC : 0 < C := by dsimp [C]; have := fineGridSmallBallConstant_pos; positivity
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_fineGrid_root_error_four, eventually_fineGrid_window_disagreement, hcap]
    with j hr hw hc
  intro k hk
  let R := fun ε ↦ intervalRootCount ε (2 ^ j) (dyadicPoint k) (dyadicPoint (k + 1))
  let G := fun ε ↦ gridSignChanges ε (2 ^ j) (dyadicFineGrid j k) (fineGridLength j)
  let W := fun ε ↦ windowGridSignChanges ε (dyadicCoefficientWindow (2 ^ j) k (windowWidthScale j))
    (dyadicFineGrid j k) (fineGridLength j)
  have h₁ := measureReal_disagreement_triangle sequenceLaw R G (fun ε ↦ min (W ε) (windowCapScale j))
  have h₂ := measureReal_disagreement_triangle sequenceLaw G W (fun ε ↦ min (W ε) (windowCapScale j))
  have h₃ := measureReal_capping_disagreement sequenceLaw W (windowCapScale j)
  have hrk := hr k hk
  have hwk := hw k hk
  have hck := hc k hk
  change sequenceLaw.real {ε | R ε ≠ min (W ε) (windowCapScale j)} ≤ _
  dsimp only [R, G, W] at h₁ h₂ h₃ ⊢
  dsimp only [C]
  linarith

end Erdos521
