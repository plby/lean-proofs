import ErdosProblems.Erdos747.SelectedSurvivalExceptions

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Constant-success thinning diagnostics from relative survival -/

lemma card_mul_div_sub_le_two_mul (m d : ℕ) (p : ℝ)
    (hlarge : 2 * d < m) (hp : 0 ≤ p) :
    ((m : ℝ) * p) / ((m - d : ℕ) : ℝ) ≤ 2 * p := by
  have hdm : d ≤ m := by omega
  have hden : (0 : ℝ) < (m - d : ℕ) := by exact_mod_cast (show 0 < m - d by omega)
  apply (div_le_iff₀ hden).mpr
  rw [Nat.cast_sub hdm]
  have hlargeR : (2 : ℝ) * d ≤ m := by exact_mod_cast hlarge.le
  nlinarith

lemma upperWeightBlockDiagnostic_top_miss_le_selected
    {n k d e : ℕ} {H : Finset (Edge n)} {L delta eta etaGlobal r p : ℝ}
    (hL : 1 + delta ≤ L) (hspread : PresentWeightSpread H delta eta)
    (hglobalBudget : ((2 * d : ℕ) : ℝ) + eta * H.card ≤ etaGlobal * (allEdges n).card)
    (hglobal : ¬ GlobalUpperWeightSpread n H L etaGlobal)
    (hk : k + 1 ≤ H.card) (hp : 0 ≤ p) (hr : 0 < r)
    (hscale : 1 + delta ≤ r * L)
    (hdiagnostic : ∀ T ∈ H.powersetCard (k + 1),
      (e : ℝ) ≤ (3 / 4 : ℝ) * ((k + 1 : ℕ) : ℝ) *
        ((d : ℝ) / (allEdges n \ (H \ T)).card))
    (hrelative : ∀ Z ∈ coarseUpperBadNonedges n H L,
      finsetProbability (H.powersetCard (k + 1))
        (fun T ↦ (completionWeight (H \ T) Z : ℝ) <
          r * (completionWeight H Z : ℝ)) ≤ p) :
    finsetProbability (H.powersetCard (k + 1))
        (fun T ↦ ¬ UpperWeightBlockDiagnostic n d (k + 1) ⟨H, T⟩) ≤
      2 * p + (((k + 1 : ℕ) : ℝ) * eta) / (e + 1 : ℕ) := by
  let X := coarseUpperBadNonedges n H L
  have hlarge : 2 * d < X.card :=
    coarseUpperBadNonedges_card_gt_two_mul_of_not_global_of_spread hL hspread hglobalBudget hglobal
  have hXd : X ⊆ allEdges n \ H := Finset.filter_subset _ _
  have hambient : ∀ T ∈ H.powersetCard (k + 1),
      d ≤ (allEdges n \ (H \ T)).card := by
    intro T hT
    apply (show d ≤ X.card by omega).trans
    apply Finset.card_le_card
    intro Z hZX
    rcases Finset.mem_sdiff.mp (hXd hZX) with ⟨hZall, hZnotH⟩
    exact Finset.mem_sdiff.mpr ⟨hZall, fun h ↦ hZnotH (Finset.mem_sdiff.mp h).1⟩
  have hpoint : ∀ Z ∈ X,
      finsetProbability (H.powersetCard (k + 1))
        (fun T ↦ ¬ (1 + delta) * matchingWeightTarget n H <
          (completionWeight (H \ T) Z : ℝ)) ≤ p := by
    intro Z hZX
    apply upperBad_absolute_failure_probability_le_of_relative
      H L ((1 + delta) * matchingWeightTarget n H) r p hZX hr
    · have htarget : 0 ≤ matchingWeightTarget n H := by unfold matchingWeightTarget; positivity
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hscale htarget
    · exact hrelative Z hZX
  have hExc := presentUpperWeightException_probability_le_markov (e := e) H delta eta hk hspread
  have hmiss := upperWeightBlockDiagnostic_top_miss_probability_le
    hXd (show d < X.card by omega) hambient hdiagnostic hpoint hExc
  exact hmiss.trans (add_le_add (card_mul_div_sub_le_two_mul X.card d p hlarge hp) le_rfl)

lemma lowerWeightBlockDiagnostic_top_miss_le_selected
    {n k d eLow eFail : ℕ} {H : Finset (Edge n)}
    {L delta eta etaGlobal r p : ℝ}
    (hL : L ≤ 1 - delta) (hspread : PresentWeightSpread H delta eta)
    (hglobalBudget : ((2 * d : ℕ) : ℝ) + eta * H.card ≤ etaGlobal * (allEdges n).card)
    (hglobal : ¬ GlobalLowerWeightSpread n H L etaGlobal)
    (hk : k + 1 ≤ H.card) (hp : 0 ≤ p) (hr : 0 ≤ r)
    (hscale : L ≤ r * (1 - delta))
    (hdiagnostic : ∀ T ∈ H.powersetCard (k + 1),
      ((eLow + eFail : ℕ) : ℝ) ≤ (3 / 4 : ℝ) * ((k + 1 : ℕ) : ℝ) *
        ((d : ℝ) / (allEdges n \ (H \ T)).card))
    (hrelative : ∀ Z ∈ H, Z ∉ presentLowerWeightExceptions H delta →
      finsetProbability ((H.erase Z).powersetCard k)
        (fun U ↦ (completionWeight ((H.erase Z) \ U) Z : ℝ) <
          r * (completionWeight (H.erase Z) Z : ℝ)) ≤ p) :
    finsetProbability (H.powersetCard (k + 1))
        (fun T ↦ ¬ LowerWeightBlockDiagnostic n d (k + 1) ⟨H, T⟩) ≤
      (((k + 1 : ℕ) : ℝ) * eta) / (eLow + 1 : ℕ) +
        (((k + 1 : ℕ) : ℝ) * p) / (eFail + 1 : ℕ) := by
  have hlarge := predicateLowerBadNonedges_card_gt_two_mul_of_not_global_of_spread
    hL hspread hglobalBudget hglobal
  have htarget : 0 ≤ matchingWeightTarget n H := by unfold matchingWeightTarget; positivity
  have hscale' : L * matchingWeightTarget n H ≤ r * ((1 - delta) * matchingWeightTarget n H) := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hscale htarget
  have hExc := presentLowerWeightException_probability_le_selected
    (eLow := eLow) (eFail := eFail) H delta eta r (L * matchingWeightTarget n H) p
    hk hr hp hspread hscale' hrelative
  exact lowerWeightBlockDiagnostic_top_of_many_badNonedges
    hlarge hdiagnostic hExc le_rfl

end

end Erdos747
