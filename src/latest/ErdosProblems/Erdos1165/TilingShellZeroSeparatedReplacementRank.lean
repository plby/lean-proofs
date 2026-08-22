/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingShellZeroReplacementRankObstruction

/-!
# Testing the one-new-site shell replacement screen

Requiring the partner endpoint to remain below level `m` is sufficient for
one moved `I₁ → I₀` domino to create exactly one new threshold site.  It is
not, however, a consequence of the present coordinate windows: on the
literal one-coordinate obstruction the strengthened replacement window is
empty while the source window is nonempty.
-/

namespace Erdos1165.TilingShellZeroSeparatedReplacementRank

open HLOZShellZeroReplacementWindows LazyDecomposition
open TilingInsertedLocalTime TilingLazyDecomposition
open TilingShellZeroReplacementRankObstruction

/-- Number of threshold endpoints contributed by one ordered domino. -/
def dominoThresholdContribution (m base partner : ℕ) : ℕ :=
  (if m ≤ base then 1 else 0) + (if m ≤ partner then 1 else 0)

/-- The proposed partner-separation screen does force exactly one new
threshold site on an individual moved domino. -/
theorem moved_domino_contributes_exactly_one
    {m w sourceBase sourcePartner replacementBase replacementPartner : ℕ}
    (hsourceDom : sourcePartner ≤ sourceBase)
    (hsource : sourceBase ∈ shellZeroSourceTotalWindow m w)
    (hreplacement : replacementBase ∈ shellZeroReplacementTotalWindow m w)
    (hpartner : replacementPartner < m) :
    dominoThresholdContribution m replacementBase replacementPartner =
      dominoThresholdContribution m sourceBase sourcePartner + 1 := by
  simp only [mem_shellZeroSourceTotalWindow] at hsource
  simp only [mem_shellZeroReplacementTotalWindow] at hreplacement
  unfold dominoThresholdContribution
  simp only [if_neg (Nat.not_le.mpr hsource.2),
    if_neg (Nat.not_le.mpr (lt_of_le_of_lt hsourceDom hsource.2)),
    if_pos (le_trans (Nat.le_add_right m 1) hreplacement.1),
    if_neg (Nat.not_le.mpr hpartner)]

/-- The current pure source coordinate window is nonempty on the checked
one-domino obstruction. -/
theorem obstruction_source_window_nonempty
    {m w : ℕ} (hm : 2 ≤ m) (hw : 2 ≤ w) :
    ∃ n : ℕ,
      listLocalTime (obstructionPath n) (0, 0) ∈
        shellZeroSourceTotalWindow m w := by
  refine ⟨m - 2, ?_⟩
  rw [obstruction_base_localTime]
  simp only [mem_shellZeroSourceTotalWindow]
  omega

/-- On the same literal fibre, every value in the present replacement
window raises the partner to level `m`.  Hence adding `partner < m` deletes
the entire replacement coordinate window. -/
theorem obstruction_separated_replacement_window_empty
    {m w n : ℕ}
    (hreplacement : listLocalTime (obstructionPath n) (0, 0) ∈
      shellZeroReplacementTotalWindow m w) :
    ¬listLocalTime (obstructionPath n) (1, 0) < m := by
  rw [obstruction_base_localTime] at hreplacement
  rw [obstruction_partner_localTime]
  simp only [mem_shellZeroReplacementTotalWindow] at hreplacement
  omega

/-- The unstrengthened `V₂(I₀)` local shape really permits a second new
threshold endpoint. -/
theorem current_replacement_window_allows_two_threshold_sites
    {m w : ℕ} (hm : 2 ≤ m) (hw : 2 ≤ w) :
    listLocalTime (obstructionPath (m - 2)) (1, 0) ≤
        listLocalTime (obstructionPath (m - 2)) (0, 0) ∧
      listLocalTime (obstructionPath (m - 2)) (0, 0) ∈
        shellZeroSourceTotalWindow m w ∧
      listLocalTime (obstructionPath m) (1, 0) ≤
        listLocalTime (obstructionPath m) (0, 0) ∧
      listLocalTime (obstructionPath m) (0, 0) ∈
        shellZeroReplacementTotalWindow m w ∧
      ¬listLocalTime (obstructionPath m) (1, 0) < m := by
  rw [obstruction_base_localTime, obstruction_partner_localTime,
    obstruction_base_localTime, obstruction_partner_localTime]
  simp only [mem_shellZeroSourceTotalWindow,
    mem_shellZeroReplacementTotalWindow]
  omega

end Erdos1165.TilingShellZeroSeparatedReplacementRank
