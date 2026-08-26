import ErdosProblems.Erdos1038.CircleLogLayerCake

/-!
# Compression of terminal shells for the logarithmic circle deficit

The even extension of an increasing density restricted to an angular
interval has terminal-shell superlevel sets.  Each shell is the union of two
arcs of equal radius.  Compression to a centered arc leaves the same-sign
center separation unchanged and decreases the opposite-sign separation.
The two-arc layer-cake theorem therefore says that the logarithmic deficit
cross-energy cannot decrease.
-/

set_option warningAsError false

open Set

namespace Erdos1038

noncomputable section

/-- Radius of either component of the terminal shell
`[-upper,-lower] ∪ [lower,upper]`. -/
def terminalShellComponentRadius (lower upper : ℝ) : ℝ :=
  (upper - lower) / 2

/-- Circular separation of opposite components of two terminal shells with
common outer endpoint `upper`. -/
def terminalShellOppositeSeparation (lower₁ upper lower₂ : ℝ) : ℝ :=
  min (upper + (lower₁ + lower₂) / 2)
    (2 * Real.pi - (upper + (lower₁ + lower₂) / 2))

/-- Opposite-component separation after both terminal shells are compressed
to centered arcs. -/
def centeredCompressionOppositeSeparation
    (lower₁ upper lower₂ : ℝ) : ℝ :=
  upper - (lower₁ + lower₂) / 2

lemma terminalShellComponentRadius_mem_Icc
    {lower upper : ℝ} (hlower : 0 ≤ lower)
    (hlowerUpper : lower ≤ upper) (hupper : upper ≤ Real.pi) :
    terminalShellComponentRadius lower upper ∈ Icc 0 Real.pi := by
  unfold terminalShellComponentRadius
  constructor <;> linarith [Real.pi_pos]

lemma centeredCompressionOppositeSeparation_mem_Icc
    {lower₁ upper lower₂ : ℝ}
    (hlower₁ : 0 ≤ lower₁) (hlower₂ : 0 ≤ lower₂)
    (hlower₁Upper : lower₁ ≤ upper) (hlower₂Upper : lower₂ ≤ upper)
    (hupper : upper ≤ Real.pi) :
    centeredCompressionOppositeSeparation lower₁ upper lower₂ ∈
      Icc 0 Real.pi := by
  unfold centeredCompressionOppositeSeparation
  constructor <;> linarith

lemma terminalShellOppositeSeparation_mem_Icc
    {lower₁ upper lower₂ : ℝ}
    (hlower₁ : 0 ≤ lower₁) (hlower₂ : 0 ≤ lower₂)
    (hlower₁Upper : lower₁ ≤ upper) (hlower₂Upper : lower₂ ≤ upper)
    (hupper : upper ≤ Real.pi) :
    terminalShellOppositeSeparation lower₁ upper lower₂ ∈
      Icc 0 Real.pi := by
  let x := upper + (lower₁ + lower₂) / 2
  have hx0 : 0 ≤ x := by dsimp only [x]; linarith
  have hx2pi : x ≤ 2 * Real.pi := by
    dsimp only [x]
    linarith
  have hminpi : min x (2 * Real.pi - x) ≤ Real.pi := by
    rcases le_total x Real.pi with hx | hx
    · exact (min_le_left _ _).trans hx
    · exact (min_le_right _ _).trans (by linarith)
  unfold terminalShellOppositeSeparation
  change min x (2 * Real.pi - x) ∈ Icc 0 Real.pi
  exact ⟨le_min hx0 (by linarith), hminpi⟩

theorem circleLogTerminalShell_oppositeEnergy_le_compressed
    {lower₁ upper lower₂ : ℝ}
    (hlower₁ : 0 ≤ lower₁) (hlower₂ : 0 ≤ lower₂)
    (hlower₁Upper : lower₁ ≤ upper) (hlower₂Upper : lower₂ ≤ upper)
    (hupper : upper ≤ Real.pi) :
    circleLogTwoArcEnergy
        (terminalShellComponentRadius lower₁ upper)
        (terminalShellComponentRadius lower₂ upper)
        (terminalShellOppositeSeparation lower₁ upper lower₂) ≤
      circleLogTwoArcEnergy
        (terminalShellComponentRadius lower₁ upper)
        (terminalShellComponentRadius lower₂ upper)
        (centeredCompressionOppositeSeparation lower₁ upper lower₂) := by
  have hr := terminalShellComponentRadius_mem_Icc
    hlower₁ hlower₁Upper hupper
  have hs := terminalShellComponentRadius_mem_Icc
    hlower₂ hlower₂Upper hupper
  have hcompressed := centeredCompressionOppositeSeparation_mem_Icc
    hlower₁ hlower₂ hlower₁Upper hlower₂Upper hupper
  have hopposite := terminalShellOppositeSeparation_mem_Icc
    hlower₁ hlower₂ hlower₁Upper hlower₂Upper hupper
  apply circleLogTwoArcEnergy_antitoneOn
    hr.1 hr.2 hs.1 hs.2 hcompressed hopposite
  exact compressedShell_crossDistance_le hlower₁ hlower₂ hupper

/-- Four-component form of terminal-shell compression.  The two same-sign
interactions are unchanged; the two opposite-sign interactions improve by
the preceding theorem. -/
theorem circleLogTerminalShell_crossDeficit_le_compressed
    {lower₁ upper lower₂ same : ℝ}
    (hlower₁ : 0 ≤ lower₁) (hlower₂ : 0 ≤ lower₂)
    (hlower₁Upper : lower₁ ≤ upper) (hlower₂Upper : lower₂ ≤ upper)
    (hupper : upper ≤ Real.pi) :
    2 * circleLogTwoArcEnergy
          (terminalShellComponentRadius lower₁ upper)
          (terminalShellComponentRadius lower₂ upper) same +
        2 * circleLogTwoArcEnergy
          (terminalShellComponentRadius lower₁ upper)
          (terminalShellComponentRadius lower₂ upper)
          (terminalShellOppositeSeparation lower₁ upper lower₂) ≤
      2 * circleLogTwoArcEnergy
          (terminalShellComponentRadius lower₁ upper)
          (terminalShellComponentRadius lower₂ upper) same +
        2 * circleLogTwoArcEnergy
          (terminalShellComponentRadius lower₁ upper)
          (terminalShellComponentRadius lower₂ upper)
          (centeredCompressionOppositeSeparation lower₁ upper lower₂) := by
  gcongr
  exact circleLogTerminalShell_oppositeEnergy_le_compressed
    hlower₁ hlower₂ hlower₁Upper hlower₂Upper hupper

end

end Erdos1038
