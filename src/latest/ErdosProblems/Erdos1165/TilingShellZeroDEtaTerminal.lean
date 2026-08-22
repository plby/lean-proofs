/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZThetaSourceBalance

/-!
# The terminal domino of a shell source is in `V₁`

This is the deterministic terminal clause needed when the source `D_η`
classification is enlarged to the replacement `Dtilde_η` classification.
It is not an additional screen: the source terminal has local time `m`, and
neither `V₂(I₁)` nor `V₃` can contain its domino when `low < m`.
-/

namespace Erdos1165.TilingShellZeroDEtaTerminal

open HLOZShellZeroReplacementWindows LazyDecomposition TilingLazyDecomposition
open TilingShellZeroSourcePartition HLOZThetaSourceBalance

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The terminal domino is automatically a `V₁` domino on `D_η`. -/
theorem tilingVOneAt_terminalBase_of_tilingDEtaAt
    {t : DominoTiling} {m k w low : ℕ} {s : WalkPath} {n : ℕ}
    (hlow : low < m) (hD : tilingDEtaAt t m k w low s n) :
    tilingVOneAt t m s n (tilingBase t (s n)) := by
  let b := tilingBase t (s n)
  have hbClass := hD.2.1 b (isTilingBase_tilingBase t (s n))
  have hterminal : localTime s n (s n) = m := hD.2.2
  rcases point_eq_tilingBase_or_partner_base t (s n) with hbase | hpartner
  · have hlocalBase : localTime s n b = m := by
      dsimp only [b]
      rw [← hbase]
      exact hterminal
    rcases hbClass with hVOne | hVTwo | hVThree
    · exact hVOne
    · have hwindow :=
        (mem_shellZeroSourceTotalWindow.mp hVTwo.2).2
      omega
    · rcases hVThree with hlowBase | hpartnerDominant
      · omega
      · omega
  · have hlocalPartner : localTime s n (tilingPartner t b) = m := by
      have hpb : tilingPartner t b = s n := by
        exact hpartner.symm
      simpa only [hpb] using hterminal
    rcases hbClass with hVOne | hVTwo | hVThree
    · exact hVOne
    · have hwindow :=
        (mem_shellZeroSourceTotalWindow.mp hVTwo.2).2
      have hle := hVTwo.1
      rw [hlocalPartner] at hle
      omega
    · rcases hVThree with hlowBase | hpartnerDominant
      · right
        exact ⟨hlocalPartner, lt_of_le_of_lt hlowBase hlow⟩
      · omega

end

end Erdos1165.TilingShellZeroDEtaTerminal
