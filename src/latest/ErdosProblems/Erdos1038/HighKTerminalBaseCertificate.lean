import ErdosProblems.Erdos1038.HighKTerminalScalarSimpleCertificate
import ErdosProblems.Erdos1038.HighKTerminalScalarRefinedCertificate
import ErdosProblems.Erdos1038.HighKTerminalRatioBound
import ErdosProblems.Erdos1038.HighKPlatformNumericalCoverReduction

/-!
# Unconditional exact terminal base certificate
-/

set_option warningAsError false
set_option maxHeartbeats 4000000

namespace Erdos1038

noncomputable section

open OneCutTailCertificate
open HighKTerminalFormula
open HighKTerminalFormula.CertificateData

/-- The exact tail and bridge charts prove the remaining terminal scalar
leaf in the high-ratio platform reduction. -/
theorem highKTerminalBaseCertificate : HighKTerminalBaseCertificate := by
  intro q hq hqs hk
  have hqCap : q < (terminalScalarQCapRat : ℝ) :=
    q_lt_terminalScalarQCap_of_ratio_gt hq hqs hk
  by_cases htail : q ≤ (tailQ : ℝ)
  · exact terminalCircleRectangleBase_pos_of_denominator_lt_one hq hqs
      (denominator_lt_one_of_tailCheck tail_certified hq htail)
  by_cases hsimple : q < ((26631 / 10 ^ 6 : Rat) : ℝ)
  · have hlo : (tailQ : ℝ) ≤ q := le_of_not_ge htail
    obtain ⟨B, hBmem, hBq⟩ := QCover.sound simple_cover hlo hsimple
    have hcert : SimpleCertified B :=
      AllSimpleCertified.of_mem simple_certified hBmem
    exact terminalCircleRectangleBase_pos_of_denominator_lt_one hq hqs
      (denominator_lt_one_of_simpleCertified hcert hBq)
  · have hlo : (((26631 / 10 ^ 6 : Rat) : ℝ)) ≤ q :=
      le_of_not_gt hsimple
    have hcapCast : (terminalScalarQCapRat : ℝ) =
        (((41542 / 10 ^ 6 : Rat) : ℝ)) := by
      norm_num [terminalScalarQCapRat]
    have hhi : q < (((41542 / 10 ^ 6 : Rat) : ℝ)) := by
      rwa [← hcapCast]
    obtain ⟨B, hBmem, hBq⟩ := QCover.sound refined_cover hlo hhi
    obtain ⟨d, hdmem, hroot⟩ := List.mem_map.mp hBmem
    have hcert : RefinedCertified d :=
      AllRefinedCertified.of_mem refined_certified hdmem
    subst B
    exact base_pos_of_refinedCertified hcert hBq

end

end Erdos1038
