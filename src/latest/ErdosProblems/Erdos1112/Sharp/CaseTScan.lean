/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Copyright 2026 Johan Land.
Licensed under the Apache License, Version 2.0; see LICENSE and NOTICE.
Modified for this repository and Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 1112.
Informal proof: Johan Land, using Claude Fable 5 and Claude Opus 4.8.
Formal proof: Johan Land, using Claude Fable 5 and Claude Opus 4.8.
GPT-5.5 and Gemini 3.1 supplied advice and adversarial review.
Source: https://www.erdosproblems.com/1112#post-7375
https://github.com/beetree/math_erdos_1112/tree/63ed94d3e802782aeb521095c17d6109a2dc57b5
Original Lean version: 4.27.0.
Original Mathlib commit: a3a10db0e9d66acbebf76c5e6a135066525ac900.
-/
/-
Case T scan dispatch (T-tail, part (i)): the 50 per-line scans
assembled into one statement over the line parameters. GENERATED FILE.
-/
import ErdosProblems.Erdos1112.Sharp.CaseTScanE1
import ErdosProblems.Erdos1112.Sharp.CaseTScanE2
import ErdosProblems.Erdos1112.Sharp.CaseTScanE3
import ErdosProblems.Erdos1112.Sharp.CaseTScanE4
import ErdosProblems.Erdos1112.Sharp.CaseTScanE5
import ErdosProblems.Erdos1112.Sharp.CaseTScanE6
import ErdosProblems.Erdos1112.Sharp.CaseTScanE7
import ErdosProblems.Erdos1112.Sharp.CaseTScanE8
import ErdosProblems.Erdos1112.Sharp.CaseTScanE9
import ErdosProblems.Erdos1112.Sharp.CaseTScanE10

namespace Erdos1112
namespace Proof

set_option maxHeartbeats 4000000 in
-- Allow extra elaboration work for the arithmetic and combinatorial case splits.
/-- **T-tail, part (i)**, decided: on every T-line (`1 ≤ e, h`, `e+h ≤ 11`,
`e ≠ h`) and every `a ≤ 3000`, side conditions imply budget-or-table. -/
theorem T_scan_all {e h a : ℕ} (he : 1 ≤ e) (hh : 1 ≤ h)
    (hμ : e + h ≤ 11) (hne : e ≠ h) (ha : a ≤ 3000) :
    TlineGo e h a = true := by
  have he10 : e ≤ 10 := by omega
  have hh10 : h ≤ 10 := by omega
  interval_cases e <;> interval_cases h <;>
    first
      | exact absurd rfl hne
      | exact T_scan_1_2 a ha
      | exact T_scan_1_3 a ha
      | exact T_scan_1_4 a ha
      | exact T_scan_1_5 a ha
      | exact T_scan_1_6 a ha
      | exact T_scan_1_7 a ha
      | exact T_scan_1_8 a ha
      | exact T_scan_1_9 a ha
      | exact T_scan_1_10 a ha
      | exact T_scan_2_1 a ha
      | exact T_scan_2_3 a ha
      | exact T_scan_2_4 a ha
      | exact T_scan_2_5 a ha
      | exact T_scan_2_6 a ha
      | exact T_scan_2_7 a ha
      | exact T_scan_2_8 a ha
      | exact T_scan_2_9 a ha
      | exact T_scan_3_1 a ha
      | exact T_scan_3_2 a ha
      | exact T_scan_3_4 a ha
      | exact T_scan_3_5 a ha
      | exact T_scan_3_6 a ha
      | exact T_scan_3_7 a ha
      | exact T_scan_3_8 a ha
      | exact T_scan_4_1 a ha
      | exact T_scan_4_2 a ha
      | exact T_scan_4_3 a ha
      | exact T_scan_4_5 a ha
      | exact T_scan_4_6 a ha
      | exact T_scan_4_7 a ha
      | exact T_scan_5_1 a ha
      | exact T_scan_5_2 a ha
      | exact T_scan_5_3 a ha
      | exact T_scan_5_4 a ha
      | exact T_scan_5_6 a ha
      | exact T_scan_6_1 a ha
      | exact T_scan_6_2 a ha
      | exact T_scan_6_3 a ha
      | exact T_scan_6_4 a ha
      | exact T_scan_6_5 a ha
      | exact T_scan_7_1 a ha
      | exact T_scan_7_2 a ha
      | exact T_scan_7_3 a ha
      | exact T_scan_7_4 a ha
      | exact T_scan_8_1 a ha
      | exact T_scan_8_2 a ha
      | exact T_scan_8_3 a ha
      | exact T_scan_9_1 a ha
      | exact T_scan_9_2 a ha
      | exact T_scan_10_1 a ha
      | exact absurd hμ (by decide)

end Proof
end Erdos1112
