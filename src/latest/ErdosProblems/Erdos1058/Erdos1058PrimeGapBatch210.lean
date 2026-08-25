import ErdosProblems.Erdos1058.Erdos1058PrimeBatchData0
import ErdosProblems.Erdos1058.Erdos1058PrimeBatchData1
import ErdosProblems.Erdos1058.Erdos1058PrimeBatchData2
import ErdosProblems.Erdos1058.Erdos1058PrimeBatchData3

namespace Erdos1058.PrimeGapBatch210Certificate

open PrimeGap210Certificate

def primeGapCover : List ℕ :=
  primeBatchCover0 ++ primeBatchCover1 ++ primeBatchCover2 ++ primeBatchCover3

lemma primeGapCover_segment : CertifiedSegment primeGapCover 439 36000127 := by
  exact ((primeBatchCover0_segment.append primeBatchCover1_segment
    (by unfold GapStep; decide)).append primeBatchCover2_segment
      (by unfold GapStep; decide)).append primeBatchCover3_segment
        (by unfold GapStep; decide)

theorem prime_gap_le_210_below_36000000 {p q : ℕ}
    (hp433 : 433 < p) (_hp : p.Prime)
    (hqfirst : IsFirstPrimeAfter p q) (hq36 : q < 36000000) :
    q - p ≤ 210 := by
  have hpq : p < q := hqfirst.1
  obtain ⟨r, _, hrprime, hpr, hrbound⟩ :=
    primeGapCover_segment.exists_prime_after (p := p) (by omega) (by omega)
  have hqr : q ≤ r := hqfirst.2.2 r hrprime hpr
  omega

end Erdos1058.PrimeGapBatch210Certificate
