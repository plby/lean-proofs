import ErdosProblems.Erdos1058.Erdos1058PrimeGapData360
import ErdosProblems.Erdos1058.Erdos1058PrimeGapData361
import ErdosProblems.Erdos1058.Erdos1058PrimeGapData362

namespace Erdos1058

namespace PrimeGap210Certificate

def primeGapBlock18 : List ℕ :=
  primeGapDataGroup360 ++ primeGapDataGroup361 ++ primeGapDataGroup362

private lemma primeGapDataGroup360_segment :
    CertifiedSegment primeGapDataGroup360 35707127 35805727 :=
  ⟨primeGapDataGroup360_primes, primeGapDataGroup360_chain,
    primeGapDataGroup360_head, primeGapDataGroup360_last⟩

private lemma primeGapDataGroup361_segment :
    CertifiedSegment primeGapDataGroup361 35805919 35904383 :=
  ⟨primeGapDataGroup361_primes, primeGapDataGroup361_chain,
    primeGapDataGroup361_head, primeGapDataGroup361_last⟩

private lemma primeGapDataGroup362_segment :
    CertifiedSegment primeGapDataGroup362 35904553 36000127 :=
  ⟨primeGapDataGroup362_primes, primeGapDataGroup362_chain,
    primeGapDataGroup362_head, primeGapDataGroup362_last⟩

lemma primeGapBlock18_segment :
    CertifiedSegment primeGapBlock18 35707127 36000127 := by
  unfold primeGapBlock18
  apply primeGapDataGroup360_segment.append
  · apply primeGapDataGroup361_segment.append
    · exact primeGapDataGroup362_segment
    · norm_num [GapStep]
  · norm_num [GapStep]

end PrimeGap210Certificate

end Erdos1058
