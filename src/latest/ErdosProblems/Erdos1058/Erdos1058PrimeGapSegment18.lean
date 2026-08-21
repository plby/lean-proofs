import ErdosProblems.Erdos1058.Erdos1058PrimeGapData360
import ErdosProblems.Erdos1058.Erdos1058PrimeGapData361
import ErdosProblems.Erdos1058.Erdos1058PrimeGapData362

namespace Erdos1058

namespace PrimeGap210Certificate

private lemma primeGapDataGroup360_certified :
    CertifiedSegment primeGapDataGroup360 35707127 35805727 :=
  ⟨primeGapDataGroup360_primes, primeGapDataGroup360_chain,
    primeGapDataGroup360_head, primeGapDataGroup360_last⟩

private lemma primeGapDataGroup361_certified :
    CertifiedSegment primeGapDataGroup361 35805919 35904383 :=
  ⟨primeGapDataGroup361_primes, primeGapDataGroup361_chain,
    primeGapDataGroup361_head, primeGapDataGroup361_last⟩

private lemma primeGapDataGroup362_certified :
    CertifiedSegment primeGapDataGroup362 35904553 36000127 :=
  ⟨primeGapDataGroup362_primes, primeGapDataGroup362_chain,
    primeGapDataGroup362_head, primeGapDataGroup362_last⟩

private def primeGapSegment18Step0 : List ℕ := primeGapDataGroup360

private lemma primeGapSegment18Step0_certified :
    CertifiedSegment primeGapSegment18Step0 35707127 35805727 := by
  unfold primeGapSegment18Step0
  exact primeGapDataGroup360_certified

private def primeGapSegment18Step1 : List ℕ :=
  primeGapSegment18Step0 ++ primeGapDataGroup361

private lemma primeGapSegment18Step1_certified :
    CertifiedSegment primeGapSegment18Step1 35707127 35904383 := by
  unfold primeGapSegment18Step1
  exact primeGapSegment18Step0_certified.append primeGapDataGroup361_certified (by norm_num [GapStep])

private def primeGapSegment18Step2 : List ℕ :=
  primeGapSegment18Step1 ++ primeGapDataGroup362

private lemma primeGapSegment18Step2_certified :
    CertifiedSegment primeGapSegment18Step2 35707127 36000127 := by
  unfold primeGapSegment18Step2
  exact primeGapSegment18Step1_certified.append primeGapDataGroup362_certified (by norm_num [GapStep])

def primeGapSegment18 : List ℕ := primeGapSegment18Step2

lemma primeGapSegment18_certified :
    CertifiedSegment primeGapSegment18 35707127 36000127 := by
  unfold primeGapSegment18
  exact primeGapSegment18Step2_certified

end PrimeGap210Certificate

end Erdos1058
