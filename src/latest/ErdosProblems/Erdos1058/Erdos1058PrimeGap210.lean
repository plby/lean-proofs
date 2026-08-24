import ErdosProblems.Erdos1058.Erdos1058Core
import ErdosProblems.Erdos1058.Erdos1058PrimeGapCertified000
import ErdosProblems.Erdos1058.Erdos1058PrimeGapCertified001
import ErdosProblems.Erdos1058.Erdos1058PrimeGapCertifiedBatch00
import ErdosProblems.Erdos1058.Erdos1058PrimeGapCertifiedBatch01
import ErdosProblems.Erdos1058.Erdos1058PrimeGapCertifiedBatch02
import ErdosProblems.Erdos1058.Erdos1058PrimeGapCertifiedBatch03
import ErdosProblems.Erdos1058.Erdos1058PrimeGapCertifiedBatch04
import ErdosProblems.Erdos1058.Erdos1058PrimeGapCertifiedBatch05
import ErdosProblems.Erdos1058.Erdos1058PrimeGapCertifiedBatch06
import ErdosProblems.Erdos1058.Erdos1058PrimeGapCertifiedBatch07
import ErdosProblems.Erdos1058.Erdos1058PrimeGapCertifiedBatch08
import ErdosProblems.Erdos1058.Erdos1058PrimeGapCertifiedBatch09
import ErdosProblems.Erdos1058.Erdos1058PrimeGapCertifiedBatch10
import ErdosProblems.Erdos1058.Erdos1058PrimeGapCertifiedBatch11
import ErdosProblems.Erdos1058.Erdos1058PrimeGapCertifiedBatch12
import ErdosProblems.Erdos1058.Erdos1058PrimeGapCertifiedBatch13
import ErdosProblems.Erdos1058.Erdos1058PrimeGapCertifiedBatch14
import ErdosProblems.Erdos1058.Erdos1058PrimeGapCertifiedBatch15
import ErdosProblems.Erdos1058.Erdos1058PrimeGapCertifiedBatch16
import ErdosProblems.Erdos1058.Erdos1058PrimeGapCertifiedBatch17
import ErdosProblems.Erdos1058.Erdos1058PrimeGapCertifiedBatch18
import ErdosProblems.Erdos1058.Erdos1058PrimeGapCertifiedBatch19
import ErdosProblems.Erdos1058.Erdos1058PrimeGapCertifiedBatch20
import ErdosProblems.Erdos1058.Erdos1058PrimeGapCertifiedBatch21
import ErdosProblems.Erdos1058.Erdos1058PrimeGapCertifiedBatch22
import ErdosProblems.Erdos1058.Erdos1058PrimeGapCertifiedBatch23
import ErdosProblems.Erdos1058.Erdos1058PrimeGapCertifiedBatch24
import ErdosProblems.Erdos1058.Erdos1058PrimeGapCertifiedBatch25
import ErdosProblems.Erdos1058.Erdos1058PrimeGapCertifiedBatch26
import ErdosProblems.Erdos1058.Erdos1058PrimeGapCertifiedBatch27
import ErdosProblems.Erdos1058.Erdos1058PrimeGapCertifiedBatch28
import ErdosProblems.Erdos1058.Erdos1058PrimeGapCertifiedBatch29
import ErdosProblems.Erdos1058.Erdos1058PrimeGapCertifiedBatch30
import ErdosProblems.Erdos1058.Erdos1058PrimeGapCertifiedBatch31
import ErdosProblems.Erdos1058.Erdos1058PrimeGapCertifiedBatch32
import ErdosProblems.Erdos1058.Erdos1058PrimeGapCertifiedBatch33
import ErdosProblems.Erdos1058.Erdos1058PrimeGapCertifiedBatch34
import ErdosProblems.Erdos1058.Erdos1058PrimeGapCertifiedBatch35
import ErdosProblems.Erdos1058.Erdos1058PrimeGapCertifiedBatch36

-- The cover is assembled from hundreds of generated declarations; joining each
-- declaration before starting the next one bounds the elaborator's live state.
set_option Elab.async false

namespace Erdos1058

open Nat

namespace PrimeGap210Certificate

private def primeGapCoverStep0 : List ℕ := primeGapCertifiedGroup0

private lemma primeGapCoverStep0_segment :
    CertifiedSegment primeGapCoverStep0 439 102101 := by
  unfold primeGapCoverStep0
  exact primeGapCertifiedGroup0_segment

private def primeGapCoverStep1 : List ℕ :=
  primeGapCoverStep0 ++ primeGapCertifiedGroup1

private lemma primeGapCoverStep1_segment :
    CertifiedSegment primeGapCoverStep1 439 203591 := by
  unfold primeGapCoverStep1
  exact primeGapCoverStep0_segment.append primeGapCertifiedGroup1_segment
    (by norm_num [GapStep])

private def primeGapCoverStep2 : List ℕ :=
  primeGapCoverStep1 ++ primeGapCertifiedGroup2

private lemma primeGapCoverStep2_segment :
    CertifiedSegment primeGapCoverStep2 439 304709 := by
  unfold primeGapCoverStep2
  exact primeGapCoverStep1_segment.append primeGapCertifiedGroup2_segment
    (by norm_num [GapStep])

private def primeGapCoverStep3 : List ℕ :=
  primeGapCoverStep2 ++ primeGapCertifiedGroup3

private lemma primeGapCoverStep3_segment :
    CertifiedSegment primeGapCoverStep3 439 405781 := by
  unfold primeGapCoverStep3
  exact primeGapCoverStep2_segment.append primeGapCertifiedGroup3_segment
    (by norm_num [GapStep])

private def primeGapCoverStep4 : List ℕ :=
  primeGapCoverStep3 ++ primeGapCertifiedGroup4

private lemma primeGapCoverStep4_segment :
    CertifiedSegment primeGapCoverStep4 439 506999 := by
  unfold primeGapCoverStep4
  exact primeGapCoverStep3_segment.append primeGapCertifiedGroup4_segment
    (by norm_num [GapStep])

private def primeGapCoverStep5 : List ℕ :=
  primeGapCoverStep4 ++ primeGapCertifiedGroup5

private lemma primeGapCoverStep5_segment :
    CertifiedSegment primeGapCoverStep5 439 608303 := by
  unfold primeGapCoverStep5
  exact primeGapCoverStep4_segment.append primeGapCertifiedGroup5_segment
    (by norm_num [GapStep])

private def primeGapCoverStep6 : List ℕ :=
  primeGapCoverStep5 ++ primeGapCertifiedGroup6

private lemma primeGapCoverStep6_segment :
    CertifiedSegment primeGapCoverStep6 439 708959 := by
  unfold primeGapCoverStep6
  exact primeGapCoverStep5_segment.append primeGapCertifiedGroup6_segment
    (by norm_num [GapStep])

private def primeGapCoverStep7 : List ℕ :=
  primeGapCoverStep6 ++ primeGapCertifiedGroup7

private lemma primeGapCoverStep7_segment :
    CertifiedSegment primeGapCoverStep7 439 809357 := by
  unfold primeGapCoverStep7
  exact primeGapCoverStep6_segment.append primeGapCertifiedGroup7_segment
    (by norm_num [GapStep])

private def primeGapCoverStep8 : List ℕ :=
  primeGapCoverStep7 ++ primeGapCertifiedGroup8

private lemma primeGapCoverStep8_segment :
    CertifiedSegment primeGapCoverStep8 439 909917 := by
  unfold primeGapCoverStep8
  exact primeGapCoverStep7_segment.append primeGapCertifiedGroup8_segment
    (by norm_num [GapStep])

private def primeGapCoverStep9 : List ℕ :=
  primeGapCoverStep8 ++ primeGapCertifiedGroup9

private lemma primeGapCoverStep9_segment :
    CertifiedSegment primeGapCoverStep9 439 1010353 := by
  unfold primeGapCoverStep9
  exact primeGapCoverStep8_segment.append primeGapCertifiedGroup9_segment
    (by norm_num [GapStep])

private def primeGapCoverStep10 : List ℕ :=
  primeGapCoverStep9 ++ primeGapCertifiedGroup10

private lemma primeGapCoverStep10_segment :
    CertifiedSegment primeGapCoverStep10 439 1111259 := by
  unfold primeGapCoverStep10
  exact primeGapCoverStep9_segment.append primeGapCertifiedGroup10_segment
    (by norm_num [GapStep])

private def primeGapCoverStep11 : List ℕ :=
  primeGapCoverStep10 ++ primeGapCertifiedGroup11

private lemma primeGapCoverStep11_segment :
    CertifiedSegment primeGapCoverStep11 439 1211653 := by
  unfold primeGapCoverStep11
  exact primeGapCoverStep10_segment.append primeGapCertifiedGroup11_segment
    (by norm_num [GapStep])

private def primeGapCoverStep12 : List ℕ :=
  primeGapCoverStep11 ++ primeGapCertifiedGroup12

private lemma primeGapCoverStep12_segment :
    CertifiedSegment primeGapCoverStep12 439 1312177 := by
  unfold primeGapCoverStep12
  exact primeGapCoverStep11_segment.append primeGapCertifiedGroup12_segment
    (by norm_num [GapStep])

private def primeGapCoverStep13 : List ℕ :=
  primeGapCoverStep12 ++ primeGapCertifiedGroup13

private lemma primeGapCoverStep13_segment :
    CertifiedSegment primeGapCoverStep13 439 1412497 := by
  unfold primeGapCoverStep13
  exact primeGapCoverStep12_segment.append primeGapCertifiedGroup13_segment
    (by norm_num [GapStep])

private def primeGapCoverStep14 : List ℕ :=
  primeGapCoverStep13 ++ primeGapCertifiedGroup14

private lemma primeGapCoverStep14_segment :
    CertifiedSegment primeGapCoverStep14 439 1512569 := by
  unfold primeGapCoverStep14
  exact primeGapCoverStep13_segment.append primeGapCertifiedGroup14_segment
    (by norm_num [GapStep])

private def primeGapCoverStep15 : List ℕ :=
  primeGapCoverStep14 ++ primeGapCertifiedGroup15

private lemma primeGapCoverStep15_segment :
    CertifiedSegment primeGapCoverStep15 439 1612957 := by
  unfold primeGapCoverStep15
  exact primeGapCoverStep14_segment.append primeGapCertifiedGroup15_segment
    (by norm_num [GapStep])

private def primeGapCoverStep16 : List ℕ :=
  primeGapCoverStep15 ++ primeGapCertifiedGroup16

private lemma primeGapCoverStep16_segment :
    CertifiedSegment primeGapCoverStep16 439 1712981 := by
  unfold primeGapCoverStep16
  exact primeGapCoverStep15_segment.append primeGapCertifiedGroup16_segment
    (by norm_num [GapStep])

private def primeGapCoverStep17 : List ℕ :=
  primeGapCoverStep16 ++ primeGapCertifiedGroup17

private lemma primeGapCoverStep17_segment :
    CertifiedSegment primeGapCoverStep17 439 1813211 := by
  unfold primeGapCoverStep17
  exact primeGapCoverStep16_segment.append primeGapCertifiedGroup17_segment
    (by norm_num [GapStep])

private def primeGapCoverStep18 : List ℕ :=
  primeGapCoverStep17 ++ primeGapCertifiedGroup18

private lemma primeGapCoverStep18_segment :
    CertifiedSegment primeGapCoverStep18 439 1913551 := by
  unfold primeGapCoverStep18
  exact primeGapCoverStep17_segment.append primeGapCertifiedGroup18_segment
    (by norm_num [GapStep])

private def primeGapCoverStep19 : List ℕ :=
  primeGapCoverStep18 ++ primeGapCertifiedGroup19

private lemma primeGapCoverStep19_segment :
    CertifiedSegment primeGapCoverStep19 439 2013751 := by
  unfold primeGapCoverStep19
  exact primeGapCoverStep18_segment.append primeGapCertifiedGroup19_segment
    (by norm_num [GapStep])

private def primeGapCoverStep20 : List ℕ :=
  primeGapCoverStep19 ++ primeGapCertifiedGroup20

private lemma primeGapCoverStep20_segment :
    CertifiedSegment primeGapCoverStep20 439 2113819 := by
  unfold primeGapCoverStep20
  exact primeGapCoverStep19_segment.append primeGapCertifiedGroup20_segment
    (by norm_num [GapStep])

private def primeGapCoverStep21 : List ℕ :=
  primeGapCoverStep20 ++ primeGapCertifiedGroup21

private lemma primeGapCoverStep21_segment :
    CertifiedSegment primeGapCoverStep21 439 2214011 := by
  unfold primeGapCoverStep21
  exact primeGapCoverStep20_segment.append primeGapCertifiedGroup21_segment
    (by norm_num [GapStep])

private def primeGapCoverStep22 : List ℕ :=
  primeGapCoverStep21 ++ primeGapCertifiedGroup22

private lemma primeGapCoverStep22_segment :
    CertifiedSegment primeGapCoverStep22 439 2313977 := by
  unfold primeGapCoverStep22
  exact primeGapCoverStep21_segment.append primeGapCertifiedGroup22_segment
    (by norm_num [GapStep])

private def primeGapCoverStep23 : List ℕ :=
  primeGapCoverStep22 ++ primeGapCertifiedGroup23

private lemma primeGapCoverStep23_segment :
    CertifiedSegment primeGapCoverStep23 439 2414089 := by
  unfold primeGapCoverStep23
  exact primeGapCoverStep22_segment.append primeGapCertifiedGroup23_segment
    (by norm_num [GapStep])

private def primeGapCoverStep24 : List ℕ :=
  primeGapCoverStep23 ++ primeGapCertifiedGroup24

private lemma primeGapCoverStep24_segment :
    CertifiedSegment primeGapCoverStep24 439 2514151 := by
  unfold primeGapCoverStep24
  exact primeGapCoverStep23_segment.append primeGapCertifiedGroup24_segment
    (by norm_num [GapStep])

private def primeGapCoverStep25 : List ℕ :=
  primeGapCoverStep24 ++ primeGapCertifiedGroup25

private lemma primeGapCoverStep25_segment :
    CertifiedSegment primeGapCoverStep25 439 2613953 := by
  unfold primeGapCoverStep25
  exact primeGapCoverStep24_segment.append primeGapCertifiedGroup25_segment
    (by norm_num [GapStep])

private def primeGapCoverStep26 : List ℕ :=
  primeGapCoverStep25 ++ primeGapCertifiedGroup26

private lemma primeGapCoverStep26_segment :
    CertifiedSegment primeGapCoverStep26 439 2713717 := by
  unfold primeGapCoverStep26
  exact primeGapCoverStep25_segment.append primeGapCertifiedGroup26_segment
    (by norm_num [GapStep])

private def primeGapCoverStep27 : List ℕ :=
  primeGapCoverStep26 ++ primeGapCertifiedGroup27

private lemma primeGapCoverStep27_segment :
    CertifiedSegment primeGapCoverStep27 439 2813453 := by
  unfold primeGapCoverStep27
  exact primeGapCoverStep26_segment.append primeGapCertifiedGroup27_segment
    (by norm_num [GapStep])

private def primeGapCoverStep28 : List ℕ :=
  primeGapCoverStep27 ++ primeGapCertifiedGroup28

private lemma primeGapCoverStep28_segment :
    CertifiedSegment primeGapCoverStep28 439 2913271 := by
  unfold primeGapCoverStep28
  exact primeGapCoverStep27_segment.append primeGapCertifiedGroup28_segment
    (by norm_num [GapStep])

private def primeGapCoverStep29 : List ℕ :=
  primeGapCoverStep28 ++ primeGapCertifiedGroup29

private lemma primeGapCoverStep29_segment :
    CertifiedSegment primeGapCoverStep29 439 3013037 := by
  unfold primeGapCoverStep29
  exact primeGapCoverStep28_segment.append primeGapCertifiedGroup29_segment
    (by norm_num [GapStep])

private def primeGapCoverStep30 : List ℕ :=
  primeGapCoverStep29 ++ primeGapCertifiedGroup30

private lemma primeGapCoverStep30_segment :
    CertifiedSegment primeGapCoverStep30 439 3112519 := by
  unfold primeGapCoverStep30
  exact primeGapCoverStep29_segment.append primeGapCertifiedGroup30_segment
    (by norm_num [GapStep])

private def primeGapCoverStep31 : List ℕ :=
  primeGapCoverStep30 ++ primeGapCertifiedGroup31

private lemma primeGapCoverStep31_segment :
    CertifiedSegment primeGapCoverStep31 439 3212423 := by
  unfold primeGapCoverStep31
  exact primeGapCoverStep30_segment.append primeGapCertifiedGroup31_segment
    (by norm_num [GapStep])

private def primeGapCoverStep32 : List ℕ :=
  primeGapCoverStep31 ++ primeGapCertifiedGroup32

private lemma primeGapCoverStep32_segment :
    CertifiedSegment primeGapCoverStep32 439 3312139 := by
  unfold primeGapCoverStep32
  exact primeGapCoverStep31_segment.append primeGapCertifiedGroup32_segment
    (by norm_num [GapStep])

private def primeGapCoverStep33 : List ℕ :=
  primeGapCoverStep32 ++ primeGapCertifiedGroup33

private lemma primeGapCoverStep33_segment :
    CertifiedSegment primeGapCoverStep33 439 3411971 := by
  unfold primeGapCoverStep33
  exact primeGapCoverStep32_segment.append primeGapCertifiedGroup33_segment
    (by norm_num [GapStep])

private def primeGapCoverStep34 : List ℕ :=
  primeGapCoverStep33 ++ primeGapCertifiedGroup34

private lemma primeGapCoverStep34_segment :
    CertifiedSegment primeGapCoverStep34 439 3511531 := by
  unfold primeGapCoverStep34
  exact primeGapCoverStep33_segment.append primeGapCertifiedGroup34_segment
    (by norm_num [GapStep])

private def primeGapCoverStep35 : List ℕ :=
  primeGapCoverStep34 ++ primeGapCertifiedGroup35

private lemma primeGapCoverStep35_segment :
    CertifiedSegment primeGapCoverStep35 439 3611093 := by
  unfold primeGapCoverStep35
  exact primeGapCoverStep34_segment.append primeGapCertifiedGroup35_segment
    (by norm_num [GapStep])

private def primeGapCoverStep36 : List ℕ :=
  primeGapCoverStep35 ++ primeGapCertifiedGroup36

private lemma primeGapCoverStep36_segment :
    CertifiedSegment primeGapCoverStep36 439 3710921 := by
  unfold primeGapCoverStep36
  exact primeGapCoverStep35_segment.append primeGapCertifiedGroup36_segment
    (by norm_num [GapStep])

private def primeGapCoverStep37 : List ℕ :=
  primeGapCoverStep36 ++ primeGapCertifiedGroup37

private lemma primeGapCoverStep37_segment :
    CertifiedSegment primeGapCoverStep37 439 3810931 := by
  unfold primeGapCoverStep37
  exact primeGapCoverStep36_segment.append primeGapCertifiedGroup37_segment
    (by norm_num [GapStep])

private def primeGapCoverStep38 : List ℕ :=
  primeGapCoverStep37 ++ primeGapCertifiedGroup38

private lemma primeGapCoverStep38_segment :
    CertifiedSegment primeGapCoverStep38 439 3911153 := by
  unfold primeGapCoverStep38
  exact primeGapCoverStep37_segment.append primeGapCertifiedGroup38_segment
    (by norm_num [GapStep])

private def primeGapCoverStep39 : List ℕ :=
  primeGapCoverStep38 ++ primeGapCertifiedGroup39

private lemma primeGapCoverStep39_segment :
    CertifiedSegment primeGapCoverStep39 439 4011377 := by
  unfold primeGapCoverStep39
  exact primeGapCoverStep38_segment.append primeGapCertifiedGroup39_segment
    (by norm_num [GapStep])

private def primeGapCoverStep40 : List ℕ :=
  primeGapCoverStep39 ++ primeGapCertifiedGroup40

private lemma primeGapCoverStep40_segment :
    CertifiedSegment primeGapCoverStep40 439 4111171 := by
  unfold primeGapCoverStep40
  exact primeGapCoverStep39_segment.append primeGapCertifiedGroup40_segment
    (by norm_num [GapStep])

private def primeGapCoverStep41 : List ℕ :=
  primeGapCoverStep40 ++ primeGapCertifiedGroup41

private lemma primeGapCoverStep41_segment :
    CertifiedSegment primeGapCoverStep41 439 4210919 := by
  unfold primeGapCoverStep41
  exact primeGapCoverStep40_segment.append primeGapCertifiedGroup41_segment
    (by norm_num [GapStep])

private def primeGapCoverStep42 : List ℕ :=
  primeGapCoverStep41 ++ primeGapCertifiedGroup42

private lemma primeGapCoverStep42_segment :
    CertifiedSegment primeGapCoverStep42 439 4310851 := by
  unfold primeGapCoverStep42
  exact primeGapCoverStep41_segment.append primeGapCertifiedGroup42_segment
    (by norm_num [GapStep])

private def primeGapCoverStep43 : List ℕ :=
  primeGapCoverStep42 ++ primeGapCertifiedGroup43

private lemma primeGapCoverStep43_segment :
    CertifiedSegment primeGapCoverStep43 439 4410589 := by
  unfold primeGapCoverStep43
  exact primeGapCoverStep42_segment.append primeGapCertifiedGroup43_segment
    (by norm_num [GapStep])

private def primeGapCoverStep44 : List ℕ :=
  primeGapCoverStep43 ++ primeGapCertifiedGroup44

private lemma primeGapCoverStep44_segment :
    CertifiedSegment primeGapCoverStep44 439 4510057 := by
  unfold primeGapCoverStep44
  exact primeGapCoverStep43_segment.append primeGapCertifiedGroup44_segment
    (by norm_num [GapStep])

private def primeGapCoverStep45 : List ℕ :=
  primeGapCoverStep44 ++ primeGapCertifiedGroup45

private lemma primeGapCoverStep45_segment :
    CertifiedSegment primeGapCoverStep45 439 4609547 := by
  unfold primeGapCoverStep45
  exact primeGapCoverStep44_segment.append primeGapCertifiedGroup45_segment
    (by norm_num [GapStep])

private def primeGapCoverStep46 : List ℕ :=
  primeGapCoverStep45 ++ primeGapCertifiedGroup46

private lemma primeGapCoverStep46_segment :
    CertifiedSegment primeGapCoverStep46 439 4709041 := by
  unfold primeGapCoverStep46
  exact primeGapCoverStep45_segment.append primeGapCertifiedGroup46_segment
    (by norm_num [GapStep])

private def primeGapCoverStep47 : List ℕ :=
  primeGapCoverStep46 ++ primeGapCertifiedGroup47

private lemma primeGapCoverStep47_segment :
    CertifiedSegment primeGapCoverStep47 439 4808747 := by
  unfold primeGapCoverStep47
  exact primeGapCoverStep46_segment.append primeGapCertifiedGroup47_segment
    (by norm_num [GapStep])

private def primeGapCoverStep48 : List ℕ :=
  primeGapCoverStep47 ++ primeGapCertifiedGroup48

private lemma primeGapCoverStep48_segment :
    CertifiedSegment primeGapCoverStep48 439 4908661 := by
  unfold primeGapCoverStep48
  exact primeGapCoverStep47_segment.append primeGapCertifiedGroup48_segment
    (by norm_num [GapStep])

private def primeGapCoverStep49 : List ℕ :=
  primeGapCoverStep48 ++ primeGapCertifiedGroup49

private lemma primeGapCoverStep49_segment :
    CertifiedSegment primeGapCoverStep49 439 5008573 := by
  unfold primeGapCoverStep49
  exact primeGapCoverStep48_segment.append primeGapCertifiedGroup49_segment
    (by norm_num [GapStep])

private def primeGapCoverStep50 : List ℕ :=
  primeGapCoverStep49 ++ primeGapCertifiedGroup50

private lemma primeGapCoverStep50_segment :
    CertifiedSegment primeGapCoverStep50 439 5108039 := by
  unfold primeGapCoverStep50
  exact primeGapCoverStep49_segment.append primeGapCertifiedGroup50_segment
    (by norm_num [GapStep])

private def primeGapCoverStep51 : List ℕ :=
  primeGapCoverStep50 ++ primeGapCertifiedGroup51

private lemma primeGapCoverStep51_segment :
    CertifiedSegment primeGapCoverStep51 439 5207611 := by
  unfold primeGapCoverStep51
  exact primeGapCoverStep50_segment.append primeGapCertifiedGroup51_segment
    (by norm_num [GapStep])

private def primeGapCoverStep52 : List ℕ :=
  primeGapCoverStep51 ++ primeGapCertifiedGroup52

private lemma primeGapCoverStep52_segment :
    CertifiedSegment primeGapCoverStep52 439 5307397 := by
  unfold primeGapCoverStep52
  exact primeGapCoverStep51_segment.append primeGapCertifiedGroup52_segment
    (by norm_num [GapStep])

private def primeGapCoverStep53 : List ℕ :=
  primeGapCoverStep52 ++ primeGapCertifiedGroup53

private lemma primeGapCoverStep53_segment :
    CertifiedSegment primeGapCoverStep53 439 5407243 := by
  unfold primeGapCoverStep53
  exact primeGapCoverStep52_segment.append primeGapCertifiedGroup53_segment
    (by norm_num [GapStep])

private def primeGapCoverStep54 : List ℕ :=
  primeGapCoverStep53 ++ primeGapCertifiedGroup54

private lemma primeGapCoverStep54_segment :
    CertifiedSegment primeGapCoverStep54 439 5507111 := by
  unfold primeGapCoverStep54
  exact primeGapCoverStep53_segment.append primeGapCertifiedGroup54_segment
    (by norm_num [GapStep])

private def primeGapCoverStep55 : List ℕ :=
  primeGapCoverStep54 ++ primeGapCertifiedGroup55

private lemma primeGapCoverStep55_segment :
    CertifiedSegment primeGapCoverStep55 439 5606303 := by
  unfold primeGapCoverStep55
  exact primeGapCoverStep54_segment.append primeGapCertifiedGroup55_segment
    (by norm_num [GapStep])

private def primeGapCoverStep56 : List ℕ :=
  primeGapCoverStep55 ++ primeGapCertifiedGroup56

private lemma primeGapCoverStep56_segment :
    CertifiedSegment primeGapCoverStep56 439 5705873 := by
  unfold primeGapCoverStep56
  exact primeGapCoverStep55_segment.append primeGapCertifiedGroup56_segment
    (by norm_num [GapStep])

private def primeGapCoverStep57 : List ℕ :=
  primeGapCoverStep56 ++ primeGapCertifiedGroup57

private lemma primeGapCoverStep57_segment :
    CertifiedSegment primeGapCoverStep57 439 5805871 := by
  unfold primeGapCoverStep57
  exact primeGapCoverStep56_segment.append primeGapCertifiedGroup57_segment
    (by norm_num [GapStep])

private def primeGapCoverStep58 : List ℕ :=
  primeGapCoverStep57 ++ primeGapCertifiedGroup58

private lemma primeGapCoverStep58_segment :
    CertifiedSegment primeGapCoverStep58 439 5905441 := by
  unfold primeGapCoverStep58
  exact primeGapCoverStep57_segment.append primeGapCertifiedGroup58_segment
    (by norm_num [GapStep])

private def primeGapCoverStep59 : List ℕ :=
  primeGapCoverStep58 ++ primeGapCertifiedGroup59

private lemma primeGapCoverStep59_segment :
    CertifiedSegment primeGapCoverStep59 439 6005357 := by
  unfold primeGapCoverStep59
  exact primeGapCoverStep58_segment.append primeGapCertifiedGroup59_segment
    (by norm_num [GapStep])

private def primeGapCoverStep60 : List ℕ :=
  primeGapCoverStep59 ++ primeGapCertifiedGroup60

private lemma primeGapCoverStep60_segment :
    CertifiedSegment primeGapCoverStep60 439 6104807 := by
  unfold primeGapCoverStep60
  exact primeGapCoverStep59_segment.append primeGapCertifiedGroup60_segment
    (by norm_num [GapStep])

private def primeGapCoverStep61 : List ℕ :=
  primeGapCoverStep60 ++ primeGapCertifiedGroup61

private lemma primeGapCoverStep61_segment :
    CertifiedSegment primeGapCoverStep61 439 6204383 := by
  unfold primeGapCoverStep61
  exact primeGapCoverStep60_segment.append primeGapCertifiedGroup61_segment
    (by norm_num [GapStep])

private def primeGapCoverStep62 : List ℕ :=
  primeGapCoverStep61 ++ primeGapCertifiedGroup62

private lemma primeGapCoverStep62_segment :
    CertifiedSegment primeGapCoverStep62 439 6304169 := by
  unfold primeGapCoverStep62
  exact primeGapCoverStep61_segment.append primeGapCertifiedGroup62_segment
    (by norm_num [GapStep])

private def primeGapCoverStep63 : List ℕ :=
  primeGapCoverStep62 ++ primeGapCertifiedGroup63

private lemma primeGapCoverStep63_segment :
    CertifiedSegment primeGapCoverStep63 439 6403181 := by
  unfold primeGapCoverStep63
  exact primeGapCoverStep62_segment.append primeGapCertifiedGroup63_segment
    (by norm_num [GapStep])

private def primeGapCoverStep64 : List ℕ :=
  primeGapCoverStep63 ++ primeGapCertifiedGroup64

private lemma primeGapCoverStep64_segment :
    CertifiedSegment primeGapCoverStep64 439 6503143 := by
  unfold primeGapCoverStep64
  exact primeGapCoverStep63_segment.append primeGapCertifiedGroup64_segment
    (by norm_num [GapStep])

private def primeGapCoverStep65 : List ℕ :=
  primeGapCoverStep64 ++ primeGapCertifiedGroup65

private lemma primeGapCoverStep65_segment :
    CertifiedSegment primeGapCoverStep65 439 6602879 := by
  unfold primeGapCoverStep65
  exact primeGapCoverStep64_segment.append primeGapCertifiedGroup65_segment
    (by norm_num [GapStep])

private def primeGapCoverStep66 : List ℕ :=
  primeGapCoverStep65 ++ primeGapCertifiedGroup66

private lemma primeGapCoverStep66_segment :
    CertifiedSegment primeGapCoverStep66 439 6702559 := by
  unfold primeGapCoverStep66
  exact primeGapCoverStep65_segment.append primeGapCertifiedGroup66_segment
    (by norm_num [GapStep])

private def primeGapCoverStep67 : List ℕ :=
  primeGapCoverStep66 ++ primeGapCertifiedGroup67

private lemma primeGapCoverStep67_segment :
    CertifiedSegment primeGapCoverStep67 439 6802637 := by
  unfold primeGapCoverStep67
  exact primeGapCoverStep66_segment.append primeGapCertifiedGroup67_segment
    (by norm_num [GapStep])

private def primeGapCoverStep68 : List ℕ :=
  primeGapCoverStep67 ++ primeGapCertifiedGroup68

private lemma primeGapCoverStep68_segment :
    CertifiedSegment primeGapCoverStep68 439 6901859 := by
  unfold primeGapCoverStep68
  exact primeGapCoverStep67_segment.append primeGapCertifiedGroup68_segment
    (by norm_num [GapStep])

private def primeGapCoverStep69 : List ℕ :=
  primeGapCoverStep68 ++ primeGapCertifiedGroup69

private lemma primeGapCoverStep69_segment :
    CertifiedSegment primeGapCoverStep69 439 7001723 := by
  unfold primeGapCoverStep69
  exact primeGapCoverStep68_segment.append primeGapCertifiedGroup69_segment
    (by norm_num [GapStep])

private def primeGapCoverStep70 : List ℕ :=
  primeGapCoverStep69 ++ primeGapCertifiedGroup70

private lemma primeGapCoverStep70_segment :
    CertifiedSegment primeGapCoverStep70 439 7101287 := by
  unfold primeGapCoverStep70
  exact primeGapCoverStep69_segment.append primeGapCertifiedGroup70_segment
    (by norm_num [GapStep])

private def primeGapCoverStep71 : List ℕ :=
  primeGapCoverStep70 ++ primeGapCertifiedGroup71

private lemma primeGapCoverStep71_segment :
    CertifiedSegment primeGapCoverStep71 439 7200719 := by
  unfold primeGapCoverStep71
  exact primeGapCoverStep70_segment.append primeGapCertifiedGroup71_segment
    (by norm_num [GapStep])

private def primeGapCoverStep72 : List ℕ :=
  primeGapCoverStep71 ++ primeGapCertifiedGroup72

private lemma primeGapCoverStep72_segment :
    CertifiedSegment primeGapCoverStep72 439 7299823 := by
  unfold primeGapCoverStep72
  exact primeGapCoverStep71_segment.append primeGapCertifiedGroup72_segment
    (by norm_num [GapStep])

private def primeGapCoverStep73 : List ℕ :=
  primeGapCoverStep72 ++ primeGapCertifiedGroup73

private lemma primeGapCoverStep73_segment :
    CertifiedSegment primeGapCoverStep73 439 7399439 := by
  unfold primeGapCoverStep73
  exact primeGapCoverStep72_segment.append primeGapCertifiedGroup73_segment
    (by norm_num [GapStep])

private def primeGapCoverStep74 : List ℕ :=
  primeGapCoverStep73 ++ primeGapCertifiedGroup74

private lemma primeGapCoverStep74_segment :
    CertifiedSegment primeGapCoverStep74 439 7499069 := by
  unfold primeGapCoverStep74
  exact primeGapCoverStep73_segment.append primeGapCertifiedGroup74_segment
    (by norm_num [GapStep])

private def primeGapCoverStep75 : List ℕ :=
  primeGapCoverStep74 ++ primeGapCertifiedGroup75

private lemma primeGapCoverStep75_segment :
    CertifiedSegment primeGapCoverStep75 439 7598359 := by
  unfold primeGapCoverStep75
  exact primeGapCoverStep74_segment.append primeGapCertifiedGroup75_segment
    (by norm_num [GapStep])

private def primeGapCoverStep76 : List ℕ :=
  primeGapCoverStep75 ++ primeGapCertifiedGroup76

private lemma primeGapCoverStep76_segment :
    CertifiedSegment primeGapCoverStep76 439 7697567 := by
  unfold primeGapCoverStep76
  exact primeGapCoverStep75_segment.append primeGapCertifiedGroup76_segment
    (by norm_num [GapStep])

private def primeGapCoverStep77 : List ℕ :=
  primeGapCoverStep76 ++ primeGapCertifiedGroup77

private lemma primeGapCoverStep77_segment :
    CertifiedSegment primeGapCoverStep77 439 7797173 := by
  unfold primeGapCoverStep77
  exact primeGapCoverStep76_segment.append primeGapCertifiedGroup77_segment
    (by norm_num [GapStep])

private def primeGapCoverStep78 : List ℕ :=
  primeGapCoverStep77 ++ primeGapCertifiedGroup78

private lemma primeGapCoverStep78_segment :
    CertifiedSegment primeGapCoverStep78 439 7897147 := by
  unfold primeGapCoverStep78
  exact primeGapCoverStep77_segment.append primeGapCertifiedGroup78_segment
    (by norm_num [GapStep])

private def primeGapCoverStep79 : List ℕ :=
  primeGapCoverStep78 ++ primeGapCertifiedGroup79

private lemma primeGapCoverStep79_segment :
    CertifiedSegment primeGapCoverStep79 439 7996487 := by
  unfold primeGapCoverStep79
  exact primeGapCoverStep78_segment.append primeGapCertifiedGroup79_segment
    (by norm_num [GapStep])

private def primeGapCoverStep80 : List ℕ :=
  primeGapCoverStep79 ++ primeGapCertifiedGroup80

private lemma primeGapCoverStep80_segment :
    CertifiedSegment primeGapCoverStep80 439 8096219 := by
  unfold primeGapCoverStep80
  exact primeGapCoverStep79_segment.append primeGapCertifiedGroup80_segment
    (by norm_num [GapStep])

private def primeGapCoverStep81 : List ℕ :=
  primeGapCoverStep80 ++ primeGapCertifiedGroup81

private lemma primeGapCoverStep81_segment :
    CertifiedSegment primeGapCoverStep81 439 8195729 := by
  unfold primeGapCoverStep81
  exact primeGapCoverStep80_segment.append primeGapCertifiedGroup81_segment
    (by norm_num [GapStep])

private def primeGapCoverStep82 : List ℕ :=
  primeGapCoverStep81 ++ primeGapCertifiedGroup82

private lemma primeGapCoverStep82_segment :
    CertifiedSegment primeGapCoverStep82 439 8295317 := by
  unfold primeGapCoverStep82
  exact primeGapCoverStep81_segment.append primeGapCertifiedGroup82_segment
    (by norm_num [GapStep])

private def primeGapCoverStep83 : List ℕ :=
  primeGapCoverStep82 ++ primeGapCertifiedGroup83

private lemma primeGapCoverStep83_segment :
    CertifiedSegment primeGapCoverStep83 439 8394383 := by
  unfold primeGapCoverStep83
  exact primeGapCoverStep82_segment.append primeGapCertifiedGroup83_segment
    (by norm_num [GapStep])

private def primeGapCoverStep84 : List ℕ :=
  primeGapCoverStep83 ++ primeGapCertifiedGroup84

private lemma primeGapCoverStep84_segment :
    CertifiedSegment primeGapCoverStep84 439 8493559 := by
  unfold primeGapCoverStep84
  exact primeGapCoverStep83_segment.append primeGapCertifiedGroup84_segment
    (by norm_num [GapStep])

private def primeGapCoverStep85 : List ℕ :=
  primeGapCoverStep84 ++ primeGapCertifiedGroup85

private lemma primeGapCoverStep85_segment :
    CertifiedSegment primeGapCoverStep85 439 8592581 := by
  unfold primeGapCoverStep85
  exact primeGapCoverStep84_segment.append primeGapCertifiedGroup85_segment
    (by norm_num [GapStep])

private def primeGapCoverStep86 : List ℕ :=
  primeGapCoverStep85 ++ primeGapCertifiedGroup86

private lemma primeGapCoverStep86_segment :
    CertifiedSegment primeGapCoverStep86 439 8691853 := by
  unfold primeGapCoverStep86
  exact primeGapCoverStep85_segment.append primeGapCertifiedGroup86_segment
    (by norm_num [GapStep])

private def primeGapCoverStep87 : List ℕ :=
  primeGapCoverStep86 ++ primeGapCertifiedGroup87

private lemma primeGapCoverStep87_segment :
    CertifiedSegment primeGapCoverStep87 439 8790983 := by
  unfold primeGapCoverStep87
  exact primeGapCoverStep86_segment.append primeGapCertifiedGroup87_segment
    (by norm_num [GapStep])

private def primeGapCoverStep88 : List ℕ :=
  primeGapCoverStep87 ++ primeGapCertifiedGroup88

private lemma primeGapCoverStep88_segment :
    CertifiedSegment primeGapCoverStep88 439 8890747 := by
  unfold primeGapCoverStep88
  exact primeGapCoverStep87_segment.append primeGapCertifiedGroup88_segment
    (by norm_num [GapStep])

private def primeGapCoverStep89 : List ℕ :=
  primeGapCoverStep88 ++ primeGapCertifiedGroup89

private lemma primeGapCoverStep89_segment :
    CertifiedSegment primeGapCoverStep89 439 8990027 := by
  unfold primeGapCoverStep89
  exact primeGapCoverStep88_segment.append primeGapCertifiedGroup89_segment
    (by norm_num [GapStep])

private def primeGapCoverStep90 : List ℕ :=
  primeGapCoverStep89 ++ primeGapCertifiedGroup90

private lemma primeGapCoverStep90_segment :
    CertifiedSegment primeGapCoverStep90 439 9089737 := by
  unfold primeGapCoverStep90
  exact primeGapCoverStep89_segment.append primeGapCertifiedGroup90_segment
    (by norm_num [GapStep])

private def primeGapCoverStep91 : List ℕ :=
  primeGapCoverStep90 ++ primeGapCertifiedGroup91

private lemma primeGapCoverStep91_segment :
    CertifiedSegment primeGapCoverStep91 439 9189353 := by
  unfold primeGapCoverStep91
  exact primeGapCoverStep90_segment.append primeGapCertifiedGroup91_segment
    (by norm_num [GapStep])

private def primeGapCoverStep92 : List ℕ :=
  primeGapCoverStep91 ++ primeGapCertifiedGroup92

private lemma primeGapCoverStep92_segment :
    CertifiedSegment primeGapCoverStep92 439 9288893 := by
  unfold primeGapCoverStep92
  exact primeGapCoverStep91_segment.append primeGapCertifiedGroup92_segment
    (by norm_num [GapStep])

private def primeGapCoverStep93 : List ℕ :=
  primeGapCoverStep92 ++ primeGapCertifiedGroup93

private lemma primeGapCoverStep93_segment :
    CertifiedSegment primeGapCoverStep93 439 9388529 := by
  unfold primeGapCoverStep93
  exact primeGapCoverStep92_segment.append primeGapCertifiedGroup93_segment
    (by norm_num [GapStep])

private def primeGapCoverStep94 : List ℕ :=
  primeGapCoverStep93 ++ primeGapCertifiedGroup94

private lemma primeGapCoverStep94_segment :
    CertifiedSegment primeGapCoverStep94 439 9487529 := by
  unfold primeGapCoverStep94
  exact primeGapCoverStep93_segment.append primeGapCertifiedGroup94_segment
    (by norm_num [GapStep])

private def primeGapCoverStep95 : List ℕ :=
  primeGapCoverStep94 ++ primeGapCertifiedGroup95

private lemma primeGapCoverStep95_segment :
    CertifiedSegment primeGapCoverStep95 439 9586777 := by
  unfold primeGapCoverStep95
  exact primeGapCoverStep94_segment.append primeGapCertifiedGroup95_segment
    (by norm_num [GapStep])

private def primeGapCoverStep96 : List ℕ :=
  primeGapCoverStep95 ++ primeGapCertifiedGroup96

private lemma primeGapCoverStep96_segment :
    CertifiedSegment primeGapCoverStep96 439 9686401 := by
  unfold primeGapCoverStep96
  exact primeGapCoverStep95_segment.append primeGapCertifiedGroup96_segment
    (by norm_num [GapStep])

private def primeGapCoverStep97 : List ℕ :=
  primeGapCoverStep96 ++ primeGapCertifiedGroup97

private lemma primeGapCoverStep97_segment :
    CertifiedSegment primeGapCoverStep97 439 9785333 := by
  unfold primeGapCoverStep97
  exact primeGapCoverStep96_segment.append primeGapCertifiedGroup97_segment
    (by norm_num [GapStep])

private def primeGapCoverStep98 : List ℕ :=
  primeGapCoverStep97 ++ primeGapCertifiedGroup98

private lemma primeGapCoverStep98_segment :
    CertifiedSegment primeGapCoverStep98 439 9884527 := by
  unfold primeGapCoverStep98
  exact primeGapCoverStep97_segment.append primeGapCertifiedGroup98_segment
    (by norm_num [GapStep])

private def primeGapCoverStep99 : List ℕ :=
  primeGapCoverStep98 ++ primeGapCertifiedGroup99

private lemma primeGapCoverStep99_segment :
    CertifiedSegment primeGapCoverStep99 439 9983371 := by
  unfold primeGapCoverStep99
  exact primeGapCoverStep98_segment.append primeGapCertifiedGroup99_segment
    (by norm_num [GapStep])

private def primeGapCoverStep100 : List ℕ :=
  primeGapCoverStep99 ++ primeGapCertifiedGroup100

private lemma primeGapCoverStep100_segment :
    CertifiedSegment primeGapCoverStep100 439 10083001 := by
  unfold primeGapCoverStep100
  exact primeGapCoverStep99_segment.append primeGapCertifiedGroup100_segment
    (by norm_num [GapStep])

private def primeGapCoverStep101 : List ℕ :=
  primeGapCoverStep100 ++ primeGapCertifiedGroup101

private lemma primeGapCoverStep101_segment :
    CertifiedSegment primeGapCoverStep101 439 10182239 := by
  unfold primeGapCoverStep101
  exact primeGapCoverStep100_segment.append primeGapCertifiedGroup101_segment
    (by norm_num [GapStep])

private def primeGapCoverStep102 : List ℕ :=
  primeGapCoverStep101 ++ primeGapCertifiedGroup102

private lemma primeGapCoverStep102_segment :
    CertifiedSegment primeGapCoverStep102 439 10281653 := by
  unfold primeGapCoverStep102
  exact primeGapCoverStep101_segment.append primeGapCertifiedGroup102_segment
    (by norm_num [GapStep])

private def primeGapCoverStep103 : List ℕ :=
  primeGapCoverStep102 ++ primeGapCertifiedGroup103

private lemma primeGapCoverStep103_segment :
    CertifiedSegment primeGapCoverStep103 439 10380907 := by
  unfold primeGapCoverStep103
  exact primeGapCoverStep102_segment.append primeGapCertifiedGroup103_segment
    (by norm_num [GapStep])

private def primeGapCoverStep104 : List ℕ :=
  primeGapCoverStep103 ++ primeGapCertifiedGroup104

private lemma primeGapCoverStep104_segment :
    CertifiedSegment primeGapCoverStep104 439 10480333 := by
  unfold primeGapCoverStep104
  exact primeGapCoverStep103_segment.append primeGapCertifiedGroup104_segment
    (by norm_num [GapStep])

private def primeGapCoverStep105 : List ℕ :=
  primeGapCoverStep104 ++ primeGapCertifiedGroup105

private lemma primeGapCoverStep105_segment :
    CertifiedSegment primeGapCoverStep105 439 10580257 := by
  unfold primeGapCoverStep105
  exact primeGapCoverStep104_segment.append primeGapCertifiedGroup105_segment
    (by norm_num [GapStep])

private def primeGapCoverStep106 : List ℕ :=
  primeGapCoverStep105 ++ primeGapCertifiedGroup106

private lemma primeGapCoverStep106_segment :
    CertifiedSegment primeGapCoverStep106 439 10679831 := by
  unfold primeGapCoverStep106
  exact primeGapCoverStep105_segment.append primeGapCertifiedGroup106_segment
    (by norm_num [GapStep])

private def primeGapCoverStep107 : List ℕ :=
  primeGapCoverStep106 ++ primeGapCertifiedGroup107

private lemma primeGapCoverStep107_segment :
    CertifiedSegment primeGapCoverStep107 439 10779239 := by
  unfold primeGapCoverStep107
  exact primeGapCoverStep106_segment.append primeGapCertifiedGroup107_segment
    (by norm_num [GapStep])

private def primeGapCoverStep108 : List ℕ :=
  primeGapCoverStep107 ++ primeGapCertifiedGroup108

private lemma primeGapCoverStep108_segment :
    CertifiedSegment primeGapCoverStep108 439 10878587 := by
  unfold primeGapCoverStep108
  exact primeGapCoverStep107_segment.append primeGapCertifiedGroup108_segment
    (by norm_num [GapStep])

private def primeGapCoverStep109 : List ℕ :=
  primeGapCoverStep108 ++ primeGapCertifiedGroup109

private lemma primeGapCoverStep109_segment :
    CertifiedSegment primeGapCoverStep109 439 10977581 := by
  unfold primeGapCoverStep109
  exact primeGapCoverStep108_segment.append primeGapCertifiedGroup109_segment
    (by norm_num [GapStep])

private def primeGapCoverStep110 : List ℕ :=
  primeGapCoverStep109 ++ primeGapCertifiedGroup110

private lemma primeGapCoverStep110_segment :
    CertifiedSegment primeGapCoverStep110 439 11077379 := by
  unfold primeGapCoverStep110
  exact primeGapCoverStep109_segment.append primeGapCertifiedGroup110_segment
    (by norm_num [GapStep])

private def primeGapCoverStep111 : List ℕ :=
  primeGapCoverStep110 ++ primeGapCertifiedGroup111

private lemma primeGapCoverStep111_segment :
    CertifiedSegment primeGapCoverStep111 439 11176423 := by
  unfold primeGapCoverStep111
  exact primeGapCoverStep110_segment.append primeGapCertifiedGroup111_segment
    (by norm_num [GapStep])

private def primeGapCoverStep112 : List ℕ :=
  primeGapCoverStep111 ++ primeGapCertifiedGroup112

private lemma primeGapCoverStep112_segment :
    CertifiedSegment primeGapCoverStep112 439 11275283 := by
  unfold primeGapCoverStep112
  exact primeGapCoverStep111_segment.append primeGapCertifiedGroup112_segment
    (by norm_num [GapStep])

private def primeGapCoverStep113 : List ℕ :=
  primeGapCoverStep112 ++ primeGapCertifiedGroup113

private lemma primeGapCoverStep113_segment :
    CertifiedSegment primeGapCoverStep113 439 11374639 := by
  unfold primeGapCoverStep113
  exact primeGapCoverStep112_segment.append primeGapCertifiedGroup113_segment
    (by norm_num [GapStep])

private def primeGapCoverStep114 : List ℕ :=
  primeGapCoverStep113 ++ primeGapCertifiedGroup114

private lemma primeGapCoverStep114_segment :
    CertifiedSegment primeGapCoverStep114 439 11474093 := by
  unfold primeGapCoverStep114
  exact primeGapCoverStep113_segment.append primeGapCertifiedGroup114_segment
    (by norm_num [GapStep])

private def primeGapCoverStep115 : List ℕ :=
  primeGapCoverStep114 ++ primeGapCertifiedGroup115

private lemma primeGapCoverStep115_segment :
    CertifiedSegment primeGapCoverStep115 439 11573621 := by
  unfold primeGapCoverStep115
  exact primeGapCoverStep114_segment.append primeGapCertifiedGroup115_segment
    (by norm_num [GapStep])

private def primeGapCoverStep116 : List ℕ :=
  primeGapCoverStep115 ++ primeGapCertifiedGroup116

private lemma primeGapCoverStep116_segment :
    CertifiedSegment primeGapCoverStep116 439 11673187 := by
  unfold primeGapCoverStep116
  exact primeGapCoverStep115_segment.append primeGapCertifiedGroup116_segment
    (by norm_num [GapStep])

private def primeGapCoverStep117 : List ℕ :=
  primeGapCoverStep116 ++ primeGapCertifiedGroup117

private lemma primeGapCoverStep117_segment :
    CertifiedSegment primeGapCoverStep117 439 11772427 := by
  unfold primeGapCoverStep117
  exact primeGapCoverStep116_segment.append primeGapCertifiedGroup117_segment
    (by norm_num [GapStep])

private def primeGapCoverStep118 : List ℕ :=
  primeGapCoverStep117 ++ primeGapCertifiedGroup118

private lemma primeGapCoverStep118_segment :
    CertifiedSegment primeGapCoverStep118 439 11871983 := by
  unfold primeGapCoverStep118
  exact primeGapCoverStep117_segment.append primeGapCertifiedGroup118_segment
    (by norm_num [GapStep])

private def primeGapCoverStep119 : List ℕ :=
  primeGapCoverStep118 ++ primeGapCertifiedGroup119

private lemma primeGapCoverStep119_segment :
    CertifiedSegment primeGapCoverStep119 439 11971117 := by
  unfold primeGapCoverStep119
  exact primeGapCoverStep118_segment.append primeGapCertifiedGroup119_segment
    (by norm_num [GapStep])

private def primeGapCoverStep120 : List ℕ :=
  primeGapCoverStep119 ++ primeGapCertifiedGroup120

private lemma primeGapCoverStep120_segment :
    CertifiedSegment primeGapCoverStep120 439 12070337 := by
  unfold primeGapCoverStep120
  exact primeGapCoverStep119_segment.append primeGapCertifiedGroup120_segment
    (by norm_num [GapStep])

private def primeGapCoverStep121 : List ℕ :=
  primeGapCoverStep120 ++ primeGapCertifiedGroup121

private lemma primeGapCoverStep121_segment :
    CertifiedSegment primeGapCoverStep121 439 12169379 := by
  unfold primeGapCoverStep121
  exact primeGapCoverStep120_segment.append primeGapCertifiedGroup121_segment
    (by norm_num [GapStep])

private def primeGapCoverStep122 : List ℕ :=
  primeGapCoverStep121 ++ primeGapCertifiedGroup122

private lemma primeGapCoverStep122_segment :
    CertifiedSegment primeGapCoverStep122 439 12268367 := by
  unfold primeGapCoverStep122
  exact primeGapCoverStep121_segment.append primeGapCertifiedGroup122_segment
    (by norm_num [GapStep])

private def primeGapCoverStep123 : List ℕ :=
  primeGapCoverStep122 ++ primeGapCertifiedGroup123

private lemma primeGapCoverStep123_segment :
    CertifiedSegment primeGapCoverStep123 439 12367919 := by
  unfold primeGapCoverStep123
  exact primeGapCoverStep122_segment.append primeGapCertifiedGroup123_segment
    (by norm_num [GapStep])

private def primeGapCoverStep124 : List ℕ :=
  primeGapCoverStep123 ++ primeGapCertifiedGroup124

private lemma primeGapCoverStep124_segment :
    CertifiedSegment primeGapCoverStep124 439 12467437 := by
  unfold primeGapCoverStep124
  exact primeGapCoverStep123_segment.append primeGapCertifiedGroup124_segment
    (by norm_num [GapStep])

private def primeGapCoverStep125 : List ℕ :=
  primeGapCoverStep124 ++ primeGapCertifiedGroup125

private lemma primeGapCoverStep125_segment :
    CertifiedSegment primeGapCoverStep125 439 12566243 := by
  unfold primeGapCoverStep125
  exact primeGapCoverStep124_segment.append primeGapCertifiedGroup125_segment
    (by norm_num [GapStep])

private def primeGapCoverStep126 : List ℕ :=
  primeGapCoverStep125 ++ primeGapCertifiedGroup126

private lemma primeGapCoverStep126_segment :
    CertifiedSegment primeGapCoverStep126 439 12665297 := by
  unfold primeGapCoverStep126
  exact primeGapCoverStep125_segment.append primeGapCertifiedGroup126_segment
    (by norm_num [GapStep])

private def primeGapCoverStep127 : List ℕ :=
  primeGapCoverStep126 ++ primeGapCertifiedGroup127

private lemma primeGapCoverStep127_segment :
    CertifiedSegment primeGapCoverStep127 439 12764303 := by
  unfold primeGapCoverStep127
  exact primeGapCoverStep126_segment.append primeGapCertifiedGroup127_segment
    (by norm_num [GapStep])

private def primeGapCoverStep128 : List ℕ :=
  primeGapCoverStep127 ++ primeGapCertifiedGroup128

private lemma primeGapCoverStep128_segment :
    CertifiedSegment primeGapCoverStep128 439 12863699 := by
  unfold primeGapCoverStep128
  exact primeGapCoverStep127_segment.append primeGapCertifiedGroup128_segment
    (by norm_num [GapStep])

private def primeGapCoverStep129 : List ℕ :=
  primeGapCoverStep128 ++ primeGapCertifiedGroup129

private lemma primeGapCoverStep129_segment :
    CertifiedSegment primeGapCoverStep129 439 12963311 := by
  unfold primeGapCoverStep129
  exact primeGapCoverStep128_segment.append primeGapCertifiedGroup129_segment
    (by norm_num [GapStep])

private def primeGapCoverStep130 : List ℕ :=
  primeGapCoverStep129 ++ primeGapCertifiedGroup130

private lemma primeGapCoverStep130_segment :
    CertifiedSegment primeGapCoverStep130 439 13062053 := by
  unfold primeGapCoverStep130
  exact primeGapCoverStep129_segment.append primeGapCertifiedGroup130_segment
    (by norm_num [GapStep])

private def primeGapCoverStep131 : List ℕ :=
  primeGapCoverStep130 ++ primeGapCertifiedGroup131

private lemma primeGapCoverStep131_segment :
    CertifiedSegment primeGapCoverStep131 439 13160731 := by
  unfold primeGapCoverStep131
  exact primeGapCoverStep130_segment.append primeGapCertifiedGroup131_segment
    (by norm_num [GapStep])

private def primeGapCoverStep132 : List ℕ :=
  primeGapCoverStep131 ++ primeGapCertifiedGroup132

private lemma primeGapCoverStep132_segment :
    CertifiedSegment primeGapCoverStep132 439 13259899 := by
  unfold primeGapCoverStep132
  exact primeGapCoverStep131_segment.append primeGapCertifiedGroup132_segment
    (by norm_num [GapStep])

private def primeGapCoverStep133 : List ℕ :=
  primeGapCoverStep132 ++ primeGapCertifiedGroup133

private lemma primeGapCoverStep133_segment :
    CertifiedSegment primeGapCoverStep133 439 13358827 := by
  unfold primeGapCoverStep133
  exact primeGapCoverStep132_segment.append primeGapCertifiedGroup133_segment
    (by norm_num [GapStep])

private def primeGapCoverStep134 : List ℕ :=
  primeGapCoverStep133 ++ primeGapCertifiedGroup134

private lemma primeGapCoverStep134_segment :
    CertifiedSegment primeGapCoverStep134 439 13458323 := by
  unfold primeGapCoverStep134
  exact primeGapCoverStep133_segment.append primeGapCertifiedGroup134_segment
    (by norm_num [GapStep])

private def primeGapCoverStep135 : List ℕ :=
  primeGapCoverStep134 ++ primeGapCertifiedGroup135

private lemma primeGapCoverStep135_segment :
    CertifiedSegment primeGapCoverStep135 439 13557391 := by
  unfold primeGapCoverStep135
  exact primeGapCoverStep134_segment.append primeGapCertifiedGroup135_segment
    (by norm_num [GapStep])

private def primeGapCoverStep136 : List ℕ :=
  primeGapCoverStep135 ++ primeGapCertifiedGroup136

private lemma primeGapCoverStep136_segment :
    CertifiedSegment primeGapCoverStep136 439 13656761 := by
  unfold primeGapCoverStep136
  exact primeGapCoverStep135_segment.append primeGapCertifiedGroup136_segment
    (by norm_num [GapStep])

private def primeGapCoverStep137 : List ℕ :=
  primeGapCoverStep136 ++ primeGapCertifiedGroup137

private lemma primeGapCoverStep137_segment :
    CertifiedSegment primeGapCoverStep137 439 13755719 := by
  unfold primeGapCoverStep137
  exact primeGapCoverStep136_segment.append primeGapCertifiedGroup137_segment
    (by norm_num [GapStep])

private def primeGapCoverStep138 : List ℕ :=
  primeGapCoverStep137 ++ primeGapCertifiedGroup138

private lemma primeGapCoverStep138_segment :
    CertifiedSegment primeGapCoverStep138 439 13855067 := by
  unfold primeGapCoverStep138
  exact primeGapCoverStep137_segment.append primeGapCertifiedGroup138_segment
    (by norm_num [GapStep])

private def primeGapCoverStep139 : List ℕ :=
  primeGapCoverStep138 ++ primeGapCertifiedGroup139

private lemma primeGapCoverStep139_segment :
    CertifiedSegment primeGapCoverStep139 439 13954397 := by
  unfold primeGapCoverStep139
  exact primeGapCoverStep138_segment.append primeGapCertifiedGroup139_segment
    (by norm_num [GapStep])

private def primeGapCoverStep140 : List ℕ :=
  primeGapCoverStep139 ++ primeGapCertifiedGroup140

private lemma primeGapCoverStep140_segment :
    CertifiedSegment primeGapCoverStep140 439 14053717 := by
  unfold primeGapCoverStep140
  exact primeGapCoverStep139_segment.append primeGapCertifiedGroup140_segment
    (by norm_num [GapStep])

private def primeGapCoverStep141 : List ℕ :=
  primeGapCoverStep140 ++ primeGapCertifiedGroup141

private lemma primeGapCoverStep141_segment :
    CertifiedSegment primeGapCoverStep141 439 14152973 := by
  unfold primeGapCoverStep141
  exact primeGapCoverStep140_segment.append primeGapCertifiedGroup141_segment
    (by norm_num [GapStep])

private def primeGapCoverStep142 : List ℕ :=
  primeGapCoverStep141 ++ primeGapCertifiedGroup142

private lemma primeGapCoverStep142_segment :
    CertifiedSegment primeGapCoverStep142 439 14251649 := by
  unfold primeGapCoverStep142
  exact primeGapCoverStep141_segment.append primeGapCertifiedGroup142_segment
    (by norm_num [GapStep])

private def primeGapCoverStep143 : List ℕ :=
  primeGapCoverStep142 ++ primeGapCertifiedGroup143

private lemma primeGapCoverStep143_segment :
    CertifiedSegment primeGapCoverStep143 439 14350841 := by
  unfold primeGapCoverStep143
  exact primeGapCoverStep142_segment.append primeGapCertifiedGroup143_segment
    (by norm_num [GapStep])

private def primeGapCoverStep144 : List ℕ :=
  primeGapCoverStep143 ++ primeGapCertifiedGroup144

private lemma primeGapCoverStep144_segment :
    CertifiedSegment primeGapCoverStep144 439 14450209 := by
  unfold primeGapCoverStep144
  exact primeGapCoverStep143_segment.append primeGapCertifiedGroup144_segment
    (by norm_num [GapStep])

private def primeGapCoverStep145 : List ℕ :=
  primeGapCoverStep144 ++ primeGapCertifiedGroup145

private lemma primeGapCoverStep145_segment :
    CertifiedSegment primeGapCoverStep145 439 14549599 := by
  unfold primeGapCoverStep145
  exact primeGapCoverStep144_segment.append primeGapCertifiedGroup145_segment
    (by norm_num [GapStep])

private def primeGapCoverStep146 : List ℕ :=
  primeGapCoverStep145 ++ primeGapCertifiedGroup146

private lemma primeGapCoverStep146_segment :
    CertifiedSegment primeGapCoverStep146 439 14648839 := by
  unfold primeGapCoverStep146
  exact primeGapCoverStep145_segment.append primeGapCertifiedGroup146_segment
    (by norm_num [GapStep])

private def primeGapCoverStep147 : List ℕ :=
  primeGapCoverStep146 ++ primeGapCertifiedGroup147

private lemma primeGapCoverStep147_segment :
    CertifiedSegment primeGapCoverStep147 439 14748203 := by
  unfold primeGapCoverStep147
  exact primeGapCoverStep146_segment.append primeGapCertifiedGroup147_segment
    (by norm_num [GapStep])

private def primeGapCoverStep148 : List ℕ :=
  primeGapCoverStep147 ++ primeGapCertifiedGroup148

private lemma primeGapCoverStep148_segment :
    CertifiedSegment primeGapCoverStep148 439 14847281 := by
  unfold primeGapCoverStep148
  exact primeGapCoverStep147_segment.append primeGapCertifiedGroup148_segment
    (by norm_num [GapStep])

private def primeGapCoverStep149 : List ℕ :=
  primeGapCoverStep148 ++ primeGapCertifiedGroup149

private lemma primeGapCoverStep149_segment :
    CertifiedSegment primeGapCoverStep149 439 14946359 := by
  unfold primeGapCoverStep149
  exact primeGapCoverStep148_segment.append primeGapCertifiedGroup149_segment
    (by norm_num [GapStep])

private def primeGapCoverStep150 : List ℕ :=
  primeGapCoverStep149 ++ primeGapCertifiedGroup150

private lemma primeGapCoverStep150_segment :
    CertifiedSegment primeGapCoverStep150 439 15045139 := by
  unfold primeGapCoverStep150
  exact primeGapCoverStep149_segment.append primeGapCertifiedGroup150_segment
    (by norm_num [GapStep])

private def primeGapCoverStep151 : List ℕ :=
  primeGapCoverStep150 ++ primeGapCertifiedGroup151

private lemma primeGapCoverStep151_segment :
    CertifiedSegment primeGapCoverStep151 439 15143977 := by
  unfold primeGapCoverStep151
  exact primeGapCoverStep150_segment.append primeGapCertifiedGroup151_segment
    (by norm_num [GapStep])

private def primeGapCoverStep152 : List ℕ :=
  primeGapCoverStep151 ++ primeGapCertifiedGroup152

private lemma primeGapCoverStep152_segment :
    CertifiedSegment primeGapCoverStep152 439 15243343 := by
  unfold primeGapCoverStep152
  exact primeGapCoverStep151_segment.append primeGapCertifiedGroup152_segment
    (by norm_num [GapStep])

private def primeGapCoverStep153 : List ℕ :=
  primeGapCoverStep152 ++ primeGapCertifiedGroup153

private lemma primeGapCoverStep153_segment :
    CertifiedSegment primeGapCoverStep153 439 15342343 := by
  unfold primeGapCoverStep153
  exact primeGapCoverStep152_segment.append primeGapCertifiedGroup153_segment
    (by norm_num [GapStep])

private def primeGapCoverStep154 : List ℕ :=
  primeGapCoverStep153 ++ primeGapCertifiedGroup154

private lemma primeGapCoverStep154_segment :
    CertifiedSegment primeGapCoverStep154 439 15441313 := by
  unfold primeGapCoverStep154
  exact primeGapCoverStep153_segment.append primeGapCertifiedGroup154_segment
    (by norm_num [GapStep])

private def primeGapCoverStep155 : List ℕ :=
  primeGapCoverStep154 ++ primeGapCertifiedGroup155

private lemma primeGapCoverStep155_segment :
    CertifiedSegment primeGapCoverStep155 439 15540307 := by
  unfold primeGapCoverStep155
  exact primeGapCoverStep154_segment.append primeGapCertifiedGroup155_segment
    (by norm_num [GapStep])

private def primeGapCoverStep156 : List ℕ :=
  primeGapCoverStep155 ++ primeGapCertifiedGroup156

private lemma primeGapCoverStep156_segment :
    CertifiedSegment primeGapCoverStep156 439 15639997 := by
  unfold primeGapCoverStep156
  exact primeGapCoverStep155_segment.append primeGapCertifiedGroup156_segment
    (by norm_num [GapStep])

private def primeGapCoverStep157 : List ℕ :=
  primeGapCoverStep156 ++ primeGapCertifiedGroup157

private lemma primeGapCoverStep157_segment :
    CertifiedSegment primeGapCoverStep157 439 15739223 := by
  unfold primeGapCoverStep157
  exact primeGapCoverStep156_segment.append primeGapCertifiedGroup157_segment
    (by norm_num [GapStep])

private def primeGapCoverStep158 : List ℕ :=
  primeGapCoverStep157 ++ primeGapCertifiedGroup158

private lemma primeGapCoverStep158_segment :
    CertifiedSegment primeGapCoverStep158 439 15838313 := by
  unfold primeGapCoverStep158
  exact primeGapCoverStep157_segment.append primeGapCertifiedGroup158_segment
    (by norm_num [GapStep])

private def primeGapCoverStep159 : List ℕ :=
  primeGapCoverStep158 ++ primeGapCertifiedGroup159

private lemma primeGapCoverStep159_segment :
    CertifiedSegment primeGapCoverStep159 439 15937723 := by
  unfold primeGapCoverStep159
  exact primeGapCoverStep158_segment.append primeGapCertifiedGroup159_segment
    (by norm_num [GapStep])

private def primeGapCoverStep160 : List ℕ :=
  primeGapCoverStep159 ++ primeGapCertifiedGroup160

private lemma primeGapCoverStep160_segment :
    CertifiedSegment primeGapCoverStep160 439 16036547 := by
  unfold primeGapCoverStep160
  exact primeGapCoverStep159_segment.append primeGapCertifiedGroup160_segment
    (by norm_num [GapStep])

private def primeGapCoverStep161 : List ℕ :=
  primeGapCoverStep160 ++ primeGapCertifiedGroup161

private lemma primeGapCoverStep161_segment :
    CertifiedSegment primeGapCoverStep161 439 16135453 := by
  unfold primeGapCoverStep161
  exact primeGapCoverStep160_segment.append primeGapCertifiedGroup161_segment
    (by norm_num [GapStep])

private def primeGapCoverStep162 : List ℕ :=
  primeGapCoverStep161 ++ primeGapCertifiedGroup162

private lemma primeGapCoverStep162_segment :
    CertifiedSegment primeGapCoverStep162 439 16234633 := by
  unfold primeGapCoverStep162
  exact primeGapCoverStep161_segment.append primeGapCertifiedGroup162_segment
    (by norm_num [GapStep])

private def primeGapCoverStep163 : List ℕ :=
  primeGapCoverStep162 ++ primeGapCertifiedGroup163

private lemma primeGapCoverStep163_segment :
    CertifiedSegment primeGapCoverStep163 439 16333477 := by
  unfold primeGapCoverStep163
  exact primeGapCoverStep162_segment.append primeGapCertifiedGroup163_segment
    (by norm_num [GapStep])

private def primeGapCoverStep164 : List ℕ :=
  primeGapCoverStep163 ++ primeGapCertifiedGroup164

private lemma primeGapCoverStep164_segment :
    CertifiedSegment primeGapCoverStep164 439 16432501 := by
  unfold primeGapCoverStep164
  exact primeGapCoverStep163_segment.append primeGapCertifiedGroup164_segment
    (by norm_num [GapStep])

private def primeGapCoverStep165 : List ℕ :=
  primeGapCoverStep164 ++ primeGapCertifiedGroup165

private lemma primeGapCoverStep165_segment :
    CertifiedSegment primeGapCoverStep165 439 16531381 := by
  unfold primeGapCoverStep165
  exact primeGapCoverStep164_segment.append primeGapCertifiedGroup165_segment
    (by norm_num [GapStep])

private def primeGapCoverStep166 : List ℕ :=
  primeGapCoverStep165 ++ primeGapCertifiedGroup166

private lemma primeGapCoverStep166_segment :
    CertifiedSegment primeGapCoverStep166 439 16630177 := by
  unfold primeGapCoverStep166
  exact primeGapCoverStep165_segment.append primeGapCertifiedGroup166_segment
    (by norm_num [GapStep])

private def primeGapCoverStep167 : List ℕ :=
  primeGapCoverStep166 ++ primeGapCertifiedGroup167

private lemma primeGapCoverStep167_segment :
    CertifiedSegment primeGapCoverStep167 439 16729103 := by
  unfold primeGapCoverStep167
  exact primeGapCoverStep166_segment.append primeGapCertifiedGroup167_segment
    (by norm_num [GapStep])

private def primeGapCoverStep168 : List ℕ :=
  primeGapCoverStep167 ++ primeGapCertifiedGroup168

private lemma primeGapCoverStep168_segment :
    CertifiedSegment primeGapCoverStep168 439 16828067 := by
  unfold primeGapCoverStep168
  exact primeGapCoverStep167_segment.append primeGapCertifiedGroup168_segment
    (by norm_num [GapStep])

private def primeGapCoverStep169 : List ℕ :=
  primeGapCoverStep168 ++ primeGapCertifiedGroup169

private lemma primeGapCoverStep169_segment :
    CertifiedSegment primeGapCoverStep169 439 16927199 := by
  unfold primeGapCoverStep169
  exact primeGapCoverStep168_segment.append primeGapCertifiedGroup169_segment
    (by norm_num [GapStep])

private def primeGapCoverStep170 : List ℕ :=
  primeGapCoverStep169 ++ primeGapCertifiedGroup170

private lemma primeGapCoverStep170_segment :
    CertifiedSegment primeGapCoverStep170 439 17026391 := by
  unfold primeGapCoverStep170
  exact primeGapCoverStep169_segment.append primeGapCertifiedGroup170_segment
    (by norm_num [GapStep])

private def primeGapCoverStep171 : List ℕ :=
  primeGapCoverStep170 ++ primeGapCertifiedGroup171

private lemma primeGapCoverStep171_segment :
    CertifiedSegment primeGapCoverStep171 439 17125093 := by
  unfold primeGapCoverStep171
  exact primeGapCoverStep170_segment.append primeGapCertifiedGroup171_segment
    (by norm_num [GapStep])

private def primeGapCoverStep172 : List ℕ :=
  primeGapCoverStep171 ++ primeGapCertifiedGroup172

private lemma primeGapCoverStep172_segment :
    CertifiedSegment primeGapCoverStep172 439 17223473 := by
  unfold primeGapCoverStep172
  exact primeGapCoverStep171_segment.append primeGapCertifiedGroup172_segment
    (by norm_num [GapStep])

private def primeGapCoverStep173 : List ℕ :=
  primeGapCoverStep172 ++ primeGapCertifiedGroup173

private lemma primeGapCoverStep173_segment :
    CertifiedSegment primeGapCoverStep173 439 17322553 := by
  unfold primeGapCoverStep173
  exact primeGapCoverStep172_segment.append primeGapCertifiedGroup173_segment
    (by norm_num [GapStep])

private def primeGapCoverStep174 : List ℕ :=
  primeGapCoverStep173 ++ primeGapCertifiedGroup174

private lemma primeGapCoverStep174_segment :
    CertifiedSegment primeGapCoverStep174 439 17421449 := by
  unfold primeGapCoverStep174
  exact primeGapCoverStep173_segment.append primeGapCertifiedGroup174_segment
    (by norm_num [GapStep])

private def primeGapCoverStep175 : List ℕ :=
  primeGapCoverStep174 ++ primeGapCertifiedGroup175

private lemma primeGapCoverStep175_segment :
    CertifiedSegment primeGapCoverStep175 439 17520343 := by
  unfold primeGapCoverStep175
  exact primeGapCoverStep174_segment.append primeGapCertifiedGroup175_segment
    (by norm_num [GapStep])

private def primeGapCoverStep176 : List ℕ :=
  primeGapCoverStep175 ++ primeGapCertifiedGroup176

private lemma primeGapCoverStep176_segment :
    CertifiedSegment primeGapCoverStep176 439 17619079 := by
  unfold primeGapCoverStep176
  exact primeGapCoverStep175_segment.append primeGapCertifiedGroup176_segment
    (by norm_num [GapStep])

private def primeGapCoverStep177 : List ℕ :=
  primeGapCoverStep176 ++ primeGapCertifiedGroup177

private lemma primeGapCoverStep177_segment :
    CertifiedSegment primeGapCoverStep177 439 17717851 := by
  unfold primeGapCoverStep177
  exact primeGapCoverStep176_segment.append primeGapCertifiedGroup177_segment
    (by norm_num [GapStep])

private def primeGapCoverStep178 : List ℕ :=
  primeGapCoverStep177 ++ primeGapCertifiedGroup178

private lemma primeGapCoverStep178_segment :
    CertifiedSegment primeGapCoverStep178 439 17816801 := by
  unfold primeGapCoverStep178
  exact primeGapCoverStep177_segment.append primeGapCertifiedGroup178_segment
    (by norm_num [GapStep])

private def primeGapCoverStep179 : List ℕ :=
  primeGapCoverStep178 ++ primeGapCertifiedGroup179

private lemma primeGapCoverStep179_segment :
    CertifiedSegment primeGapCoverStep179 439 17915903 := by
  unfold primeGapCoverStep179
  exact primeGapCoverStep178_segment.append primeGapCertifiedGroup179_segment
    (by norm_num [GapStep])

private def primeGapCoverStep180 : List ℕ :=
  primeGapCoverStep179 ++ primeGapCertifiedGroup180

private lemma primeGapCoverStep180_segment :
    CertifiedSegment primeGapCoverStep180 439 18015407 := by
  unfold primeGapCoverStep180
  exact primeGapCoverStep179_segment.append primeGapCertifiedGroup180_segment
    (by norm_num [GapStep])

private def primeGapCoverStep181 : List ℕ :=
  primeGapCoverStep180 ++ primeGapCertifiedGroup181

private lemma primeGapCoverStep181_segment :
    CertifiedSegment primeGapCoverStep181 439 18114091 := by
  unfold primeGapCoverStep181
  exact primeGapCoverStep180_segment.append primeGapCertifiedGroup181_segment
    (by norm_num [GapStep])

private def primeGapCoverStep182 : List ℕ :=
  primeGapCoverStep181 ++ primeGapCertifiedGroup182

private lemma primeGapCoverStep182_segment :
    CertifiedSegment primeGapCoverStep182 439 18213029 := by
  unfold primeGapCoverStep182
  exact primeGapCoverStep181_segment.append primeGapCertifiedGroup182_segment
    (by norm_num [GapStep])

private def primeGapCoverStep183 : List ℕ :=
  primeGapCoverStep182 ++ primeGapCertifiedGroup183

private lemma primeGapCoverStep183_segment :
    CertifiedSegment primeGapCoverStep183 439 18312037 := by
  unfold primeGapCoverStep183
  exact primeGapCoverStep182_segment.append primeGapCertifiedGroup183_segment
    (by norm_num [GapStep])

private def primeGapCoverStep184 : List ℕ :=
  primeGapCoverStep183 ++ primeGapCertifiedGroup184

private lemma primeGapCoverStep184_segment :
    CertifiedSegment primeGapCoverStep184 439 18410989 := by
  unfold primeGapCoverStep184
  exact primeGapCoverStep183_segment.append primeGapCertifiedGroup184_segment
    (by norm_num [GapStep])

private def primeGapCoverStep185 : List ℕ :=
  primeGapCoverStep184 ++ primeGapCertifiedGroup185

private lemma primeGapCoverStep185_segment :
    CertifiedSegment primeGapCoverStep185 439 18509473 := by
  unfold primeGapCoverStep185
  exact primeGapCoverStep184_segment.append primeGapCertifiedGroup185_segment
    (by norm_num [GapStep])

private def primeGapCoverStep186 : List ℕ :=
  primeGapCoverStep185 ++ primeGapCertifiedGroup186

private lemma primeGapCoverStep186_segment :
    CertifiedSegment primeGapCoverStep186 439 18608753 := by
  unfold primeGapCoverStep186
  exact primeGapCoverStep185_segment.append primeGapCertifiedGroup186_segment
    (by norm_num [GapStep])

private def primeGapCoverStep187 : List ℕ :=
  primeGapCoverStep186 ++ primeGapCertifiedGroup187

private lemma primeGapCoverStep187_segment :
    CertifiedSegment primeGapCoverStep187 439 18708119 := by
  unfold primeGapCoverStep187
  exact primeGapCoverStep186_segment.append primeGapCertifiedGroup187_segment
    (by norm_num [GapStep])

private def primeGapCoverStep188 : List ℕ :=
  primeGapCoverStep187 ++ primeGapCertifiedGroup188

private lemma primeGapCoverStep188_segment :
    CertifiedSegment primeGapCoverStep188 439 18807247 := by
  unfold primeGapCoverStep188
  exact primeGapCoverStep187_segment.append primeGapCertifiedGroup188_segment
    (by norm_num [GapStep])

private def primeGapCoverStep189 : List ℕ :=
  primeGapCoverStep188 ++ primeGapCertifiedGroup189

private lemma primeGapCoverStep189_segment :
    CertifiedSegment primeGapCoverStep189 439 18905963 := by
  unfold primeGapCoverStep189
  exact primeGapCoverStep188_segment.append primeGapCertifiedGroup189_segment
    (by norm_num [GapStep])

private def primeGapCoverStep190 : List ℕ :=
  primeGapCoverStep189 ++ primeGapCertifiedGroup190

private lemma primeGapCoverStep190_segment :
    CertifiedSegment primeGapCoverStep190 439 19005433 := by
  unfold primeGapCoverStep190
  exact primeGapCoverStep189_segment.append primeGapCertifiedGroup190_segment
    (by norm_num [GapStep])

private def primeGapCoverStep191 : List ℕ :=
  primeGapCoverStep190 ++ primeGapCertifiedGroup191

private lemma primeGapCoverStep191_segment :
    CertifiedSegment primeGapCoverStep191 439 19104637 := by
  unfold primeGapCoverStep191
  exact primeGapCoverStep190_segment.append primeGapCertifiedGroup191_segment
    (by norm_num [GapStep])

private def primeGapCoverStep192 : List ℕ :=
  primeGapCoverStep191 ++ primeGapCertifiedGroup192

private lemma primeGapCoverStep192_segment :
    CertifiedSegment primeGapCoverStep192 439 19203941 := by
  unfold primeGapCoverStep192
  exact primeGapCoverStep191_segment.append primeGapCertifiedGroup192_segment
    (by norm_num [GapStep])

private def primeGapCoverStep193 : List ℕ :=
  primeGapCoverStep192 ++ primeGapCertifiedGroup193

private lemma primeGapCoverStep193_segment :
    CertifiedSegment primeGapCoverStep193 439 19303201 := by
  unfold primeGapCoverStep193
  exact primeGapCoverStep192_segment.append primeGapCertifiedGroup193_segment
    (by norm_num [GapStep])

private def primeGapCoverStep194 : List ℕ :=
  primeGapCoverStep193 ++ primeGapCertifiedGroup194

private lemma primeGapCoverStep194_segment :
    CertifiedSegment primeGapCoverStep194 439 19402199 := by
  unfold primeGapCoverStep194
  exact primeGapCoverStep193_segment.append primeGapCertifiedGroup194_segment
    (by norm_num [GapStep])

private def primeGapCoverStep195 : List ℕ :=
  primeGapCoverStep194 ++ primeGapCertifiedGroup195

private lemma primeGapCoverStep195_segment :
    CertifiedSegment primeGapCoverStep195 439 19501019 := by
  unfold primeGapCoverStep195
  exact primeGapCoverStep194_segment.append primeGapCertifiedGroup195_segment
    (by norm_num [GapStep])

private def primeGapCoverStep196 : List ℕ :=
  primeGapCoverStep195 ++ primeGapCertifiedGroup196

private lemma primeGapCoverStep196_segment :
    CertifiedSegment primeGapCoverStep196 439 19600171 := by
  unfold primeGapCoverStep196
  exact primeGapCoverStep195_segment.append primeGapCertifiedGroup196_segment
    (by norm_num [GapStep])

private def primeGapCoverStep197 : List ℕ :=
  primeGapCoverStep196 ++ primeGapCertifiedGroup197

private lemma primeGapCoverStep197_segment :
    CertifiedSegment primeGapCoverStep197 439 19699657 := by
  unfold primeGapCoverStep197
  exact primeGapCoverStep196_segment.append primeGapCertifiedGroup197_segment
    (by norm_num [GapStep])

private def primeGapCoverStep198 : List ℕ :=
  primeGapCoverStep197 ++ primeGapCertifiedGroup198

private lemma primeGapCoverStep198_segment :
    CertifiedSegment primeGapCoverStep198 439 19798687 := by
  unfold primeGapCoverStep198
  exact primeGapCoverStep197_segment.append primeGapCertifiedGroup198_segment
    (by norm_num [GapStep])

private def primeGapCoverStep199 : List ℕ :=
  primeGapCoverStep198 ++ primeGapCertifiedGroup199

private lemma primeGapCoverStep199_segment :
    CertifiedSegment primeGapCoverStep199 439 19897987 := by
  unfold primeGapCoverStep199
  exact primeGapCoverStep198_segment.append primeGapCertifiedGroup199_segment
    (by norm_num [GapStep])

private def primeGapCoverStep200 : List ℕ :=
  primeGapCoverStep199 ++ primeGapCertifiedGroup200

private lemma primeGapCoverStep200_segment :
    CertifiedSegment primeGapCoverStep200 439 19997357 := by
  unfold primeGapCoverStep200
  exact primeGapCoverStep199_segment.append primeGapCertifiedGroup200_segment
    (by norm_num [GapStep])

private def primeGapCoverStep201 : List ℕ :=
  primeGapCoverStep200 ++ primeGapCertifiedGroup201

private lemma primeGapCoverStep201_segment :
    CertifiedSegment primeGapCoverStep201 439 20096081 := by
  unfold primeGapCoverStep201
  exact primeGapCoverStep200_segment.append primeGapCertifiedGroup201_segment
    (by norm_num [GapStep])

private def primeGapCoverStep202 : List ℕ :=
  primeGapCoverStep201 ++ primeGapCertifiedGroup202

private lemma primeGapCoverStep202_segment :
    CertifiedSegment primeGapCoverStep202 439 20195579 := by
  unfold primeGapCoverStep202
  exact primeGapCoverStep201_segment.append primeGapCertifiedGroup202_segment
    (by norm_num [GapStep])

private def primeGapCoverStep203 : List ℕ :=
  primeGapCoverStep202 ++ primeGapCertifiedGroup203

private lemma primeGapCoverStep203_segment :
    CertifiedSegment primeGapCoverStep203 439 20294333 := by
  unfold primeGapCoverStep203
  exact primeGapCoverStep202_segment.append primeGapCertifiedGroup203_segment
    (by norm_num [GapStep])

private def primeGapCoverStep204 : List ℕ :=
  primeGapCoverStep203 ++ primeGapCertifiedGroup204

private lemma primeGapCoverStep204_segment :
    CertifiedSegment primeGapCoverStep204 439 20392781 := by
  unfold primeGapCoverStep204
  exact primeGapCoverStep203_segment.append primeGapCertifiedGroup204_segment
    (by norm_num [GapStep])

private def primeGapCoverStep205 : List ℕ :=
  primeGapCoverStep204 ++ primeGapCertifiedGroup205

private lemma primeGapCoverStep205_segment :
    CertifiedSegment primeGapCoverStep205 439 20491561 := by
  unfold primeGapCoverStep205
  exact primeGapCoverStep204_segment.append primeGapCertifiedGroup205_segment
    (by norm_num [GapStep])

private def primeGapCoverStep206 : List ℕ :=
  primeGapCoverStep205 ++ primeGapCertifiedGroup206

private lemma primeGapCoverStep206_segment :
    CertifiedSegment primeGapCoverStep206 439 20590793 := by
  unfold primeGapCoverStep206
  exact primeGapCoverStep205_segment.append primeGapCertifiedGroup206_segment
    (by norm_num [GapStep])

private def primeGapCoverStep207 : List ℕ :=
  primeGapCoverStep206 ++ primeGapCertifiedGroup207

private lemma primeGapCoverStep207_segment :
    CertifiedSegment primeGapCoverStep207 439 20689709 := by
  unfold primeGapCoverStep207
  exact primeGapCoverStep206_segment.append primeGapCertifiedGroup207_segment
    (by norm_num [GapStep])

private def primeGapCoverStep208 : List ℕ :=
  primeGapCoverStep207 ++ primeGapCertifiedGroup208

private lemma primeGapCoverStep208_segment :
    CertifiedSegment primeGapCoverStep208 439 20788657 := by
  unfold primeGapCoverStep208
  exact primeGapCoverStep207_segment.append primeGapCertifiedGroup208_segment
    (by norm_num [GapStep])

private def primeGapCoverStep209 : List ℕ :=
  primeGapCoverStep208 ++ primeGapCertifiedGroup209

private lemma primeGapCoverStep209_segment :
    CertifiedSegment primeGapCoverStep209 439 20887687 := by
  unfold primeGapCoverStep209
  exact primeGapCoverStep208_segment.append primeGapCertifiedGroup209_segment
    (by norm_num [GapStep])

private def primeGapCoverStep210 : List ℕ :=
  primeGapCoverStep209 ++ primeGapCertifiedGroup210

private lemma primeGapCoverStep210_segment :
    CertifiedSegment primeGapCoverStep210 439 20986447 := by
  unfold primeGapCoverStep210
  exact primeGapCoverStep209_segment.append primeGapCertifiedGroup210_segment
    (by norm_num [GapStep])

private def primeGapCoverStep211 : List ℕ :=
  primeGapCoverStep210 ++ primeGapCertifiedGroup211

private lemma primeGapCoverStep211_segment :
    CertifiedSegment primeGapCoverStep211 439 21085643 := by
  unfold primeGapCoverStep211
  exact primeGapCoverStep210_segment.append primeGapCertifiedGroup211_segment
    (by norm_num [GapStep])

private def primeGapCoverStep212 : List ℕ :=
  primeGapCoverStep211 ++ primeGapCertifiedGroup212

private lemma primeGapCoverStep212_segment :
    CertifiedSegment primeGapCoverStep212 439 21184469 := by
  unfold primeGapCoverStep212
  exact primeGapCoverStep211_segment.append primeGapCertifiedGroup212_segment
    (by norm_num [GapStep])

private def primeGapCoverStep213 : List ℕ :=
  primeGapCoverStep212 ++ primeGapCertifiedGroup213

private lemma primeGapCoverStep213_segment :
    CertifiedSegment primeGapCoverStep213 439 21283127 := by
  unfold primeGapCoverStep213
  exact primeGapCoverStep212_segment.append primeGapCertifiedGroup213_segment
    (by norm_num [GapStep])

private def primeGapCoverStep214 : List ℕ :=
  primeGapCoverStep213 ++ primeGapCertifiedGroup214

private lemma primeGapCoverStep214_segment :
    CertifiedSegment primeGapCoverStep214 439 21381931 := by
  unfold primeGapCoverStep214
  exact primeGapCoverStep213_segment.append primeGapCertifiedGroup214_segment
    (by norm_num [GapStep])

private def primeGapCoverStep215 : List ℕ :=
  primeGapCoverStep214 ++ primeGapCertifiedGroup215

private lemma primeGapCoverStep215_segment :
    CertifiedSegment primeGapCoverStep215 439 21480353 := by
  unfold primeGapCoverStep215
  exact primeGapCoverStep214_segment.append primeGapCertifiedGroup215_segment
    (by norm_num [GapStep])

private def primeGapCoverStep216 : List ℕ :=
  primeGapCoverStep215 ++ primeGapCertifiedGroup216

private lemma primeGapCoverStep216_segment :
    CertifiedSegment primeGapCoverStep216 439 21579167 := by
  unfold primeGapCoverStep216
  exact primeGapCoverStep215_segment.append primeGapCertifiedGroup216_segment
    (by norm_num [GapStep])

private def primeGapCoverStep217 : List ℕ :=
  primeGapCoverStep216 ++ primeGapCertifiedGroup217

private lemma primeGapCoverStep217_segment :
    CertifiedSegment primeGapCoverStep217 439 21678143 := by
  unfold primeGapCoverStep217
  exact primeGapCoverStep216_segment.append primeGapCertifiedGroup217_segment
    (by norm_num [GapStep])

private def primeGapCoverStep218 : List ℕ :=
  primeGapCoverStep217 ++ primeGapCertifiedGroup218

private lemma primeGapCoverStep218_segment :
    CertifiedSegment primeGapCoverStep218 439 21776969 := by
  unfold primeGapCoverStep218
  exact primeGapCoverStep217_segment.append primeGapCertifiedGroup218_segment
    (by norm_num [GapStep])

private def primeGapCoverStep219 : List ℕ :=
  primeGapCoverStep218 ++ primeGapCertifiedGroup219

private lemma primeGapCoverStep219_segment :
    CertifiedSegment primeGapCoverStep219 439 21876053 := by
  unfold primeGapCoverStep219
  exact primeGapCoverStep218_segment.append primeGapCertifiedGroup219_segment
    (by norm_num [GapStep])

private def primeGapCoverStep220 : List ℕ :=
  primeGapCoverStep219 ++ primeGapCertifiedGroup220

private lemma primeGapCoverStep220_segment :
    CertifiedSegment primeGapCoverStep220 439 21975091 := by
  unfold primeGapCoverStep220
  exact primeGapCoverStep219_segment.append primeGapCertifiedGroup220_segment
    (by norm_num [GapStep])

private def primeGapCoverStep221 : List ℕ :=
  primeGapCoverStep220 ++ primeGapCertifiedGroup221

private lemma primeGapCoverStep221_segment :
    CertifiedSegment primeGapCoverStep221 439 22074049 := by
  unfold primeGapCoverStep221
  exact primeGapCoverStep220_segment.append primeGapCertifiedGroup221_segment
    (by norm_num [GapStep])

private def primeGapCoverStep222 : List ℕ :=
  primeGapCoverStep221 ++ primeGapCertifiedGroup222

private lemma primeGapCoverStep222_segment :
    CertifiedSegment primeGapCoverStep222 439 22173421 := by
  unfold primeGapCoverStep222
  exact primeGapCoverStep221_segment.append primeGapCertifiedGroup222_segment
    (by norm_num [GapStep])

private def primeGapCoverStep223 : List ℕ :=
  primeGapCoverStep222 ++ primeGapCertifiedGroup223

private lemma primeGapCoverStep223_segment :
    CertifiedSegment primeGapCoverStep223 439 22272013 := by
  unfold primeGapCoverStep223
  exact primeGapCoverStep222_segment.append primeGapCertifiedGroup223_segment
    (by norm_num [GapStep])

private def primeGapCoverStep224 : List ℕ :=
  primeGapCoverStep223 ++ primeGapCertifiedGroup224

private lemma primeGapCoverStep224_segment :
    CertifiedSegment primeGapCoverStep224 439 22370969 := by
  unfold primeGapCoverStep224
  exact primeGapCoverStep223_segment.append primeGapCertifiedGroup224_segment
    (by norm_num [GapStep])

private def primeGapCoverStep225 : List ℕ :=
  primeGapCoverStep224 ++ primeGapCertifiedGroup225

private lemma primeGapCoverStep225_segment :
    CertifiedSegment primeGapCoverStep225 439 22469939 := by
  unfold primeGapCoverStep225
  exact primeGapCoverStep224_segment.append primeGapCertifiedGroup225_segment
    (by norm_num [GapStep])

private def primeGapCoverStep226 : List ℕ :=
  primeGapCoverStep225 ++ primeGapCertifiedGroup226

private lemma primeGapCoverStep226_segment :
    CertifiedSegment primeGapCoverStep226 439 22568659 := by
  unfold primeGapCoverStep226
  exact primeGapCoverStep225_segment.append primeGapCertifiedGroup226_segment
    (by norm_num [GapStep])

private def primeGapCoverStep227 : List ℕ :=
  primeGapCoverStep226 ++ primeGapCertifiedGroup227

private lemma primeGapCoverStep227_segment :
    CertifiedSegment primeGapCoverStep227 439 22667363 := by
  unfold primeGapCoverStep227
  exact primeGapCoverStep226_segment.append primeGapCertifiedGroup227_segment
    (by norm_num [GapStep])

private def primeGapCoverStep228 : List ℕ :=
  primeGapCoverStep227 ++ primeGapCertifiedGroup228

private lemma primeGapCoverStep228_segment :
    CertifiedSegment primeGapCoverStep228 439 22766053 := by
  unfold primeGapCoverStep228
  exact primeGapCoverStep227_segment.append primeGapCertifiedGroup228_segment
    (by norm_num [GapStep])

private def primeGapCoverStep229 : List ℕ :=
  primeGapCoverStep228 ++ primeGapCertifiedGroup229

private lemma primeGapCoverStep229_segment :
    CertifiedSegment primeGapCoverStep229 439 22864739 := by
  unfold primeGapCoverStep229
  exact primeGapCoverStep228_segment.append primeGapCertifiedGroup229_segment
    (by norm_num [GapStep])

private def primeGapCoverStep230 : List ℕ :=
  primeGapCoverStep229 ++ primeGapCertifiedGroup230

private lemma primeGapCoverStep230_segment :
    CertifiedSegment primeGapCoverStep230 439 22963561 := by
  unfold primeGapCoverStep230
  exact primeGapCoverStep229_segment.append primeGapCertifiedGroup230_segment
    (by norm_num [GapStep])

private def primeGapCoverStep231 : List ℕ :=
  primeGapCoverStep230 ++ primeGapCertifiedGroup231

private lemma primeGapCoverStep231_segment :
    CertifiedSegment primeGapCoverStep231 439 23062159 := by
  unfold primeGapCoverStep231
  exact primeGapCoverStep230_segment.append primeGapCertifiedGroup231_segment
    (by norm_num [GapStep])

private def primeGapCoverStep232 : List ℕ :=
  primeGapCoverStep231 ++ primeGapCertifiedGroup232

private lemma primeGapCoverStep232_segment :
    CertifiedSegment primeGapCoverStep232 439 23160679 := by
  unfold primeGapCoverStep232
  exact primeGapCoverStep231_segment.append primeGapCertifiedGroup232_segment
    (by norm_num [GapStep])

private def primeGapCoverStep233 : List ℕ :=
  primeGapCoverStep232 ++ primeGapCertifiedGroup233

private lemma primeGapCoverStep233_segment :
    CertifiedSegment primeGapCoverStep233 439 23259437 := by
  unfold primeGapCoverStep233
  exact primeGapCoverStep232_segment.append primeGapCertifiedGroup233_segment
    (by norm_num [GapStep])

private def primeGapCoverStep234 : List ℕ :=
  primeGapCoverStep233 ++ primeGapCertifiedGroup234

private lemma primeGapCoverStep234_segment :
    CertifiedSegment primeGapCoverStep234 439 23357951 := by
  unfold primeGapCoverStep234
  exact primeGapCoverStep233_segment.append primeGapCertifiedGroup234_segment
    (by norm_num [GapStep])

private def primeGapCoverStep235 : List ℕ :=
  primeGapCoverStep234 ++ primeGapCertifiedGroup235

private lemma primeGapCoverStep235_segment :
    CertifiedSegment primeGapCoverStep235 439 23457113 := by
  unfold primeGapCoverStep235
  exact primeGapCoverStep234_segment.append primeGapCertifiedGroup235_segment
    (by norm_num [GapStep])

private def primeGapCoverStep236 : List ℕ :=
  primeGapCoverStep235 ++ primeGapCertifiedGroup236

private lemma primeGapCoverStep236_segment :
    CertifiedSegment primeGapCoverStep236 439 23556139 := by
  unfold primeGapCoverStep236
  exact primeGapCoverStep235_segment.append primeGapCertifiedGroup236_segment
    (by norm_num [GapStep])

private def primeGapCoverStep237 : List ℕ :=
  primeGapCoverStep236 ++ primeGapCertifiedGroup237

private lemma primeGapCoverStep237_segment :
    CertifiedSegment primeGapCoverStep237 439 23654863 := by
  unfold primeGapCoverStep237
  exact primeGapCoverStep236_segment.append primeGapCertifiedGroup237_segment
    (by norm_num [GapStep])

private def primeGapCoverStep238 : List ℕ :=
  primeGapCoverStep237 ++ primeGapCertifiedGroup238

private lemma primeGapCoverStep238_segment :
    CertifiedSegment primeGapCoverStep238 439 23753713 := by
  unfold primeGapCoverStep238
  exact primeGapCoverStep237_segment.append primeGapCertifiedGroup238_segment
    (by norm_num [GapStep])

private def primeGapCoverStep239 : List ℕ :=
  primeGapCoverStep238 ++ primeGapCertifiedGroup239

private lemma primeGapCoverStep239_segment :
    CertifiedSegment primeGapCoverStep239 439 23852911 := by
  unfold primeGapCoverStep239
  exact primeGapCoverStep238_segment.append primeGapCertifiedGroup239_segment
    (by norm_num [GapStep])

private def primeGapCoverStep240 : List ℕ :=
  primeGapCoverStep239 ++ primeGapCertifiedGroup240

private lemma primeGapCoverStep240_segment :
    CertifiedSegment primeGapCoverStep240 439 23951821 := by
  unfold primeGapCoverStep240
  exact primeGapCoverStep239_segment.append primeGapCertifiedGroup240_segment
    (by norm_num [GapStep])

private def primeGapCoverStep241 : List ℕ :=
  primeGapCoverStep240 ++ primeGapCertifiedGroup241

private lemma primeGapCoverStep241_segment :
    CertifiedSegment primeGapCoverStep241 439 24051119 := by
  unfold primeGapCoverStep241
  exact primeGapCoverStep240_segment.append primeGapCertifiedGroup241_segment
    (by norm_num [GapStep])

private def primeGapCoverStep242 : List ℕ :=
  primeGapCoverStep241 ++ primeGapCertifiedGroup242

private lemma primeGapCoverStep242_segment :
    CertifiedSegment primeGapCoverStep242 439 24150811 := by
  unfold primeGapCoverStep242
  exact primeGapCoverStep241_segment.append primeGapCertifiedGroup242_segment
    (by norm_num [GapStep])

private def primeGapCoverStep243 : List ℕ :=
  primeGapCoverStep242 ++ primeGapCertifiedGroup243

private lemma primeGapCoverStep243_segment :
    CertifiedSegment primeGapCoverStep243 439 24250141 := by
  unfold primeGapCoverStep243
  exact primeGapCoverStep242_segment.append primeGapCertifiedGroup243_segment
    (by norm_num [GapStep])

private def primeGapCoverStep244 : List ℕ :=
  primeGapCoverStep243 ++ primeGapCertifiedGroup244

private lemma primeGapCoverStep244_segment :
    CertifiedSegment primeGapCoverStep244 439 24348851 := by
  unfold primeGapCoverStep244
  exact primeGapCoverStep243_segment.append primeGapCertifiedGroup244_segment
    (by norm_num [GapStep])

private def primeGapCoverStep245 : List ℕ :=
  primeGapCoverStep244 ++ primeGapCertifiedGroup245

private lemma primeGapCoverStep245_segment :
    CertifiedSegment primeGapCoverStep245 439 24447911 := by
  unfold primeGapCoverStep245
  exact primeGapCoverStep244_segment.append primeGapCertifiedGroup245_segment
    (by norm_num [GapStep])

private def primeGapCoverStep246 : List ℕ :=
  primeGapCoverStep245 ++ primeGapCertifiedGroup246

private lemma primeGapCoverStep246_segment :
    CertifiedSegment primeGapCoverStep246 439 24546751 := by
  unfold primeGapCoverStep246
  exact primeGapCoverStep245_segment.append primeGapCertifiedGroup246_segment
    (by norm_num [GapStep])

private def primeGapCoverStep247 : List ℕ :=
  primeGapCoverStep246 ++ primeGapCertifiedGroup247

private lemma primeGapCoverStep247_segment :
    CertifiedSegment primeGapCoverStep247 439 24645661 := by
  unfold primeGapCoverStep247
  exact primeGapCoverStep246_segment.append primeGapCertifiedGroup247_segment
    (by norm_num [GapStep])

private def primeGapCoverStep248 : List ℕ :=
  primeGapCoverStep247 ++ primeGapCertifiedGroup248

private lemma primeGapCoverStep248_segment :
    CertifiedSegment primeGapCoverStep248 439 24745103 := by
  unfold primeGapCoverStep248
  exact primeGapCoverStep247_segment.append primeGapCertifiedGroup248_segment
    (by norm_num [GapStep])

private def primeGapCoverStep249 : List ℕ :=
  primeGapCoverStep248 ++ primeGapCertifiedGroup249

private lemma primeGapCoverStep249_segment :
    CertifiedSegment primeGapCoverStep249 439 24843913 := by
  unfold primeGapCoverStep249
  exact primeGapCoverStep248_segment.append primeGapCertifiedGroup249_segment
    (by norm_num [GapStep])

private def primeGapCoverStep250 : List ℕ :=
  primeGapCoverStep249 ++ primeGapCertifiedGroup250

private lemma primeGapCoverStep250_segment :
    CertifiedSegment primeGapCoverStep250 439 24942539 := by
  unfold primeGapCoverStep250
  exact primeGapCoverStep249_segment.append primeGapCertifiedGroup250_segment
    (by norm_num [GapStep])

private def primeGapCoverStep251 : List ℕ :=
  primeGapCoverStep250 ++ primeGapCertifiedGroup251

private lemma primeGapCoverStep251_segment :
    CertifiedSegment primeGapCoverStep251 439 25040621 := by
  unfold primeGapCoverStep251
  exact primeGapCoverStep250_segment.append primeGapCertifiedGroup251_segment
    (by norm_num [GapStep])

private def primeGapCoverStep252 : List ℕ :=
  primeGapCoverStep251 ++ primeGapCertifiedGroup252

private lemma primeGapCoverStep252_segment :
    CertifiedSegment primeGapCoverStep252 439 25139453 := by
  unfold primeGapCoverStep252
  exact primeGapCoverStep251_segment.append primeGapCertifiedGroup252_segment
    (by norm_num [GapStep])

private def primeGapCoverStep253 : List ℕ :=
  primeGapCoverStep252 ++ primeGapCertifiedGroup253

private lemma primeGapCoverStep253_segment :
    CertifiedSegment primeGapCoverStep253 439 25237753 := by
  unfold primeGapCoverStep253
  exact primeGapCoverStep252_segment.append primeGapCertifiedGroup253_segment
    (by norm_num [GapStep])

private def primeGapCoverStep254 : List ℕ :=
  primeGapCoverStep253 ++ primeGapCertifiedGroup254

private lemma primeGapCoverStep254_segment :
    CertifiedSegment primeGapCoverStep254 439 25336361 := by
  unfold primeGapCoverStep254
  exact primeGapCoverStep253_segment.append primeGapCertifiedGroup254_segment
    (by norm_num [GapStep])

private def primeGapCoverStep255 : List ℕ :=
  primeGapCoverStep254 ++ primeGapCertifiedGroup255

private lemma primeGapCoverStep255_segment :
    CertifiedSegment primeGapCoverStep255 439 25435373 := by
  unfold primeGapCoverStep255
  exact primeGapCoverStep254_segment.append primeGapCertifiedGroup255_segment
    (by norm_num [GapStep])

private def primeGapCoverStep256 : List ℕ :=
  primeGapCoverStep255 ++ primeGapCertifiedGroup256

private lemma primeGapCoverStep256_segment :
    CertifiedSegment primeGapCoverStep256 439 25534721 := by
  unfold primeGapCoverStep256
  exact primeGapCoverStep255_segment.append primeGapCertifiedGroup256_segment
    (by norm_num [GapStep])

private def primeGapCoverStep257 : List ℕ :=
  primeGapCoverStep256 ++ primeGapCertifiedGroup257

private lemma primeGapCoverStep257_segment :
    CertifiedSegment primeGapCoverStep257 439 25632947 := by
  unfold primeGapCoverStep257
  exact primeGapCoverStep256_segment.append primeGapCertifiedGroup257_segment
    (by norm_num [GapStep])

private def primeGapCoverStep258 : List ℕ :=
  primeGapCoverStep257 ++ primeGapCertifiedGroup258

private lemma primeGapCoverStep258_segment :
    CertifiedSegment primeGapCoverStep258 439 25732313 := by
  unfold primeGapCoverStep258
  exact primeGapCoverStep257_segment.append primeGapCertifiedGroup258_segment
    (by norm_num [GapStep])

private def primeGapCoverStep259 : List ℕ :=
  primeGapCoverStep258 ++ primeGapCertifiedGroup259

private lemma primeGapCoverStep259_segment :
    CertifiedSegment primeGapCoverStep259 439 25831229 := by
  unfold primeGapCoverStep259
  exact primeGapCoverStep258_segment.append primeGapCertifiedGroup259_segment
    (by norm_num [GapStep])

private def primeGapCoverStep260 : List ℕ :=
  primeGapCoverStep259 ++ primeGapCertifiedGroup260

private lemma primeGapCoverStep260_segment :
    CertifiedSegment primeGapCoverStep260 439 25930979 := by
  unfold primeGapCoverStep260
  exact primeGapCoverStep259_segment.append primeGapCertifiedGroup260_segment
    (by norm_num [GapStep])

private def primeGapCoverStep261 : List ℕ :=
  primeGapCoverStep260 ++ primeGapCertifiedGroup261

private lemma primeGapCoverStep261_segment :
    CertifiedSegment primeGapCoverStep261 439 26029459 := by
  unfold primeGapCoverStep261
  exact primeGapCoverStep260_segment.append primeGapCertifiedGroup261_segment
    (by norm_num [GapStep])

private def primeGapCoverStep262 : List ℕ :=
  primeGapCoverStep261 ++ primeGapCertifiedGroup262

private lemma primeGapCoverStep262_segment :
    CertifiedSegment primeGapCoverStep262 439 26128831 := by
  unfold primeGapCoverStep262
  exact primeGapCoverStep261_segment.append primeGapCertifiedGroup262_segment
    (by norm_num [GapStep])

private def primeGapCoverStep263 : List ℕ :=
  primeGapCoverStep262 ++ primeGapCertifiedGroup263

private lemma primeGapCoverStep263_segment :
    CertifiedSegment primeGapCoverStep263 439 26227813 := by
  unfold primeGapCoverStep263
  exact primeGapCoverStep262_segment.append primeGapCertifiedGroup263_segment
    (by norm_num [GapStep])

private def primeGapCoverStep264 : List ℕ :=
  primeGapCoverStep263 ++ primeGapCertifiedGroup264

private lemma primeGapCoverStep264_segment :
    CertifiedSegment primeGapCoverStep264 439 26326691 := by
  unfold primeGapCoverStep264
  exact primeGapCoverStep263_segment.append primeGapCertifiedGroup264_segment
    (by norm_num [GapStep])

private def primeGapCoverStep265 : List ℕ :=
  primeGapCoverStep264 ++ primeGapCertifiedGroup265

private lemma primeGapCoverStep265_segment :
    CertifiedSegment primeGapCoverStep265 439 26425381 := by
  unfold primeGapCoverStep265
  exact primeGapCoverStep264_segment.append primeGapCertifiedGroup265_segment
    (by norm_num [GapStep])

private def primeGapCoverStep266 : List ℕ :=
  primeGapCoverStep265 ++ primeGapCertifiedGroup266

private lemma primeGapCoverStep266_segment :
    CertifiedSegment primeGapCoverStep266 439 26524439 := by
  unfold primeGapCoverStep266
  exact primeGapCoverStep265_segment.append primeGapCertifiedGroup266_segment
    (by norm_num [GapStep])

private def primeGapCoverStep267 : List ℕ :=
  primeGapCoverStep266 ++ primeGapCertifiedGroup267

private lemma primeGapCoverStep267_segment :
    CertifiedSegment primeGapCoverStep267 439 26623271 := by
  unfold primeGapCoverStep267
  exact primeGapCoverStep266_segment.append primeGapCertifiedGroup267_segment
    (by norm_num [GapStep])

private def primeGapCoverStep268 : List ℕ :=
  primeGapCoverStep267 ++ primeGapCertifiedGroup268

private lemma primeGapCoverStep268_segment :
    CertifiedSegment primeGapCoverStep268 439 26722309 := by
  unfold primeGapCoverStep268
  exact primeGapCoverStep267_segment.append primeGapCertifiedGroup268_segment
    (by norm_num [GapStep])

private def primeGapCoverStep269 : List ℕ :=
  primeGapCoverStep268 ++ primeGapCertifiedGroup269

private lemma primeGapCoverStep269_segment :
    CertifiedSegment primeGapCoverStep269 439 26820821 := by
  unfold primeGapCoverStep269
  exact primeGapCoverStep268_segment.append primeGapCertifiedGroup269_segment
    (by norm_num [GapStep])

private def primeGapCoverStep270 : List ℕ :=
  primeGapCoverStep269 ++ primeGapCertifiedGroup270

private lemma primeGapCoverStep270_segment :
    CertifiedSegment primeGapCoverStep270 439 26919341 := by
  unfold primeGapCoverStep270
  exact primeGapCoverStep269_segment.append primeGapCertifiedGroup270_segment
    (by norm_num [GapStep])

private def primeGapCoverStep271 : List ℕ :=
  primeGapCoverStep270 ++ primeGapCertifiedGroup271

private lemma primeGapCoverStep271_segment :
    CertifiedSegment primeGapCoverStep271 439 27017953 := by
  unfold primeGapCoverStep271
  exact primeGapCoverStep270_segment.append primeGapCertifiedGroup271_segment
    (by norm_num [GapStep])

private def primeGapCoverStep272 : List ℕ :=
  primeGapCoverStep271 ++ primeGapCertifiedGroup272

private lemma primeGapCoverStep272_segment :
    CertifiedSegment primeGapCoverStep272 439 27116899 := by
  unfold primeGapCoverStep272
  exact primeGapCoverStep271_segment.append primeGapCertifiedGroup272_segment
    (by norm_num [GapStep])

private def primeGapCoverStep273 : List ℕ :=
  primeGapCoverStep272 ++ primeGapCertifiedGroup273

private lemma primeGapCoverStep273_segment :
    CertifiedSegment primeGapCoverStep273 439 27216403 := by
  unfold primeGapCoverStep273
  exact primeGapCoverStep272_segment.append primeGapCertifiedGroup273_segment
    (by norm_num [GapStep])

private def primeGapCoverStep274 : List ℕ :=
  primeGapCoverStep273 ++ primeGapCertifiedGroup274

private lemma primeGapCoverStep274_segment :
    CertifiedSegment primeGapCoverStep274 439 27315271 := by
  unfold primeGapCoverStep274
  exact primeGapCoverStep273_segment.append primeGapCertifiedGroup274_segment
    (by norm_num [GapStep])

private def primeGapCoverStep275 : List ℕ :=
  primeGapCoverStep274 ++ primeGapCertifiedGroup275

private lemma primeGapCoverStep275_segment :
    CertifiedSegment primeGapCoverStep275 439 27413807 := by
  unfold primeGapCoverStep275
  exact primeGapCoverStep274_segment.append primeGapCertifiedGroup275_segment
    (by norm_num [GapStep])

private def primeGapCoverStep276 : List ℕ :=
  primeGapCoverStep275 ++ primeGapCertifiedGroup276

private lemma primeGapCoverStep276_segment :
    CertifiedSegment primeGapCoverStep276 439 27513169 := by
  unfold primeGapCoverStep276
  exact primeGapCoverStep275_segment.append primeGapCertifiedGroup276_segment
    (by norm_num [GapStep])

private def primeGapCoverStep277 : List ℕ :=
  primeGapCoverStep276 ++ primeGapCertifiedGroup277

private lemma primeGapCoverStep277_segment :
    CertifiedSegment primeGapCoverStep277 439 27611531 := by
  unfold primeGapCoverStep277
  exact primeGapCoverStep276_segment.append primeGapCertifiedGroup277_segment
    (by norm_num [GapStep])

private def primeGapCoverStep278 : List ℕ :=
  primeGapCoverStep277 ++ primeGapCertifiedGroup278

private lemma primeGapCoverStep278_segment :
    CertifiedSegment primeGapCoverStep278 439 27710279 := by
  unfold primeGapCoverStep278
  exact primeGapCoverStep277_segment.append primeGapCertifiedGroup278_segment
    (by norm_num [GapStep])

private def primeGapCoverStep279 : List ℕ :=
  primeGapCoverStep278 ++ primeGapCertifiedGroup279

private lemma primeGapCoverStep279_segment :
    CertifiedSegment primeGapCoverStep279 439 27808789 := by
  unfold primeGapCoverStep279
  exact primeGapCoverStep278_segment.append primeGapCertifiedGroup279_segment
    (by norm_num [GapStep])

private def primeGapCoverStep280 : List ℕ :=
  primeGapCoverStep279 ++ primeGapCertifiedGroup280

private lemma primeGapCoverStep280_segment :
    CertifiedSegment primeGapCoverStep280 439 27907357 := by
  unfold primeGapCoverStep280
  exact primeGapCoverStep279_segment.append primeGapCertifiedGroup280_segment
    (by norm_num [GapStep])

private def primeGapCoverStep281 : List ℕ :=
  primeGapCoverStep280 ++ primeGapCertifiedGroup281

private lemma primeGapCoverStep281_segment :
    CertifiedSegment primeGapCoverStep281 439 28006243 := by
  unfold primeGapCoverStep281
  exact primeGapCoverStep280_segment.append primeGapCertifiedGroup281_segment
    (by norm_num [GapStep])

private def primeGapCoverStep282 : List ℕ :=
  primeGapCoverStep281 ++ primeGapCertifiedGroup282

private lemma primeGapCoverStep282_segment :
    CertifiedSegment primeGapCoverStep282 439 28104841 := by
  unfold primeGapCoverStep282
  exact primeGapCoverStep281_segment.append primeGapCertifiedGroup282_segment
    (by norm_num [GapStep])

private def primeGapCoverStep283 : List ℕ :=
  primeGapCoverStep282 ++ primeGapCertifiedGroup283

private lemma primeGapCoverStep283_segment :
    CertifiedSegment primeGapCoverStep283 439 28204093 := by
  unfold primeGapCoverStep283
  exact primeGapCoverStep282_segment.append primeGapCertifiedGroup283_segment
    (by norm_num [GapStep])

private def primeGapCoverStep284 : List ℕ :=
  primeGapCoverStep283 ++ primeGapCertifiedGroup284

private lemma primeGapCoverStep284_segment :
    CertifiedSegment primeGapCoverStep284 439 28303229 := by
  unfold primeGapCoverStep284
  exact primeGapCoverStep283_segment.append primeGapCertifiedGroup284_segment
    (by norm_num [GapStep])

private def primeGapCoverStep285 : List ℕ :=
  primeGapCoverStep284 ++ primeGapCertifiedGroup285

private lemma primeGapCoverStep285_segment :
    CertifiedSegment primeGapCoverStep285 439 28402141 := by
  unfold primeGapCoverStep285
  exact primeGapCoverStep284_segment.append primeGapCertifiedGroup285_segment
    (by norm_num [GapStep])

private def primeGapCoverStep286 : List ℕ :=
  primeGapCoverStep285 ++ primeGapCertifiedGroup286

private lemma primeGapCoverStep286_segment :
    CertifiedSegment primeGapCoverStep286 439 28501337 := by
  unfold primeGapCoverStep286
  exact primeGapCoverStep285_segment.append primeGapCertifiedGroup286_segment
    (by norm_num [GapStep])

private def primeGapCoverStep287 : List ℕ :=
  primeGapCoverStep286 ++ primeGapCertifiedGroup287

private lemma primeGapCoverStep287_segment :
    CertifiedSegment primeGapCoverStep287 439 28600331 := by
  unfold primeGapCoverStep287
  exact primeGapCoverStep286_segment.append primeGapCertifiedGroup287_segment
    (by norm_num [GapStep])

private def primeGapCoverStep288 : List ℕ :=
  primeGapCoverStep287 ++ primeGapCertifiedGroup288

private lemma primeGapCoverStep288_segment :
    CertifiedSegment primeGapCoverStep288 439 28698899 := by
  unfold primeGapCoverStep288
  exact primeGapCoverStep287_segment.append primeGapCertifiedGroup288_segment
    (by norm_num [GapStep])

private def primeGapCoverStep289 : List ℕ :=
  primeGapCoverStep288 ++ primeGapCertifiedGroup289

private lemma primeGapCoverStep289_segment :
    CertifiedSegment primeGapCoverStep289 439 28797577 := by
  unfold primeGapCoverStep289
  exact primeGapCoverStep288_segment.append primeGapCertifiedGroup289_segment
    (by norm_num [GapStep])

private def primeGapCoverStep290 : List ℕ :=
  primeGapCoverStep289 ++ primeGapCertifiedGroup290

private lemma primeGapCoverStep290_segment :
    CertifiedSegment primeGapCoverStep290 439 28896299 := by
  unfold primeGapCoverStep290
  exact primeGapCoverStep289_segment.append primeGapCertifiedGroup290_segment
    (by norm_num [GapStep])

private def primeGapCoverStep291 : List ℕ :=
  primeGapCoverStep290 ++ primeGapCertifiedGroup291

private lemma primeGapCoverStep291_segment :
    CertifiedSegment primeGapCoverStep291 439 28995059 := by
  unfold primeGapCoverStep291
  exact primeGapCoverStep290_segment.append primeGapCertifiedGroup291_segment
    (by norm_num [GapStep])

private def primeGapCoverStep292 : List ℕ :=
  primeGapCoverStep291 ++ primeGapCertifiedGroup292

private lemma primeGapCoverStep292_segment :
    CertifiedSegment primeGapCoverStep292 439 29093863 := by
  unfold primeGapCoverStep292
  exact primeGapCoverStep291_segment.append primeGapCertifiedGroup292_segment
    (by norm_num [GapStep])

private def primeGapCoverStep293 : List ℕ :=
  primeGapCoverStep292 ++ primeGapCertifiedGroup293

private lemma primeGapCoverStep293_segment :
    CertifiedSegment primeGapCoverStep293 439 29192467 := by
  unfold primeGapCoverStep293
  exact primeGapCoverStep292_segment.append primeGapCertifiedGroup293_segment
    (by norm_num [GapStep])

private def primeGapCoverStep294 : List ℕ :=
  primeGapCoverStep293 ++ primeGapCertifiedGroup294

private lemma primeGapCoverStep294_segment :
    CertifiedSegment primeGapCoverStep294 439 29290819 := by
  unfold primeGapCoverStep294
  exact primeGapCoverStep293_segment.append primeGapCertifiedGroup294_segment
    (by norm_num [GapStep])

private def primeGapCoverStep295 : List ℕ :=
  primeGapCoverStep294 ++ primeGapCertifiedGroup295

private lemma primeGapCoverStep295_segment :
    CertifiedSegment primeGapCoverStep295 439 29389747 := by
  unfold primeGapCoverStep295
  exact primeGapCoverStep294_segment.append primeGapCertifiedGroup295_segment
    (by norm_num [GapStep])

private def primeGapCoverStep296 : List ℕ :=
  primeGapCoverStep295 ++ primeGapCertifiedGroup296

private lemma primeGapCoverStep296_segment :
    CertifiedSegment primeGapCoverStep296 439 29488289 := by
  unfold primeGapCoverStep296
  exact primeGapCoverStep295_segment.append primeGapCertifiedGroup296_segment
    (by norm_num [GapStep])

private def primeGapCoverStep297 : List ℕ :=
  primeGapCoverStep296 ++ primeGapCertifiedGroup297

private lemma primeGapCoverStep297_segment :
    CertifiedSegment primeGapCoverStep297 439 29586751 := by
  unfold primeGapCoverStep297
  exact primeGapCoverStep296_segment.append primeGapCertifiedGroup297_segment
    (by norm_num [GapStep])

private def primeGapCoverStep298 : List ℕ :=
  primeGapCoverStep297 ++ primeGapCertifiedGroup298

private lemma primeGapCoverStep298_segment :
    CertifiedSegment primeGapCoverStep298 439 29685421 := by
  unfold primeGapCoverStep298
  exact primeGapCoverStep297_segment.append primeGapCertifiedGroup298_segment
    (by norm_num [GapStep])

private def primeGapCoverStep299 : List ℕ :=
  primeGapCoverStep298 ++ primeGapCertifiedGroup299

private lemma primeGapCoverStep299_segment :
    CertifiedSegment primeGapCoverStep299 439 29784311 := by
  unfold primeGapCoverStep299
  exact primeGapCoverStep298_segment.append primeGapCertifiedGroup299_segment
    (by norm_num [GapStep])

private def primeGapCoverStep300 : List ℕ :=
  primeGapCoverStep299 ++ primeGapCertifiedGroup300

private lemma primeGapCoverStep300_segment :
    CertifiedSegment primeGapCoverStep300 439 29883443 := by
  unfold primeGapCoverStep300
  exact primeGapCoverStep299_segment.append primeGapCertifiedGroup300_segment
    (by norm_num [GapStep])

private def primeGapCoverStep301 : List ℕ :=
  primeGapCoverStep300 ++ primeGapCertifiedGroup301

private lemma primeGapCoverStep301_segment :
    CertifiedSegment primeGapCoverStep301 439 29982431 := by
  unfold primeGapCoverStep301
  exact primeGapCoverStep300_segment.append primeGapCertifiedGroup301_segment
    (by norm_num [GapStep])

private def primeGapCoverStep302 : List ℕ :=
  primeGapCoverStep301 ++ primeGapCertifiedGroup302

private lemma primeGapCoverStep302_segment :
    CertifiedSegment primeGapCoverStep302 439 30081131 := by
  unfold primeGapCoverStep302
  exact primeGapCoverStep301_segment.append primeGapCertifiedGroup302_segment
    (by norm_num [GapStep])

private def primeGapCoverStep303 : List ℕ :=
  primeGapCoverStep302 ++ primeGapCertifiedGroup303

private lemma primeGapCoverStep303_segment :
    CertifiedSegment primeGapCoverStep303 439 30179273 := by
  unfold primeGapCoverStep303
  exact primeGapCoverStep302_segment.append primeGapCertifiedGroup303_segment
    (by norm_num [GapStep])

private def primeGapCoverStep304 : List ℕ :=
  primeGapCoverStep303 ++ primeGapCertifiedGroup304

private lemma primeGapCoverStep304_segment :
    CertifiedSegment primeGapCoverStep304 439 30278569 := by
  unfold primeGapCoverStep304
  exact primeGapCoverStep303_segment.append primeGapCertifiedGroup304_segment
    (by norm_num [GapStep])

private def primeGapCoverStep305 : List ℕ :=
  primeGapCoverStep304 ++ primeGapCertifiedGroup305

private lemma primeGapCoverStep305_segment :
    CertifiedSegment primeGapCoverStep305 439 30377381 := by
  unfold primeGapCoverStep305
  exact primeGapCoverStep304_segment.append primeGapCertifiedGroup305_segment
    (by norm_num [GapStep])

private def primeGapCoverStep306 : List ℕ :=
  primeGapCoverStep305 ++ primeGapCertifiedGroup306

private lemma primeGapCoverStep306_segment :
    CertifiedSegment primeGapCoverStep306 439 30475859 := by
  unfold primeGapCoverStep306
  exact primeGapCoverStep305_segment.append primeGapCertifiedGroup306_segment
    (by norm_num [GapStep])

private def primeGapCoverStep307 : List ℕ :=
  primeGapCoverStep306 ++ primeGapCertifiedGroup307

private lemma primeGapCoverStep307_segment :
    CertifiedSegment primeGapCoverStep307 439 30574759 := by
  unfold primeGapCoverStep307
  exact primeGapCoverStep306_segment.append primeGapCertifiedGroup307_segment
    (by norm_num [GapStep])

private def primeGapCoverStep308 : List ℕ :=
  primeGapCoverStep307 ++ primeGapCertifiedGroup308

private lemma primeGapCoverStep308_segment :
    CertifiedSegment primeGapCoverStep308 439 30673241 := by
  unfold primeGapCoverStep308
  exact primeGapCoverStep307_segment.append primeGapCertifiedGroup308_segment
    (by norm_num [GapStep])

private def primeGapCoverStep309 : List ℕ :=
  primeGapCoverStep308 ++ primeGapCertifiedGroup309

private lemma primeGapCoverStep309_segment :
    CertifiedSegment primeGapCoverStep309 439 30772253 := by
  unfold primeGapCoverStep309
  exact primeGapCoverStep308_segment.append primeGapCertifiedGroup309_segment
    (by norm_num [GapStep])

private def primeGapCoverStep310 : List ℕ :=
  primeGapCoverStep309 ++ primeGapCertifiedGroup310

private lemma primeGapCoverStep310_segment :
    CertifiedSegment primeGapCoverStep310 439 30871111 := by
  unfold primeGapCoverStep310
  exact primeGapCoverStep309_segment.append primeGapCertifiedGroup310_segment
    (by norm_num [GapStep])

private def primeGapCoverStep311 : List ℕ :=
  primeGapCoverStep310 ++ primeGapCertifiedGroup311

private lemma primeGapCoverStep311_segment :
    CertifiedSegment primeGapCoverStep311 439 30970207 := by
  unfold primeGapCoverStep311
  exact primeGapCoverStep310_segment.append primeGapCertifiedGroup311_segment
    (by norm_num [GapStep])

private def primeGapCoverStep312 : List ℕ :=
  primeGapCoverStep311 ++ primeGapCertifiedGroup312

private lemma primeGapCoverStep312_segment :
    CertifiedSegment primeGapCoverStep312 439 31068563 := by
  unfold primeGapCoverStep312
  exact primeGapCoverStep311_segment.append primeGapCertifiedGroup312_segment
    (by norm_num [GapStep])

private def primeGapCoverStep313 : List ℕ :=
  primeGapCoverStep312 ++ primeGapCertifiedGroup313

private lemma primeGapCoverStep313_segment :
    CertifiedSegment primeGapCoverStep313 439 31167379 := by
  unfold primeGapCoverStep313
  exact primeGapCoverStep312_segment.append primeGapCertifiedGroup313_segment
    (by norm_num [GapStep])

private def primeGapCoverStep314 : List ℕ :=
  primeGapCoverStep313 ++ primeGapCertifiedGroup314

private lemma primeGapCoverStep314_segment :
    CertifiedSegment primeGapCoverStep314 439 31266413 := by
  unfold primeGapCoverStep314
  exact primeGapCoverStep313_segment.append primeGapCertifiedGroup314_segment
    (by norm_num [GapStep])

private def primeGapCoverStep315 : List ℕ :=
  primeGapCoverStep314 ++ primeGapCertifiedGroup315

private lemma primeGapCoverStep315_segment :
    CertifiedSegment primeGapCoverStep315 439 31365689 := by
  unfold primeGapCoverStep315
  exact primeGapCoverStep314_segment.append primeGapCertifiedGroup315_segment
    (by norm_num [GapStep])

private def primeGapCoverStep316 : List ℕ :=
  primeGapCoverStep315 ++ primeGapCertifiedGroup316

private lemma primeGapCoverStep316_segment :
    CertifiedSegment primeGapCoverStep316 439 31464967 := by
  unfold primeGapCoverStep316
  exact primeGapCoverStep315_segment.append primeGapCertifiedGroup316_segment
    (by norm_num [GapStep])

private def primeGapCoverStep317 : List ℕ :=
  primeGapCoverStep316 ++ primeGapCertifiedGroup317

private lemma primeGapCoverStep317_segment :
    CertifiedSegment primeGapCoverStep317 439 31563601 := by
  unfold primeGapCoverStep317
  exact primeGapCoverStep316_segment.append primeGapCertifiedGroup317_segment
    (by norm_num [GapStep])

private def primeGapCoverStep318 : List ℕ :=
  primeGapCoverStep317 ++ primeGapCertifiedGroup318

private lemma primeGapCoverStep318_segment :
    CertifiedSegment primeGapCoverStep318 439 31662023 := by
  unfold primeGapCoverStep318
  exact primeGapCoverStep317_segment.append primeGapCertifiedGroup318_segment
    (by norm_num [GapStep])

private def primeGapCoverStep319 : List ℕ :=
  primeGapCoverStep318 ++ primeGapCertifiedGroup319

private lemma primeGapCoverStep319_segment :
    CertifiedSegment primeGapCoverStep319 439 31760623 := by
  unfold primeGapCoverStep319
  exact primeGapCoverStep318_segment.append primeGapCertifiedGroup319_segment
    (by norm_num [GapStep])

private def primeGapCoverStep320 : List ℕ :=
  primeGapCoverStep319 ++ primeGapCertifiedGroup320

private lemma primeGapCoverStep320_segment :
    CertifiedSegment primeGapCoverStep320 439 31859783 := by
  unfold primeGapCoverStep320
  exact primeGapCoverStep319_segment.append primeGapCertifiedGroup320_segment
    (by norm_num [GapStep])

private def primeGapCoverStep321 : List ℕ :=
  primeGapCoverStep320 ++ primeGapCertifiedGroup321

private lemma primeGapCoverStep321_segment :
    CertifiedSegment primeGapCoverStep321 439 31958243 := by
  unfold primeGapCoverStep321
  exact primeGapCoverStep320_segment.append primeGapCertifiedGroup321_segment
    (by norm_num [GapStep])

private def primeGapCoverStep322 : List ℕ :=
  primeGapCoverStep321 ++ primeGapCertifiedGroup322

private lemma primeGapCoverStep322_segment :
    CertifiedSegment primeGapCoverStep322 439 32057387 := by
  unfold primeGapCoverStep322
  exact primeGapCoverStep321_segment.append primeGapCertifiedGroup322_segment
    (by norm_num [GapStep])

private def primeGapCoverStep323 : List ℕ :=
  primeGapCoverStep322 ++ primeGapCertifiedGroup323

private lemma primeGapCoverStep323_segment :
    CertifiedSegment primeGapCoverStep323 439 32156183 := by
  unfold primeGapCoverStep323
  exact primeGapCoverStep322_segment.append primeGapCertifiedGroup323_segment
    (by norm_num [GapStep])

private def primeGapCoverStep324 : List ℕ :=
  primeGapCoverStep323 ++ primeGapCertifiedGroup324

private lemma primeGapCoverStep324_segment :
    CertifiedSegment primeGapCoverStep324 439 32254637 := by
  unfold primeGapCoverStep324
  exact primeGapCoverStep323_segment.append primeGapCertifiedGroup324_segment
    (by norm_num [GapStep])

private def primeGapCoverStep325 : List ℕ :=
  primeGapCoverStep324 ++ primeGapCertifiedGroup325

private lemma primeGapCoverStep325_segment :
    CertifiedSegment primeGapCoverStep325 439 32353957 := by
  unfold primeGapCoverStep325
  exact primeGapCoverStep324_segment.append primeGapCertifiedGroup325_segment
    (by norm_num [GapStep])

private def primeGapCoverStep326 : List ℕ :=
  primeGapCoverStep325 ++ primeGapCertifiedGroup326

private lemma primeGapCoverStep326_segment :
    CertifiedSegment primeGapCoverStep326 439 32452687 := by
  unfold primeGapCoverStep326
  exact primeGapCoverStep325_segment.append primeGapCertifiedGroup326_segment
    (by norm_num [GapStep])

private def primeGapCoverStep327 : List ℕ :=
  primeGapCoverStep326 ++ primeGapCertifiedGroup327

private lemma primeGapCoverStep327_segment :
    CertifiedSegment primeGapCoverStep327 439 32552071 := by
  unfold primeGapCoverStep327
  exact primeGapCoverStep326_segment.append primeGapCertifiedGroup327_segment
    (by norm_num [GapStep])

private def primeGapCoverStep328 : List ℕ :=
  primeGapCoverStep327 ++ primeGapCertifiedGroup328

private lemma primeGapCoverStep328_segment :
    CertifiedSegment primeGapCoverStep328 439 32650649 := by
  unfold primeGapCoverStep328
  exact primeGapCoverStep327_segment.append primeGapCertifiedGroup328_segment
    (by norm_num [GapStep])

private def primeGapCoverStep329 : List ℕ :=
  primeGapCoverStep328 ++ primeGapCertifiedGroup329

private lemma primeGapCoverStep329_segment :
    CertifiedSegment primeGapCoverStep329 439 32749183 := by
  unfold primeGapCoverStep329
  exact primeGapCoverStep328_segment.append primeGapCertifiedGroup329_segment
    (by norm_num [GapStep])

private def primeGapCoverStep330 : List ℕ :=
  primeGapCoverStep329 ++ primeGapCertifiedGroup330

private lemma primeGapCoverStep330_segment :
    CertifiedSegment primeGapCoverStep330 439 32848019 := by
  unfold primeGapCoverStep330
  exact primeGapCoverStep329_segment.append primeGapCertifiedGroup330_segment
    (by norm_num [GapStep])

private def primeGapCoverStep331 : List ℕ :=
  primeGapCoverStep330 ++ primeGapCertifiedGroup331

private lemma primeGapCoverStep331_segment :
    CertifiedSegment primeGapCoverStep331 439 32946307 := by
  unfold primeGapCoverStep331
  exact primeGapCoverStep330_segment.append primeGapCertifiedGroup331_segment
    (by norm_num [GapStep])

private def primeGapCoverStep332 : List ℕ :=
  primeGapCoverStep331 ++ primeGapCertifiedGroup332

private lemma primeGapCoverStep332_segment :
    CertifiedSegment primeGapCoverStep332 439 33045253 := by
  unfold primeGapCoverStep332
  exact primeGapCoverStep331_segment.append primeGapCertifiedGroup332_segment
    (by norm_num [GapStep])

private def primeGapCoverStep333 : List ℕ :=
  primeGapCoverStep332 ++ primeGapCertifiedGroup333

private lemma primeGapCoverStep333_segment :
    CertifiedSegment primeGapCoverStep333 439 33144919 := by
  unfold primeGapCoverStep333
  exact primeGapCoverStep332_segment.append primeGapCertifiedGroup333_segment
    (by norm_num [GapStep])

private def primeGapCoverStep334 : List ℕ :=
  primeGapCoverStep333 ++ primeGapCertifiedGroup334

private lemma primeGapCoverStep334_segment :
    CertifiedSegment primeGapCoverStep334 439 33243611 := by
  unfold primeGapCoverStep334
  exact primeGapCoverStep333_segment.append primeGapCertifiedGroup334_segment
    (by norm_num [GapStep])

private def primeGapCoverStep335 : List ℕ :=
  primeGapCoverStep334 ++ primeGapCertifiedGroup335

private lemma primeGapCoverStep335_segment :
    CertifiedSegment primeGapCoverStep335 439 33342037 := by
  unfold primeGapCoverStep335
  exact primeGapCoverStep334_segment.append primeGapCertifiedGroup335_segment
    (by norm_num [GapStep])

private def primeGapCoverStep336 : List ℕ :=
  primeGapCoverStep335 ++ primeGapCertifiedGroup336

private lemma primeGapCoverStep336_segment :
    CertifiedSegment primeGapCoverStep336 439 33440731 := by
  unfold primeGapCoverStep336
  exact primeGapCoverStep335_segment.append primeGapCertifiedGroup336_segment
    (by norm_num [GapStep])

private def primeGapCoverStep337 : List ℕ :=
  primeGapCoverStep336 ++ primeGapCertifiedGroup337

private lemma primeGapCoverStep337_segment :
    CertifiedSegment primeGapCoverStep337 439 33539393 := by
  unfold primeGapCoverStep337
  exact primeGapCoverStep336_segment.append primeGapCertifiedGroup337_segment
    (by norm_num [GapStep])

private def primeGapCoverStep338 : List ℕ :=
  primeGapCoverStep337 ++ primeGapCertifiedGroup338

private lemma primeGapCoverStep338_segment :
    CertifiedSegment primeGapCoverStep338 439 33637823 := by
  unfold primeGapCoverStep338
  exact primeGapCoverStep337_segment.append primeGapCertifiedGroup338_segment
    (by norm_num [GapStep])

private def primeGapCoverStep339 : List ℕ :=
  primeGapCoverStep338 ++ primeGapCertifiedGroup339

private lemma primeGapCoverStep339_segment :
    CertifiedSegment primeGapCoverStep339 439 33736709 := by
  unfold primeGapCoverStep339
  exact primeGapCoverStep338_segment.append primeGapCertifiedGroup339_segment
    (by norm_num [GapStep])

private def primeGapCoverStep340 : List ℕ :=
  primeGapCoverStep339 ++ primeGapCertifiedGroup340

private lemma primeGapCoverStep340_segment :
    CertifiedSegment primeGapCoverStep340 439 33835111 := by
  unfold primeGapCoverStep340
  exact primeGapCoverStep339_segment.append primeGapCertifiedGroup340_segment
    (by norm_num [GapStep])

private def primeGapCoverStep341 : List ℕ :=
  primeGapCoverStep340 ++ primeGapCertifiedGroup341

private lemma primeGapCoverStep341_segment :
    CertifiedSegment primeGapCoverStep341 439 33934001 := by
  unfold primeGapCoverStep341
  exact primeGapCoverStep340_segment.append primeGapCertifiedGroup341_segment
    (by norm_num [GapStep])

private def primeGapCoverStep342 : List ℕ :=
  primeGapCoverStep341 ++ primeGapCertifiedGroup342

private lemma primeGapCoverStep342_segment :
    CertifiedSegment primeGapCoverStep342 439 34032209 := by
  unfold primeGapCoverStep342
  exact primeGapCoverStep341_segment.append primeGapCertifiedGroup342_segment
    (by norm_num [GapStep])

private def primeGapCoverStep343 : List ℕ :=
  primeGapCoverStep342 ++ primeGapCertifiedGroup343

private lemma primeGapCoverStep343_segment :
    CertifiedSegment primeGapCoverStep343 439 34130617 := by
  unfold primeGapCoverStep343
  exact primeGapCoverStep342_segment.append primeGapCertifiedGroup343_segment
    (by norm_num [GapStep])

private def primeGapCoverStep344 : List ℕ :=
  primeGapCoverStep343 ++ primeGapCertifiedGroup344

private lemma primeGapCoverStep344_segment :
    CertifiedSegment primeGapCoverStep344 439 34229057 := by
  unfold primeGapCoverStep344
  exact primeGapCoverStep343_segment.append primeGapCertifiedGroup344_segment
    (by norm_num [GapStep])

private def primeGapCoverStep345 : List ℕ :=
  primeGapCoverStep344 ++ primeGapCertifiedGroup345

private lemma primeGapCoverStep345_segment :
    CertifiedSegment primeGapCoverStep345 439 34327519 := by
  unfold primeGapCoverStep345
  exact primeGapCoverStep344_segment.append primeGapCertifiedGroup345_segment
    (by norm_num [GapStep])

private def primeGapCoverStep346 : List ℕ :=
  primeGapCoverStep345 ++ primeGapCertifiedGroup346

private lemma primeGapCoverStep346_segment :
    CertifiedSegment primeGapCoverStep346 439 34426099 := by
  unfold primeGapCoverStep346
  exact primeGapCoverStep345_segment.append primeGapCertifiedGroup346_segment
    (by norm_num [GapStep])

private def primeGapCoverStep347 : List ℕ :=
  primeGapCoverStep346 ++ primeGapCertifiedGroup347

private lemma primeGapCoverStep347_segment :
    CertifiedSegment primeGapCoverStep347 439 34524557 := by
  unfold primeGapCoverStep347
  exact primeGapCoverStep346_segment.append primeGapCertifiedGroup347_segment
    (by norm_num [GapStep])

private def primeGapCoverStep348 : List ℕ :=
  primeGapCoverStep347 ++ primeGapCertifiedGroup348

private lemma primeGapCoverStep348_segment :
    CertifiedSegment primeGapCoverStep348 439 34623247 := by
  unfold primeGapCoverStep348
  exact primeGapCoverStep347_segment.append primeGapCertifiedGroup348_segment
    (by norm_num [GapStep])

private def primeGapCoverStep349 : List ℕ :=
  primeGapCoverStep348 ++ primeGapCertifiedGroup349

private lemma primeGapCoverStep349_segment :
    CertifiedSegment primeGapCoverStep349 439 34721867 := by
  unfold primeGapCoverStep349
  exact primeGapCoverStep348_segment.append primeGapCertifiedGroup349_segment
    (by norm_num [GapStep])

private def primeGapCoverStep350 : List ℕ :=
  primeGapCoverStep349 ++ primeGapCertifiedGroup350

private lemma primeGapCoverStep350_segment :
    CertifiedSegment primeGapCoverStep350 439 34820419 := by
  unfold primeGapCoverStep350
  exact primeGapCoverStep349_segment.append primeGapCertifiedGroup350_segment
    (by norm_num [GapStep])

private def primeGapCoverStep351 : List ℕ :=
  primeGapCoverStep350 ++ primeGapCertifiedGroup351

private lemma primeGapCoverStep351_segment :
    CertifiedSegment primeGapCoverStep351 439 34918781 := by
  unfold primeGapCoverStep351
  exact primeGapCoverStep350_segment.append primeGapCertifiedGroup351_segment
    (by norm_num [GapStep])

private def primeGapCoverStep352 : List ℕ :=
  primeGapCoverStep351 ++ primeGapCertifiedGroup352

private lemma primeGapCoverStep352_segment :
    CertifiedSegment primeGapCoverStep352 439 35017249 := by
  unfold primeGapCoverStep352
  exact primeGapCoverStep351_segment.append primeGapCertifiedGroup352_segment
    (by norm_num [GapStep])

private def primeGapCoverStep353 : List ℕ :=
  primeGapCoverStep352 ++ primeGapCertifiedGroup353

private lemma primeGapCoverStep353_segment :
    CertifiedSegment primeGapCoverStep353 439 35115329 := by
  unfold primeGapCoverStep353
  exact primeGapCoverStep352_segment.append primeGapCertifiedGroup353_segment
    (by norm_num [GapStep])

private def primeGapCoverStep354 : List ℕ :=
  primeGapCoverStep353 ++ primeGapCertifiedGroup354

private lemma primeGapCoverStep354_segment :
    CertifiedSegment primeGapCoverStep354 439 35214199 := by
  unfold primeGapCoverStep354
  exact primeGapCoverStep353_segment.append primeGapCertifiedGroup354_segment
    (by norm_num [GapStep])

private def primeGapCoverStep355 : List ℕ :=
  primeGapCoverStep354 ++ primeGapCertifiedGroup355

private lemma primeGapCoverStep355_segment :
    CertifiedSegment primeGapCoverStep355 439 35313137 := by
  unfold primeGapCoverStep355
  exact primeGapCoverStep354_segment.append primeGapCertifiedGroup355_segment
    (by norm_num [GapStep])

private def primeGapCoverStep356 : List ℕ :=
  primeGapCoverStep355 ++ primeGapCertifiedGroup356

private lemma primeGapCoverStep356_segment :
    CertifiedSegment primeGapCoverStep356 439 35411947 := by
  unfold primeGapCoverStep356
  exact primeGapCoverStep355_segment.append primeGapCertifiedGroup356_segment
    (by norm_num [GapStep])

private def primeGapCoverStep357 : List ℕ :=
  primeGapCoverStep356 ++ primeGapCertifiedGroup357

private lemma primeGapCoverStep357_segment :
    CertifiedSegment primeGapCoverStep357 439 35510567 := by
  unfold primeGapCoverStep357
  exact primeGapCoverStep356_segment.append primeGapCertifiedGroup357_segment
    (by norm_num [GapStep])

private def primeGapCoverStep358 : List ℕ :=
  primeGapCoverStep357 ++ primeGapCertifiedGroup358

private lemma primeGapCoverStep358_segment :
    CertifiedSegment primeGapCoverStep358 439 35608721 := by
  unfold primeGapCoverStep358
  exact primeGapCoverStep357_segment.append primeGapCertifiedGroup358_segment
    (by norm_num [GapStep])

private def primeGapCoverStep359 : List ℕ :=
  primeGapCoverStep358 ++ primeGapCertifiedGroup359

private lemma primeGapCoverStep359_segment :
    CertifiedSegment primeGapCoverStep359 439 35706929 := by
  unfold primeGapCoverStep359
  exact primeGapCoverStep358_segment.append primeGapCertifiedGroup359_segment
    (by norm_num [GapStep])

private def primeGapCoverStep360 : List ℕ :=
  primeGapCoverStep359 ++ primeGapCertifiedGroup360

private lemma primeGapCoverStep360_segment :
    CertifiedSegment primeGapCoverStep360 439 35805727 := by
  unfold primeGapCoverStep360
  exact primeGapCoverStep359_segment.append primeGapCertifiedGroup360_segment
    (by norm_num [GapStep])

private def primeGapCoverStep361 : List ℕ :=
  primeGapCoverStep360 ++ primeGapCertifiedGroup361

private lemma primeGapCoverStep361_segment :
    CertifiedSegment primeGapCoverStep361 439 35904383 := by
  unfold primeGapCoverStep361
  exact primeGapCoverStep360_segment.append primeGapCertifiedGroup361_segment
    (by norm_num [GapStep])

private def primeGapCoverStep362 : List ℕ :=
  primeGapCoverStep361 ++ primeGapCertifiedGroup362

private lemma primeGapCoverStep362_segment :
    CertifiedSegment primeGapCoverStep362 439 36000127 := by
  unfold primeGapCoverStep362
  exact primeGapCoverStep361_segment.append primeGapCertifiedGroup362_segment
    (by norm_num [GapStep])

def primeGapCover : List ℕ := primeGapCoverStep362

lemma primeGapCover_segment : CertifiedSegment primeGapCover 439 36000127 := by
  unfold primeGapCover
  exact primeGapCoverStep362_segment

theorem prime_gap_le_210_below_36000000 {p q : ℕ}
    (hp433 : 433 < p) (hp : p.Prime)
    (hqfirst : IsFirstPrimeAfter p q) (hq36 : q < 36000000) :
    q - p ≤ 210 := by
  have hcert := primeGapCover_segment
  have hpq : p < q := hqfirst.1
  obtain ⟨r, hrmem, hrprime, hpr, hrbound⟩ :=
    hcert.exists_prime_after (p := p) (by omega) (by omega)
  have hqr : q ≤ r := hqfirst.2.2 r hrprime hpr
  omega

end PrimeGap210Certificate

end Erdos1058
