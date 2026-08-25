/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate216 : CompactCertificate where
  left := 97
  right := 195 / 2
  center := 389 / 4
  grid := fun i =>
    match i.val with
    | 0 => 31
    | 1 => 23
    | 2 => 37
    | 3 => 7
    | 4 => 18
    | 5 => 49
    | 6 => 36
    | 7 => 61
    | 8 => 45
    | 9 => 69
    | 10 => 40
    | 11 => 71
    | 12 => 66
    | 13 => 47
    | 14 => 54
    | 15 => 45
    | 16 => 40
    | 17 => 57
    | 18 => 32
    | 19 => 27
    | 20 => 17
    | 21 => 9
    | 22 => 25
    | 23 => 34
    | 24 => 14
    | 25 => 58
    | _ => 38
  point := fun i =>
    match i.val with
    | 0 => 389 / 4
    | 1 => 573071278733489 / 8000000000000
    | 2 => 185319477049937 / 1600000000000
    | 3 => 167220769874323 / 8000000000000
    | 4 => 449178509429431 / 8000000000000
    | 5 => 1219607030764827 / 8000000000000
    | 6 => 898357018859251 / 8000000000000
    | 7 => 1539350063820223 / 8000000000000
    | 8 => 1133878289834557 / 8000000000000
    | 9 => 1739660886494611 / 8000000000000
    | 10 => 1004393681116219 / 8000000000000
    | 11 => 1782314212566071 / 8000000000000
    | 12 => 1665269133098099 / 8000000000000
    | 13 => 1188414630224867 / 8000000000000
    | 14 => 1347535528288293 / 8000000000000
    | 15 => 1123434635845717 / 8000000000000
    | 16 => 992588571124057 / 8000000000000
    | 17 => 287690855909643 / 1600000000000
    | 18 => 795768047786321 / 8000000000000
    | 19 => 674581386998281 / 8000000000000
    | 20 => 422121710165443 / 8000000000000
    | 21 => 227018459640381 / 8000000000000
    | 22 => 616399279304143 / 8000000000000
    | 23 => 841640518294511 / 8000000000000
    | 24 => 355878289834557 / 8000000000000
    | 25 => 1446625490405597 / 8000000000000
    | _ => 966278785087123 / 8000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-48625095300 / 1000000000000) (-48625095299 / 1000000000000), orderedInterval (-64417176013 / 1000000000000) (-64417176012 / 1000000000000))
    | 1 => (orderedInterval (-15105741096 / 1000000000000) (-15105741095 / 1000000000000), orderedInterval (-92949124861 / 1000000000000) (-92949124860 / 1000000000000))
    | 2 => (orderedInterval (-26813657881 / 1000000000000) (-26813657880 / 1000000000000), orderedInterval (-69003528660 / 1000000000000) (-69003528659 / 1000000000000))
    | 3 => (orderedInterval (53085545927 / 1000000000000) (53085546775 / 1000000000000), orderedInterval (-167538449952 / 1000000000000) (-167538449104 / 1000000000000))
    | 4 => (orderedInterval (39675234896 / 1000000000000) (39675234897 / 1000000000000), orderedInterval (98462622742 / 1000000000000) (98462622743 / 1000000000000))
    | 5 => (orderedInterval (41757523126 / 1000000000000) (41757550865 / 1000000000000), orderedInterval (-49454434588 / 1000000000000) (-49454406849 / 1000000000000))
    | 6 => (orderedInterval (-1387064627 / 1000000000000) (-1387064619 / 1000000000000), orderedInterval (75287806643 / 1000000000000) (75287806651 / 1000000000000))
    | 7 => (orderedInterval (-57519001871 / 1000000000000) (-57519001810 / 1000000000000), orderedInterval (-106020955 / 1000000000000) (-106020894 / 1000000000000))
    | 8 => (orderedInterval (-61107914758 / 1000000000000) (-61107914757 / 1000000000000), orderedInterval (-27305897325 / 1000000000000) (-27305897324 / 1000000000000))
    | 9 => (orderedInterval (-53845875045 / 1000000000000) (-53845875027 / 1000000000000), orderedInterval (-5183939264 / 1000000000000) (-5183939246 / 1000000000000))
    | 10 => (orderedInterval (44214215595 / 1000000000000) (44214215596 / 1000000000000), orderedInterval (55643195605 / 1000000000000) (55643195606 / 1000000000000))
    | 11 => (orderedInterval (-26608986279 / 1000000000000) (-26608986278 / 1000000000000), orderedInterval (-46302582360 / 1000000000000) (-46302582359 / 1000000000000))
    | 12 => (orderedInterval (55281222810 / 1000000000000) (55281222917 / 1000000000000), orderedInterval (-1654947155 / 1000000000000) (-1654947048 / 1000000000000))
    | 13 => (orderedInterval (-65062640665 / 1000000000000) (-65062640443 / 1000000000000), orderedInterval (7453297722 / 1000000000000) (7453297944 / 1000000000000))
    | 14 => (orderedInterval (-25034628007 / 1000000000000) (-25034626635 / 1000000000000), orderedInterval (56223573762 / 1000000000000) (56223575133 / 1000000000000))
    | 15 => (orderedInterval (10582782442 / 1000000000000) (10582782496 / 1000000000000), orderedInterval (-66531392665 / 1000000000000) (-66531392611 / 1000000000000))
    | 16 => (orderedInterval (-51670501471 / 1000000000000) (-51670423029 / 1000000000000), orderedInterval (49818134708 / 1000000000000) (49818213150 / 1000000000000))
    | 17 => (orderedInterval (-59428003410 / 1000000000000) (-59428003382 / 1000000000000), orderedInterval (-2813977773 / 1000000000000) (-2813977745 / 1000000000000))
    | 18 => (orderedInterval (-21786633343 / 1000000000000) (-21786632981 / 1000000000000), orderedInterval (77086552140 / 1000000000000) (77086552502 / 1000000000000))
    | 19 => (orderedInterval (-24311652463 / 1000000000000) (-24311652462 / 1000000000000), orderedInterval (-83275633509 / 1000000000000) (-83275633508 / 1000000000000))
    | 20 => (orderedInterval (-15454329278 / 1000000000000) (-15454329276 / 1000000000000), orderedInterval (-108604776606 / 1000000000000) (-108604776604 / 1000000000000))
    | 21 => (orderedInterval (-115810392476 / 1000000000000) (-115810392475 / 1000000000000), orderedInterval (-92941069103 / 1000000000000) (-92941069102 / 1000000000000))
    | 22 => (orderedInterval (58982513398 / 1000000000000) (58982553660 / 1000000000000), orderedInterval (-69545766675 / 1000000000000) (-69545726413 / 1000000000000))
    | 23 => (orderedInterval (-57133349782 / 1000000000000) (-57133250009 / 1000000000000), orderedInterval (53063592684 / 1000000000000) (53063692457 / 1000000000000))
    | 24 => (orderedInterval (114774980455 / 1000000000000) (114774980456 / 1000000000000), orderedInterval (32428049889 / 1000000000000) (32428049890 / 1000000000000))
    | 25 => (orderedInterval (-33477261629 / 1000000000000) (-33477252667 / 1000000000000), orderedInterval (49080889732 / 1000000000000) (49080898693 / 1000000000000))
    | _ => (orderedInterval (59175613614 / 1000000000000) (59175659540 / 1000000000000), orderedInterval (-42303527677 / 1000000000000) (-42303481751 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-20987497776 / 1000000000000) (-20987497768 / 1000000000000)
      | 1 => orderedInterval (-2095857752 / 1000000000000) (-2095855758 / 1000000000000)
      | 2 => orderedInterval (297258412 / 1000000000000) (297258421 / 1000000000000)
      | 3 => orderedInterval (9061047195 / 1000000000000) (9061047237 / 1000000000000)
      | 4 => orderedInterval (-7023816818 / 1000000000000) (-7023816776 / 1000000000000)
      | 5 => orderedInterval (1557541455 / 1000000000000) (1557545956 / 1000000000000)
      | 6 => orderedInterval (4356436520 / 1000000000000) (4356436603 / 1000000000000)
      | 7 => orderedInterval (5178951105 / 1000000000000) (5178959678 / 1000000000000)
      | _ => orderedInterval (-7685914412 / 1000000000000) (-7685905038 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-30993283751 / 1000000000000) (-30993283742 / 1000000000000)
      | 1 => orderedInterval (7977552778 / 1000000000000) (7977555886 / 1000000000000)
      | 2 => orderedInterval (-955329153 / 1000000000000) (-955329139 / 1000000000000)
      | 3 => orderedInterval (-7696995632 / 1000000000000) (-7696995544 / 1000000000000)
      | 4 => orderedInterval (647748222 / 1000000000000) (647748290 / 1000000000000)
      | 5 => orderedInterval (-4879891630 / 1000000000000) (-4879885887 / 1000000000000)
      | 6 => orderedInterval (-10438550769 / 1000000000000) (-10438550687 / 1000000000000)
      | 7 => orderedInterval (-2648577990 / 1000000000000) (-2648568983 / 1000000000000)
      | _ => orderedInterval (2518648009 / 1000000000000) (2518660106 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (21900267553 / 1000000000000) (21900267564 / 1000000000000)
      | 1 => orderedInterval (6756644576 / 1000000000000) (6756649474 / 1000000000000)
      | 2 => orderedInterval (-3798598348 / 1000000000000) (-3798598323 / 1000000000000)
      | 3 => orderedInterval (-33367591011 / 1000000000000) (-33367590822 / 1000000000000)
      | 4 => orderedInterval (18541469085 / 1000000000000) (18541469196 / 1000000000000)
      | 5 => orderedInterval (183837668 / 1000000000000) (183845058 / 1000000000000)
      | 6 => orderedInterval (-4423523316 / 1000000000000) (-4423523232 / 1000000000000)
      | 7 => orderedInterval (-4439157601 / 1000000000000) (-4439147975 / 1000000000000)
      | _ => orderedInterval (7534519246 / 1000000000000) (7534535241 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (32491144333 / 1000000000000) (32491144345 / 1000000000000)
      | 1 => orderedInterval (-14322099024 / 1000000000000) (-14322091349 / 1000000000000)
      | 2 => orderedInterval (2056581151 / 1000000000000) (2056581197 / 1000000000000)
      | 3 => orderedInterval (60311003007 / 1000000000000) (60311003420 / 1000000000000)
      | 4 => orderedInterval (-1517233890 / 1000000000000) (-1517233705 / 1000000000000)
      | 5 => orderedInterval (8686697005 / 1000000000000) (8686706440 / 1000000000000)
      | 6 => orderedInterval (10726039061 / 1000000000000) (10726039146 / 1000000000000)
      | 7 => orderedInterval (4366620543 / 1000000000000) (4366630786 / 1000000000000)
      | _ => orderedInterval (10382006918 / 1000000000000) (10382028364 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-23146495241 / 1000000000000) (-23146495227 / 1000000000000)
      | 1 => orderedInterval (-17471818895 / 1000000000000) (-17471806788 / 1000000000000)
      | 2 => orderedInterval (20484308069 / 1000000000000) (20484308156 / 1000000000000)
      | 3 => orderedInterval (142863340588 / 1000000000000) (142863341507 / 1000000000000)
      | 4 => orderedInterval (-53271911534 / 1000000000000) (-53271911221 / 1000000000000)
      | 5 => orderedInterval (-9594325115 / 1000000000000) (-9594312971 / 1000000000000)
      | 6 => orderedInterval (4325936401 / 1000000000000) (4325936487 / 1000000000000)
      | 7 => orderedInterval (5394861980 / 1000000000000) (5394873030 / 1000000000000)
      | _ => orderedInterval (5973222238 / 1000000000000) (5973252033 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-17341852071 / 1000000000000) (-17341827445 / 1000000000000)
    | 1 => orderedInterval (-46468679916 / 1000000000000) (-46468649700 / 1000000000000)
    | 2 => orderedInterval (8887867852 / 1000000000000) (8887906181 / 1000000000000)
    | 3 => orderedInterval (113180759104 / 1000000000000) (113180808644 / 1000000000000)
    | _ => orderedInterval (75557118491 / 1000000000000) (75557185006 / 1000000000000)

theorem compactCertificate216_stateChecks0 :
    compactCertificate216.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (389 / 4)) (orderedInterval (-48625095300 / 1000000000000) (-48625095299 / 1000000000000), orderedInterval (-64417176013 / 1000000000000) (-64417176012 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (573071278733489 / 8000000000000)) (orderedInterval (-15105741096 / 1000000000000) (-15105741095 / 1000000000000), orderedInterval (-92949124861 / 1000000000000) (-92949124860 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (185319477049937 / 1600000000000)) (orderedInterval (-26813657881 / 1000000000000) (-26813657880 / 1000000000000), orderedInterval (-69003528660 / 1000000000000) (-69003528659 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState023, besselGridState025, besselGridState027, besselGridState031, besselGridState032, besselGridState034, besselGridState036, besselGridState037, besselGridState038, besselGridState040, besselGridState045, besselGridState047, besselGridState049, besselGridState054, besselGridState057, besselGridState058, besselGridState061, besselGridState066, besselGridState069, besselGridState071, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate216_stateChecks1 :
    compactCertificate216.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 7 12 (167220769874323 / 8000000000000)) (orderedInterval (53085545927 / 1000000000000) (53085546775 / 1000000000000), orderedInterval (-167538449952 / 1000000000000) (-167538449104 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 18 12 (449178509429431 / 8000000000000)) (orderedInterval (39675234896 / 1000000000000) (39675234897 / 1000000000000), orderedInterval (98462622742 / 1000000000000) (98462622743 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (1219607030764827 / 8000000000000)) (orderedInterval (41757523126 / 1000000000000) (41757550865 / 1000000000000), orderedInterval (-49454434588 / 1000000000000) (-49454406849 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState023, besselGridState025, besselGridState027, besselGridState031, besselGridState032, besselGridState034, besselGridState036, besselGridState037, besselGridState038, besselGridState040, besselGridState045, besselGridState047, besselGridState049, besselGridState054, besselGridState057, besselGridState058, besselGridState061, besselGridState066, besselGridState069, besselGridState071, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate216_stateChecks2 :
    compactCertificate216.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (898357018859251 / 8000000000000)) (orderedInterval (-1387064627 / 1000000000000) (-1387064619 / 1000000000000), orderedInterval (75287806643 / 1000000000000) (75287806651 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (1539350063820223 / 8000000000000)) (orderedInterval (-57519001871 / 1000000000000) (-57519001810 / 1000000000000), orderedInterval (-106020955 / 1000000000000) (-106020894 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (1133878289834557 / 8000000000000)) (orderedInterval (-61107914758 / 1000000000000) (-61107914757 / 1000000000000), orderedInterval (-27305897325 / 1000000000000) (-27305897324 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState023, besselGridState025, besselGridState027, besselGridState031, besselGridState032, besselGridState034, besselGridState036, besselGridState037, besselGridState038, besselGridState040, besselGridState045, besselGridState047, besselGridState049, besselGridState054, besselGridState057, besselGridState058, besselGridState061, besselGridState066, besselGridState069, besselGridState071, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate216_stateChecks3 :
    compactCertificate216.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (1739660886494611 / 8000000000000)) (orderedInterval (-53845875045 / 1000000000000) (-53845875027 / 1000000000000), orderedInterval (-5183939264 / 1000000000000) (-5183939246 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (1004393681116219 / 8000000000000)) (orderedInterval (44214215595 / 1000000000000) (44214215596 / 1000000000000), orderedInterval (55643195605 / 1000000000000) (55643195606 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (1782314212566071 / 8000000000000)) (orderedInterval (-26608986279 / 1000000000000) (-26608986278 / 1000000000000), orderedInterval (-46302582360 / 1000000000000) (-46302582359 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState023, besselGridState025, besselGridState027, besselGridState031, besselGridState032, besselGridState034, besselGridState036, besselGridState037, besselGridState038, besselGridState040, besselGridState045, besselGridState047, besselGridState049, besselGridState054, besselGridState057, besselGridState058, besselGridState061, besselGridState066, besselGridState069, besselGridState071, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate216_stateChecks4 :
    compactCertificate216.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (1665269133098099 / 8000000000000)) (orderedInterval (55281222810 / 1000000000000) (55281222917 / 1000000000000), orderedInterval (-1654947155 / 1000000000000) (-1654947048 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (1188414630224867 / 8000000000000)) (orderedInterval (-65062640665 / 1000000000000) (-65062640443 / 1000000000000), orderedInterval (7453297722 / 1000000000000) (7453297944 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (1347535528288293 / 8000000000000)) (orderedInterval (-25034628007 / 1000000000000) (-25034626635 / 1000000000000), orderedInterval (56223573762 / 1000000000000) (56223575133 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState023, besselGridState025, besselGridState027, besselGridState031, besselGridState032, besselGridState034, besselGridState036, besselGridState037, besselGridState038, besselGridState040, besselGridState045, besselGridState047, besselGridState049, besselGridState054, besselGridState057, besselGridState058, besselGridState061, besselGridState066, besselGridState069, besselGridState071, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate216_stateChecks5 :
    compactCertificate216.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (1123434635845717 / 8000000000000)) (orderedInterval (10582782442 / 1000000000000) (10582782496 / 1000000000000), orderedInterval (-66531392665 / 1000000000000) (-66531392611 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (992588571124057 / 8000000000000)) (orderedInterval (-51670501471 / 1000000000000) (-51670423029 / 1000000000000), orderedInterval (49818134708 / 1000000000000) (49818213150 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (287690855909643 / 1600000000000)) (orderedInterval (-59428003410 / 1000000000000) (-59428003382 / 1000000000000), orderedInterval (-2813977773 / 1000000000000) (-2813977745 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState023, besselGridState025, besselGridState027, besselGridState031, besselGridState032, besselGridState034, besselGridState036, besselGridState037, besselGridState038, besselGridState040, besselGridState045, besselGridState047, besselGridState049, besselGridState054, besselGridState057, besselGridState058, besselGridState061, besselGridState066, besselGridState069, besselGridState071, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate216_stateChecks6 :
    compactCertificate216.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (795768047786321 / 8000000000000)) (orderedInterval (-21786633343 / 1000000000000) (-21786632981 / 1000000000000), orderedInterval (77086552140 / 1000000000000) (77086552502 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (674581386998281 / 8000000000000)) (orderedInterval (-24311652463 / 1000000000000) (-24311652462 / 1000000000000), orderedInterval (-83275633509 / 1000000000000) (-83275633508 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 17 12 (422121710165443 / 8000000000000)) (orderedInterval (-15454329278 / 1000000000000) (-15454329276 / 1000000000000), orderedInterval (-108604776606 / 1000000000000) (-108604776604 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState023, besselGridState025, besselGridState027, besselGridState031, besselGridState032, besselGridState034, besselGridState036, besselGridState037, besselGridState038, besselGridState040, besselGridState045, besselGridState047, besselGridState049, besselGridState054, besselGridState057, besselGridState058, besselGridState061, besselGridState066, besselGridState069, besselGridState071, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate216_stateChecks7 :
    compactCertificate216.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 9 12 (227018459640381 / 8000000000000)) (orderedInterval (-115810392476 / 1000000000000) (-115810392475 / 1000000000000), orderedInterval (-92941069103 / 1000000000000) (-92941069102 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (616399279304143 / 8000000000000)) (orderedInterval (58982513398 / 1000000000000) (58982553660 / 1000000000000), orderedInterval (-69545766675 / 1000000000000) (-69545726413 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (841640518294511 / 8000000000000)) (orderedInterval (-57133349782 / 1000000000000) (-57133250009 / 1000000000000), orderedInterval (53063592684 / 1000000000000) (53063692457 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState023, besselGridState025, besselGridState027, besselGridState031, besselGridState032, besselGridState034, besselGridState036, besselGridState037, besselGridState038, besselGridState040, besselGridState045, besselGridState047, besselGridState049, besselGridState054, besselGridState057, besselGridState058, besselGridState061, besselGridState066, besselGridState069, besselGridState071, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate216_stateChecks8 :
    compactCertificate216.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 14 12 (355878289834557 / 8000000000000)) (orderedInterval (114774980455 / 1000000000000) (114774980456 / 1000000000000), orderedInterval (32428049889 / 1000000000000) (32428049890 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (1446625490405597 / 8000000000000)) (orderedInterval (-33477261629 / 1000000000000) (-33477252667 / 1000000000000), orderedInterval (49080889732 / 1000000000000) (49080898693 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (966278785087123 / 8000000000000)) (orderedInterval (59175613614 / 1000000000000) (59175659540 / 1000000000000), orderedInterval (-42303527677 / 1000000000000) (-42303481751 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState009, besselGridState014, besselGridState017, besselGridState018, besselGridState023, besselGridState025, besselGridState027, besselGridState031, besselGridState032, besselGridState034, besselGridState036, besselGridState037, besselGridState038, besselGridState040, besselGridState045, besselGridState047, besselGridState049, besselGridState054, besselGridState057, besselGridState058, besselGridState061, besselGridState066, besselGridState069, besselGridState071, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate216_states : ∀ j,
    BesselStateValid (compactCertificate216.point j) (compactCertificate216.state j) :=
  compactCertificate216.statesValid_of_checks3 compactCertificate216_stateChecks0
    compactCertificate216_stateChecks1 compactCertificate216_stateChecks2
    compactCertificate216_stateChecks3 compactCertificate216_stateChecks4
    compactCertificate216_stateChecks5 compactCertificate216_stateChecks6
    compactCertificate216_stateChecks7 compactCertificate216_stateChecks8

theorem compactCertificate216_chunkChecks0_0 :
    compactCertificate216.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (389 / 4) 0 (IntervalRat.scale (389 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-48625095300 / 1000000000000) (-48625095299 / 1000000000000), orderedInterval (-64417176013 / 1000000000000) (-64417176012 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (573071278733489 / 8000000000000) 0 (IntervalRat.scale (389 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-15105741096 / 1000000000000) (-15105741095 / 1000000000000), orderedInterval (-92949124861 / 1000000000000) (-92949124860 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (185319477049937 / 1600000000000) 0 (IntervalRat.scale (389 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-26813657881 / 1000000000000) (-26813657880 / 1000000000000), orderedInterval (-69003528660 / 1000000000000) (-69003528659 / 1000000000000)))) (orderedInterval (-20987497776 / 1000000000000) (-20987497768 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (167220769874323 / 8000000000000) 0 (IntervalRat.scale (389 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (53085545927 / 1000000000000) (53085546775 / 1000000000000), orderedInterval (-167538449952 / 1000000000000) (-167538449104 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (449178509429431 / 8000000000000) 0 (IntervalRat.scale (389 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (39675234896 / 1000000000000) (39675234897 / 1000000000000), orderedInterval (98462622742 / 1000000000000) (98462622743 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1219607030764827 / 8000000000000) 0 (IntervalRat.scale (389 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (41757523126 / 1000000000000) (41757550865 / 1000000000000), orderedInterval (-49454434588 / 1000000000000) (-49454406849 / 1000000000000)))) (orderedInterval (-2095857752 / 1000000000000) (-2095855758 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (898357018859251 / 8000000000000) 0 (IntervalRat.scale (389 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-1387064627 / 1000000000000) (-1387064619 / 1000000000000), orderedInterval (75287806643 / 1000000000000) (75287806651 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1539350063820223 / 8000000000000) 0 (IntervalRat.scale (389 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-57519001871 / 1000000000000) (-57519001810 / 1000000000000), orderedInterval (-106020955 / 1000000000000) (-106020894 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1133878289834557 / 8000000000000) 0 (IntervalRat.scale (389 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-61107914758 / 1000000000000) (-61107914757 / 1000000000000), orderedInterval (-27305897325 / 1000000000000) (-27305897324 / 1000000000000)))) (orderedInterval (297258412 / 1000000000000) (297258421 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate216_chunkChecks0_1 :
    compactCertificate216.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1739660886494611 / 8000000000000) 0 (IntervalRat.scale (389 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-53845875045 / 1000000000000) (-53845875027 / 1000000000000), orderedInterval (-5183939264 / 1000000000000) (-5183939246 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1004393681116219 / 8000000000000) 0 (IntervalRat.scale (389 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (44214215595 / 1000000000000) (44214215596 / 1000000000000), orderedInterval (55643195605 / 1000000000000) (55643195606 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1782314212566071 / 8000000000000) 0 (IntervalRat.scale (389 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-26608986279 / 1000000000000) (-26608986278 / 1000000000000), orderedInterval (-46302582360 / 1000000000000) (-46302582359 / 1000000000000)))) (orderedInterval (9061047195 / 1000000000000) (9061047237 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1665269133098099 / 8000000000000) 0 (IntervalRat.scale (389 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (55281222810 / 1000000000000) (55281222917 / 1000000000000), orderedInterval (-1654947155 / 1000000000000) (-1654947048 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1188414630224867 / 8000000000000) 0 (IntervalRat.scale (389 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-65062640665 / 1000000000000) (-65062640443 / 1000000000000), orderedInterval (7453297722 / 1000000000000) (7453297944 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1347535528288293 / 8000000000000) 0 (IntervalRat.scale (389 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-25034628007 / 1000000000000) (-25034626635 / 1000000000000), orderedInterval (56223573762 / 1000000000000) (56223575133 / 1000000000000)))) (orderedInterval (-7023816818 / 1000000000000) (-7023816776 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1123434635845717 / 8000000000000) 0 (IntervalRat.scale (389 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (10582782442 / 1000000000000) (10582782496 / 1000000000000), orderedInterval (-66531392665 / 1000000000000) (-66531392611 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (992588571124057 / 8000000000000) 0 (IntervalRat.scale (389 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-51670501471 / 1000000000000) (-51670423029 / 1000000000000), orderedInterval (49818134708 / 1000000000000) (49818213150 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (287690855909643 / 1600000000000) 0 (IntervalRat.scale (389 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-59428003410 / 1000000000000) (-59428003382 / 1000000000000), orderedInterval (-2813977773 / 1000000000000) (-2813977745 / 1000000000000)))) (orderedInterval (1557541455 / 1000000000000) (1557545956 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate216_chunkChecks0_2 :
    compactCertificate216.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (795768047786321 / 8000000000000) 0 (IntervalRat.scale (389 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-21786633343 / 1000000000000) (-21786632981 / 1000000000000), orderedInterval (77086552140 / 1000000000000) (77086552502 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (674581386998281 / 8000000000000) 0 (IntervalRat.scale (389 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-24311652463 / 1000000000000) (-24311652462 / 1000000000000), orderedInterval (-83275633509 / 1000000000000) (-83275633508 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (422121710165443 / 8000000000000) 0 (IntervalRat.scale (389 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-15454329278 / 1000000000000) (-15454329276 / 1000000000000), orderedInterval (-108604776606 / 1000000000000) (-108604776604 / 1000000000000)))) (orderedInterval (4356436520 / 1000000000000) (4356436603 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (227018459640381 / 8000000000000) 0 (IntervalRat.scale (389 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-115810392476 / 1000000000000) (-115810392475 / 1000000000000), orderedInterval (-92941069103 / 1000000000000) (-92941069102 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (616399279304143 / 8000000000000) 0 (IntervalRat.scale (389 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (58982513398 / 1000000000000) (58982553660 / 1000000000000), orderedInterval (-69545766675 / 1000000000000) (-69545726413 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (841640518294511 / 8000000000000) 0 (IntervalRat.scale (389 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-57133349782 / 1000000000000) (-57133250009 / 1000000000000), orderedInterval (53063592684 / 1000000000000) (53063692457 / 1000000000000)))) (orderedInterval (5178951105 / 1000000000000) (5178959678 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (355878289834557 / 8000000000000) 0 (IntervalRat.scale (389 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (114774980455 / 1000000000000) (114774980456 / 1000000000000), orderedInterval (32428049889 / 1000000000000) (32428049890 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1446625490405597 / 8000000000000) 0 (IntervalRat.scale (389 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-33477261629 / 1000000000000) (-33477252667 / 1000000000000), orderedInterval (49080889732 / 1000000000000) (49080898693 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (966278785087123 / 8000000000000) 0 (IntervalRat.scale (389 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (59175613614 / 1000000000000) (59175659540 / 1000000000000), orderedInterval (-42303527677 / 1000000000000) (-42303481751 / 1000000000000)))) (orderedInterval (-7685914412 / 1000000000000) (-7685905038 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate216_chunkChecks0 :
    compactCertificate216.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate216.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate216_chunkChecks0_0
    compactCertificate216_chunkChecks0_1 compactCertificate216_chunkChecks0_2

theorem compactCertificate216_chunkChecks1_0 :
    compactCertificate216.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (389 / 4) 1 (IntervalRat.scale (389 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-48625095300 / 1000000000000) (-48625095299 / 1000000000000), orderedInterval (-64417176013 / 1000000000000) (-64417176012 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (573071278733489 / 8000000000000) 1 (IntervalRat.scale (389 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-15105741096 / 1000000000000) (-15105741095 / 1000000000000), orderedInterval (-92949124861 / 1000000000000) (-92949124860 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (185319477049937 / 1600000000000) 1 (IntervalRat.scale (389 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-26813657881 / 1000000000000) (-26813657880 / 1000000000000), orderedInterval (-69003528660 / 1000000000000) (-69003528659 / 1000000000000)))) (orderedInterval (-30993283751 / 1000000000000) (-30993283742 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (167220769874323 / 8000000000000) 1 (IntervalRat.scale (389 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (53085545927 / 1000000000000) (53085546775 / 1000000000000), orderedInterval (-167538449952 / 1000000000000) (-167538449104 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (449178509429431 / 8000000000000) 1 (IntervalRat.scale (389 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (39675234896 / 1000000000000) (39675234897 / 1000000000000), orderedInterval (98462622742 / 1000000000000) (98462622743 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1219607030764827 / 8000000000000) 1 (IntervalRat.scale (389 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (41757523126 / 1000000000000) (41757550865 / 1000000000000), orderedInterval (-49454434588 / 1000000000000) (-49454406849 / 1000000000000)))) (orderedInterval (7977552778 / 1000000000000) (7977555886 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (898357018859251 / 8000000000000) 1 (IntervalRat.scale (389 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-1387064627 / 1000000000000) (-1387064619 / 1000000000000), orderedInterval (75287806643 / 1000000000000) (75287806651 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1539350063820223 / 8000000000000) 1 (IntervalRat.scale (389 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-57519001871 / 1000000000000) (-57519001810 / 1000000000000), orderedInterval (-106020955 / 1000000000000) (-106020894 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1133878289834557 / 8000000000000) 1 (IntervalRat.scale (389 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-61107914758 / 1000000000000) (-61107914757 / 1000000000000), orderedInterval (-27305897325 / 1000000000000) (-27305897324 / 1000000000000)))) (orderedInterval (-955329153 / 1000000000000) (-955329139 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate216_chunkChecks1_1 :
    compactCertificate216.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1739660886494611 / 8000000000000) 1 (IntervalRat.scale (389 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-53845875045 / 1000000000000) (-53845875027 / 1000000000000), orderedInterval (-5183939264 / 1000000000000) (-5183939246 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1004393681116219 / 8000000000000) 1 (IntervalRat.scale (389 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (44214215595 / 1000000000000) (44214215596 / 1000000000000), orderedInterval (55643195605 / 1000000000000) (55643195606 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1782314212566071 / 8000000000000) 1 (IntervalRat.scale (389 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-26608986279 / 1000000000000) (-26608986278 / 1000000000000), orderedInterval (-46302582360 / 1000000000000) (-46302582359 / 1000000000000)))) (orderedInterval (-7696995632 / 1000000000000) (-7696995544 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1665269133098099 / 8000000000000) 1 (IntervalRat.scale (389 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (55281222810 / 1000000000000) (55281222917 / 1000000000000), orderedInterval (-1654947155 / 1000000000000) (-1654947048 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1188414630224867 / 8000000000000) 1 (IntervalRat.scale (389 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-65062640665 / 1000000000000) (-65062640443 / 1000000000000), orderedInterval (7453297722 / 1000000000000) (7453297944 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1347535528288293 / 8000000000000) 1 (IntervalRat.scale (389 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-25034628007 / 1000000000000) (-25034626635 / 1000000000000), orderedInterval (56223573762 / 1000000000000) (56223575133 / 1000000000000)))) (orderedInterval (647748222 / 1000000000000) (647748290 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1123434635845717 / 8000000000000) 1 (IntervalRat.scale (389 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (10582782442 / 1000000000000) (10582782496 / 1000000000000), orderedInterval (-66531392665 / 1000000000000) (-66531392611 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (992588571124057 / 8000000000000) 1 (IntervalRat.scale (389 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-51670501471 / 1000000000000) (-51670423029 / 1000000000000), orderedInterval (49818134708 / 1000000000000) (49818213150 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (287690855909643 / 1600000000000) 1 (IntervalRat.scale (389 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-59428003410 / 1000000000000) (-59428003382 / 1000000000000), orderedInterval (-2813977773 / 1000000000000) (-2813977745 / 1000000000000)))) (orderedInterval (-4879891630 / 1000000000000) (-4879885887 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate216_chunkChecks1_2 :
    compactCertificate216.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (795768047786321 / 8000000000000) 1 (IntervalRat.scale (389 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-21786633343 / 1000000000000) (-21786632981 / 1000000000000), orderedInterval (77086552140 / 1000000000000) (77086552502 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (674581386998281 / 8000000000000) 1 (IntervalRat.scale (389 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-24311652463 / 1000000000000) (-24311652462 / 1000000000000), orderedInterval (-83275633509 / 1000000000000) (-83275633508 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (422121710165443 / 8000000000000) 1 (IntervalRat.scale (389 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-15454329278 / 1000000000000) (-15454329276 / 1000000000000), orderedInterval (-108604776606 / 1000000000000) (-108604776604 / 1000000000000)))) (orderedInterval (-10438550769 / 1000000000000) (-10438550687 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (227018459640381 / 8000000000000) 1 (IntervalRat.scale (389 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-115810392476 / 1000000000000) (-115810392475 / 1000000000000), orderedInterval (-92941069103 / 1000000000000) (-92941069102 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (616399279304143 / 8000000000000) 1 (IntervalRat.scale (389 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (58982513398 / 1000000000000) (58982553660 / 1000000000000), orderedInterval (-69545766675 / 1000000000000) (-69545726413 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (841640518294511 / 8000000000000) 1 (IntervalRat.scale (389 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-57133349782 / 1000000000000) (-57133250009 / 1000000000000), orderedInterval (53063592684 / 1000000000000) (53063692457 / 1000000000000)))) (orderedInterval (-2648577990 / 1000000000000) (-2648568983 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (355878289834557 / 8000000000000) 1 (IntervalRat.scale (389 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (114774980455 / 1000000000000) (114774980456 / 1000000000000), orderedInterval (32428049889 / 1000000000000) (32428049890 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1446625490405597 / 8000000000000) 1 (IntervalRat.scale (389 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-33477261629 / 1000000000000) (-33477252667 / 1000000000000), orderedInterval (49080889732 / 1000000000000) (49080898693 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (966278785087123 / 8000000000000) 1 (IntervalRat.scale (389 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (59175613614 / 1000000000000) (59175659540 / 1000000000000), orderedInterval (-42303527677 / 1000000000000) (-42303481751 / 1000000000000)))) (orderedInterval (2518648009 / 1000000000000) (2518660106 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate216_chunkChecks1 :
    compactCertificate216.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate216.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate216_chunkChecks1_0
    compactCertificate216_chunkChecks1_1 compactCertificate216_chunkChecks1_2

theorem compactCertificate216_chunkChecks2_0 :
    compactCertificate216.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (389 / 4) 2 (IntervalRat.scale (389 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-48625095300 / 1000000000000) (-48625095299 / 1000000000000), orderedInterval (-64417176013 / 1000000000000) (-64417176012 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (573071278733489 / 8000000000000) 2 (IntervalRat.scale (389 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-15105741096 / 1000000000000) (-15105741095 / 1000000000000), orderedInterval (-92949124861 / 1000000000000) (-92949124860 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (185319477049937 / 1600000000000) 2 (IntervalRat.scale (389 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-26813657881 / 1000000000000) (-26813657880 / 1000000000000), orderedInterval (-69003528660 / 1000000000000) (-69003528659 / 1000000000000)))) (orderedInterval (21900267553 / 1000000000000) (21900267564 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (167220769874323 / 8000000000000) 2 (IntervalRat.scale (389 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (53085545927 / 1000000000000) (53085546775 / 1000000000000), orderedInterval (-167538449952 / 1000000000000) (-167538449104 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (449178509429431 / 8000000000000) 2 (IntervalRat.scale (389 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (39675234896 / 1000000000000) (39675234897 / 1000000000000), orderedInterval (98462622742 / 1000000000000) (98462622743 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1219607030764827 / 8000000000000) 2 (IntervalRat.scale (389 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (41757523126 / 1000000000000) (41757550865 / 1000000000000), orderedInterval (-49454434588 / 1000000000000) (-49454406849 / 1000000000000)))) (orderedInterval (6756644576 / 1000000000000) (6756649474 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (898357018859251 / 8000000000000) 2 (IntervalRat.scale (389 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-1387064627 / 1000000000000) (-1387064619 / 1000000000000), orderedInterval (75287806643 / 1000000000000) (75287806651 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1539350063820223 / 8000000000000) 2 (IntervalRat.scale (389 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-57519001871 / 1000000000000) (-57519001810 / 1000000000000), orderedInterval (-106020955 / 1000000000000) (-106020894 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1133878289834557 / 8000000000000) 2 (IntervalRat.scale (389 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-61107914758 / 1000000000000) (-61107914757 / 1000000000000), orderedInterval (-27305897325 / 1000000000000) (-27305897324 / 1000000000000)))) (orderedInterval (-3798598348 / 1000000000000) (-3798598323 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate216_chunkChecks2_1 :
    compactCertificate216.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1739660886494611 / 8000000000000) 2 (IntervalRat.scale (389 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-53845875045 / 1000000000000) (-53845875027 / 1000000000000), orderedInterval (-5183939264 / 1000000000000) (-5183939246 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1004393681116219 / 8000000000000) 2 (IntervalRat.scale (389 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (44214215595 / 1000000000000) (44214215596 / 1000000000000), orderedInterval (55643195605 / 1000000000000) (55643195606 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1782314212566071 / 8000000000000) 2 (IntervalRat.scale (389 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-26608986279 / 1000000000000) (-26608986278 / 1000000000000), orderedInterval (-46302582360 / 1000000000000) (-46302582359 / 1000000000000)))) (orderedInterval (-33367591011 / 1000000000000) (-33367590822 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1665269133098099 / 8000000000000) 2 (IntervalRat.scale (389 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (55281222810 / 1000000000000) (55281222917 / 1000000000000), orderedInterval (-1654947155 / 1000000000000) (-1654947048 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1188414630224867 / 8000000000000) 2 (IntervalRat.scale (389 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-65062640665 / 1000000000000) (-65062640443 / 1000000000000), orderedInterval (7453297722 / 1000000000000) (7453297944 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1347535528288293 / 8000000000000) 2 (IntervalRat.scale (389 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-25034628007 / 1000000000000) (-25034626635 / 1000000000000), orderedInterval (56223573762 / 1000000000000) (56223575133 / 1000000000000)))) (orderedInterval (18541469085 / 1000000000000) (18541469196 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1123434635845717 / 8000000000000) 2 (IntervalRat.scale (389 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (10582782442 / 1000000000000) (10582782496 / 1000000000000), orderedInterval (-66531392665 / 1000000000000) (-66531392611 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (992588571124057 / 8000000000000) 2 (IntervalRat.scale (389 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-51670501471 / 1000000000000) (-51670423029 / 1000000000000), orderedInterval (49818134708 / 1000000000000) (49818213150 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (287690855909643 / 1600000000000) 2 (IntervalRat.scale (389 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-59428003410 / 1000000000000) (-59428003382 / 1000000000000), orderedInterval (-2813977773 / 1000000000000) (-2813977745 / 1000000000000)))) (orderedInterval (183837668 / 1000000000000) (183845058 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate216_chunkChecks2_2 :
    compactCertificate216.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (795768047786321 / 8000000000000) 2 (IntervalRat.scale (389 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-21786633343 / 1000000000000) (-21786632981 / 1000000000000), orderedInterval (77086552140 / 1000000000000) (77086552502 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (674581386998281 / 8000000000000) 2 (IntervalRat.scale (389 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-24311652463 / 1000000000000) (-24311652462 / 1000000000000), orderedInterval (-83275633509 / 1000000000000) (-83275633508 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (422121710165443 / 8000000000000) 2 (IntervalRat.scale (389 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-15454329278 / 1000000000000) (-15454329276 / 1000000000000), orderedInterval (-108604776606 / 1000000000000) (-108604776604 / 1000000000000)))) (orderedInterval (-4423523316 / 1000000000000) (-4423523232 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (227018459640381 / 8000000000000) 2 (IntervalRat.scale (389 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-115810392476 / 1000000000000) (-115810392475 / 1000000000000), orderedInterval (-92941069103 / 1000000000000) (-92941069102 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (616399279304143 / 8000000000000) 2 (IntervalRat.scale (389 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (58982513398 / 1000000000000) (58982553660 / 1000000000000), orderedInterval (-69545766675 / 1000000000000) (-69545726413 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (841640518294511 / 8000000000000) 2 (IntervalRat.scale (389 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-57133349782 / 1000000000000) (-57133250009 / 1000000000000), orderedInterval (53063592684 / 1000000000000) (53063692457 / 1000000000000)))) (orderedInterval (-4439157601 / 1000000000000) (-4439147975 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (355878289834557 / 8000000000000) 2 (IntervalRat.scale (389 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (114774980455 / 1000000000000) (114774980456 / 1000000000000), orderedInterval (32428049889 / 1000000000000) (32428049890 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1446625490405597 / 8000000000000) 2 (IntervalRat.scale (389 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-33477261629 / 1000000000000) (-33477252667 / 1000000000000), orderedInterval (49080889732 / 1000000000000) (49080898693 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (966278785087123 / 8000000000000) 2 (IntervalRat.scale (389 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (59175613614 / 1000000000000) (59175659540 / 1000000000000), orderedInterval (-42303527677 / 1000000000000) (-42303481751 / 1000000000000)))) (orderedInterval (7534519246 / 1000000000000) (7534535241 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate216_chunkChecks2 :
    compactCertificate216.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate216.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate216_chunkChecks2_0
    compactCertificate216_chunkChecks2_1 compactCertificate216_chunkChecks2_2

theorem compactCertificate216_chunkChecks3_0 :
    compactCertificate216.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (389 / 4) 3 (IntervalRat.scale (389 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-48625095300 / 1000000000000) (-48625095299 / 1000000000000), orderedInterval (-64417176013 / 1000000000000) (-64417176012 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (573071278733489 / 8000000000000) 3 (IntervalRat.scale (389 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-15105741096 / 1000000000000) (-15105741095 / 1000000000000), orderedInterval (-92949124861 / 1000000000000) (-92949124860 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (185319477049937 / 1600000000000) 3 (IntervalRat.scale (389 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-26813657881 / 1000000000000) (-26813657880 / 1000000000000), orderedInterval (-69003528660 / 1000000000000) (-69003528659 / 1000000000000)))) (orderedInterval (32491144333 / 1000000000000) (32491144345 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (167220769874323 / 8000000000000) 3 (IntervalRat.scale (389 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (53085545927 / 1000000000000) (53085546775 / 1000000000000), orderedInterval (-167538449952 / 1000000000000) (-167538449104 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (449178509429431 / 8000000000000) 3 (IntervalRat.scale (389 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (39675234896 / 1000000000000) (39675234897 / 1000000000000), orderedInterval (98462622742 / 1000000000000) (98462622743 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1219607030764827 / 8000000000000) 3 (IntervalRat.scale (389 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (41757523126 / 1000000000000) (41757550865 / 1000000000000), orderedInterval (-49454434588 / 1000000000000) (-49454406849 / 1000000000000)))) (orderedInterval (-14322099024 / 1000000000000) (-14322091349 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (898357018859251 / 8000000000000) 3 (IntervalRat.scale (389 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-1387064627 / 1000000000000) (-1387064619 / 1000000000000), orderedInterval (75287806643 / 1000000000000) (75287806651 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1539350063820223 / 8000000000000) 3 (IntervalRat.scale (389 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-57519001871 / 1000000000000) (-57519001810 / 1000000000000), orderedInterval (-106020955 / 1000000000000) (-106020894 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1133878289834557 / 8000000000000) 3 (IntervalRat.scale (389 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-61107914758 / 1000000000000) (-61107914757 / 1000000000000), orderedInterval (-27305897325 / 1000000000000) (-27305897324 / 1000000000000)))) (orderedInterval (2056581151 / 1000000000000) (2056581197 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate216_chunkChecks3_1 :
    compactCertificate216.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1739660886494611 / 8000000000000) 3 (IntervalRat.scale (389 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-53845875045 / 1000000000000) (-53845875027 / 1000000000000), orderedInterval (-5183939264 / 1000000000000) (-5183939246 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1004393681116219 / 8000000000000) 3 (IntervalRat.scale (389 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (44214215595 / 1000000000000) (44214215596 / 1000000000000), orderedInterval (55643195605 / 1000000000000) (55643195606 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1782314212566071 / 8000000000000) 3 (IntervalRat.scale (389 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-26608986279 / 1000000000000) (-26608986278 / 1000000000000), orderedInterval (-46302582360 / 1000000000000) (-46302582359 / 1000000000000)))) (orderedInterval (60311003007 / 1000000000000) (60311003420 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1665269133098099 / 8000000000000) 3 (IntervalRat.scale (389 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (55281222810 / 1000000000000) (55281222917 / 1000000000000), orderedInterval (-1654947155 / 1000000000000) (-1654947048 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1188414630224867 / 8000000000000) 3 (IntervalRat.scale (389 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-65062640665 / 1000000000000) (-65062640443 / 1000000000000), orderedInterval (7453297722 / 1000000000000) (7453297944 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1347535528288293 / 8000000000000) 3 (IntervalRat.scale (389 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-25034628007 / 1000000000000) (-25034626635 / 1000000000000), orderedInterval (56223573762 / 1000000000000) (56223575133 / 1000000000000)))) (orderedInterval (-1517233890 / 1000000000000) (-1517233705 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1123434635845717 / 8000000000000) 3 (IntervalRat.scale (389 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (10582782442 / 1000000000000) (10582782496 / 1000000000000), orderedInterval (-66531392665 / 1000000000000) (-66531392611 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (992588571124057 / 8000000000000) 3 (IntervalRat.scale (389 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-51670501471 / 1000000000000) (-51670423029 / 1000000000000), orderedInterval (49818134708 / 1000000000000) (49818213150 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (287690855909643 / 1600000000000) 3 (IntervalRat.scale (389 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-59428003410 / 1000000000000) (-59428003382 / 1000000000000), orderedInterval (-2813977773 / 1000000000000) (-2813977745 / 1000000000000)))) (orderedInterval (8686697005 / 1000000000000) (8686706440 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate216_chunkChecks3_2 :
    compactCertificate216.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (795768047786321 / 8000000000000) 3 (IntervalRat.scale (389 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-21786633343 / 1000000000000) (-21786632981 / 1000000000000), orderedInterval (77086552140 / 1000000000000) (77086552502 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (674581386998281 / 8000000000000) 3 (IntervalRat.scale (389 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-24311652463 / 1000000000000) (-24311652462 / 1000000000000), orderedInterval (-83275633509 / 1000000000000) (-83275633508 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (422121710165443 / 8000000000000) 3 (IntervalRat.scale (389 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-15454329278 / 1000000000000) (-15454329276 / 1000000000000), orderedInterval (-108604776606 / 1000000000000) (-108604776604 / 1000000000000)))) (orderedInterval (10726039061 / 1000000000000) (10726039146 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (227018459640381 / 8000000000000) 3 (IntervalRat.scale (389 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-115810392476 / 1000000000000) (-115810392475 / 1000000000000), orderedInterval (-92941069103 / 1000000000000) (-92941069102 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (616399279304143 / 8000000000000) 3 (IntervalRat.scale (389 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (58982513398 / 1000000000000) (58982553660 / 1000000000000), orderedInterval (-69545766675 / 1000000000000) (-69545726413 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (841640518294511 / 8000000000000) 3 (IntervalRat.scale (389 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-57133349782 / 1000000000000) (-57133250009 / 1000000000000), orderedInterval (53063592684 / 1000000000000) (53063692457 / 1000000000000)))) (orderedInterval (4366620543 / 1000000000000) (4366630786 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (355878289834557 / 8000000000000) 3 (IntervalRat.scale (389 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (114774980455 / 1000000000000) (114774980456 / 1000000000000), orderedInterval (32428049889 / 1000000000000) (32428049890 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1446625490405597 / 8000000000000) 3 (IntervalRat.scale (389 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-33477261629 / 1000000000000) (-33477252667 / 1000000000000), orderedInterval (49080889732 / 1000000000000) (49080898693 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (966278785087123 / 8000000000000) 3 (IntervalRat.scale (389 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (59175613614 / 1000000000000) (59175659540 / 1000000000000), orderedInterval (-42303527677 / 1000000000000) (-42303481751 / 1000000000000)))) (orderedInterval (10382006918 / 1000000000000) (10382028364 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate216_chunkChecks3 :
    compactCertificate216.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate216.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate216_chunkChecks3_0
    compactCertificate216_chunkChecks3_1 compactCertificate216_chunkChecks3_2

theorem compactCertificate216_chunkChecks4_0 :
    compactCertificate216.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (389 / 4) 4 (IntervalRat.scale (389 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-48625095300 / 1000000000000) (-48625095299 / 1000000000000), orderedInterval (-64417176013 / 1000000000000) (-64417176012 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (573071278733489 / 8000000000000) 4 (IntervalRat.scale (389 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-15105741096 / 1000000000000) (-15105741095 / 1000000000000), orderedInterval (-92949124861 / 1000000000000) (-92949124860 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (185319477049937 / 1600000000000) 4 (IntervalRat.scale (389 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-26813657881 / 1000000000000) (-26813657880 / 1000000000000), orderedInterval (-69003528660 / 1000000000000) (-69003528659 / 1000000000000)))) (orderedInterval (-23146495241 / 1000000000000) (-23146495227 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (167220769874323 / 8000000000000) 4 (IntervalRat.scale (389 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (53085545927 / 1000000000000) (53085546775 / 1000000000000), orderedInterval (-167538449952 / 1000000000000) (-167538449104 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (449178509429431 / 8000000000000) 4 (IntervalRat.scale (389 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (39675234896 / 1000000000000) (39675234897 / 1000000000000), orderedInterval (98462622742 / 1000000000000) (98462622743 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1219607030764827 / 8000000000000) 4 (IntervalRat.scale (389 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (41757523126 / 1000000000000) (41757550865 / 1000000000000), orderedInterval (-49454434588 / 1000000000000) (-49454406849 / 1000000000000)))) (orderedInterval (-17471818895 / 1000000000000) (-17471806788 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (898357018859251 / 8000000000000) 4 (IntervalRat.scale (389 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-1387064627 / 1000000000000) (-1387064619 / 1000000000000), orderedInterval (75287806643 / 1000000000000) (75287806651 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1539350063820223 / 8000000000000) 4 (IntervalRat.scale (389 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-57519001871 / 1000000000000) (-57519001810 / 1000000000000), orderedInterval (-106020955 / 1000000000000) (-106020894 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1133878289834557 / 8000000000000) 4 (IntervalRat.scale (389 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-61107914758 / 1000000000000) (-61107914757 / 1000000000000), orderedInterval (-27305897325 / 1000000000000) (-27305897324 / 1000000000000)))) (orderedInterval (20484308069 / 1000000000000) (20484308156 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate216_chunkChecks4_1 :
    compactCertificate216.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1739660886494611 / 8000000000000) 4 (IntervalRat.scale (389 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-53845875045 / 1000000000000) (-53845875027 / 1000000000000), orderedInterval (-5183939264 / 1000000000000) (-5183939246 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1004393681116219 / 8000000000000) 4 (IntervalRat.scale (389 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (44214215595 / 1000000000000) (44214215596 / 1000000000000), orderedInterval (55643195605 / 1000000000000) (55643195606 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1782314212566071 / 8000000000000) 4 (IntervalRat.scale (389 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-26608986279 / 1000000000000) (-26608986278 / 1000000000000), orderedInterval (-46302582360 / 1000000000000) (-46302582359 / 1000000000000)))) (orderedInterval (142863340588 / 1000000000000) (142863341507 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1665269133098099 / 8000000000000) 4 (IntervalRat.scale (389 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (55281222810 / 1000000000000) (55281222917 / 1000000000000), orderedInterval (-1654947155 / 1000000000000) (-1654947048 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1188414630224867 / 8000000000000) 4 (IntervalRat.scale (389 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-65062640665 / 1000000000000) (-65062640443 / 1000000000000), orderedInterval (7453297722 / 1000000000000) (7453297944 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1347535528288293 / 8000000000000) 4 (IntervalRat.scale (389 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-25034628007 / 1000000000000) (-25034626635 / 1000000000000), orderedInterval (56223573762 / 1000000000000) (56223575133 / 1000000000000)))) (orderedInterval (-53271911534 / 1000000000000) (-53271911221 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1123434635845717 / 8000000000000) 4 (IntervalRat.scale (389 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (10582782442 / 1000000000000) (10582782496 / 1000000000000), orderedInterval (-66531392665 / 1000000000000) (-66531392611 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (992588571124057 / 8000000000000) 4 (IntervalRat.scale (389 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-51670501471 / 1000000000000) (-51670423029 / 1000000000000), orderedInterval (49818134708 / 1000000000000) (49818213150 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (287690855909643 / 1600000000000) 4 (IntervalRat.scale (389 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-59428003410 / 1000000000000) (-59428003382 / 1000000000000), orderedInterval (-2813977773 / 1000000000000) (-2813977745 / 1000000000000)))) (orderedInterval (-9594325115 / 1000000000000) (-9594312971 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate216_chunkChecks4_2 :
    compactCertificate216.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (795768047786321 / 8000000000000) 4 (IntervalRat.scale (389 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-21786633343 / 1000000000000) (-21786632981 / 1000000000000), orderedInterval (77086552140 / 1000000000000) (77086552502 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (674581386998281 / 8000000000000) 4 (IntervalRat.scale (389 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-24311652463 / 1000000000000) (-24311652462 / 1000000000000), orderedInterval (-83275633509 / 1000000000000) (-83275633508 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (422121710165443 / 8000000000000) 4 (IntervalRat.scale (389 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-15454329278 / 1000000000000) (-15454329276 / 1000000000000), orderedInterval (-108604776606 / 1000000000000) (-108604776604 / 1000000000000)))) (orderedInterval (4325936401 / 1000000000000) (4325936487 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (227018459640381 / 8000000000000) 4 (IntervalRat.scale (389 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-115810392476 / 1000000000000) (-115810392475 / 1000000000000), orderedInterval (-92941069103 / 1000000000000) (-92941069102 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (616399279304143 / 8000000000000) 4 (IntervalRat.scale (389 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (58982513398 / 1000000000000) (58982553660 / 1000000000000), orderedInterval (-69545766675 / 1000000000000) (-69545726413 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (841640518294511 / 8000000000000) 4 (IntervalRat.scale (389 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-57133349782 / 1000000000000) (-57133250009 / 1000000000000), orderedInterval (53063592684 / 1000000000000) (53063692457 / 1000000000000)))) (orderedInterval (5394861980 / 1000000000000) (5394873030 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (355878289834557 / 8000000000000) 4 (IntervalRat.scale (389 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (114774980455 / 1000000000000) (114774980456 / 1000000000000), orderedInterval (32428049889 / 1000000000000) (32428049890 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1446625490405597 / 8000000000000) 4 (IntervalRat.scale (389 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-33477261629 / 1000000000000) (-33477252667 / 1000000000000), orderedInterval (49080889732 / 1000000000000) (49080898693 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (966278785087123 / 8000000000000) 4 (IntervalRat.scale (389 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (59175613614 / 1000000000000) (59175659540 / 1000000000000), orderedInterval (-42303527677 / 1000000000000) (-42303481751 / 1000000000000)))) (orderedInterval (5973222238 / 1000000000000) (5973252033 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate216_chunkChecks4 :
    compactCertificate216.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate216.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate216_chunkChecks4_0
    compactCertificate216_chunkChecks4_1 compactCertificate216_chunkChecks4_2

theorem compactCertificate216_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate216.chunkCheck r b = true :=
  compactCertificate216.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate216_chunkChecks0
    · exact compactCertificate216_chunkChecks1
    · exact compactCertificate216_chunkChecks2
    · exact compactCertificate216_chunkChecks3
    · exact compactCertificate216_chunkChecks4)

theorem compactCertificate216_coefficient0 :
    compactCertificate216.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate216, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate216_coefficient1 :
    compactCertificate216.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate216, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate216_coefficient2 :
    compactCertificate216.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate216, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate216_coefficient3 :
    compactCertificate216.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate216, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate216_coefficient4 :
    compactCertificate216.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate216, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate216_coefficients : ∀ r : Fin 5,
    compactCertificate216.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate216_coefficient0
  · exact compactCertificate216_coefficient1
  · exact compactCertificate216_coefficient2
  · exact compactCertificate216_coefficient3
  · exact compactCertificate216_coefficient4

theorem compactCertificate216_lower : (1 : ℚ) ≤ compactCertificate216.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate216, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate216_proves {t : ℝ} (ht : t ∈ compactCertificate216.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate216.proves compactCertificate216_states compactCertificate216_chunks
    compactCertificate216_coefficients compactCertificate216_lower ht

end Erdos232
