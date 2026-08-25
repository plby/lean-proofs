/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate272 : CompactCertificate where
  left := 146
  right := 147
  center := 293 / 2
  grid := fun i =>
    match i.val with
    | 0 => 47
    | 1 => 34
    | 2 => 56
    | 3 => 10
    | 4 => 27
    | 5 => 73
    | 6 => 54
    | 7 => 92
    | 8 => 68
    | 9 => 104
    | 10 => 60
    | 11 => 107
    | 12 => 100
    | 13 => 71
    | 14 => 81
    | 15 => 67
    | 16 => 60
    | 17 => 86
    | 18 => 48
    | 19 => 40
    | 20 => 25
    | 21 => 14
    | 22 => 37
    | 23 => 50
    | 24 => 21
    | 25 => 87
    | _ => 58
  point := fun i =>
    match i.val with
    | 0 => 293 / 2
    | 1 => 431644947734993 / 4000000000000
    | 2 => 139585107392369 / 800000000000
    | 3 => 125952919211251 / 4000000000000
    | 4 => 338327257745047 / 4000000000000
    | 5 => 918624318802299 / 4000000000000
    | 6 => 676654515490387 / 4000000000000
    | 7 => 1159459045499551 / 4000000000000
    | 8 => 854052285145309 / 4000000000000
    | 9 => 1310335834814707 / 4000000000000
    | 10 => 756522746959003 / 4000000000000
    | 11 => 1342462890184727 / 4000000000000
    | 12 => 1254302971716563 / 4000000000000
    | 13 => 895129785747779 / 4000000000000
    | 14 => 1014981773235141 / 4000000000000
    | 15 => 846185985354229 / 4000000000000
    | 16 => 747630980306809 / 4000000000000
    | 17 => 216692598410091 / 800000000000
    | 18 => 599383131108977 / 4000000000000
    | 19 => 508103718227497 / 4000000000000
    | 20 => 317947714854691 / 4000000000000
    | 21 => 170993338495197 / 4000000000000
    | 22 => 464280176956591 / 4000000000000
    | 23 => 633934889101007 / 4000000000000
    | 24 => 268052285145309 / 4000000000000
    | 25 => 1089617657297789 / 4000000000000
    | _ => 727814097764851 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (23856879291 / 1000000000000) (23856880166 / 1000000000000), orderedInterval (-61533805649 / 1000000000000) (-61533804774 / 1000000000000))
    | 1 => (orderedInterval (73134054370 / 1000000000000) (73134056375 / 1000000000000), orderedInterval (-23808722155 / 1000000000000) (-23808720150 / 1000000000000))
    | 2 => (orderedInterval (-37183451534 / 1000000000000) (-37183434274 / 1000000000000), orderedInterval (47709435603 / 1000000000000) (47709452862 / 1000000000000))
    | 3 => (orderedInterval (107166690307 / 1000000000000) (107166690308 / 1000000000000), orderedInterval (91747435403 / 1000000000000) (91747435404 / 1000000000000))
    | 4 => (orderedInterval (-44807415887 / 1000000000000) (-44807415886 / 1000000000000), orderedInterval (-74025315186 / 1000000000000) (-74025315185 / 1000000000000))
    | 5 => (orderedInterval (-47033318446 / 1000000000000) (-47033318445 / 1000000000000), orderedInterval (-23560233310 / 1000000000000) (-23560233309 / 1000000000000))
    | 6 => (orderedInterval (18262813191 / 1000000000000) (18262813192 / 1000000000000), orderedInterval (58510688835 / 1000000000000) (58510688836 / 1000000000000))
    | 7 => (orderedInterval (46799944739 / 1000000000000) (46799945003 / 1000000000000), orderedInterval (-2535663128 / 1000000000000) (-2535662864 / 1000000000000))
    | 8 => (orderedInterval (33890709185 / 1000000000000) (33890709186 / 1000000000000), orderedInterval (42734941876 / 1000000000000) (42734941877 / 1000000000000))
    | 9 => (orderedInterval (43967801981 / 1000000000000) (43967802419 / 1000000000000), orderedInterval (-3262275502 / 1000000000000) (-3262275064 / 1000000000000))
    | 10 => (orderedInterval (57357831071 / 1000000000000) (57357831077 / 1000000000000), orderedInterval (8571844167 / 1000000000000) (8571844174 / 1000000000000))
    | 11 => (orderedInterval (-10789307145 / 1000000000000) (-10789307144 / 1000000000000), orderedInterval (-42179468798 / 1000000000000) (-42179468797 / 1000000000000))
    | 12 => (orderedInterval (9016792105 / 1000000000000) (9016792106 / 1000000000000), orderedInterval (44131906875 / 1000000000000) (44131906876 / 1000000000000))
    | 13 => (orderedInterval (-53251368477 / 1000000000000) (-53251368442 / 1000000000000), orderedInterval (-2897674576 / 1000000000000) (-2897674540 / 1000000000000))
    | 14 => (orderedInterval (-3070715589 / 1000000000000) (-3070715588 / 1000000000000), orderedInterval (-49988618826 / 1000000000000) (-49988618824 / 1000000000000))
    | 15 => (orderedInterval (-52814150227 / 1000000000000) (-52814147848 / 1000000000000), orderedInterval (14957879867 / 1000000000000) (14957882246 / 1000000000000))
    | 16 => (orderedInterval (-41991155960 / 1000000000000) (-41991097519 / 1000000000000), orderedInterval (40643879102 / 1000000000000) (40643937543 / 1000000000000))
    | 17 => (orderedInterval (48251733495 / 1000000000000) (48251733522 / 1000000000000), orderedInterval (4609980691 / 1000000000000) (4609980719 / 1000000000000))
    | 18 => (orderedInterval (-10776778915 / 1000000000000) (-10776778858 / 1000000000000), orderedInterval (64319574117 / 1000000000000) (64319574174 / 1000000000000))
    | 19 => (orderedInterval (59376771516 / 1000000000000) (59376803878 / 1000000000000), orderedInterval (-38783854928 / 1000000000000) (-38783822566 / 1000000000000))
    | 20 => (orderedInterval (-88347673694 / 1000000000000) (-88347673423 / 1000000000000), orderedInterval (14826347303 / 1000000000000) (14826347574 / 1000000000000))
    | 21 => (orderedInterval (-53242127926 / 1000000000000) (-53242124028 / 1000000000000), orderedInterval (110432383127 / 1000000000000) (110432387025 / 1000000000000))
    | 22 => (orderedInterval (-42755433319 / 1000000000000) (-42755433318 / 1000000000000), orderedInterval (-60287135304 / 1000000000000) (-60287135303 / 1000000000000))
    | 23 => (orderedInterval (51660044729 / 1000000000000) (51660098972 / 1000000000000), orderedInterval (-36880459466 / 1000000000000) (-36880405223 / 1000000000000))
    | 24 => (orderedInterval (-94379033944 / 1000000000000) (-94379033139 / 1000000000000), orderedInterval (25041377389 / 1000000000000) (25041378193 / 1000000000000))
    | 25 => (orderedInterval (6228886799 / 1000000000000) (6228886811 / 1000000000000), orderedInterval (-47951436193 / 1000000000000) (-47951436180 / 1000000000000))
    | _ => (orderedInterval (29691135344 / 1000000000000) (29691135345 / 1000000000000), orderedInterval (51077450276 / 1000000000000) (51077450277 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (7955531969 / 1000000000000) (7955533359 / 1000000000000)
      | 1 => orderedInterval (544902118 / 1000000000000) (544902136 / 1000000000000)
      | 2 => orderedInterval (-624425980 / 1000000000000) (-624425963 / 1000000000000)
      | 3 => orderedInterval (-5096567948 / 1000000000000) (-5096567811 / 1000000000000)
      | 4 => orderedInterval (-5182843364 / 1000000000000) (-5182843343 / 1000000000000)
      | 5 => orderedInterval (3028565561 / 1000000000000) (3028568948 / 1000000000000)
      | 6 => orderedInterval (-4513781476 / 1000000000000) (-4513779589 / 1000000000000)
      | 7 => orderedInterval (-2006062953 / 1000000000000) (-2006058706 / 1000000000000)
      | _ => orderedInterval (-6646834856 / 1000000000000) (-6646834809 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-21218887094 / 1000000000000) (-21218885515 / 1000000000000)
      | 1 => orderedInterval (851180466 / 1000000000000) (851180487 / 1000000000000)
      | 2 => orderedInterval (1660004942 / 1000000000000) (1660004974 / 1000000000000)
      | 3 => orderedInterval (-11620238628 / 1000000000000) (-11620238332 / 1000000000000)
      | 4 => orderedInterval (-1685734058 / 1000000000000) (-1685734023 / 1000000000000)
      | 5 => orderedInterval (-2499799048 / 1000000000000) (-2499794719 / 1000000000000)
      | 6 => orderedInterval (-8353836707 / 1000000000000) (-8353835070 / 1000000000000)
      | 7 => orderedInterval (3546291920 / 1000000000000) (3546296455 / 1000000000000)
      | _ => orderedInterval (-4575752702 / 1000000000000) (-4575752639 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-6585865494 / 1000000000000) (-6585863676 / 1000000000000)
      | 1 => orderedInterval (-7623372782 / 1000000000000) (-7623372754 / 1000000000000)
      | 2 => orderedInterval (3899966501 / 1000000000000) (3899966559 / 1000000000000)
      | 3 => orderedInterval (40108630082 / 1000000000000) (40108630732 / 1000000000000)
      | 4 => orderedInterval (12460410166 / 1000000000000) (12460410222 / 1000000000000)
      | 5 => orderedInterval (-6845987070 / 1000000000000) (-6845981507 / 1000000000000)
      | 6 => orderedInterval (1627631749 / 1000000000000) (1627633182 / 1000000000000)
      | 7 => orderedInterval (3916586061 / 1000000000000) (3916590979 / 1000000000000)
      | _ => orderedInterval (10496776348 / 1000000000000) (10496776438 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (19792734987 / 1000000000000) (19792737080 / 1000000000000)
      | 1 => orderedInterval (-5870072908 / 1000000000000) (-5870072865 / 1000000000000)
      | 2 => orderedInterval (-3829663241 / 1000000000000) (-3829663131 / 1000000000000)
      | 3 => orderedInterval (63969105370 / 1000000000000) (63969106811 / 1000000000000)
      | 4 => orderedInterval (7390047359 / 1000000000000) (7390047451 / 1000000000000)
      | 5 => orderedInterval (3610679548 / 1000000000000) (3610686665 / 1000000000000)
      | 6 => orderedInterval (9485476647 / 1000000000000) (9485477893 / 1000000000000)
      | 7 => orderedInterval (-4234502209 / 1000000000000) (-4234496894 / 1000000000000)
      | _ => orderedInterval (-6819215826 / 1000000000000) (-6819215688 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (4995838328 / 1000000000000) (4995840764 / 1000000000000)
      | 1 => orderedInterval (20087239256 / 1000000000000) (20087239321 / 1000000000000)
      | 2 => orderedInterval (-18375234668 / 1000000000000) (-18375234456 / 1000000000000)
      | 3 => orderedInterval (-226625449719 / 1000000000000) (-226625446500 / 1000000000000)
      | 4 => orderedInterval (-30793332007 / 1000000000000) (-30793331850 / 1000000000000)
      | 5 => orderedInterval (18102724466 / 1000000000000) (18102733624 / 1000000000000)
      | 6 => orderedInterval (-392216973 / 1000000000000) (-392215879 / 1000000000000)
      | 7 => orderedInterval (-4975089416 / 1000000000000) (-4975083633 / 1000000000000)
      | _ => orderedInterval (-19248407056 / 1000000000000) (-19248406834 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-12541516929 / 1000000000000) (-12541505778 / 1000000000000)
    | 1 => orderedInterval (-43896770909 / 1000000000000) (-43896758382 / 1000000000000)
    | 2 => orderedInterval (51454775561 / 1000000000000) (51454790175 / 1000000000000)
    | 3 => orderedInterval (83494589727 / 1000000000000) (83494607322 / 1000000000000)
    | _ => orderedInterval (-257223927789 / 1000000000000) (-257223905443 / 1000000000000)

theorem compactCertificate272_stateChecks0 :
    compactCertificate272.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (293 / 2)) (orderedInterval (23856879291 / 1000000000000) (23856880166 / 1000000000000), orderedInterval (-61533805649 / 1000000000000) (-61533804774 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (431644947734993 / 4000000000000)) (orderedInterval (73134054370 / 1000000000000) (73134056375 / 1000000000000), orderedInterval (-23808722155 / 1000000000000) (-23808720150 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (139585107392369 / 800000000000)) (orderedInterval (-37183451534 / 1000000000000) (-37183434274 / 1000000000000), orderedInterval (47709435603 / 1000000000000) (47709452862 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState014, besselGridState021, besselGridState025, besselGridState027, besselGridState034, besselGridState037, besselGridState040, besselGridState047, besselGridState048, besselGridState050, besselGridState054, besselGridState056, besselGridState058, besselGridState060, besselGridState067, besselGridState068, besselGridState071, besselGridState073, besselGridState081, besselGridState086, besselGridState087, besselGridState092, besselGridState100, besselGridState104, besselGridState107, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate272_stateChecks1 :
    compactCertificate272.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 10 12 (125952919211251 / 4000000000000)) (orderedInterval (107166690307 / 1000000000000) (107166690308 / 1000000000000), orderedInterval (91747435403 / 1000000000000) (91747435404 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (338327257745047 / 4000000000000)) (orderedInterval (-44807415887 / 1000000000000) (-44807415886 / 1000000000000), orderedInterval (-74025315186 / 1000000000000) (-74025315185 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (918624318802299 / 4000000000000)) (orderedInterval (-47033318446 / 1000000000000) (-47033318445 / 1000000000000), orderedInterval (-23560233310 / 1000000000000) (-23560233309 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState014, besselGridState021, besselGridState025, besselGridState027, besselGridState034, besselGridState037, besselGridState040, besselGridState047, besselGridState048, besselGridState050, besselGridState054, besselGridState056, besselGridState058, besselGridState060, besselGridState067, besselGridState068, besselGridState071, besselGridState073, besselGridState081, besselGridState086, besselGridState087, besselGridState092, besselGridState100, besselGridState104, besselGridState107, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate272_stateChecks2 :
    compactCertificate272.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (676654515490387 / 4000000000000)) (orderedInterval (18262813191 / 1000000000000) (18262813192 / 1000000000000), orderedInterval (58510688835 / 1000000000000) (58510688836 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 92 12 (1159459045499551 / 4000000000000)) (orderedInterval (46799944739 / 1000000000000) (46799945003 / 1000000000000), orderedInterval (-2535663128 / 1000000000000) (-2535662864 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (854052285145309 / 4000000000000)) (orderedInterval (33890709185 / 1000000000000) (33890709186 / 1000000000000), orderedInterval (42734941876 / 1000000000000) (42734941877 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState014, besselGridState021, besselGridState025, besselGridState027, besselGridState034, besselGridState037, besselGridState040, besselGridState047, besselGridState048, besselGridState050, besselGridState054, besselGridState056, besselGridState058, besselGridState060, besselGridState067, besselGridState068, besselGridState071, besselGridState073, besselGridState081, besselGridState086, besselGridState087, besselGridState092, besselGridState100, besselGridState104, besselGridState107, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate272_stateChecks3 :
    compactCertificate272.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 104 12 (1310335834814707 / 4000000000000)) (orderedInterval (43967801981 / 1000000000000) (43967802419 / 1000000000000), orderedInterval (-3262275502 / 1000000000000) (-3262275064 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (756522746959003 / 4000000000000)) (orderedInterval (57357831071 / 1000000000000) (57357831077 / 1000000000000), orderedInterval (8571844167 / 1000000000000) (8571844174 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 107 12 (1342462890184727 / 4000000000000)) (orderedInterval (-10789307145 / 1000000000000) (-10789307144 / 1000000000000), orderedInterval (-42179468798 / 1000000000000) (-42179468797 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState014, besselGridState021, besselGridState025, besselGridState027, besselGridState034, besselGridState037, besselGridState040, besselGridState047, besselGridState048, besselGridState050, besselGridState054, besselGridState056, besselGridState058, besselGridState060, besselGridState067, besselGridState068, besselGridState071, besselGridState073, besselGridState081, besselGridState086, besselGridState087, besselGridState092, besselGridState100, besselGridState104, besselGridState107, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate272_stateChecks4 :
    compactCertificate272.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 100 12 (1254302971716563 / 4000000000000)) (orderedInterval (9016792105 / 1000000000000) (9016792106 / 1000000000000), orderedInterval (44131906875 / 1000000000000) (44131906876 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (895129785747779 / 4000000000000)) (orderedInterval (-53251368477 / 1000000000000) (-53251368442 / 1000000000000), orderedInterval (-2897674576 / 1000000000000) (-2897674540 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (1014981773235141 / 4000000000000)) (orderedInterval (-3070715589 / 1000000000000) (-3070715588 / 1000000000000), orderedInterval (-49988618826 / 1000000000000) (-49988618824 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState014, besselGridState021, besselGridState025, besselGridState027, besselGridState034, besselGridState037, besselGridState040, besselGridState047, besselGridState048, besselGridState050, besselGridState054, besselGridState056, besselGridState058, besselGridState060, besselGridState067, besselGridState068, besselGridState071, besselGridState073, besselGridState081, besselGridState086, besselGridState087, besselGridState092, besselGridState100, besselGridState104, besselGridState107, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate272_stateChecks5 :
    compactCertificate272.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (846185985354229 / 4000000000000)) (orderedInterval (-52814150227 / 1000000000000) (-52814147848 / 1000000000000), orderedInterval (14957879867 / 1000000000000) (14957882246 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (747630980306809 / 4000000000000)) (orderedInterval (-41991155960 / 1000000000000) (-41991097519 / 1000000000000), orderedInterval (40643879102 / 1000000000000) (40643937543 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (216692598410091 / 800000000000)) (orderedInterval (48251733495 / 1000000000000) (48251733522 / 1000000000000), orderedInterval (4609980691 / 1000000000000) (4609980719 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState014, besselGridState021, besselGridState025, besselGridState027, besselGridState034, besselGridState037, besselGridState040, besselGridState047, besselGridState048, besselGridState050, besselGridState054, besselGridState056, besselGridState058, besselGridState060, besselGridState067, besselGridState068, besselGridState071, besselGridState073, besselGridState081, besselGridState086, besselGridState087, besselGridState092, besselGridState100, besselGridState104, besselGridState107, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate272_stateChecks6 :
    compactCertificate272.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (599383131108977 / 4000000000000)) (orderedInterval (-10776778915 / 1000000000000) (-10776778858 / 1000000000000), orderedInterval (64319574117 / 1000000000000) (64319574174 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (508103718227497 / 4000000000000)) (orderedInterval (59376771516 / 1000000000000) (59376803878 / 1000000000000), orderedInterval (-38783854928 / 1000000000000) (-38783822566 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (317947714854691 / 4000000000000)) (orderedInterval (-88347673694 / 1000000000000) (-88347673423 / 1000000000000), orderedInterval (14826347303 / 1000000000000) (14826347574 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState014, besselGridState021, besselGridState025, besselGridState027, besselGridState034, besselGridState037, besselGridState040, besselGridState047, besselGridState048, besselGridState050, besselGridState054, besselGridState056, besselGridState058, besselGridState060, besselGridState067, besselGridState068, besselGridState071, besselGridState073, besselGridState081, besselGridState086, besselGridState087, besselGridState092, besselGridState100, besselGridState104, besselGridState107, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate272_stateChecks7 :
    compactCertificate272.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 14 12 (170993338495197 / 4000000000000)) (orderedInterval (-53242127926 / 1000000000000) (-53242124028 / 1000000000000), orderedInterval (110432383127 / 1000000000000) (110432387025 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (464280176956591 / 4000000000000)) (orderedInterval (-42755433319 / 1000000000000) (-42755433318 / 1000000000000), orderedInterval (-60287135304 / 1000000000000) (-60287135303 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (633934889101007 / 4000000000000)) (orderedInterval (51660044729 / 1000000000000) (51660098972 / 1000000000000), orderedInterval (-36880459466 / 1000000000000) (-36880405223 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState014, besselGridState021, besselGridState025, besselGridState027, besselGridState034, besselGridState037, besselGridState040, besselGridState047, besselGridState048, besselGridState050, besselGridState054, besselGridState056, besselGridState058, besselGridState060, besselGridState067, besselGridState068, besselGridState071, besselGridState073, besselGridState081, besselGridState086, besselGridState087, besselGridState092, besselGridState100, besselGridState104, besselGridState107, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate272_stateChecks8 :
    compactCertificate272.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 21 12 (268052285145309 / 4000000000000)) (orderedInterval (-94379033944 / 1000000000000) (-94379033139 / 1000000000000), orderedInterval (25041377389 / 1000000000000) (25041378193 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (1089617657297789 / 4000000000000)) (orderedInterval (6228886799 / 1000000000000) (6228886811 / 1000000000000), orderedInterval (-47951436193 / 1000000000000) (-47951436180 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (727814097764851 / 4000000000000)) (orderedInterval (29691135344 / 1000000000000) (29691135345 / 1000000000000), orderedInterval (51077450276 / 1000000000000) (51077450277 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState010, besselGridState014, besselGridState021, besselGridState025, besselGridState027, besselGridState034, besselGridState037, besselGridState040, besselGridState047, besselGridState048, besselGridState050, besselGridState054, besselGridState056, besselGridState058, besselGridState060, besselGridState067, besselGridState068, besselGridState071, besselGridState073, besselGridState081, besselGridState086, besselGridState087, besselGridState092, besselGridState100, besselGridState104, besselGridState107, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate272_states : ∀ j,
    BesselStateValid (compactCertificate272.point j) (compactCertificate272.state j) :=
  compactCertificate272.statesValid_of_checks3 compactCertificate272_stateChecks0
    compactCertificate272_stateChecks1 compactCertificate272_stateChecks2
    compactCertificate272_stateChecks3 compactCertificate272_stateChecks4
    compactCertificate272_stateChecks5 compactCertificate272_stateChecks6
    compactCertificate272_stateChecks7 compactCertificate272_stateChecks8

theorem compactCertificate272_chunkChecks0_0 :
    compactCertificate272.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (293 / 2) 0 (IntervalRat.scale (293 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (23856879291 / 1000000000000) (23856880166 / 1000000000000), orderedInterval (-61533805649 / 1000000000000) (-61533804774 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (431644947734993 / 4000000000000) 0 (IntervalRat.scale (293 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (73134054370 / 1000000000000) (73134056375 / 1000000000000), orderedInterval (-23808722155 / 1000000000000) (-23808720150 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (139585107392369 / 800000000000) 0 (IntervalRat.scale (293 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-37183451534 / 1000000000000) (-37183434274 / 1000000000000), orderedInterval (47709435603 / 1000000000000) (47709452862 / 1000000000000)))) (orderedInterval (7955531969 / 1000000000000) (7955533359 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (125952919211251 / 4000000000000) 0 (IntervalRat.scale (293 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (107166690307 / 1000000000000) (107166690308 / 1000000000000), orderedInterval (91747435403 / 1000000000000) (91747435404 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (338327257745047 / 4000000000000) 0 (IntervalRat.scale (293 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-44807415887 / 1000000000000) (-44807415886 / 1000000000000), orderedInterval (-74025315186 / 1000000000000) (-74025315185 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (918624318802299 / 4000000000000) 0 (IntervalRat.scale (293 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-47033318446 / 1000000000000) (-47033318445 / 1000000000000), orderedInterval (-23560233310 / 1000000000000) (-23560233309 / 1000000000000)))) (orderedInterval (544902118 / 1000000000000) (544902136 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (676654515490387 / 4000000000000) 0 (IntervalRat.scale (293 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (18262813191 / 1000000000000) (18262813192 / 1000000000000), orderedInterval (58510688835 / 1000000000000) (58510688836 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1159459045499551 / 4000000000000) 0 (IntervalRat.scale (293 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (46799944739 / 1000000000000) (46799945003 / 1000000000000), orderedInterval (-2535663128 / 1000000000000) (-2535662864 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (854052285145309 / 4000000000000) 0 (IntervalRat.scale (293 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (33890709185 / 1000000000000) (33890709186 / 1000000000000), orderedInterval (42734941876 / 1000000000000) (42734941877 / 1000000000000)))) (orderedInterval (-624425980 / 1000000000000) (-624425963 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate272_chunkChecks0_1 :
    compactCertificate272.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1310335834814707 / 4000000000000) 0 (IntervalRat.scale (293 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (43967801981 / 1000000000000) (43967802419 / 1000000000000), orderedInterval (-3262275502 / 1000000000000) (-3262275064 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (756522746959003 / 4000000000000) 0 (IntervalRat.scale (293 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (57357831071 / 1000000000000) (57357831077 / 1000000000000), orderedInterval (8571844167 / 1000000000000) (8571844174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1342462890184727 / 4000000000000) 0 (IntervalRat.scale (293 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-10789307145 / 1000000000000) (-10789307144 / 1000000000000), orderedInterval (-42179468798 / 1000000000000) (-42179468797 / 1000000000000)))) (orderedInterval (-5096567948 / 1000000000000) (-5096567811 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1254302971716563 / 4000000000000) 0 (IntervalRat.scale (293 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (9016792105 / 1000000000000) (9016792106 / 1000000000000), orderedInterval (44131906875 / 1000000000000) (44131906876 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (895129785747779 / 4000000000000) 0 (IntervalRat.scale (293 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-53251368477 / 1000000000000) (-53251368442 / 1000000000000), orderedInterval (-2897674576 / 1000000000000) (-2897674540 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1014981773235141 / 4000000000000) 0 (IntervalRat.scale (293 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-3070715589 / 1000000000000) (-3070715588 / 1000000000000), orderedInterval (-49988618826 / 1000000000000) (-49988618824 / 1000000000000)))) (orderedInterval (-5182843364 / 1000000000000) (-5182843343 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (846185985354229 / 4000000000000) 0 (IntervalRat.scale (293 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-52814150227 / 1000000000000) (-52814147848 / 1000000000000), orderedInterval (14957879867 / 1000000000000) (14957882246 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (747630980306809 / 4000000000000) 0 (IntervalRat.scale (293 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-41991155960 / 1000000000000) (-41991097519 / 1000000000000), orderedInterval (40643879102 / 1000000000000) (40643937543 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (216692598410091 / 800000000000) 0 (IntervalRat.scale (293 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (48251733495 / 1000000000000) (48251733522 / 1000000000000), orderedInterval (4609980691 / 1000000000000) (4609980719 / 1000000000000)))) (orderedInterval (3028565561 / 1000000000000) (3028568948 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate272_chunkChecks0_2 :
    compactCertificate272.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (599383131108977 / 4000000000000) 0 (IntervalRat.scale (293 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-10776778915 / 1000000000000) (-10776778858 / 1000000000000), orderedInterval (64319574117 / 1000000000000) (64319574174 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (508103718227497 / 4000000000000) 0 (IntervalRat.scale (293 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (59376771516 / 1000000000000) (59376803878 / 1000000000000), orderedInterval (-38783854928 / 1000000000000) (-38783822566 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (317947714854691 / 4000000000000) 0 (IntervalRat.scale (293 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-88347673694 / 1000000000000) (-88347673423 / 1000000000000), orderedInterval (14826347303 / 1000000000000) (14826347574 / 1000000000000)))) (orderedInterval (-4513781476 / 1000000000000) (-4513779589 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (170993338495197 / 4000000000000) 0 (IntervalRat.scale (293 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-53242127926 / 1000000000000) (-53242124028 / 1000000000000), orderedInterval (110432383127 / 1000000000000) (110432387025 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (464280176956591 / 4000000000000) 0 (IntervalRat.scale (293 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-42755433319 / 1000000000000) (-42755433318 / 1000000000000), orderedInterval (-60287135304 / 1000000000000) (-60287135303 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (633934889101007 / 4000000000000) 0 (IntervalRat.scale (293 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (51660044729 / 1000000000000) (51660098972 / 1000000000000), orderedInterval (-36880459466 / 1000000000000) (-36880405223 / 1000000000000)))) (orderedInterval (-2006062953 / 1000000000000) (-2006058706 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (268052285145309 / 4000000000000) 0 (IntervalRat.scale (293 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-94379033944 / 1000000000000) (-94379033139 / 1000000000000), orderedInterval (25041377389 / 1000000000000) (25041378193 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1089617657297789 / 4000000000000) 0 (IntervalRat.scale (293 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (6228886799 / 1000000000000) (6228886811 / 1000000000000), orderedInterval (-47951436193 / 1000000000000) (-47951436180 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (727814097764851 / 4000000000000) 0 (IntervalRat.scale (293 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (29691135344 / 1000000000000) (29691135345 / 1000000000000), orderedInterval (51077450276 / 1000000000000) (51077450277 / 1000000000000)))) (orderedInterval (-6646834856 / 1000000000000) (-6646834809 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate272_chunkChecks0 :
    compactCertificate272.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate272.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate272_chunkChecks0_0
    compactCertificate272_chunkChecks0_1 compactCertificate272_chunkChecks0_2

theorem compactCertificate272_chunkChecks1_0 :
    compactCertificate272.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (293 / 2) 1 (IntervalRat.scale (293 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (23856879291 / 1000000000000) (23856880166 / 1000000000000), orderedInterval (-61533805649 / 1000000000000) (-61533804774 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (431644947734993 / 4000000000000) 1 (IntervalRat.scale (293 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (73134054370 / 1000000000000) (73134056375 / 1000000000000), orderedInterval (-23808722155 / 1000000000000) (-23808720150 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (139585107392369 / 800000000000) 1 (IntervalRat.scale (293 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-37183451534 / 1000000000000) (-37183434274 / 1000000000000), orderedInterval (47709435603 / 1000000000000) (47709452862 / 1000000000000)))) (orderedInterval (-21218887094 / 1000000000000) (-21218885515 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (125952919211251 / 4000000000000) 1 (IntervalRat.scale (293 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (107166690307 / 1000000000000) (107166690308 / 1000000000000), orderedInterval (91747435403 / 1000000000000) (91747435404 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (338327257745047 / 4000000000000) 1 (IntervalRat.scale (293 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-44807415887 / 1000000000000) (-44807415886 / 1000000000000), orderedInterval (-74025315186 / 1000000000000) (-74025315185 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (918624318802299 / 4000000000000) 1 (IntervalRat.scale (293 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-47033318446 / 1000000000000) (-47033318445 / 1000000000000), orderedInterval (-23560233310 / 1000000000000) (-23560233309 / 1000000000000)))) (orderedInterval (851180466 / 1000000000000) (851180487 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (676654515490387 / 4000000000000) 1 (IntervalRat.scale (293 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (18262813191 / 1000000000000) (18262813192 / 1000000000000), orderedInterval (58510688835 / 1000000000000) (58510688836 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1159459045499551 / 4000000000000) 1 (IntervalRat.scale (293 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (46799944739 / 1000000000000) (46799945003 / 1000000000000), orderedInterval (-2535663128 / 1000000000000) (-2535662864 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (854052285145309 / 4000000000000) 1 (IntervalRat.scale (293 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (33890709185 / 1000000000000) (33890709186 / 1000000000000), orderedInterval (42734941876 / 1000000000000) (42734941877 / 1000000000000)))) (orderedInterval (1660004942 / 1000000000000) (1660004974 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate272_chunkChecks1_1 :
    compactCertificate272.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1310335834814707 / 4000000000000) 1 (IntervalRat.scale (293 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (43967801981 / 1000000000000) (43967802419 / 1000000000000), orderedInterval (-3262275502 / 1000000000000) (-3262275064 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (756522746959003 / 4000000000000) 1 (IntervalRat.scale (293 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (57357831071 / 1000000000000) (57357831077 / 1000000000000), orderedInterval (8571844167 / 1000000000000) (8571844174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1342462890184727 / 4000000000000) 1 (IntervalRat.scale (293 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-10789307145 / 1000000000000) (-10789307144 / 1000000000000), orderedInterval (-42179468798 / 1000000000000) (-42179468797 / 1000000000000)))) (orderedInterval (-11620238628 / 1000000000000) (-11620238332 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1254302971716563 / 4000000000000) 1 (IntervalRat.scale (293 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (9016792105 / 1000000000000) (9016792106 / 1000000000000), orderedInterval (44131906875 / 1000000000000) (44131906876 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (895129785747779 / 4000000000000) 1 (IntervalRat.scale (293 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-53251368477 / 1000000000000) (-53251368442 / 1000000000000), orderedInterval (-2897674576 / 1000000000000) (-2897674540 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1014981773235141 / 4000000000000) 1 (IntervalRat.scale (293 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-3070715589 / 1000000000000) (-3070715588 / 1000000000000), orderedInterval (-49988618826 / 1000000000000) (-49988618824 / 1000000000000)))) (orderedInterval (-1685734058 / 1000000000000) (-1685734023 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (846185985354229 / 4000000000000) 1 (IntervalRat.scale (293 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-52814150227 / 1000000000000) (-52814147848 / 1000000000000), orderedInterval (14957879867 / 1000000000000) (14957882246 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (747630980306809 / 4000000000000) 1 (IntervalRat.scale (293 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-41991155960 / 1000000000000) (-41991097519 / 1000000000000), orderedInterval (40643879102 / 1000000000000) (40643937543 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (216692598410091 / 800000000000) 1 (IntervalRat.scale (293 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (48251733495 / 1000000000000) (48251733522 / 1000000000000), orderedInterval (4609980691 / 1000000000000) (4609980719 / 1000000000000)))) (orderedInterval (-2499799048 / 1000000000000) (-2499794719 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate272_chunkChecks1_2 :
    compactCertificate272.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (599383131108977 / 4000000000000) 1 (IntervalRat.scale (293 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-10776778915 / 1000000000000) (-10776778858 / 1000000000000), orderedInterval (64319574117 / 1000000000000) (64319574174 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (508103718227497 / 4000000000000) 1 (IntervalRat.scale (293 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (59376771516 / 1000000000000) (59376803878 / 1000000000000), orderedInterval (-38783854928 / 1000000000000) (-38783822566 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (317947714854691 / 4000000000000) 1 (IntervalRat.scale (293 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-88347673694 / 1000000000000) (-88347673423 / 1000000000000), orderedInterval (14826347303 / 1000000000000) (14826347574 / 1000000000000)))) (orderedInterval (-8353836707 / 1000000000000) (-8353835070 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (170993338495197 / 4000000000000) 1 (IntervalRat.scale (293 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-53242127926 / 1000000000000) (-53242124028 / 1000000000000), orderedInterval (110432383127 / 1000000000000) (110432387025 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (464280176956591 / 4000000000000) 1 (IntervalRat.scale (293 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-42755433319 / 1000000000000) (-42755433318 / 1000000000000), orderedInterval (-60287135304 / 1000000000000) (-60287135303 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (633934889101007 / 4000000000000) 1 (IntervalRat.scale (293 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (51660044729 / 1000000000000) (51660098972 / 1000000000000), orderedInterval (-36880459466 / 1000000000000) (-36880405223 / 1000000000000)))) (orderedInterval (3546291920 / 1000000000000) (3546296455 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (268052285145309 / 4000000000000) 1 (IntervalRat.scale (293 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-94379033944 / 1000000000000) (-94379033139 / 1000000000000), orderedInterval (25041377389 / 1000000000000) (25041378193 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1089617657297789 / 4000000000000) 1 (IntervalRat.scale (293 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (6228886799 / 1000000000000) (6228886811 / 1000000000000), orderedInterval (-47951436193 / 1000000000000) (-47951436180 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (727814097764851 / 4000000000000) 1 (IntervalRat.scale (293 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (29691135344 / 1000000000000) (29691135345 / 1000000000000), orderedInterval (51077450276 / 1000000000000) (51077450277 / 1000000000000)))) (orderedInterval (-4575752702 / 1000000000000) (-4575752639 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate272_chunkChecks1 :
    compactCertificate272.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate272.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate272_chunkChecks1_0
    compactCertificate272_chunkChecks1_1 compactCertificate272_chunkChecks1_2

theorem compactCertificate272_chunkChecks2_0 :
    compactCertificate272.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (293 / 2) 2 (IntervalRat.scale (293 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (23856879291 / 1000000000000) (23856880166 / 1000000000000), orderedInterval (-61533805649 / 1000000000000) (-61533804774 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (431644947734993 / 4000000000000) 2 (IntervalRat.scale (293 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (73134054370 / 1000000000000) (73134056375 / 1000000000000), orderedInterval (-23808722155 / 1000000000000) (-23808720150 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (139585107392369 / 800000000000) 2 (IntervalRat.scale (293 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-37183451534 / 1000000000000) (-37183434274 / 1000000000000), orderedInterval (47709435603 / 1000000000000) (47709452862 / 1000000000000)))) (orderedInterval (-6585865494 / 1000000000000) (-6585863676 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (125952919211251 / 4000000000000) 2 (IntervalRat.scale (293 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (107166690307 / 1000000000000) (107166690308 / 1000000000000), orderedInterval (91747435403 / 1000000000000) (91747435404 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (338327257745047 / 4000000000000) 2 (IntervalRat.scale (293 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-44807415887 / 1000000000000) (-44807415886 / 1000000000000), orderedInterval (-74025315186 / 1000000000000) (-74025315185 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (918624318802299 / 4000000000000) 2 (IntervalRat.scale (293 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-47033318446 / 1000000000000) (-47033318445 / 1000000000000), orderedInterval (-23560233310 / 1000000000000) (-23560233309 / 1000000000000)))) (orderedInterval (-7623372782 / 1000000000000) (-7623372754 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (676654515490387 / 4000000000000) 2 (IntervalRat.scale (293 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (18262813191 / 1000000000000) (18262813192 / 1000000000000), orderedInterval (58510688835 / 1000000000000) (58510688836 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1159459045499551 / 4000000000000) 2 (IntervalRat.scale (293 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (46799944739 / 1000000000000) (46799945003 / 1000000000000), orderedInterval (-2535663128 / 1000000000000) (-2535662864 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (854052285145309 / 4000000000000) 2 (IntervalRat.scale (293 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (33890709185 / 1000000000000) (33890709186 / 1000000000000), orderedInterval (42734941876 / 1000000000000) (42734941877 / 1000000000000)))) (orderedInterval (3899966501 / 1000000000000) (3899966559 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate272_chunkChecks2_1 :
    compactCertificate272.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1310335834814707 / 4000000000000) 2 (IntervalRat.scale (293 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (43967801981 / 1000000000000) (43967802419 / 1000000000000), orderedInterval (-3262275502 / 1000000000000) (-3262275064 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (756522746959003 / 4000000000000) 2 (IntervalRat.scale (293 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (57357831071 / 1000000000000) (57357831077 / 1000000000000), orderedInterval (8571844167 / 1000000000000) (8571844174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1342462890184727 / 4000000000000) 2 (IntervalRat.scale (293 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-10789307145 / 1000000000000) (-10789307144 / 1000000000000), orderedInterval (-42179468798 / 1000000000000) (-42179468797 / 1000000000000)))) (orderedInterval (40108630082 / 1000000000000) (40108630732 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1254302971716563 / 4000000000000) 2 (IntervalRat.scale (293 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (9016792105 / 1000000000000) (9016792106 / 1000000000000), orderedInterval (44131906875 / 1000000000000) (44131906876 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (895129785747779 / 4000000000000) 2 (IntervalRat.scale (293 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-53251368477 / 1000000000000) (-53251368442 / 1000000000000), orderedInterval (-2897674576 / 1000000000000) (-2897674540 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1014981773235141 / 4000000000000) 2 (IntervalRat.scale (293 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-3070715589 / 1000000000000) (-3070715588 / 1000000000000), orderedInterval (-49988618826 / 1000000000000) (-49988618824 / 1000000000000)))) (orderedInterval (12460410166 / 1000000000000) (12460410222 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (846185985354229 / 4000000000000) 2 (IntervalRat.scale (293 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-52814150227 / 1000000000000) (-52814147848 / 1000000000000), orderedInterval (14957879867 / 1000000000000) (14957882246 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (747630980306809 / 4000000000000) 2 (IntervalRat.scale (293 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-41991155960 / 1000000000000) (-41991097519 / 1000000000000), orderedInterval (40643879102 / 1000000000000) (40643937543 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (216692598410091 / 800000000000) 2 (IntervalRat.scale (293 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (48251733495 / 1000000000000) (48251733522 / 1000000000000), orderedInterval (4609980691 / 1000000000000) (4609980719 / 1000000000000)))) (orderedInterval (-6845987070 / 1000000000000) (-6845981507 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate272_chunkChecks2_2 :
    compactCertificate272.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (599383131108977 / 4000000000000) 2 (IntervalRat.scale (293 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-10776778915 / 1000000000000) (-10776778858 / 1000000000000), orderedInterval (64319574117 / 1000000000000) (64319574174 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (508103718227497 / 4000000000000) 2 (IntervalRat.scale (293 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (59376771516 / 1000000000000) (59376803878 / 1000000000000), orderedInterval (-38783854928 / 1000000000000) (-38783822566 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (317947714854691 / 4000000000000) 2 (IntervalRat.scale (293 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-88347673694 / 1000000000000) (-88347673423 / 1000000000000), orderedInterval (14826347303 / 1000000000000) (14826347574 / 1000000000000)))) (orderedInterval (1627631749 / 1000000000000) (1627633182 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (170993338495197 / 4000000000000) 2 (IntervalRat.scale (293 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-53242127926 / 1000000000000) (-53242124028 / 1000000000000), orderedInterval (110432383127 / 1000000000000) (110432387025 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (464280176956591 / 4000000000000) 2 (IntervalRat.scale (293 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-42755433319 / 1000000000000) (-42755433318 / 1000000000000), orderedInterval (-60287135304 / 1000000000000) (-60287135303 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (633934889101007 / 4000000000000) 2 (IntervalRat.scale (293 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (51660044729 / 1000000000000) (51660098972 / 1000000000000), orderedInterval (-36880459466 / 1000000000000) (-36880405223 / 1000000000000)))) (orderedInterval (3916586061 / 1000000000000) (3916590979 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (268052285145309 / 4000000000000) 2 (IntervalRat.scale (293 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-94379033944 / 1000000000000) (-94379033139 / 1000000000000), orderedInterval (25041377389 / 1000000000000) (25041378193 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1089617657297789 / 4000000000000) 2 (IntervalRat.scale (293 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (6228886799 / 1000000000000) (6228886811 / 1000000000000), orderedInterval (-47951436193 / 1000000000000) (-47951436180 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (727814097764851 / 4000000000000) 2 (IntervalRat.scale (293 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (29691135344 / 1000000000000) (29691135345 / 1000000000000), orderedInterval (51077450276 / 1000000000000) (51077450277 / 1000000000000)))) (orderedInterval (10496776348 / 1000000000000) (10496776438 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate272_chunkChecks2 :
    compactCertificate272.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate272.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate272_chunkChecks2_0
    compactCertificate272_chunkChecks2_1 compactCertificate272_chunkChecks2_2

theorem compactCertificate272_chunkChecks3_0 :
    compactCertificate272.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (293 / 2) 3 (IntervalRat.scale (293 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (23856879291 / 1000000000000) (23856880166 / 1000000000000), orderedInterval (-61533805649 / 1000000000000) (-61533804774 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (431644947734993 / 4000000000000) 3 (IntervalRat.scale (293 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (73134054370 / 1000000000000) (73134056375 / 1000000000000), orderedInterval (-23808722155 / 1000000000000) (-23808720150 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (139585107392369 / 800000000000) 3 (IntervalRat.scale (293 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-37183451534 / 1000000000000) (-37183434274 / 1000000000000), orderedInterval (47709435603 / 1000000000000) (47709452862 / 1000000000000)))) (orderedInterval (19792734987 / 1000000000000) (19792737080 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (125952919211251 / 4000000000000) 3 (IntervalRat.scale (293 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (107166690307 / 1000000000000) (107166690308 / 1000000000000), orderedInterval (91747435403 / 1000000000000) (91747435404 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (338327257745047 / 4000000000000) 3 (IntervalRat.scale (293 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-44807415887 / 1000000000000) (-44807415886 / 1000000000000), orderedInterval (-74025315186 / 1000000000000) (-74025315185 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (918624318802299 / 4000000000000) 3 (IntervalRat.scale (293 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-47033318446 / 1000000000000) (-47033318445 / 1000000000000), orderedInterval (-23560233310 / 1000000000000) (-23560233309 / 1000000000000)))) (orderedInterval (-5870072908 / 1000000000000) (-5870072865 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (676654515490387 / 4000000000000) 3 (IntervalRat.scale (293 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (18262813191 / 1000000000000) (18262813192 / 1000000000000), orderedInterval (58510688835 / 1000000000000) (58510688836 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1159459045499551 / 4000000000000) 3 (IntervalRat.scale (293 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (46799944739 / 1000000000000) (46799945003 / 1000000000000), orderedInterval (-2535663128 / 1000000000000) (-2535662864 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (854052285145309 / 4000000000000) 3 (IntervalRat.scale (293 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (33890709185 / 1000000000000) (33890709186 / 1000000000000), orderedInterval (42734941876 / 1000000000000) (42734941877 / 1000000000000)))) (orderedInterval (-3829663241 / 1000000000000) (-3829663131 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate272_chunkChecks3_1 :
    compactCertificate272.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1310335834814707 / 4000000000000) 3 (IntervalRat.scale (293 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (43967801981 / 1000000000000) (43967802419 / 1000000000000), orderedInterval (-3262275502 / 1000000000000) (-3262275064 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (756522746959003 / 4000000000000) 3 (IntervalRat.scale (293 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (57357831071 / 1000000000000) (57357831077 / 1000000000000), orderedInterval (8571844167 / 1000000000000) (8571844174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1342462890184727 / 4000000000000) 3 (IntervalRat.scale (293 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-10789307145 / 1000000000000) (-10789307144 / 1000000000000), orderedInterval (-42179468798 / 1000000000000) (-42179468797 / 1000000000000)))) (orderedInterval (63969105370 / 1000000000000) (63969106811 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1254302971716563 / 4000000000000) 3 (IntervalRat.scale (293 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (9016792105 / 1000000000000) (9016792106 / 1000000000000), orderedInterval (44131906875 / 1000000000000) (44131906876 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (895129785747779 / 4000000000000) 3 (IntervalRat.scale (293 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-53251368477 / 1000000000000) (-53251368442 / 1000000000000), orderedInterval (-2897674576 / 1000000000000) (-2897674540 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1014981773235141 / 4000000000000) 3 (IntervalRat.scale (293 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-3070715589 / 1000000000000) (-3070715588 / 1000000000000), orderedInterval (-49988618826 / 1000000000000) (-49988618824 / 1000000000000)))) (orderedInterval (7390047359 / 1000000000000) (7390047451 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (846185985354229 / 4000000000000) 3 (IntervalRat.scale (293 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-52814150227 / 1000000000000) (-52814147848 / 1000000000000), orderedInterval (14957879867 / 1000000000000) (14957882246 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (747630980306809 / 4000000000000) 3 (IntervalRat.scale (293 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-41991155960 / 1000000000000) (-41991097519 / 1000000000000), orderedInterval (40643879102 / 1000000000000) (40643937543 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (216692598410091 / 800000000000) 3 (IntervalRat.scale (293 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (48251733495 / 1000000000000) (48251733522 / 1000000000000), orderedInterval (4609980691 / 1000000000000) (4609980719 / 1000000000000)))) (orderedInterval (3610679548 / 1000000000000) (3610686665 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate272_chunkChecks3_2 :
    compactCertificate272.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (599383131108977 / 4000000000000) 3 (IntervalRat.scale (293 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-10776778915 / 1000000000000) (-10776778858 / 1000000000000), orderedInterval (64319574117 / 1000000000000) (64319574174 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (508103718227497 / 4000000000000) 3 (IntervalRat.scale (293 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (59376771516 / 1000000000000) (59376803878 / 1000000000000), orderedInterval (-38783854928 / 1000000000000) (-38783822566 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (317947714854691 / 4000000000000) 3 (IntervalRat.scale (293 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-88347673694 / 1000000000000) (-88347673423 / 1000000000000), orderedInterval (14826347303 / 1000000000000) (14826347574 / 1000000000000)))) (orderedInterval (9485476647 / 1000000000000) (9485477893 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (170993338495197 / 4000000000000) 3 (IntervalRat.scale (293 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-53242127926 / 1000000000000) (-53242124028 / 1000000000000), orderedInterval (110432383127 / 1000000000000) (110432387025 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (464280176956591 / 4000000000000) 3 (IntervalRat.scale (293 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-42755433319 / 1000000000000) (-42755433318 / 1000000000000), orderedInterval (-60287135304 / 1000000000000) (-60287135303 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (633934889101007 / 4000000000000) 3 (IntervalRat.scale (293 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (51660044729 / 1000000000000) (51660098972 / 1000000000000), orderedInterval (-36880459466 / 1000000000000) (-36880405223 / 1000000000000)))) (orderedInterval (-4234502209 / 1000000000000) (-4234496894 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (268052285145309 / 4000000000000) 3 (IntervalRat.scale (293 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-94379033944 / 1000000000000) (-94379033139 / 1000000000000), orderedInterval (25041377389 / 1000000000000) (25041378193 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1089617657297789 / 4000000000000) 3 (IntervalRat.scale (293 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (6228886799 / 1000000000000) (6228886811 / 1000000000000), orderedInterval (-47951436193 / 1000000000000) (-47951436180 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (727814097764851 / 4000000000000) 3 (IntervalRat.scale (293 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (29691135344 / 1000000000000) (29691135345 / 1000000000000), orderedInterval (51077450276 / 1000000000000) (51077450277 / 1000000000000)))) (orderedInterval (-6819215826 / 1000000000000) (-6819215688 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate272_chunkChecks3 :
    compactCertificate272.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate272.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate272_chunkChecks3_0
    compactCertificate272_chunkChecks3_1 compactCertificate272_chunkChecks3_2

theorem compactCertificate272_chunkChecks4_0 :
    compactCertificate272.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (293 / 2) 4 (IntervalRat.scale (293 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (23856879291 / 1000000000000) (23856880166 / 1000000000000), orderedInterval (-61533805649 / 1000000000000) (-61533804774 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (431644947734993 / 4000000000000) 4 (IntervalRat.scale (293 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (73134054370 / 1000000000000) (73134056375 / 1000000000000), orderedInterval (-23808722155 / 1000000000000) (-23808720150 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (139585107392369 / 800000000000) 4 (IntervalRat.scale (293 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-37183451534 / 1000000000000) (-37183434274 / 1000000000000), orderedInterval (47709435603 / 1000000000000) (47709452862 / 1000000000000)))) (orderedInterval (4995838328 / 1000000000000) (4995840764 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (125952919211251 / 4000000000000) 4 (IntervalRat.scale (293 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (107166690307 / 1000000000000) (107166690308 / 1000000000000), orderedInterval (91747435403 / 1000000000000) (91747435404 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (338327257745047 / 4000000000000) 4 (IntervalRat.scale (293 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-44807415887 / 1000000000000) (-44807415886 / 1000000000000), orderedInterval (-74025315186 / 1000000000000) (-74025315185 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (918624318802299 / 4000000000000) 4 (IntervalRat.scale (293 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-47033318446 / 1000000000000) (-47033318445 / 1000000000000), orderedInterval (-23560233310 / 1000000000000) (-23560233309 / 1000000000000)))) (orderedInterval (20087239256 / 1000000000000) (20087239321 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (676654515490387 / 4000000000000) 4 (IntervalRat.scale (293 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (18262813191 / 1000000000000) (18262813192 / 1000000000000), orderedInterval (58510688835 / 1000000000000) (58510688836 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1159459045499551 / 4000000000000) 4 (IntervalRat.scale (293 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (46799944739 / 1000000000000) (46799945003 / 1000000000000), orderedInterval (-2535663128 / 1000000000000) (-2535662864 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (854052285145309 / 4000000000000) 4 (IntervalRat.scale (293 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (33890709185 / 1000000000000) (33890709186 / 1000000000000), orderedInterval (42734941876 / 1000000000000) (42734941877 / 1000000000000)))) (orderedInterval (-18375234668 / 1000000000000) (-18375234456 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate272_chunkChecks4_1 :
    compactCertificate272.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1310335834814707 / 4000000000000) 4 (IntervalRat.scale (293 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (43967801981 / 1000000000000) (43967802419 / 1000000000000), orderedInterval (-3262275502 / 1000000000000) (-3262275064 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (756522746959003 / 4000000000000) 4 (IntervalRat.scale (293 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (57357831071 / 1000000000000) (57357831077 / 1000000000000), orderedInterval (8571844167 / 1000000000000) (8571844174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1342462890184727 / 4000000000000) 4 (IntervalRat.scale (293 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-10789307145 / 1000000000000) (-10789307144 / 1000000000000), orderedInterval (-42179468798 / 1000000000000) (-42179468797 / 1000000000000)))) (orderedInterval (-226625449719 / 1000000000000) (-226625446500 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1254302971716563 / 4000000000000) 4 (IntervalRat.scale (293 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (9016792105 / 1000000000000) (9016792106 / 1000000000000), orderedInterval (44131906875 / 1000000000000) (44131906876 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (895129785747779 / 4000000000000) 4 (IntervalRat.scale (293 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-53251368477 / 1000000000000) (-53251368442 / 1000000000000), orderedInterval (-2897674576 / 1000000000000) (-2897674540 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1014981773235141 / 4000000000000) 4 (IntervalRat.scale (293 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-3070715589 / 1000000000000) (-3070715588 / 1000000000000), orderedInterval (-49988618826 / 1000000000000) (-49988618824 / 1000000000000)))) (orderedInterval (-30793332007 / 1000000000000) (-30793331850 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (846185985354229 / 4000000000000) 4 (IntervalRat.scale (293 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-52814150227 / 1000000000000) (-52814147848 / 1000000000000), orderedInterval (14957879867 / 1000000000000) (14957882246 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (747630980306809 / 4000000000000) 4 (IntervalRat.scale (293 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-41991155960 / 1000000000000) (-41991097519 / 1000000000000), orderedInterval (40643879102 / 1000000000000) (40643937543 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (216692598410091 / 800000000000) 4 (IntervalRat.scale (293 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (48251733495 / 1000000000000) (48251733522 / 1000000000000), orderedInterval (4609980691 / 1000000000000) (4609980719 / 1000000000000)))) (orderedInterval (18102724466 / 1000000000000) (18102733624 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate272_chunkChecks4_2 :
    compactCertificate272.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (599383131108977 / 4000000000000) 4 (IntervalRat.scale (293 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-10776778915 / 1000000000000) (-10776778858 / 1000000000000), orderedInterval (64319574117 / 1000000000000) (64319574174 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (508103718227497 / 4000000000000) 4 (IntervalRat.scale (293 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (59376771516 / 1000000000000) (59376803878 / 1000000000000), orderedInterval (-38783854928 / 1000000000000) (-38783822566 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (317947714854691 / 4000000000000) 4 (IntervalRat.scale (293 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-88347673694 / 1000000000000) (-88347673423 / 1000000000000), orderedInterval (14826347303 / 1000000000000) (14826347574 / 1000000000000)))) (orderedInterval (-392216973 / 1000000000000) (-392215879 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (170993338495197 / 4000000000000) 4 (IntervalRat.scale (293 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-53242127926 / 1000000000000) (-53242124028 / 1000000000000), orderedInterval (110432383127 / 1000000000000) (110432387025 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (464280176956591 / 4000000000000) 4 (IntervalRat.scale (293 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-42755433319 / 1000000000000) (-42755433318 / 1000000000000), orderedInterval (-60287135304 / 1000000000000) (-60287135303 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (633934889101007 / 4000000000000) 4 (IntervalRat.scale (293 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (51660044729 / 1000000000000) (51660098972 / 1000000000000), orderedInterval (-36880459466 / 1000000000000) (-36880405223 / 1000000000000)))) (orderedInterval (-4975089416 / 1000000000000) (-4975083633 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (268052285145309 / 4000000000000) 4 (IntervalRat.scale (293 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-94379033944 / 1000000000000) (-94379033139 / 1000000000000), orderedInterval (25041377389 / 1000000000000) (25041378193 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1089617657297789 / 4000000000000) 4 (IntervalRat.scale (293 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (6228886799 / 1000000000000) (6228886811 / 1000000000000), orderedInterval (-47951436193 / 1000000000000) (-47951436180 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (727814097764851 / 4000000000000) 4 (IntervalRat.scale (293 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (29691135344 / 1000000000000) (29691135345 / 1000000000000), orderedInterval (51077450276 / 1000000000000) (51077450277 / 1000000000000)))) (orderedInterval (-19248407056 / 1000000000000) (-19248406834 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate272_chunkChecks4 :
    compactCertificate272.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate272.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate272_chunkChecks4_0
    compactCertificate272_chunkChecks4_1 compactCertificate272_chunkChecks4_2

theorem compactCertificate272_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate272.chunkCheck r b = true :=
  compactCertificate272.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate272_chunkChecks0
    · exact compactCertificate272_chunkChecks1
    · exact compactCertificate272_chunkChecks2
    · exact compactCertificate272_chunkChecks3
    · exact compactCertificate272_chunkChecks4)

theorem compactCertificate272_coefficient0 :
    compactCertificate272.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate272, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate272_coefficient1 :
    compactCertificate272.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate272, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate272_coefficient2 :
    compactCertificate272.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate272, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate272_coefficient3 :
    compactCertificate272.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate272, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate272_coefficient4 :
    compactCertificate272.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate272, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate272_coefficients : ∀ r : Fin 5,
    compactCertificate272.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate272_coefficient0
  · exact compactCertificate272_coefficient1
  · exact compactCertificate272_coefficient2
  · exact compactCertificate272_coefficient3
  · exact compactCertificate272_coefficient4

theorem compactCertificate272_lower : (1 : ℚ) ≤ compactCertificate272.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate272, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate272_proves {t : ℝ} (ht : t ∈ compactCertificate272.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate272.proves compactCertificate272_states compactCertificate272_chunks
    compactCertificate272_coefficients compactCertificate272_lower ht

end Erdos232
