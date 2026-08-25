/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate212 : CompactCertificate where
  left := 93
  right := 94
  center := 187 / 2
  grid := fun i =>
    match i.val with
    | 0 => 30
    | 1 => 22
    | 2 => 35
    | 3 => 6
    | 4 => 17
    | 5 => 47
    | 6 => 34
    | 7 => 59
    | 8 => 43
    | 9 => 67
    | 10 => 38
    | 11 => 68
    | 12 => 64
    | 13 => 45
    | 14 => 52
    | 15 => 43
    | 16 => 38
    | 17 => 55
    | 18 => 30
    | 19 => 26
    | 20 => 16
    | 21 => 9
    | 22 => 24
    | 23 => 32
    | 24 => 14
    | 25 => 55
    | _ => 37
  point := fun i =>
    match i.val with
    | 0 => 187 / 2
    | 1 => 275486707257487 / 4000000000000
    | 2 => 89086740895471 / 800000000000
    | 3 => 80386334104109 / 4000000000000
    | 4 => 215929000676873 / 4000000000000
    | 5 => 586289241010341 / 4000000000000
    | 6 => 431858001353933 / 4000000000000
    | 7 => 739996046103809 / 4000000000000
    | 8 => 545077738300931 / 4000000000000
    | 9 => 836289423584813 / 4000000000000
    | 10 => 482831923827077 / 4000000000000
    | 11 => 856793721721993 / 4000000000000
    | 12 => 800527835191117 / 4000000000000
    | 13 => 571294436637661 / 4000000000000
    | 14 => 647787002030619 / 4000000000000
    | 15 => 540057267103211 / 4000000000000
    | 16 => 477156973779431 / 4000000000000
    | 17 => 138298689087669 / 800000000000
    | 18 => 382541452277743 / 4000000000000
    | 19 => 324284625626423 / 4000000000000
    | 20 => 202922261699069 / 4000000000000
    | 21 => 109132267230723 / 4000000000000
    | 22 => 296315334781169 / 4000000000000
    | 23 => 404593256866513 / 4000000000000
    | 24 => 171077738300931 / 4000000000000
    | 25 => 695421508241251 / 4000000000000
    | _ => 464509338846509 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (2993118668 / 1000000000000) (2993118672 / 1000000000000), orderedInterval (82445536663 / 1000000000000) (82445536667 / 1000000000000))
    | 1 => (orderedInterval (49448451608 / 1000000000000) (49448451609 / 1000000000000), orderedInterval (82094225611 / 1000000000000) (82094225612 / 1000000000000))
    | 2 => (orderedInterval (-61705087984 / 1000000000000) (-61705044607 / 1000000000000), orderedInterval (43972779239 / 1000000000000) (43972822615 / 1000000000000))
    | 3 => (orderedInterval (159818044453 / 1000000000000) (159818050709 / 1000000000000), orderedInterval (-82269505420 / 1000000000000) (-82269499163 / 1000000000000))
    | 4 => (orderedInterval (-106150347719 / 1000000000000) (-106150347717 / 1000000000000), orderedInterval (-21924845717 / 1000000000000) (-21924845715 / 1000000000000))
    | 5 => (orderedInterval (19349994261 / 1000000000000) (19349994617 / 1000000000000), orderedInterval (-63065866916 / 1000000000000) (-63065866560 / 1000000000000))
    | 6 => (orderedInterval (71763133497 / 1000000000000) (71763137106 / 1000000000000), orderedInterval (-27655790386 / 1000000000000) (-27655786777 / 1000000000000))
    | 7 => (orderedInterval (-24441945329 / 1000000000000) (-24441945328 / 1000000000000), orderedInterval (-53261287070 / 1000000000000) (-53261287069 / 1000000000000))
    | 8 => (orderedInterval (-63096537059 / 1000000000000) (-63096531250 / 1000000000000), orderedInterval (26510349617 / 1000000000000) (26510355426 / 1000000000000))
    | 9 => (orderedInterval (32489712373 / 1000000000000) (32489722872 / 1000000000000), orderedInterval (-44680331520 / 1000000000000) (-44680321020 / 1000000000000))
    | 10 => (orderedInterval (62250437240 / 1000000000000) (62250460030 / 1000000000000), orderedInterval (-37659854586 / 1000000000000) (-37659831795 / 1000000000000))
    | 11 => (orderedInterval (53251819920 / 1000000000000) (53251819923 / 1000000000000), orderedInterval (11552133726 / 1000000000000) (11552133729 / 1000000000000))
    | 12 => (orderedInterval (-8160430762 / 1000000000000) (-8160430733 / 1000000000000), orderedInterval (55827348865 / 1000000000000) (55827348893 / 1000000000000))
    | 13 => (orderedInterval (-52509845653 / 1000000000000) (-52509769073 / 1000000000000), orderedInterval (41416032008 / 1000000000000) (41416108588 / 1000000000000))
    | 14 => (orderedInterval (-37011111168 / 1000000000000) (-37011097658 / 1000000000000), orderedInterval (50722833871 / 1000000000000) (50722847380 / 1000000000000))
    | 15 => (orderedInterval (-44775412460 / 1000000000000) (-44775412459 / 1000000000000), orderedInterval (-51895391727 / 1000000000000) (-51895391726 / 1000000000000))
    | 16 => (orderedInterval (46673807468 / 1000000000000) (46673807469 / 1000000000000), orderedInterval (56003468668 / 1000000000000) (56003468669 / 1000000000000))
    | 17 => (orderedInterval (-46399868167 / 1000000000000) (-46399868166 / 1000000000000), orderedInterval (-38976263398 / 1000000000000) (-38976263397 / 1000000000000))
    | 18 => (orderedInterval (67297215379 / 1000000000000) (67297250638 / 1000000000000), orderedInterval (-46479821347 / 1000000000000) (-46479786088 / 1000000000000))
    | 19 => (orderedInterval (15306588478 / 1000000000000) (15306588479 / 1000000000000), orderedInterval (87189355912 / 1000000000000) (87189355913 / 1000000000000))
    | 20 => (orderedInterval (106234806382 / 1000000000000) (106234806383 / 1000000000000), orderedInterval (34487781306 / 1000000000000) (34487781307 / 1000000000000))
    | 21 => (orderedInterval (31907299388 / 1000000000000) (31907299626 / 1000000000000), orderedInterval (-149981243363 / 1000000000000) (-149981243125 / 1000000000000))
    | 22 => (orderedInterval (-47317315929 / 1000000000000) (-47317307881 / 1000000000000), orderedInterval (80037483632 / 1000000000000) (80037491680 / 1000000000000))
    | 23 => (orderedInterval (78199735588 / 1000000000000) (78199735590 / 1000000000000), orderedInterval (12979546212 / 1000000000000) (12979546215 / 1000000000000))
    | 24 => (orderedInterval (-50900907793 / 1000000000000) (-50900904691 / 1000000000000), orderedInterval (111476374781 / 1000000000000) (111476377883 / 1000000000000))
    | 25 => (orderedInterval (-58127961707 / 1000000000000) (-58127959606 / 1000000000000), orderedInterval (16986958366 / 1000000000000) (16986960467 / 1000000000000))
    | _ => (orderedInterval (-46136435886 / 1000000000000) (-46136435885 / 1000000000000), orderedInterval (-57710980201 / 1000000000000) (-57710980200 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-1973793811 / 1000000000000) (-1973791257 / 1000000000000)
      | 1 => orderedInterval (-6985231250 / 1000000000000) (-6985231144 / 1000000000000)
      | 2 => orderedInterval (-771031428 / 1000000000000) (-771031282 / 1000000000000)
      | 3 => orderedInterval (6409273610 / 1000000000000) (6409277202 / 1000000000000)
      | 4 => orderedInterval (-4630863074 / 1000000000000) (-4630855751 / 1000000000000)
      | 5 => orderedInterval (-4376058501 / 1000000000000) (-4376058491 / 1000000000000)
      | 6 => orderedInterval (-8168171080 / 1000000000000) (-8168165418 / 1000000000000)
      | 7 => orderedInterval (-5508830163 / 1000000000000) (-5508829963 / 1000000000000)
      | _ => orderedInterval (13081291058 / 1000000000000) (13081291274 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (36315211820 / 1000000000000) (36315214861 / 1000000000000)
      | 1 => orderedInterval (6757817766 / 1000000000000) (6757817834 / 1000000000000)
      | 2 => orderedInterval (4184202787 / 1000000000000) (4184203002 / 1000000000000)
      | 3 => orderedInterval (17912356395 / 1000000000000) (17912362826 / 1000000000000)
      | 4 => orderedInterval (3380569754 / 1000000000000) (3380580954 / 1000000000000)
      | 5 => orderedInterval (-6799333353 / 1000000000000) (-6799333339 / 1000000000000)
      | 6 => orderedInterval (3931751099 / 1000000000000) (3931756888 / 1000000000000)
      | 7 => orderedInterval (-1706631606 / 1000000000000) (-1706631449 / 1000000000000)
      | _ => orderedInterval (11184808652 / 1000000000000) (11184809016 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (3311439411 / 1000000000000) (3311443064 / 1000000000000)
      | 1 => orderedInterval (4680136075 / 1000000000000) (4680136160 / 1000000000000)
      | 2 => orderedInterval (242960201 / 1000000000000) (242960518 / 1000000000000)
      | 3 => orderedInterval (-18742600600 / 1000000000000) (-18742588222 / 1000000000000)
      | 4 => orderedInterval (10313103967 / 1000000000000) (10313121223 / 1000000000000)
      | 5 => orderedInterval (9559684783 / 1000000000000) (9559684804 / 1000000000000)
      | 6 => orderedInterval (10848569923 / 1000000000000) (10848575904 / 1000000000000)
      | 7 => orderedInterval (6408294393 / 1000000000000) (6408294520 / 1000000000000)
      | _ => orderedInterval (-29768151540 / 1000000000000) (-29768150887 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-37374813576 / 1000000000000) (-37374809226 / 1000000000000)
      | 1 => orderedInterval (-17175251682 / 1000000000000) (-17175251556 / 1000000000000)
      | 2 => orderedInterval (-14710492122 / 1000000000000) (-14710491654 / 1000000000000)
      | 3 => orderedInterval (-102300488029 / 1000000000000) (-102300463042 / 1000000000000)
      | 4 => orderedInterval (-2851605957 / 1000000000000) (-2851579554 / 1000000000000)
      | 5 => orderedInterval (14664376105 / 1000000000000) (14664376136 / 1000000000000)
      | 6 => orderedInterval (-5030636886 / 1000000000000) (-5030630770 / 1000000000000)
      | 7 => orderedInterval (2024876730 / 1000000000000) (2024876833 / 1000000000000)
      | _ => orderedInterval (-11600501650 / 1000000000000) (-11600500458 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-5163796442 / 1000000000000) (-5163791216 / 1000000000000)
      | 1 => orderedInterval (-8373506893 / 1000000000000) (-8373506696 / 1000000000000)
      | 2 => orderedInterval (4988737022 / 1000000000000) (4988737721 / 1000000000000)
      | 3 => orderedInterval (79177822934 / 1000000000000) (79177875597 / 1000000000000)
      | 4 => orderedInterval (-22194122988 / 1000000000000) (-22194082292 / 1000000000000)
      | 5 => orderedInterval (-23520523614 / 1000000000000) (-23520523566 / 1000000000000)
      | 6 => orderedInterval (-11858607891 / 1000000000000) (-11858601572 / 1000000000000)
      | 7 => orderedInterval (-7831962486 / 1000000000000) (-7831962400 / 1000000000000)
      | _ => orderedInterval (77391540557 / 1000000000000) (77391542760 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-12923414639 / 1000000000000) (-12923394830 / 1000000000000)
    | 1 => orderedInterval (75160753314 / 1000000000000) (75160780593 / 1000000000000)
    | 2 => orderedInterval (-3146563387 / 1000000000000) (-3146522916 / 1000000000000)
    | 3 => orderedInterval (-174354537067 / 1000000000000) (-174354473291 / 1000000000000)
    | _ => orderedInterval (82615580199 / 1000000000000) (82615688336 / 1000000000000)

theorem compactCertificate212_stateChecks0 :
    compactCertificate212.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (187 / 2)) (orderedInterval (2993118668 / 1000000000000) (2993118672 / 1000000000000), orderedInterval (82445536663 / 1000000000000) (82445536667 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 22 12 (275486707257487 / 4000000000000)) (orderedInterval (49448451608 / 1000000000000) (49448451609 / 1000000000000), orderedInterval (82094225611 / 1000000000000) (82094225612 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (89086740895471 / 800000000000)) (orderedInterval (-61705087984 / 1000000000000) (-61705044607 / 1000000000000), orderedInterval (43972779239 / 1000000000000) (43972822615 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState014, besselGridState016, besselGridState017, besselGridState022, besselGridState024, besselGridState026, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState047, besselGridState052, besselGridState055, besselGridState059, besselGridState064, besselGridState067, besselGridState068, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate212_stateChecks1 :
    compactCertificate212.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 6 12 (80386334104109 / 4000000000000)) (orderedInterval (159818044453 / 1000000000000) (159818050709 / 1000000000000), orderedInterval (-82269505420 / 1000000000000) (-82269499163 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 17 12 (215929000676873 / 4000000000000)) (orderedInterval (-106150347719 / 1000000000000) (-106150347717 / 1000000000000), orderedInterval (-21924845717 / 1000000000000) (-21924845715 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (586289241010341 / 4000000000000)) (orderedInterval (19349994261 / 1000000000000) (19349994617 / 1000000000000), orderedInterval (-63065866916 / 1000000000000) (-63065866560 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState014, besselGridState016, besselGridState017, besselGridState022, besselGridState024, besselGridState026, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState047, besselGridState052, besselGridState055, besselGridState059, besselGridState064, besselGridState067, besselGridState068, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate212_stateChecks2 :
    compactCertificate212.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (431858001353933 / 4000000000000)) (orderedInterval (71763133497 / 1000000000000) (71763137106 / 1000000000000), orderedInterval (-27655790386 / 1000000000000) (-27655786777 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (739996046103809 / 4000000000000)) (orderedInterval (-24441945329 / 1000000000000) (-24441945328 / 1000000000000), orderedInterval (-53261287070 / 1000000000000) (-53261287069 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (545077738300931 / 4000000000000)) (orderedInterval (-63096537059 / 1000000000000) (-63096531250 / 1000000000000), orderedInterval (26510349617 / 1000000000000) (26510355426 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState014, besselGridState016, besselGridState017, besselGridState022, besselGridState024, besselGridState026, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState047, besselGridState052, besselGridState055, besselGridState059, besselGridState064, besselGridState067, besselGridState068, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate212_stateChecks3 :
    compactCertificate212.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (836289423584813 / 4000000000000)) (orderedInterval (32489712373 / 1000000000000) (32489722872 / 1000000000000), orderedInterval (-44680331520 / 1000000000000) (-44680321020 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (482831923827077 / 4000000000000)) (orderedInterval (62250437240 / 1000000000000) (62250460030 / 1000000000000), orderedInterval (-37659854586 / 1000000000000) (-37659831795 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (856793721721993 / 4000000000000)) (orderedInterval (53251819920 / 1000000000000) (53251819923 / 1000000000000), orderedInterval (11552133726 / 1000000000000) (11552133729 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState014, besselGridState016, besselGridState017, besselGridState022, besselGridState024, besselGridState026, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState047, besselGridState052, besselGridState055, besselGridState059, besselGridState064, besselGridState067, besselGridState068, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate212_stateChecks4 :
    compactCertificate212.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (800527835191117 / 4000000000000)) (orderedInterval (-8160430762 / 1000000000000) (-8160430733 / 1000000000000), orderedInterval (55827348865 / 1000000000000) (55827348893 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (571294436637661 / 4000000000000)) (orderedInterval (-52509845653 / 1000000000000) (-52509769073 / 1000000000000), orderedInterval (41416032008 / 1000000000000) (41416108588 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (647787002030619 / 4000000000000)) (orderedInterval (-37011111168 / 1000000000000) (-37011097658 / 1000000000000), orderedInterval (50722833871 / 1000000000000) (50722847380 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState014, besselGridState016, besselGridState017, besselGridState022, besselGridState024, besselGridState026, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState047, besselGridState052, besselGridState055, besselGridState059, besselGridState064, besselGridState067, besselGridState068, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate212_stateChecks5 :
    compactCertificate212.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (540057267103211 / 4000000000000)) (orderedInterval (-44775412460 / 1000000000000) (-44775412459 / 1000000000000), orderedInterval (-51895391727 / 1000000000000) (-51895391726 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (477156973779431 / 4000000000000)) (orderedInterval (46673807468 / 1000000000000) (46673807469 / 1000000000000), orderedInterval (56003468668 / 1000000000000) (56003468669 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (138298689087669 / 800000000000)) (orderedInterval (-46399868167 / 1000000000000) (-46399868166 / 1000000000000), orderedInterval (-38976263398 / 1000000000000) (-38976263397 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState014, besselGridState016, besselGridState017, besselGridState022, besselGridState024, besselGridState026, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState047, besselGridState052, besselGridState055, besselGridState059, besselGridState064, besselGridState067, besselGridState068, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate212_stateChecks6 :
    compactCertificate212.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (382541452277743 / 4000000000000)) (orderedInterval (67297215379 / 1000000000000) (67297250638 / 1000000000000), orderedInterval (-46479821347 / 1000000000000) (-46479786088 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (324284625626423 / 4000000000000)) (orderedInterval (15306588478 / 1000000000000) (15306588479 / 1000000000000), orderedInterval (87189355912 / 1000000000000) (87189355913 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 16 12 (202922261699069 / 4000000000000)) (orderedInterval (106234806382 / 1000000000000) (106234806383 / 1000000000000), orderedInterval (34487781306 / 1000000000000) (34487781307 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState014, besselGridState016, besselGridState017, besselGridState022, besselGridState024, besselGridState026, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState047, besselGridState052, besselGridState055, besselGridState059, besselGridState064, besselGridState067, besselGridState068, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate212_stateChecks7 :
    compactCertificate212.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 9 12 (109132267230723 / 4000000000000)) (orderedInterval (31907299388 / 1000000000000) (31907299626 / 1000000000000), orderedInterval (-149981243363 / 1000000000000) (-149981243125 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 24 12 (296315334781169 / 4000000000000)) (orderedInterval (-47317315929 / 1000000000000) (-47317307881 / 1000000000000), orderedInterval (80037483632 / 1000000000000) (80037491680 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (404593256866513 / 4000000000000)) (orderedInterval (78199735588 / 1000000000000) (78199735590 / 1000000000000), orderedInterval (12979546212 / 1000000000000) (12979546215 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState014, besselGridState016, besselGridState017, besselGridState022, besselGridState024, besselGridState026, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState047, besselGridState052, besselGridState055, besselGridState059, besselGridState064, besselGridState067, besselGridState068, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate212_stateChecks8 :
    compactCertificate212.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 14 12 (171077738300931 / 4000000000000)) (orderedInterval (-50900907793 / 1000000000000) (-50900904691 / 1000000000000), orderedInterval (111476374781 / 1000000000000) (111476377883 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (695421508241251 / 4000000000000)) (orderedInterval (-58127961707 / 1000000000000) (-58127959606 / 1000000000000), orderedInterval (16986958366 / 1000000000000) (16986960467 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (464509338846509 / 4000000000000)) (orderedInterval (-46136435886 / 1000000000000) (-46136435885 / 1000000000000), orderedInterval (-57710980201 / 1000000000000) (-57710980200 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState014, besselGridState016, besselGridState017, besselGridState022, besselGridState024, besselGridState026, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState047, besselGridState052, besselGridState055, besselGridState059, besselGridState064, besselGridState067, besselGridState068, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate212_states : ∀ j,
    BesselStateValid (compactCertificate212.point j) (compactCertificate212.state j) :=
  compactCertificate212.statesValid_of_checks3 compactCertificate212_stateChecks0
    compactCertificate212_stateChecks1 compactCertificate212_stateChecks2
    compactCertificate212_stateChecks3 compactCertificate212_stateChecks4
    compactCertificate212_stateChecks5 compactCertificate212_stateChecks6
    compactCertificate212_stateChecks7 compactCertificate212_stateChecks8

theorem compactCertificate212_chunkChecks0_0 :
    compactCertificate212.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (187 / 2) 0 (IntervalRat.scale (187 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (2993118668 / 1000000000000) (2993118672 / 1000000000000), orderedInterval (82445536663 / 1000000000000) (82445536667 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (275486707257487 / 4000000000000) 0 (IntervalRat.scale (187 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (49448451608 / 1000000000000) (49448451609 / 1000000000000), orderedInterval (82094225611 / 1000000000000) (82094225612 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (89086740895471 / 800000000000) 0 (IntervalRat.scale (187 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-61705087984 / 1000000000000) (-61705044607 / 1000000000000), orderedInterval (43972779239 / 1000000000000) (43972822615 / 1000000000000)))) (orderedInterval (-1973793811 / 1000000000000) (-1973791257 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (80386334104109 / 4000000000000) 0 (IntervalRat.scale (187 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (159818044453 / 1000000000000) (159818050709 / 1000000000000), orderedInterval (-82269505420 / 1000000000000) (-82269499163 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (215929000676873 / 4000000000000) 0 (IntervalRat.scale (187 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-106150347719 / 1000000000000) (-106150347717 / 1000000000000), orderedInterval (-21924845717 / 1000000000000) (-21924845715 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (586289241010341 / 4000000000000) 0 (IntervalRat.scale (187 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (19349994261 / 1000000000000) (19349994617 / 1000000000000), orderedInterval (-63065866916 / 1000000000000) (-63065866560 / 1000000000000)))) (orderedInterval (-6985231250 / 1000000000000) (-6985231144 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (431858001353933 / 4000000000000) 0 (IntervalRat.scale (187 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (71763133497 / 1000000000000) (71763137106 / 1000000000000), orderedInterval (-27655790386 / 1000000000000) (-27655786777 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (739996046103809 / 4000000000000) 0 (IntervalRat.scale (187 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-24441945329 / 1000000000000) (-24441945328 / 1000000000000), orderedInterval (-53261287070 / 1000000000000) (-53261287069 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (545077738300931 / 4000000000000) 0 (IntervalRat.scale (187 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-63096537059 / 1000000000000) (-63096531250 / 1000000000000), orderedInterval (26510349617 / 1000000000000) (26510355426 / 1000000000000)))) (orderedInterval (-771031428 / 1000000000000) (-771031282 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate212_chunkChecks0_1 :
    compactCertificate212.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (836289423584813 / 4000000000000) 0 (IntervalRat.scale (187 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (32489712373 / 1000000000000) (32489722872 / 1000000000000), orderedInterval (-44680331520 / 1000000000000) (-44680321020 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (482831923827077 / 4000000000000) 0 (IntervalRat.scale (187 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (62250437240 / 1000000000000) (62250460030 / 1000000000000), orderedInterval (-37659854586 / 1000000000000) (-37659831795 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (856793721721993 / 4000000000000) 0 (IntervalRat.scale (187 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (53251819920 / 1000000000000) (53251819923 / 1000000000000), orderedInterval (11552133726 / 1000000000000) (11552133729 / 1000000000000)))) (orderedInterval (6409273610 / 1000000000000) (6409277202 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (800527835191117 / 4000000000000) 0 (IntervalRat.scale (187 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-8160430762 / 1000000000000) (-8160430733 / 1000000000000), orderedInterval (55827348865 / 1000000000000) (55827348893 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (571294436637661 / 4000000000000) 0 (IntervalRat.scale (187 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-52509845653 / 1000000000000) (-52509769073 / 1000000000000), orderedInterval (41416032008 / 1000000000000) (41416108588 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (647787002030619 / 4000000000000) 0 (IntervalRat.scale (187 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-37011111168 / 1000000000000) (-37011097658 / 1000000000000), orderedInterval (50722833871 / 1000000000000) (50722847380 / 1000000000000)))) (orderedInterval (-4630863074 / 1000000000000) (-4630855751 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (540057267103211 / 4000000000000) 0 (IntervalRat.scale (187 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-44775412460 / 1000000000000) (-44775412459 / 1000000000000), orderedInterval (-51895391727 / 1000000000000) (-51895391726 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (477156973779431 / 4000000000000) 0 (IntervalRat.scale (187 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (46673807468 / 1000000000000) (46673807469 / 1000000000000), orderedInterval (56003468668 / 1000000000000) (56003468669 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (138298689087669 / 800000000000) 0 (IntervalRat.scale (187 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-46399868167 / 1000000000000) (-46399868166 / 1000000000000), orderedInterval (-38976263398 / 1000000000000) (-38976263397 / 1000000000000)))) (orderedInterval (-4376058501 / 1000000000000) (-4376058491 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate212_chunkChecks0_2 :
    compactCertificate212.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (382541452277743 / 4000000000000) 0 (IntervalRat.scale (187 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (67297215379 / 1000000000000) (67297250638 / 1000000000000), orderedInterval (-46479821347 / 1000000000000) (-46479786088 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (324284625626423 / 4000000000000) 0 (IntervalRat.scale (187 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (15306588478 / 1000000000000) (15306588479 / 1000000000000), orderedInterval (87189355912 / 1000000000000) (87189355913 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (202922261699069 / 4000000000000) 0 (IntervalRat.scale (187 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (106234806382 / 1000000000000) (106234806383 / 1000000000000), orderedInterval (34487781306 / 1000000000000) (34487781307 / 1000000000000)))) (orderedInterval (-8168171080 / 1000000000000) (-8168165418 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (109132267230723 / 4000000000000) 0 (IntervalRat.scale (187 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (31907299388 / 1000000000000) (31907299626 / 1000000000000), orderedInterval (-149981243363 / 1000000000000) (-149981243125 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (296315334781169 / 4000000000000) 0 (IntervalRat.scale (187 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-47317315929 / 1000000000000) (-47317307881 / 1000000000000), orderedInterval (80037483632 / 1000000000000) (80037491680 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (404593256866513 / 4000000000000) 0 (IntervalRat.scale (187 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (78199735588 / 1000000000000) (78199735590 / 1000000000000), orderedInterval (12979546212 / 1000000000000) (12979546215 / 1000000000000)))) (orderedInterval (-5508830163 / 1000000000000) (-5508829963 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (171077738300931 / 4000000000000) 0 (IntervalRat.scale (187 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-50900907793 / 1000000000000) (-50900904691 / 1000000000000), orderedInterval (111476374781 / 1000000000000) (111476377883 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (695421508241251 / 4000000000000) 0 (IntervalRat.scale (187 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-58127961707 / 1000000000000) (-58127959606 / 1000000000000), orderedInterval (16986958366 / 1000000000000) (16986960467 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (464509338846509 / 4000000000000) 0 (IntervalRat.scale (187 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-46136435886 / 1000000000000) (-46136435885 / 1000000000000), orderedInterval (-57710980201 / 1000000000000) (-57710980200 / 1000000000000)))) (orderedInterval (13081291058 / 1000000000000) (13081291274 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate212_chunkChecks0 :
    compactCertificate212.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate212.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate212_chunkChecks0_0
    compactCertificate212_chunkChecks0_1 compactCertificate212_chunkChecks0_2

theorem compactCertificate212_chunkChecks1_0 :
    compactCertificate212.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (187 / 2) 1 (IntervalRat.scale (187 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (2993118668 / 1000000000000) (2993118672 / 1000000000000), orderedInterval (82445536663 / 1000000000000) (82445536667 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (275486707257487 / 4000000000000) 1 (IntervalRat.scale (187 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (49448451608 / 1000000000000) (49448451609 / 1000000000000), orderedInterval (82094225611 / 1000000000000) (82094225612 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (89086740895471 / 800000000000) 1 (IntervalRat.scale (187 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-61705087984 / 1000000000000) (-61705044607 / 1000000000000), orderedInterval (43972779239 / 1000000000000) (43972822615 / 1000000000000)))) (orderedInterval (36315211820 / 1000000000000) (36315214861 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (80386334104109 / 4000000000000) 1 (IntervalRat.scale (187 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (159818044453 / 1000000000000) (159818050709 / 1000000000000), orderedInterval (-82269505420 / 1000000000000) (-82269499163 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (215929000676873 / 4000000000000) 1 (IntervalRat.scale (187 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-106150347719 / 1000000000000) (-106150347717 / 1000000000000), orderedInterval (-21924845717 / 1000000000000) (-21924845715 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (586289241010341 / 4000000000000) 1 (IntervalRat.scale (187 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (19349994261 / 1000000000000) (19349994617 / 1000000000000), orderedInterval (-63065866916 / 1000000000000) (-63065866560 / 1000000000000)))) (orderedInterval (6757817766 / 1000000000000) (6757817834 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (431858001353933 / 4000000000000) 1 (IntervalRat.scale (187 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (71763133497 / 1000000000000) (71763137106 / 1000000000000), orderedInterval (-27655790386 / 1000000000000) (-27655786777 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (739996046103809 / 4000000000000) 1 (IntervalRat.scale (187 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-24441945329 / 1000000000000) (-24441945328 / 1000000000000), orderedInterval (-53261287070 / 1000000000000) (-53261287069 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (545077738300931 / 4000000000000) 1 (IntervalRat.scale (187 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-63096537059 / 1000000000000) (-63096531250 / 1000000000000), orderedInterval (26510349617 / 1000000000000) (26510355426 / 1000000000000)))) (orderedInterval (4184202787 / 1000000000000) (4184203002 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate212_chunkChecks1_1 :
    compactCertificate212.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (836289423584813 / 4000000000000) 1 (IntervalRat.scale (187 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (32489712373 / 1000000000000) (32489722872 / 1000000000000), orderedInterval (-44680331520 / 1000000000000) (-44680321020 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (482831923827077 / 4000000000000) 1 (IntervalRat.scale (187 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (62250437240 / 1000000000000) (62250460030 / 1000000000000), orderedInterval (-37659854586 / 1000000000000) (-37659831795 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (856793721721993 / 4000000000000) 1 (IntervalRat.scale (187 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (53251819920 / 1000000000000) (53251819923 / 1000000000000), orderedInterval (11552133726 / 1000000000000) (11552133729 / 1000000000000)))) (orderedInterval (17912356395 / 1000000000000) (17912362826 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (800527835191117 / 4000000000000) 1 (IntervalRat.scale (187 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-8160430762 / 1000000000000) (-8160430733 / 1000000000000), orderedInterval (55827348865 / 1000000000000) (55827348893 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (571294436637661 / 4000000000000) 1 (IntervalRat.scale (187 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-52509845653 / 1000000000000) (-52509769073 / 1000000000000), orderedInterval (41416032008 / 1000000000000) (41416108588 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (647787002030619 / 4000000000000) 1 (IntervalRat.scale (187 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-37011111168 / 1000000000000) (-37011097658 / 1000000000000), orderedInterval (50722833871 / 1000000000000) (50722847380 / 1000000000000)))) (orderedInterval (3380569754 / 1000000000000) (3380580954 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (540057267103211 / 4000000000000) 1 (IntervalRat.scale (187 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-44775412460 / 1000000000000) (-44775412459 / 1000000000000), orderedInterval (-51895391727 / 1000000000000) (-51895391726 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (477156973779431 / 4000000000000) 1 (IntervalRat.scale (187 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (46673807468 / 1000000000000) (46673807469 / 1000000000000), orderedInterval (56003468668 / 1000000000000) (56003468669 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (138298689087669 / 800000000000) 1 (IntervalRat.scale (187 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-46399868167 / 1000000000000) (-46399868166 / 1000000000000), orderedInterval (-38976263398 / 1000000000000) (-38976263397 / 1000000000000)))) (orderedInterval (-6799333353 / 1000000000000) (-6799333339 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate212_chunkChecks1_2 :
    compactCertificate212.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (382541452277743 / 4000000000000) 1 (IntervalRat.scale (187 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (67297215379 / 1000000000000) (67297250638 / 1000000000000), orderedInterval (-46479821347 / 1000000000000) (-46479786088 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (324284625626423 / 4000000000000) 1 (IntervalRat.scale (187 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (15306588478 / 1000000000000) (15306588479 / 1000000000000), orderedInterval (87189355912 / 1000000000000) (87189355913 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (202922261699069 / 4000000000000) 1 (IntervalRat.scale (187 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (106234806382 / 1000000000000) (106234806383 / 1000000000000), orderedInterval (34487781306 / 1000000000000) (34487781307 / 1000000000000)))) (orderedInterval (3931751099 / 1000000000000) (3931756888 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (109132267230723 / 4000000000000) 1 (IntervalRat.scale (187 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (31907299388 / 1000000000000) (31907299626 / 1000000000000), orderedInterval (-149981243363 / 1000000000000) (-149981243125 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (296315334781169 / 4000000000000) 1 (IntervalRat.scale (187 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-47317315929 / 1000000000000) (-47317307881 / 1000000000000), orderedInterval (80037483632 / 1000000000000) (80037491680 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (404593256866513 / 4000000000000) 1 (IntervalRat.scale (187 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (78199735588 / 1000000000000) (78199735590 / 1000000000000), orderedInterval (12979546212 / 1000000000000) (12979546215 / 1000000000000)))) (orderedInterval (-1706631606 / 1000000000000) (-1706631449 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (171077738300931 / 4000000000000) 1 (IntervalRat.scale (187 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-50900907793 / 1000000000000) (-50900904691 / 1000000000000), orderedInterval (111476374781 / 1000000000000) (111476377883 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (695421508241251 / 4000000000000) 1 (IntervalRat.scale (187 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-58127961707 / 1000000000000) (-58127959606 / 1000000000000), orderedInterval (16986958366 / 1000000000000) (16986960467 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (464509338846509 / 4000000000000) 1 (IntervalRat.scale (187 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-46136435886 / 1000000000000) (-46136435885 / 1000000000000), orderedInterval (-57710980201 / 1000000000000) (-57710980200 / 1000000000000)))) (orderedInterval (11184808652 / 1000000000000) (11184809016 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate212_chunkChecks1 :
    compactCertificate212.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate212.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate212_chunkChecks1_0
    compactCertificate212_chunkChecks1_1 compactCertificate212_chunkChecks1_2

theorem compactCertificate212_chunkChecks2_0 :
    compactCertificate212.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (187 / 2) 2 (IntervalRat.scale (187 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (2993118668 / 1000000000000) (2993118672 / 1000000000000), orderedInterval (82445536663 / 1000000000000) (82445536667 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (275486707257487 / 4000000000000) 2 (IntervalRat.scale (187 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (49448451608 / 1000000000000) (49448451609 / 1000000000000), orderedInterval (82094225611 / 1000000000000) (82094225612 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (89086740895471 / 800000000000) 2 (IntervalRat.scale (187 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-61705087984 / 1000000000000) (-61705044607 / 1000000000000), orderedInterval (43972779239 / 1000000000000) (43972822615 / 1000000000000)))) (orderedInterval (3311439411 / 1000000000000) (3311443064 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (80386334104109 / 4000000000000) 2 (IntervalRat.scale (187 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (159818044453 / 1000000000000) (159818050709 / 1000000000000), orderedInterval (-82269505420 / 1000000000000) (-82269499163 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (215929000676873 / 4000000000000) 2 (IntervalRat.scale (187 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-106150347719 / 1000000000000) (-106150347717 / 1000000000000), orderedInterval (-21924845717 / 1000000000000) (-21924845715 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (586289241010341 / 4000000000000) 2 (IntervalRat.scale (187 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (19349994261 / 1000000000000) (19349994617 / 1000000000000), orderedInterval (-63065866916 / 1000000000000) (-63065866560 / 1000000000000)))) (orderedInterval (4680136075 / 1000000000000) (4680136160 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (431858001353933 / 4000000000000) 2 (IntervalRat.scale (187 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (71763133497 / 1000000000000) (71763137106 / 1000000000000), orderedInterval (-27655790386 / 1000000000000) (-27655786777 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (739996046103809 / 4000000000000) 2 (IntervalRat.scale (187 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-24441945329 / 1000000000000) (-24441945328 / 1000000000000), orderedInterval (-53261287070 / 1000000000000) (-53261287069 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (545077738300931 / 4000000000000) 2 (IntervalRat.scale (187 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-63096537059 / 1000000000000) (-63096531250 / 1000000000000), orderedInterval (26510349617 / 1000000000000) (26510355426 / 1000000000000)))) (orderedInterval (242960201 / 1000000000000) (242960518 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate212_chunkChecks2_1 :
    compactCertificate212.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (836289423584813 / 4000000000000) 2 (IntervalRat.scale (187 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (32489712373 / 1000000000000) (32489722872 / 1000000000000), orderedInterval (-44680331520 / 1000000000000) (-44680321020 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (482831923827077 / 4000000000000) 2 (IntervalRat.scale (187 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (62250437240 / 1000000000000) (62250460030 / 1000000000000), orderedInterval (-37659854586 / 1000000000000) (-37659831795 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (856793721721993 / 4000000000000) 2 (IntervalRat.scale (187 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (53251819920 / 1000000000000) (53251819923 / 1000000000000), orderedInterval (11552133726 / 1000000000000) (11552133729 / 1000000000000)))) (orderedInterval (-18742600600 / 1000000000000) (-18742588222 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (800527835191117 / 4000000000000) 2 (IntervalRat.scale (187 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-8160430762 / 1000000000000) (-8160430733 / 1000000000000), orderedInterval (55827348865 / 1000000000000) (55827348893 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (571294436637661 / 4000000000000) 2 (IntervalRat.scale (187 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-52509845653 / 1000000000000) (-52509769073 / 1000000000000), orderedInterval (41416032008 / 1000000000000) (41416108588 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (647787002030619 / 4000000000000) 2 (IntervalRat.scale (187 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-37011111168 / 1000000000000) (-37011097658 / 1000000000000), orderedInterval (50722833871 / 1000000000000) (50722847380 / 1000000000000)))) (orderedInterval (10313103967 / 1000000000000) (10313121223 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (540057267103211 / 4000000000000) 2 (IntervalRat.scale (187 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-44775412460 / 1000000000000) (-44775412459 / 1000000000000), orderedInterval (-51895391727 / 1000000000000) (-51895391726 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (477156973779431 / 4000000000000) 2 (IntervalRat.scale (187 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (46673807468 / 1000000000000) (46673807469 / 1000000000000), orderedInterval (56003468668 / 1000000000000) (56003468669 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (138298689087669 / 800000000000) 2 (IntervalRat.scale (187 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-46399868167 / 1000000000000) (-46399868166 / 1000000000000), orderedInterval (-38976263398 / 1000000000000) (-38976263397 / 1000000000000)))) (orderedInterval (9559684783 / 1000000000000) (9559684804 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate212_chunkChecks2_2 :
    compactCertificate212.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (382541452277743 / 4000000000000) 2 (IntervalRat.scale (187 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (67297215379 / 1000000000000) (67297250638 / 1000000000000), orderedInterval (-46479821347 / 1000000000000) (-46479786088 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (324284625626423 / 4000000000000) 2 (IntervalRat.scale (187 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (15306588478 / 1000000000000) (15306588479 / 1000000000000), orderedInterval (87189355912 / 1000000000000) (87189355913 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (202922261699069 / 4000000000000) 2 (IntervalRat.scale (187 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (106234806382 / 1000000000000) (106234806383 / 1000000000000), orderedInterval (34487781306 / 1000000000000) (34487781307 / 1000000000000)))) (orderedInterval (10848569923 / 1000000000000) (10848575904 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (109132267230723 / 4000000000000) 2 (IntervalRat.scale (187 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (31907299388 / 1000000000000) (31907299626 / 1000000000000), orderedInterval (-149981243363 / 1000000000000) (-149981243125 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (296315334781169 / 4000000000000) 2 (IntervalRat.scale (187 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-47317315929 / 1000000000000) (-47317307881 / 1000000000000), orderedInterval (80037483632 / 1000000000000) (80037491680 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (404593256866513 / 4000000000000) 2 (IntervalRat.scale (187 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (78199735588 / 1000000000000) (78199735590 / 1000000000000), orderedInterval (12979546212 / 1000000000000) (12979546215 / 1000000000000)))) (orderedInterval (6408294393 / 1000000000000) (6408294520 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (171077738300931 / 4000000000000) 2 (IntervalRat.scale (187 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-50900907793 / 1000000000000) (-50900904691 / 1000000000000), orderedInterval (111476374781 / 1000000000000) (111476377883 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (695421508241251 / 4000000000000) 2 (IntervalRat.scale (187 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-58127961707 / 1000000000000) (-58127959606 / 1000000000000), orderedInterval (16986958366 / 1000000000000) (16986960467 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (464509338846509 / 4000000000000) 2 (IntervalRat.scale (187 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-46136435886 / 1000000000000) (-46136435885 / 1000000000000), orderedInterval (-57710980201 / 1000000000000) (-57710980200 / 1000000000000)))) (orderedInterval (-29768151540 / 1000000000000) (-29768150887 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate212_chunkChecks2 :
    compactCertificate212.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate212.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate212_chunkChecks2_0
    compactCertificate212_chunkChecks2_1 compactCertificate212_chunkChecks2_2

theorem compactCertificate212_chunkChecks3_0 :
    compactCertificate212.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (187 / 2) 3 (IntervalRat.scale (187 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (2993118668 / 1000000000000) (2993118672 / 1000000000000), orderedInterval (82445536663 / 1000000000000) (82445536667 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (275486707257487 / 4000000000000) 3 (IntervalRat.scale (187 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (49448451608 / 1000000000000) (49448451609 / 1000000000000), orderedInterval (82094225611 / 1000000000000) (82094225612 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (89086740895471 / 800000000000) 3 (IntervalRat.scale (187 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-61705087984 / 1000000000000) (-61705044607 / 1000000000000), orderedInterval (43972779239 / 1000000000000) (43972822615 / 1000000000000)))) (orderedInterval (-37374813576 / 1000000000000) (-37374809226 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (80386334104109 / 4000000000000) 3 (IntervalRat.scale (187 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (159818044453 / 1000000000000) (159818050709 / 1000000000000), orderedInterval (-82269505420 / 1000000000000) (-82269499163 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (215929000676873 / 4000000000000) 3 (IntervalRat.scale (187 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-106150347719 / 1000000000000) (-106150347717 / 1000000000000), orderedInterval (-21924845717 / 1000000000000) (-21924845715 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (586289241010341 / 4000000000000) 3 (IntervalRat.scale (187 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (19349994261 / 1000000000000) (19349994617 / 1000000000000), orderedInterval (-63065866916 / 1000000000000) (-63065866560 / 1000000000000)))) (orderedInterval (-17175251682 / 1000000000000) (-17175251556 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (431858001353933 / 4000000000000) 3 (IntervalRat.scale (187 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (71763133497 / 1000000000000) (71763137106 / 1000000000000), orderedInterval (-27655790386 / 1000000000000) (-27655786777 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (739996046103809 / 4000000000000) 3 (IntervalRat.scale (187 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-24441945329 / 1000000000000) (-24441945328 / 1000000000000), orderedInterval (-53261287070 / 1000000000000) (-53261287069 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (545077738300931 / 4000000000000) 3 (IntervalRat.scale (187 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-63096537059 / 1000000000000) (-63096531250 / 1000000000000), orderedInterval (26510349617 / 1000000000000) (26510355426 / 1000000000000)))) (orderedInterval (-14710492122 / 1000000000000) (-14710491654 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate212_chunkChecks3_1 :
    compactCertificate212.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (836289423584813 / 4000000000000) 3 (IntervalRat.scale (187 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (32489712373 / 1000000000000) (32489722872 / 1000000000000), orderedInterval (-44680331520 / 1000000000000) (-44680321020 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (482831923827077 / 4000000000000) 3 (IntervalRat.scale (187 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (62250437240 / 1000000000000) (62250460030 / 1000000000000), orderedInterval (-37659854586 / 1000000000000) (-37659831795 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (856793721721993 / 4000000000000) 3 (IntervalRat.scale (187 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (53251819920 / 1000000000000) (53251819923 / 1000000000000), orderedInterval (11552133726 / 1000000000000) (11552133729 / 1000000000000)))) (orderedInterval (-102300488029 / 1000000000000) (-102300463042 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (800527835191117 / 4000000000000) 3 (IntervalRat.scale (187 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-8160430762 / 1000000000000) (-8160430733 / 1000000000000), orderedInterval (55827348865 / 1000000000000) (55827348893 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (571294436637661 / 4000000000000) 3 (IntervalRat.scale (187 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-52509845653 / 1000000000000) (-52509769073 / 1000000000000), orderedInterval (41416032008 / 1000000000000) (41416108588 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (647787002030619 / 4000000000000) 3 (IntervalRat.scale (187 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-37011111168 / 1000000000000) (-37011097658 / 1000000000000), orderedInterval (50722833871 / 1000000000000) (50722847380 / 1000000000000)))) (orderedInterval (-2851605957 / 1000000000000) (-2851579554 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (540057267103211 / 4000000000000) 3 (IntervalRat.scale (187 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-44775412460 / 1000000000000) (-44775412459 / 1000000000000), orderedInterval (-51895391727 / 1000000000000) (-51895391726 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (477156973779431 / 4000000000000) 3 (IntervalRat.scale (187 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (46673807468 / 1000000000000) (46673807469 / 1000000000000), orderedInterval (56003468668 / 1000000000000) (56003468669 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (138298689087669 / 800000000000) 3 (IntervalRat.scale (187 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-46399868167 / 1000000000000) (-46399868166 / 1000000000000), orderedInterval (-38976263398 / 1000000000000) (-38976263397 / 1000000000000)))) (orderedInterval (14664376105 / 1000000000000) (14664376136 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate212_chunkChecks3_2 :
    compactCertificate212.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (382541452277743 / 4000000000000) 3 (IntervalRat.scale (187 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (67297215379 / 1000000000000) (67297250638 / 1000000000000), orderedInterval (-46479821347 / 1000000000000) (-46479786088 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (324284625626423 / 4000000000000) 3 (IntervalRat.scale (187 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (15306588478 / 1000000000000) (15306588479 / 1000000000000), orderedInterval (87189355912 / 1000000000000) (87189355913 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (202922261699069 / 4000000000000) 3 (IntervalRat.scale (187 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (106234806382 / 1000000000000) (106234806383 / 1000000000000), orderedInterval (34487781306 / 1000000000000) (34487781307 / 1000000000000)))) (orderedInterval (-5030636886 / 1000000000000) (-5030630770 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (109132267230723 / 4000000000000) 3 (IntervalRat.scale (187 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (31907299388 / 1000000000000) (31907299626 / 1000000000000), orderedInterval (-149981243363 / 1000000000000) (-149981243125 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (296315334781169 / 4000000000000) 3 (IntervalRat.scale (187 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-47317315929 / 1000000000000) (-47317307881 / 1000000000000), orderedInterval (80037483632 / 1000000000000) (80037491680 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (404593256866513 / 4000000000000) 3 (IntervalRat.scale (187 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (78199735588 / 1000000000000) (78199735590 / 1000000000000), orderedInterval (12979546212 / 1000000000000) (12979546215 / 1000000000000)))) (orderedInterval (2024876730 / 1000000000000) (2024876833 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (171077738300931 / 4000000000000) 3 (IntervalRat.scale (187 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-50900907793 / 1000000000000) (-50900904691 / 1000000000000), orderedInterval (111476374781 / 1000000000000) (111476377883 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (695421508241251 / 4000000000000) 3 (IntervalRat.scale (187 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-58127961707 / 1000000000000) (-58127959606 / 1000000000000), orderedInterval (16986958366 / 1000000000000) (16986960467 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (464509338846509 / 4000000000000) 3 (IntervalRat.scale (187 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-46136435886 / 1000000000000) (-46136435885 / 1000000000000), orderedInterval (-57710980201 / 1000000000000) (-57710980200 / 1000000000000)))) (orderedInterval (-11600501650 / 1000000000000) (-11600500458 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate212_chunkChecks3 :
    compactCertificate212.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate212.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate212_chunkChecks3_0
    compactCertificate212_chunkChecks3_1 compactCertificate212_chunkChecks3_2

theorem compactCertificate212_chunkChecks4_0 :
    compactCertificate212.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (187 / 2) 4 (IntervalRat.scale (187 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (2993118668 / 1000000000000) (2993118672 / 1000000000000), orderedInterval (82445536663 / 1000000000000) (82445536667 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (275486707257487 / 4000000000000) 4 (IntervalRat.scale (187 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (49448451608 / 1000000000000) (49448451609 / 1000000000000), orderedInterval (82094225611 / 1000000000000) (82094225612 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (89086740895471 / 800000000000) 4 (IntervalRat.scale (187 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-61705087984 / 1000000000000) (-61705044607 / 1000000000000), orderedInterval (43972779239 / 1000000000000) (43972822615 / 1000000000000)))) (orderedInterval (-5163796442 / 1000000000000) (-5163791216 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (80386334104109 / 4000000000000) 4 (IntervalRat.scale (187 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (159818044453 / 1000000000000) (159818050709 / 1000000000000), orderedInterval (-82269505420 / 1000000000000) (-82269499163 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (215929000676873 / 4000000000000) 4 (IntervalRat.scale (187 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-106150347719 / 1000000000000) (-106150347717 / 1000000000000), orderedInterval (-21924845717 / 1000000000000) (-21924845715 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (586289241010341 / 4000000000000) 4 (IntervalRat.scale (187 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (19349994261 / 1000000000000) (19349994617 / 1000000000000), orderedInterval (-63065866916 / 1000000000000) (-63065866560 / 1000000000000)))) (orderedInterval (-8373506893 / 1000000000000) (-8373506696 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (431858001353933 / 4000000000000) 4 (IntervalRat.scale (187 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (71763133497 / 1000000000000) (71763137106 / 1000000000000), orderedInterval (-27655790386 / 1000000000000) (-27655786777 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (739996046103809 / 4000000000000) 4 (IntervalRat.scale (187 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-24441945329 / 1000000000000) (-24441945328 / 1000000000000), orderedInterval (-53261287070 / 1000000000000) (-53261287069 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (545077738300931 / 4000000000000) 4 (IntervalRat.scale (187 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-63096537059 / 1000000000000) (-63096531250 / 1000000000000), orderedInterval (26510349617 / 1000000000000) (26510355426 / 1000000000000)))) (orderedInterval (4988737022 / 1000000000000) (4988737721 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate212_chunkChecks4_1 :
    compactCertificate212.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (836289423584813 / 4000000000000) 4 (IntervalRat.scale (187 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (32489712373 / 1000000000000) (32489722872 / 1000000000000), orderedInterval (-44680331520 / 1000000000000) (-44680321020 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (482831923827077 / 4000000000000) 4 (IntervalRat.scale (187 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (62250437240 / 1000000000000) (62250460030 / 1000000000000), orderedInterval (-37659854586 / 1000000000000) (-37659831795 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (856793721721993 / 4000000000000) 4 (IntervalRat.scale (187 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (53251819920 / 1000000000000) (53251819923 / 1000000000000), orderedInterval (11552133726 / 1000000000000) (11552133729 / 1000000000000)))) (orderedInterval (79177822934 / 1000000000000) (79177875597 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (800527835191117 / 4000000000000) 4 (IntervalRat.scale (187 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-8160430762 / 1000000000000) (-8160430733 / 1000000000000), orderedInterval (55827348865 / 1000000000000) (55827348893 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (571294436637661 / 4000000000000) 4 (IntervalRat.scale (187 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-52509845653 / 1000000000000) (-52509769073 / 1000000000000), orderedInterval (41416032008 / 1000000000000) (41416108588 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (647787002030619 / 4000000000000) 4 (IntervalRat.scale (187 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-37011111168 / 1000000000000) (-37011097658 / 1000000000000), orderedInterval (50722833871 / 1000000000000) (50722847380 / 1000000000000)))) (orderedInterval (-22194122988 / 1000000000000) (-22194082292 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (540057267103211 / 4000000000000) 4 (IntervalRat.scale (187 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-44775412460 / 1000000000000) (-44775412459 / 1000000000000), orderedInterval (-51895391727 / 1000000000000) (-51895391726 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (477156973779431 / 4000000000000) 4 (IntervalRat.scale (187 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (46673807468 / 1000000000000) (46673807469 / 1000000000000), orderedInterval (56003468668 / 1000000000000) (56003468669 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (138298689087669 / 800000000000) 4 (IntervalRat.scale (187 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-46399868167 / 1000000000000) (-46399868166 / 1000000000000), orderedInterval (-38976263398 / 1000000000000) (-38976263397 / 1000000000000)))) (orderedInterval (-23520523614 / 1000000000000) (-23520523566 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate212_chunkChecks4_2 :
    compactCertificate212.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (382541452277743 / 4000000000000) 4 (IntervalRat.scale (187 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (67297215379 / 1000000000000) (67297250638 / 1000000000000), orderedInterval (-46479821347 / 1000000000000) (-46479786088 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (324284625626423 / 4000000000000) 4 (IntervalRat.scale (187 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (15306588478 / 1000000000000) (15306588479 / 1000000000000), orderedInterval (87189355912 / 1000000000000) (87189355913 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (202922261699069 / 4000000000000) 4 (IntervalRat.scale (187 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (106234806382 / 1000000000000) (106234806383 / 1000000000000), orderedInterval (34487781306 / 1000000000000) (34487781307 / 1000000000000)))) (orderedInterval (-11858607891 / 1000000000000) (-11858601572 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (109132267230723 / 4000000000000) 4 (IntervalRat.scale (187 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (31907299388 / 1000000000000) (31907299626 / 1000000000000), orderedInterval (-149981243363 / 1000000000000) (-149981243125 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (296315334781169 / 4000000000000) 4 (IntervalRat.scale (187 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-47317315929 / 1000000000000) (-47317307881 / 1000000000000), orderedInterval (80037483632 / 1000000000000) (80037491680 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (404593256866513 / 4000000000000) 4 (IntervalRat.scale (187 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (78199735588 / 1000000000000) (78199735590 / 1000000000000), orderedInterval (12979546212 / 1000000000000) (12979546215 / 1000000000000)))) (orderedInterval (-7831962486 / 1000000000000) (-7831962400 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (171077738300931 / 4000000000000) 4 (IntervalRat.scale (187 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-50900907793 / 1000000000000) (-50900904691 / 1000000000000), orderedInterval (111476374781 / 1000000000000) (111476377883 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (695421508241251 / 4000000000000) 4 (IntervalRat.scale (187 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-58127961707 / 1000000000000) (-58127959606 / 1000000000000), orderedInterval (16986958366 / 1000000000000) (16986960467 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (464509338846509 / 4000000000000) 4 (IntervalRat.scale (187 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-46136435886 / 1000000000000) (-46136435885 / 1000000000000), orderedInterval (-57710980201 / 1000000000000) (-57710980200 / 1000000000000)))) (orderedInterval (77391540557 / 1000000000000) (77391542760 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate212_chunkChecks4 :
    compactCertificate212.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate212.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate212_chunkChecks4_0
    compactCertificate212_chunkChecks4_1 compactCertificate212_chunkChecks4_2

theorem compactCertificate212_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate212.chunkCheck r b = true :=
  compactCertificate212.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate212_chunkChecks0
    · exact compactCertificate212_chunkChecks1
    · exact compactCertificate212_chunkChecks2
    · exact compactCertificate212_chunkChecks3
    · exact compactCertificate212_chunkChecks4)

theorem compactCertificate212_coefficient0 :
    compactCertificate212.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate212, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate212_coefficient1 :
    compactCertificate212.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate212, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate212_coefficient2 :
    compactCertificate212.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate212, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate212_coefficient3 :
    compactCertificate212.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate212, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate212_coefficient4 :
    compactCertificate212.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate212, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate212_coefficients : ∀ r : Fin 5,
    compactCertificate212.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate212_coefficient0
  · exact compactCertificate212_coefficient1
  · exact compactCertificate212_coefficient2
  · exact compactCertificate212_coefficient3
  · exact compactCertificate212_coefficient4

theorem compactCertificate212_lower : (1 : ℚ) ≤ compactCertificate212.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate212, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate212_proves {t : ℝ} (ht : t ∈ compactCertificate212.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate212.proves compactCertificate212_states compactCertificate212_chunks
    compactCertificate212_coefficients compactCertificate212_lower ht

end Erdos232
