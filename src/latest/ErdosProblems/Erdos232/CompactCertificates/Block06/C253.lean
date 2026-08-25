/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate253 : CompactCertificate where
  left := 128
  right := 129
  center := 257 / 2
  grid := fun i =>
    match i.val with
    | 0 => 41
    | 1 => 30
    | 2 => 49
    | 3 => 9
    | 4 => 24
    | 5 => 64
    | 6 => 47
    | 7 => 81
    | 8 => 60
    | 9 => 92
    | 10 => 53
    | 11 => 94
    | 12 => 88
    | 13 => 63
    | 14 => 71
    | 15 => 59
    | 16 => 52
    | 17 => 76
    | 18 => 42
    | 19 => 35
    | 20 => 22
    | 21 => 12
    | 22 => 32
    | 23 => 44
    | 24 => 19
    | 25 => 76
    | _ => 51
  point := fun i =>
    match i.val with
    | 0 => 257 / 2
    | 1 => 378610073610557 / 4000000000000
    | 2 => 122434718770781 / 800000000000
    | 3 => 110477475212599 / 4000000000000
    | 4 => 296758038363403 / 4000000000000
    | 5 => 805755801816351 / 4000000000000
    | 6 => 593516076727063 / 4000000000000
    | 7 => 1016999913629299 / 4000000000000
    | 8 => 749117533386841 / 4000000000000
    | 9 => 1149338940434743 / 4000000000000
    | 10 => 663571146650047 / 4000000000000
    | 11 => 1177518644291723 / 4000000000000
    | 12 => 1100190661198487 / 4000000000000
    | 13 => 785147969068871 / 4000000000000
    | 14 => 890274115090209 / 4000000000000
    | 15 => 742217741419921 / 4000000000000
    | 16 => 655771883750341 / 4000000000000
    | 17 => 190068251847759 / 800000000000
    | 18 => 525738787354973 / 4000000000000
    | 19 => 445674592438453 / 4000000000000
    | 20 => 278882466613159 / 4000000000000
    | 21 => 149983918065753 / 4000000000000
    | 22 => 407235513576259 / 4000000000000
    | 23 => 556045278153443 / 4000000000000
    | 24 => 235117533386841 / 4000000000000
    | 25 => 955739719882361 / 4000000000000
    | _ => 638389840018999 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-32448293167 / 1000000000000) (-32448293166 / 1000000000000), orderedInterval (-62334686200 / 1000000000000) (-62334686199 / 1000000000000))
    | 1 => (orderedInterval (76100134541 / 1000000000000) (76100134542 / 1000000000000), orderedInterval (30168648840 / 1000000000000) (30168648841 / 1000000000000))
    | 2 => (orderedInterval (7084097557 / 1000000000000) (7084097581 / 1000000000000), orderedInterval (-64129078518 / 1000000000000) (-64129078494 / 1000000000000))
    | 3 => (orderedInterval (-19063867110 / 1000000000000) (-19063867108 / 1000000000000), orderedInterval (-150286922549 / 1000000000000) (-150286922547 / 1000000000000))
    | 4 => (orderedInterval (-38194404204 / 1000000000000) (-38194401717 / 1000000000000), orderedInterval (84651181240 / 1000000000000) (84651183727 / 1000000000000))
    | 5 => (orderedInterval (51580207560 / 1000000000000) (51580207561 / 1000000000000), orderedInterval (22228992247 / 1000000000000) (22228992248 / 1000000000000))
    | 6 => (orderedInterval (-65375538322 / 1000000000000) (-65375538303 / 1000000000000), orderedInterval (-3843206858 / 1000000000000) (-3843206840 / 1000000000000))
    | 7 => (orderedInterval (-26828886602 / 1000000000000) (-26828886601 / 1000000000000), orderedInterval (-42186151399 / 1000000000000) (-42186151398 / 1000000000000))
    | 8 => (orderedInterval (-24381570755 / 1000000000000) (-24381569343 / 1000000000000), orderedInterval (53025947026 / 1000000000000) (53025948439 / 1000000000000))
    | 9 => (orderedInterval (-37070226623 / 1000000000000) (-37070134622 / 1000000000000), orderedInterval (29071424567 / 1000000000000) (29071516568 / 1000000000000))
    | 10 => (orderedInterval (-10664840722 / 1000000000000) (-10664840721 / 1000000000000), orderedInterval (-60990925628 / 1000000000000) (-60990925627 / 1000000000000))
    | 11 => (orderedInterval (-6722849794 / 1000000000000) (-6722849780 / 1000000000000), orderedInterval (46026491987 / 1000000000000) (46026492000 / 1000000000000))
    | 12 => (orderedInterval (-28248241215 / 1000000000000) (-28248233860 / 1000000000000), orderedInterval (38995128391 / 1000000000000) (38995135746 / 1000000000000))
    | 13 => (orderedInterval (42732081442 / 1000000000000) (42732164395 / 1000000000000), orderedInterval (-37755606727 / 1000000000000) (-37755523774 / 1000000000000))
    | 14 => (orderedInterval (-15819670204 / 1000000000000) (-15819670203 / 1000000000000), orderedInterval (-51053359149 / 1000000000000) (-51053359148 / 1000000000000))
    | 15 => (orderedInterval (-48814194719 / 1000000000000) (-48814194718 / 1000000000000), orderedInterval (-32242455416 / 1000000000000) (-32242455415 / 1000000000000))
    | 16 => (orderedInterval (60997379119 / 1000000000000) (60997379122 / 1000000000000), orderedInterval (12560788736 / 1000000000000) (12560788738 / 1000000000000))
    | 17 => (orderedInterval (-19721081319 / 1000000000000) (-19721080676 / 1000000000000), orderedInterval (47901976249 / 1000000000000) (47901976892 / 1000000000000))
    | 18 => (orderedInterval (18714447289 / 1000000000000) (18714447290 / 1000000000000), orderedInterval (66961783471 / 1000000000000) (66961783472 / 1000000000000))
    | 19 => (orderedInterval (-58947449799 / 1000000000000) (-58947376399 / 1000000000000), orderedInterval (47582063551 / 1000000000000) (47582136952 / 1000000000000))
    | 20 => (orderedInterval (93983573360 / 1000000000000) (93983573362 / 1000000000000), orderedInterval (16585242915 / 1000000000000) (16585242917 / 1000000000000))
    | 21 => (orderedInterval (71288601363 / 1000000000000) (71288601364 / 1000000000000), orderedInterval (108122408446 / 1000000000000) (108122408447 / 1000000000000))
    | 22 => (orderedInterval (69723358487 / 1000000000000) (69723371432 / 1000000000000), orderedInterval (-37647882445 / 1000000000000) (-37647869501 / 1000000000000))
    | 23 => (orderedInterval (67671846382 / 1000000000000) (67671846422 / 1000000000000), orderedInterval (98655989 / 1000000000000) (98656030 / 1000000000000))
    | 24 => (orderedInterval (13243682581 / 1000000000000) (13243682644 / 1000000000000), orderedInterval (-103338846998 / 1000000000000) (-103338846936 / 1000000000000))
    | 25 => (orderedInterval (42248250067 / 1000000000000) (42248250068 / 1000000000000), orderedInterval (29567784979 / 1000000000000) (29567784980 / 1000000000000))
    | _ => (orderedInterval (-10115136247 / 1000000000000) (-10115136246 / 1000000000000), orderedInterval (-62311006931 / 1000000000000) (-62311006930 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-11736558959 / 1000000000000) (-11736558947 / 1000000000000)
      | 1 => orderedInterval (-4854533389 / 1000000000000) (-4854533282 / 1000000000000)
      | 2 => orderedInterval (238255741 / 1000000000000) (238255783 / 1000000000000)
      | 3 => orderedInterval (4841045666 / 1000000000000) (4841062067 / 1000000000000)
      | 4 => orderedInterval (4630892522 / 1000000000000) (4630900515 / 1000000000000)
      | 5 => orderedInterval (-4559305111 / 1000000000000) (-4559305082 / 1000000000000)
      | 6 => orderedInterval (3403780916 / 1000000000000) (3403785104 / 1000000000000)
      | 7 => orderedInterval (-8084450719 / 1000000000000) (-8084450407 / 1000000000000)
      | _ => orderedInterval (-1461377502 / 1000000000000) (-1461377465 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-28982150136 / 1000000000000) (-28982150123 / 1000000000000)
      | 1 => orderedInterval (-342322251 / 1000000000000) (-342322180 / 1000000000000)
      | 2 => orderedInterval (4442272928 / 1000000000000) (4442272991 / 1000000000000)
      | 3 => orderedInterval (-2395505249 / 1000000000000) (-2395468584 / 1000000000000)
      | 4 => orderedInterval (-6513037259 / 1000000000000) (-6513024966 / 1000000000000)
      | 5 => orderedInterval (812939945 / 1000000000000) (812939994 / 1000000000000)
      | 6 => orderedInterval (-12993398310 / 1000000000000) (-12993394677 / 1000000000000)
      | 7 => orderedInterval (85950812 / 1000000000000) (85951062 / 1000000000000)
      | _ => orderedInterval (9760177975 / 1000000000000) (9760178027 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (12112502111 / 1000000000000) (12112502126 / 1000000000000)
      | 1 => orderedInterval (9468896036 / 1000000000000) (9468896092 / 1000000000000)
      | 2 => orderedInterval (-2022520386 / 1000000000000) (-2022520290 / 1000000000000)
      | 3 => orderedInterval (-26583400632 / 1000000000000) (-26583318372 / 1000000000000)
      | 4 => orderedInterval (-11954624159 / 1000000000000) (-11954605110 / 1000000000000)
      | 5 => orderedInterval (8577009047 / 1000000000000) (8577009132 / 1000000000000)
      | 6 => orderedInterval (-177431494 / 1000000000000) (-177428313 / 1000000000000)
      | 7 => orderedInterval (7173816967 / 1000000000000) (7173817171 / 1000000000000)
      | _ => orderedInterval (8870118118 / 1000000000000) (8870118193 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (30856446045 / 1000000000000) (30856446062 / 1000000000000)
      | 1 => orderedInterval (5402896910 / 1000000000000) (5402896965 / 1000000000000)
      | 2 => orderedInterval (-14030167240 / 1000000000000) (-14030167092 / 1000000000000)
      | 3 => orderedInterval (-10982411902 / 1000000000000) (-10982227981 / 1000000000000)
      | 4 => orderedInterval (18379023048 / 1000000000000) (18379052525 / 1000000000000)
      | 5 => orderedInterval (-5204830780 / 1000000000000) (-5204830634 / 1000000000000)
      | 6 => orderedInterval (13127069220 / 1000000000000) (13127071981 / 1000000000000)
      | 7 => orderedInterval (-421424942 / 1000000000000) (-421424775 / 1000000000000)
      | _ => orderedInterval (-6934482489 / 1000000000000) (-6934482374 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-12295697183 / 1000000000000) (-12295697163 / 1000000000000)
      | 1 => orderedInterval (-22381751992 / 1000000000000) (-22381751924 / 1000000000000)
      | 2 => orderedInterval (10242151100 / 1000000000000) (10242151332 / 1000000000000)
      | 3 => orderedInterval (136324171897 / 1000000000000) (136324584571 / 1000000000000)
      | 4 => orderedInterval (33138409500 / 1000000000000) (33138455568 / 1000000000000)
      | 5 => orderedInterval (-17518441270 / 1000000000000) (-17518441010 / 1000000000000)
      | 6 => orderedInterval (-1328501396 / 1000000000000) (-1328498979 / 1000000000000)
      | 7 => orderedInterval (-7728885886 / 1000000000000) (-7728885748 / 1000000000000)
      | _ => orderedInterval (-36482120278 / 1000000000000) (-36482120093 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-17582250835 / 1000000000000) (-17582221714 / 1000000000000)
    | 1 => orderedInterval (-36125071545 / 1000000000000) (-36125018456 / 1000000000000)
    | 2 => orderedInterval (5464365608 / 1000000000000) (5464470629 / 1000000000000)
    | 3 => orderedInterval (30192117870 / 1000000000000) (30192334677 / 1000000000000)
    | _ => orderedInterval (81969334492 / 1000000000000) (81969796554 / 1000000000000)

theorem compactCertificate253_stateChecks0 :
    compactCertificate253.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (257 / 2)) (orderedInterval (-32448293167 / 1000000000000) (-32448293166 / 1000000000000), orderedInterval (-62334686200 / 1000000000000) (-62334686199 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (378610073610557 / 4000000000000)) (orderedInterval (76100134541 / 1000000000000) (76100134542 / 1000000000000), orderedInterval (30168648840 / 1000000000000) (30168648841 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (122434718770781 / 800000000000)) (orderedInterval (7084097557 / 1000000000000) (7084097581 / 1000000000000), orderedInterval (-64129078518 / 1000000000000) (-64129078494 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState022, besselGridState024, besselGridState030, besselGridState032, besselGridState035, besselGridState041, besselGridState042, besselGridState044, besselGridState047, besselGridState049, besselGridState051, besselGridState052, besselGridState053, besselGridState059, besselGridState060, besselGridState063, besselGridState064, besselGridState071, besselGridState076, besselGridState081, besselGridState088, besselGridState092, besselGridState094, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate253_stateChecks1 :
    compactCertificate253.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 9 12 (110477475212599 / 4000000000000)) (orderedInterval (-19063867110 / 1000000000000) (-19063867108 / 1000000000000), orderedInterval (-150286922549 / 1000000000000) (-150286922547 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 24 12 (296758038363403 / 4000000000000)) (orderedInterval (-38194404204 / 1000000000000) (-38194401717 / 1000000000000), orderedInterval (84651181240 / 1000000000000) (84651183727 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (805755801816351 / 4000000000000)) (orderedInterval (51580207560 / 1000000000000) (51580207561 / 1000000000000), orderedInterval (22228992247 / 1000000000000) (22228992248 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState022, besselGridState024, besselGridState030, besselGridState032, besselGridState035, besselGridState041, besselGridState042, besselGridState044, besselGridState047, besselGridState049, besselGridState051, besselGridState052, besselGridState053, besselGridState059, besselGridState060, besselGridState063, besselGridState064, besselGridState071, besselGridState076, besselGridState081, besselGridState088, besselGridState092, besselGridState094, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate253_stateChecks2 :
    compactCertificate253.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (593516076727063 / 4000000000000)) (orderedInterval (-65375538322 / 1000000000000) (-65375538303 / 1000000000000), orderedInterval (-3843206858 / 1000000000000) (-3843206840 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (1016999913629299 / 4000000000000)) (orderedInterval (-26828886602 / 1000000000000) (-26828886601 / 1000000000000), orderedInterval (-42186151399 / 1000000000000) (-42186151398 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (749117533386841 / 4000000000000)) (orderedInterval (-24381570755 / 1000000000000) (-24381569343 / 1000000000000), orderedInterval (53025947026 / 1000000000000) (53025948439 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState022, besselGridState024, besselGridState030, besselGridState032, besselGridState035, besselGridState041, besselGridState042, besselGridState044, besselGridState047, besselGridState049, besselGridState051, besselGridState052, besselGridState053, besselGridState059, besselGridState060, besselGridState063, besselGridState064, besselGridState071, besselGridState076, besselGridState081, besselGridState088, besselGridState092, besselGridState094, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate253_stateChecks3 :
    compactCertificate253.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 92 12 (1149338940434743 / 4000000000000)) (orderedInterval (-37070226623 / 1000000000000) (-37070134622 / 1000000000000), orderedInterval (29071424567 / 1000000000000) (29071516568 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (663571146650047 / 4000000000000)) (orderedInterval (-10664840722 / 1000000000000) (-10664840721 / 1000000000000), orderedInterval (-60990925628 / 1000000000000) (-60990925627 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 94 12 (1177518644291723 / 4000000000000)) (orderedInterval (-6722849794 / 1000000000000) (-6722849780 / 1000000000000), orderedInterval (46026491987 / 1000000000000) (46026492000 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState022, besselGridState024, besselGridState030, besselGridState032, besselGridState035, besselGridState041, besselGridState042, besselGridState044, besselGridState047, besselGridState049, besselGridState051, besselGridState052, besselGridState053, besselGridState059, besselGridState060, besselGridState063, besselGridState064, besselGridState071, besselGridState076, besselGridState081, besselGridState088, besselGridState092, besselGridState094, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate253_stateChecks4 :
    compactCertificate253.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 88 12 (1100190661198487 / 4000000000000)) (orderedInterval (-28248241215 / 1000000000000) (-28248233860 / 1000000000000), orderedInterval (38995128391 / 1000000000000) (38995135746 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (785147969068871 / 4000000000000)) (orderedInterval (42732081442 / 1000000000000) (42732164395 / 1000000000000), orderedInterval (-37755606727 / 1000000000000) (-37755523774 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (890274115090209 / 4000000000000)) (orderedInterval (-15819670204 / 1000000000000) (-15819670203 / 1000000000000), orderedInterval (-51053359149 / 1000000000000) (-51053359148 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState022, besselGridState024, besselGridState030, besselGridState032, besselGridState035, besselGridState041, besselGridState042, besselGridState044, besselGridState047, besselGridState049, besselGridState051, besselGridState052, besselGridState053, besselGridState059, besselGridState060, besselGridState063, besselGridState064, besselGridState071, besselGridState076, besselGridState081, besselGridState088, besselGridState092, besselGridState094, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate253_stateChecks5 :
    compactCertificate253.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (742217741419921 / 4000000000000)) (orderedInterval (-48814194719 / 1000000000000) (-48814194718 / 1000000000000), orderedInterval (-32242455416 / 1000000000000) (-32242455415 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (655771883750341 / 4000000000000)) (orderedInterval (60997379119 / 1000000000000) (60997379122 / 1000000000000), orderedInterval (12560788736 / 1000000000000) (12560788738 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (190068251847759 / 800000000000)) (orderedInterval (-19721081319 / 1000000000000) (-19721080676 / 1000000000000), orderedInterval (47901976249 / 1000000000000) (47901976892 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState022, besselGridState024, besselGridState030, besselGridState032, besselGridState035, besselGridState041, besselGridState042, besselGridState044, besselGridState047, besselGridState049, besselGridState051, besselGridState052, besselGridState053, besselGridState059, besselGridState060, besselGridState063, besselGridState064, besselGridState071, besselGridState076, besselGridState081, besselGridState088, besselGridState092, besselGridState094, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate253_stateChecks6 :
    compactCertificate253.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (525738787354973 / 4000000000000)) (orderedInterval (18714447289 / 1000000000000) (18714447290 / 1000000000000), orderedInterval (66961783471 / 1000000000000) (66961783472 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (445674592438453 / 4000000000000)) (orderedInterval (-58947449799 / 1000000000000) (-58947376399 / 1000000000000), orderedInterval (47582063551 / 1000000000000) (47582136952 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 22 12 (278882466613159 / 4000000000000)) (orderedInterval (93983573360 / 1000000000000) (93983573362 / 1000000000000), orderedInterval (16585242915 / 1000000000000) (16585242917 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState022, besselGridState024, besselGridState030, besselGridState032, besselGridState035, besselGridState041, besselGridState042, besselGridState044, besselGridState047, besselGridState049, besselGridState051, besselGridState052, besselGridState053, besselGridState059, besselGridState060, besselGridState063, besselGridState064, besselGridState071, besselGridState076, besselGridState081, besselGridState088, besselGridState092, besselGridState094, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate253_stateChecks7 :
    compactCertificate253.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 12 12 (149983918065753 / 4000000000000)) (orderedInterval (71288601363 / 1000000000000) (71288601364 / 1000000000000), orderedInterval (108122408446 / 1000000000000) (108122408447 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (407235513576259 / 4000000000000)) (orderedInterval (69723358487 / 1000000000000) (69723371432 / 1000000000000), orderedInterval (-37647882445 / 1000000000000) (-37647869501 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (556045278153443 / 4000000000000)) (orderedInterval (67671846382 / 1000000000000) (67671846422 / 1000000000000), orderedInterval (98655989 / 1000000000000) (98656030 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState022, besselGridState024, besselGridState030, besselGridState032, besselGridState035, besselGridState041, besselGridState042, besselGridState044, besselGridState047, besselGridState049, besselGridState051, besselGridState052, besselGridState053, besselGridState059, besselGridState060, besselGridState063, besselGridState064, besselGridState071, besselGridState076, besselGridState081, besselGridState088, besselGridState092, besselGridState094, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate253_stateChecks8 :
    compactCertificate253.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 19 12 (235117533386841 / 4000000000000)) (orderedInterval (13243682581 / 1000000000000) (13243682644 / 1000000000000), orderedInterval (-103338846998 / 1000000000000) (-103338846936 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (955739719882361 / 4000000000000)) (orderedInterval (42248250067 / 1000000000000) (42248250068 / 1000000000000), orderedInterval (29567784979 / 1000000000000) (29567784980 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (638389840018999 / 4000000000000)) (orderedInterval (-10115136247 / 1000000000000) (-10115136246 / 1000000000000), orderedInterval (-62311006931 / 1000000000000) (-62311006930 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState012, besselGridState019, besselGridState022, besselGridState024, besselGridState030, besselGridState032, besselGridState035, besselGridState041, besselGridState042, besselGridState044, besselGridState047, besselGridState049, besselGridState051, besselGridState052, besselGridState053, besselGridState059, besselGridState060, besselGridState063, besselGridState064, besselGridState071, besselGridState076, besselGridState081, besselGridState088, besselGridState092, besselGridState094, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate253_states : ∀ j,
    BesselStateValid (compactCertificate253.point j) (compactCertificate253.state j) :=
  compactCertificate253.statesValid_of_checks3 compactCertificate253_stateChecks0
    compactCertificate253_stateChecks1 compactCertificate253_stateChecks2
    compactCertificate253_stateChecks3 compactCertificate253_stateChecks4
    compactCertificate253_stateChecks5 compactCertificate253_stateChecks6
    compactCertificate253_stateChecks7 compactCertificate253_stateChecks8

theorem compactCertificate253_chunkChecks0_0 :
    compactCertificate253.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (257 / 2) 0 (IntervalRat.scale (257 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-32448293167 / 1000000000000) (-32448293166 / 1000000000000), orderedInterval (-62334686200 / 1000000000000) (-62334686199 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (378610073610557 / 4000000000000) 0 (IntervalRat.scale (257 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (76100134541 / 1000000000000) (76100134542 / 1000000000000), orderedInterval (30168648840 / 1000000000000) (30168648841 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (122434718770781 / 800000000000) 0 (IntervalRat.scale (257 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (7084097557 / 1000000000000) (7084097581 / 1000000000000), orderedInterval (-64129078518 / 1000000000000) (-64129078494 / 1000000000000)))) (orderedInterval (-11736558959 / 1000000000000) (-11736558947 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (110477475212599 / 4000000000000) 0 (IntervalRat.scale (257 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-19063867110 / 1000000000000) (-19063867108 / 1000000000000), orderedInterval (-150286922549 / 1000000000000) (-150286922547 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (296758038363403 / 4000000000000) 0 (IntervalRat.scale (257 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-38194404204 / 1000000000000) (-38194401717 / 1000000000000), orderedInterval (84651181240 / 1000000000000) (84651183727 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (805755801816351 / 4000000000000) 0 (IntervalRat.scale (257 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (51580207560 / 1000000000000) (51580207561 / 1000000000000), orderedInterval (22228992247 / 1000000000000) (22228992248 / 1000000000000)))) (orderedInterval (-4854533389 / 1000000000000) (-4854533282 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (593516076727063 / 4000000000000) 0 (IntervalRat.scale (257 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-65375538322 / 1000000000000) (-65375538303 / 1000000000000), orderedInterval (-3843206858 / 1000000000000) (-3843206840 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1016999913629299 / 4000000000000) 0 (IntervalRat.scale (257 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-26828886602 / 1000000000000) (-26828886601 / 1000000000000), orderedInterval (-42186151399 / 1000000000000) (-42186151398 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (749117533386841 / 4000000000000) 0 (IntervalRat.scale (257 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-24381570755 / 1000000000000) (-24381569343 / 1000000000000), orderedInterval (53025947026 / 1000000000000) (53025948439 / 1000000000000)))) (orderedInterval (238255741 / 1000000000000) (238255783 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate253_chunkChecks0_1 :
    compactCertificate253.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1149338940434743 / 4000000000000) 0 (IntervalRat.scale (257 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-37070226623 / 1000000000000) (-37070134622 / 1000000000000), orderedInterval (29071424567 / 1000000000000) (29071516568 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (663571146650047 / 4000000000000) 0 (IntervalRat.scale (257 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-10664840722 / 1000000000000) (-10664840721 / 1000000000000), orderedInterval (-60990925628 / 1000000000000) (-60990925627 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1177518644291723 / 4000000000000) 0 (IntervalRat.scale (257 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-6722849794 / 1000000000000) (-6722849780 / 1000000000000), orderedInterval (46026491987 / 1000000000000) (46026492000 / 1000000000000)))) (orderedInterval (4841045666 / 1000000000000) (4841062067 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1100190661198487 / 4000000000000) 0 (IntervalRat.scale (257 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-28248241215 / 1000000000000) (-28248233860 / 1000000000000), orderedInterval (38995128391 / 1000000000000) (38995135746 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (785147969068871 / 4000000000000) 0 (IntervalRat.scale (257 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (42732081442 / 1000000000000) (42732164395 / 1000000000000), orderedInterval (-37755606727 / 1000000000000) (-37755523774 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (890274115090209 / 4000000000000) 0 (IntervalRat.scale (257 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-15819670204 / 1000000000000) (-15819670203 / 1000000000000), orderedInterval (-51053359149 / 1000000000000) (-51053359148 / 1000000000000)))) (orderedInterval (4630892522 / 1000000000000) (4630900515 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (742217741419921 / 4000000000000) 0 (IntervalRat.scale (257 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-48814194719 / 1000000000000) (-48814194718 / 1000000000000), orderedInterval (-32242455416 / 1000000000000) (-32242455415 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (655771883750341 / 4000000000000) 0 (IntervalRat.scale (257 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (60997379119 / 1000000000000) (60997379122 / 1000000000000), orderedInterval (12560788736 / 1000000000000) (12560788738 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (190068251847759 / 800000000000) 0 (IntervalRat.scale (257 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-19721081319 / 1000000000000) (-19721080676 / 1000000000000), orderedInterval (47901976249 / 1000000000000) (47901976892 / 1000000000000)))) (orderedInterval (-4559305111 / 1000000000000) (-4559305082 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate253_chunkChecks0_2 :
    compactCertificate253.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (525738787354973 / 4000000000000) 0 (IntervalRat.scale (257 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (18714447289 / 1000000000000) (18714447290 / 1000000000000), orderedInterval (66961783471 / 1000000000000) (66961783472 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (445674592438453 / 4000000000000) 0 (IntervalRat.scale (257 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-58947449799 / 1000000000000) (-58947376399 / 1000000000000), orderedInterval (47582063551 / 1000000000000) (47582136952 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (278882466613159 / 4000000000000) 0 (IntervalRat.scale (257 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (93983573360 / 1000000000000) (93983573362 / 1000000000000), orderedInterval (16585242915 / 1000000000000) (16585242917 / 1000000000000)))) (orderedInterval (3403780916 / 1000000000000) (3403785104 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (149983918065753 / 4000000000000) 0 (IntervalRat.scale (257 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (71288601363 / 1000000000000) (71288601364 / 1000000000000), orderedInterval (108122408446 / 1000000000000) (108122408447 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (407235513576259 / 4000000000000) 0 (IntervalRat.scale (257 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (69723358487 / 1000000000000) (69723371432 / 1000000000000), orderedInterval (-37647882445 / 1000000000000) (-37647869501 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (556045278153443 / 4000000000000) 0 (IntervalRat.scale (257 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (67671846382 / 1000000000000) (67671846422 / 1000000000000), orderedInterval (98655989 / 1000000000000) (98656030 / 1000000000000)))) (orderedInterval (-8084450719 / 1000000000000) (-8084450407 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (235117533386841 / 4000000000000) 0 (IntervalRat.scale (257 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (13243682581 / 1000000000000) (13243682644 / 1000000000000), orderedInterval (-103338846998 / 1000000000000) (-103338846936 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (955739719882361 / 4000000000000) 0 (IntervalRat.scale (257 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (42248250067 / 1000000000000) (42248250068 / 1000000000000), orderedInterval (29567784979 / 1000000000000) (29567784980 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (638389840018999 / 4000000000000) 0 (IntervalRat.scale (257 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-10115136247 / 1000000000000) (-10115136246 / 1000000000000), orderedInterval (-62311006931 / 1000000000000) (-62311006930 / 1000000000000)))) (orderedInterval (-1461377502 / 1000000000000) (-1461377465 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate253_chunkChecks0 :
    compactCertificate253.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate253.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate253_chunkChecks0_0
    compactCertificate253_chunkChecks0_1 compactCertificate253_chunkChecks0_2

theorem compactCertificate253_chunkChecks1_0 :
    compactCertificate253.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (257 / 2) 1 (IntervalRat.scale (257 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-32448293167 / 1000000000000) (-32448293166 / 1000000000000), orderedInterval (-62334686200 / 1000000000000) (-62334686199 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (378610073610557 / 4000000000000) 1 (IntervalRat.scale (257 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (76100134541 / 1000000000000) (76100134542 / 1000000000000), orderedInterval (30168648840 / 1000000000000) (30168648841 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (122434718770781 / 800000000000) 1 (IntervalRat.scale (257 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (7084097557 / 1000000000000) (7084097581 / 1000000000000), orderedInterval (-64129078518 / 1000000000000) (-64129078494 / 1000000000000)))) (orderedInterval (-28982150136 / 1000000000000) (-28982150123 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (110477475212599 / 4000000000000) 1 (IntervalRat.scale (257 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-19063867110 / 1000000000000) (-19063867108 / 1000000000000), orderedInterval (-150286922549 / 1000000000000) (-150286922547 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (296758038363403 / 4000000000000) 1 (IntervalRat.scale (257 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-38194404204 / 1000000000000) (-38194401717 / 1000000000000), orderedInterval (84651181240 / 1000000000000) (84651183727 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (805755801816351 / 4000000000000) 1 (IntervalRat.scale (257 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (51580207560 / 1000000000000) (51580207561 / 1000000000000), orderedInterval (22228992247 / 1000000000000) (22228992248 / 1000000000000)))) (orderedInterval (-342322251 / 1000000000000) (-342322180 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (593516076727063 / 4000000000000) 1 (IntervalRat.scale (257 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-65375538322 / 1000000000000) (-65375538303 / 1000000000000), orderedInterval (-3843206858 / 1000000000000) (-3843206840 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1016999913629299 / 4000000000000) 1 (IntervalRat.scale (257 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-26828886602 / 1000000000000) (-26828886601 / 1000000000000), orderedInterval (-42186151399 / 1000000000000) (-42186151398 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (749117533386841 / 4000000000000) 1 (IntervalRat.scale (257 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-24381570755 / 1000000000000) (-24381569343 / 1000000000000), orderedInterval (53025947026 / 1000000000000) (53025948439 / 1000000000000)))) (orderedInterval (4442272928 / 1000000000000) (4442272991 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate253_chunkChecks1_1 :
    compactCertificate253.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1149338940434743 / 4000000000000) 1 (IntervalRat.scale (257 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-37070226623 / 1000000000000) (-37070134622 / 1000000000000), orderedInterval (29071424567 / 1000000000000) (29071516568 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (663571146650047 / 4000000000000) 1 (IntervalRat.scale (257 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-10664840722 / 1000000000000) (-10664840721 / 1000000000000), orderedInterval (-60990925628 / 1000000000000) (-60990925627 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1177518644291723 / 4000000000000) 1 (IntervalRat.scale (257 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-6722849794 / 1000000000000) (-6722849780 / 1000000000000), orderedInterval (46026491987 / 1000000000000) (46026492000 / 1000000000000)))) (orderedInterval (-2395505249 / 1000000000000) (-2395468584 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1100190661198487 / 4000000000000) 1 (IntervalRat.scale (257 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-28248241215 / 1000000000000) (-28248233860 / 1000000000000), orderedInterval (38995128391 / 1000000000000) (38995135746 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (785147969068871 / 4000000000000) 1 (IntervalRat.scale (257 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (42732081442 / 1000000000000) (42732164395 / 1000000000000), orderedInterval (-37755606727 / 1000000000000) (-37755523774 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (890274115090209 / 4000000000000) 1 (IntervalRat.scale (257 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-15819670204 / 1000000000000) (-15819670203 / 1000000000000), orderedInterval (-51053359149 / 1000000000000) (-51053359148 / 1000000000000)))) (orderedInterval (-6513037259 / 1000000000000) (-6513024966 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (742217741419921 / 4000000000000) 1 (IntervalRat.scale (257 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-48814194719 / 1000000000000) (-48814194718 / 1000000000000), orderedInterval (-32242455416 / 1000000000000) (-32242455415 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (655771883750341 / 4000000000000) 1 (IntervalRat.scale (257 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (60997379119 / 1000000000000) (60997379122 / 1000000000000), orderedInterval (12560788736 / 1000000000000) (12560788738 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (190068251847759 / 800000000000) 1 (IntervalRat.scale (257 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-19721081319 / 1000000000000) (-19721080676 / 1000000000000), orderedInterval (47901976249 / 1000000000000) (47901976892 / 1000000000000)))) (orderedInterval (812939945 / 1000000000000) (812939994 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate253_chunkChecks1_2 :
    compactCertificate253.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (525738787354973 / 4000000000000) 1 (IntervalRat.scale (257 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (18714447289 / 1000000000000) (18714447290 / 1000000000000), orderedInterval (66961783471 / 1000000000000) (66961783472 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (445674592438453 / 4000000000000) 1 (IntervalRat.scale (257 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-58947449799 / 1000000000000) (-58947376399 / 1000000000000), orderedInterval (47582063551 / 1000000000000) (47582136952 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (278882466613159 / 4000000000000) 1 (IntervalRat.scale (257 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (93983573360 / 1000000000000) (93983573362 / 1000000000000), orderedInterval (16585242915 / 1000000000000) (16585242917 / 1000000000000)))) (orderedInterval (-12993398310 / 1000000000000) (-12993394677 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (149983918065753 / 4000000000000) 1 (IntervalRat.scale (257 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (71288601363 / 1000000000000) (71288601364 / 1000000000000), orderedInterval (108122408446 / 1000000000000) (108122408447 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (407235513576259 / 4000000000000) 1 (IntervalRat.scale (257 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (69723358487 / 1000000000000) (69723371432 / 1000000000000), orderedInterval (-37647882445 / 1000000000000) (-37647869501 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (556045278153443 / 4000000000000) 1 (IntervalRat.scale (257 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (67671846382 / 1000000000000) (67671846422 / 1000000000000), orderedInterval (98655989 / 1000000000000) (98656030 / 1000000000000)))) (orderedInterval (85950812 / 1000000000000) (85951062 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (235117533386841 / 4000000000000) 1 (IntervalRat.scale (257 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (13243682581 / 1000000000000) (13243682644 / 1000000000000), orderedInterval (-103338846998 / 1000000000000) (-103338846936 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (955739719882361 / 4000000000000) 1 (IntervalRat.scale (257 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (42248250067 / 1000000000000) (42248250068 / 1000000000000), orderedInterval (29567784979 / 1000000000000) (29567784980 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (638389840018999 / 4000000000000) 1 (IntervalRat.scale (257 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-10115136247 / 1000000000000) (-10115136246 / 1000000000000), orderedInterval (-62311006931 / 1000000000000) (-62311006930 / 1000000000000)))) (orderedInterval (9760177975 / 1000000000000) (9760178027 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate253_chunkChecks1 :
    compactCertificate253.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate253.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate253_chunkChecks1_0
    compactCertificate253_chunkChecks1_1 compactCertificate253_chunkChecks1_2

theorem compactCertificate253_chunkChecks2_0 :
    compactCertificate253.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (257 / 2) 2 (IntervalRat.scale (257 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-32448293167 / 1000000000000) (-32448293166 / 1000000000000), orderedInterval (-62334686200 / 1000000000000) (-62334686199 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (378610073610557 / 4000000000000) 2 (IntervalRat.scale (257 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (76100134541 / 1000000000000) (76100134542 / 1000000000000), orderedInterval (30168648840 / 1000000000000) (30168648841 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (122434718770781 / 800000000000) 2 (IntervalRat.scale (257 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (7084097557 / 1000000000000) (7084097581 / 1000000000000), orderedInterval (-64129078518 / 1000000000000) (-64129078494 / 1000000000000)))) (orderedInterval (12112502111 / 1000000000000) (12112502126 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (110477475212599 / 4000000000000) 2 (IntervalRat.scale (257 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-19063867110 / 1000000000000) (-19063867108 / 1000000000000), orderedInterval (-150286922549 / 1000000000000) (-150286922547 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (296758038363403 / 4000000000000) 2 (IntervalRat.scale (257 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-38194404204 / 1000000000000) (-38194401717 / 1000000000000), orderedInterval (84651181240 / 1000000000000) (84651183727 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (805755801816351 / 4000000000000) 2 (IntervalRat.scale (257 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (51580207560 / 1000000000000) (51580207561 / 1000000000000), orderedInterval (22228992247 / 1000000000000) (22228992248 / 1000000000000)))) (orderedInterval (9468896036 / 1000000000000) (9468896092 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (593516076727063 / 4000000000000) 2 (IntervalRat.scale (257 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-65375538322 / 1000000000000) (-65375538303 / 1000000000000), orderedInterval (-3843206858 / 1000000000000) (-3843206840 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1016999913629299 / 4000000000000) 2 (IntervalRat.scale (257 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-26828886602 / 1000000000000) (-26828886601 / 1000000000000), orderedInterval (-42186151399 / 1000000000000) (-42186151398 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (749117533386841 / 4000000000000) 2 (IntervalRat.scale (257 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-24381570755 / 1000000000000) (-24381569343 / 1000000000000), orderedInterval (53025947026 / 1000000000000) (53025948439 / 1000000000000)))) (orderedInterval (-2022520386 / 1000000000000) (-2022520290 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate253_chunkChecks2_1 :
    compactCertificate253.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1149338940434743 / 4000000000000) 2 (IntervalRat.scale (257 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-37070226623 / 1000000000000) (-37070134622 / 1000000000000), orderedInterval (29071424567 / 1000000000000) (29071516568 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (663571146650047 / 4000000000000) 2 (IntervalRat.scale (257 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-10664840722 / 1000000000000) (-10664840721 / 1000000000000), orderedInterval (-60990925628 / 1000000000000) (-60990925627 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1177518644291723 / 4000000000000) 2 (IntervalRat.scale (257 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-6722849794 / 1000000000000) (-6722849780 / 1000000000000), orderedInterval (46026491987 / 1000000000000) (46026492000 / 1000000000000)))) (orderedInterval (-26583400632 / 1000000000000) (-26583318372 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1100190661198487 / 4000000000000) 2 (IntervalRat.scale (257 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-28248241215 / 1000000000000) (-28248233860 / 1000000000000), orderedInterval (38995128391 / 1000000000000) (38995135746 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (785147969068871 / 4000000000000) 2 (IntervalRat.scale (257 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (42732081442 / 1000000000000) (42732164395 / 1000000000000), orderedInterval (-37755606727 / 1000000000000) (-37755523774 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (890274115090209 / 4000000000000) 2 (IntervalRat.scale (257 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-15819670204 / 1000000000000) (-15819670203 / 1000000000000), orderedInterval (-51053359149 / 1000000000000) (-51053359148 / 1000000000000)))) (orderedInterval (-11954624159 / 1000000000000) (-11954605110 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (742217741419921 / 4000000000000) 2 (IntervalRat.scale (257 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-48814194719 / 1000000000000) (-48814194718 / 1000000000000), orderedInterval (-32242455416 / 1000000000000) (-32242455415 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (655771883750341 / 4000000000000) 2 (IntervalRat.scale (257 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (60997379119 / 1000000000000) (60997379122 / 1000000000000), orderedInterval (12560788736 / 1000000000000) (12560788738 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (190068251847759 / 800000000000) 2 (IntervalRat.scale (257 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-19721081319 / 1000000000000) (-19721080676 / 1000000000000), orderedInterval (47901976249 / 1000000000000) (47901976892 / 1000000000000)))) (orderedInterval (8577009047 / 1000000000000) (8577009132 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate253_chunkChecks2_2 :
    compactCertificate253.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (525738787354973 / 4000000000000) 2 (IntervalRat.scale (257 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (18714447289 / 1000000000000) (18714447290 / 1000000000000), orderedInterval (66961783471 / 1000000000000) (66961783472 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (445674592438453 / 4000000000000) 2 (IntervalRat.scale (257 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-58947449799 / 1000000000000) (-58947376399 / 1000000000000), orderedInterval (47582063551 / 1000000000000) (47582136952 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (278882466613159 / 4000000000000) 2 (IntervalRat.scale (257 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (93983573360 / 1000000000000) (93983573362 / 1000000000000), orderedInterval (16585242915 / 1000000000000) (16585242917 / 1000000000000)))) (orderedInterval (-177431494 / 1000000000000) (-177428313 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (149983918065753 / 4000000000000) 2 (IntervalRat.scale (257 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (71288601363 / 1000000000000) (71288601364 / 1000000000000), orderedInterval (108122408446 / 1000000000000) (108122408447 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (407235513576259 / 4000000000000) 2 (IntervalRat.scale (257 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (69723358487 / 1000000000000) (69723371432 / 1000000000000), orderedInterval (-37647882445 / 1000000000000) (-37647869501 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (556045278153443 / 4000000000000) 2 (IntervalRat.scale (257 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (67671846382 / 1000000000000) (67671846422 / 1000000000000), orderedInterval (98655989 / 1000000000000) (98656030 / 1000000000000)))) (orderedInterval (7173816967 / 1000000000000) (7173817171 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (235117533386841 / 4000000000000) 2 (IntervalRat.scale (257 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (13243682581 / 1000000000000) (13243682644 / 1000000000000), orderedInterval (-103338846998 / 1000000000000) (-103338846936 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (955739719882361 / 4000000000000) 2 (IntervalRat.scale (257 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (42248250067 / 1000000000000) (42248250068 / 1000000000000), orderedInterval (29567784979 / 1000000000000) (29567784980 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (638389840018999 / 4000000000000) 2 (IntervalRat.scale (257 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-10115136247 / 1000000000000) (-10115136246 / 1000000000000), orderedInterval (-62311006931 / 1000000000000) (-62311006930 / 1000000000000)))) (orderedInterval (8870118118 / 1000000000000) (8870118193 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate253_chunkChecks2 :
    compactCertificate253.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate253.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate253_chunkChecks2_0
    compactCertificate253_chunkChecks2_1 compactCertificate253_chunkChecks2_2

theorem compactCertificate253_chunkChecks3_0 :
    compactCertificate253.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (257 / 2) 3 (IntervalRat.scale (257 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-32448293167 / 1000000000000) (-32448293166 / 1000000000000), orderedInterval (-62334686200 / 1000000000000) (-62334686199 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (378610073610557 / 4000000000000) 3 (IntervalRat.scale (257 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (76100134541 / 1000000000000) (76100134542 / 1000000000000), orderedInterval (30168648840 / 1000000000000) (30168648841 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (122434718770781 / 800000000000) 3 (IntervalRat.scale (257 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (7084097557 / 1000000000000) (7084097581 / 1000000000000), orderedInterval (-64129078518 / 1000000000000) (-64129078494 / 1000000000000)))) (orderedInterval (30856446045 / 1000000000000) (30856446062 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (110477475212599 / 4000000000000) 3 (IntervalRat.scale (257 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-19063867110 / 1000000000000) (-19063867108 / 1000000000000), orderedInterval (-150286922549 / 1000000000000) (-150286922547 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (296758038363403 / 4000000000000) 3 (IntervalRat.scale (257 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-38194404204 / 1000000000000) (-38194401717 / 1000000000000), orderedInterval (84651181240 / 1000000000000) (84651183727 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (805755801816351 / 4000000000000) 3 (IntervalRat.scale (257 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (51580207560 / 1000000000000) (51580207561 / 1000000000000), orderedInterval (22228992247 / 1000000000000) (22228992248 / 1000000000000)))) (orderedInterval (5402896910 / 1000000000000) (5402896965 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (593516076727063 / 4000000000000) 3 (IntervalRat.scale (257 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-65375538322 / 1000000000000) (-65375538303 / 1000000000000), orderedInterval (-3843206858 / 1000000000000) (-3843206840 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1016999913629299 / 4000000000000) 3 (IntervalRat.scale (257 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-26828886602 / 1000000000000) (-26828886601 / 1000000000000), orderedInterval (-42186151399 / 1000000000000) (-42186151398 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (749117533386841 / 4000000000000) 3 (IntervalRat.scale (257 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-24381570755 / 1000000000000) (-24381569343 / 1000000000000), orderedInterval (53025947026 / 1000000000000) (53025948439 / 1000000000000)))) (orderedInterval (-14030167240 / 1000000000000) (-14030167092 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate253_chunkChecks3_1 :
    compactCertificate253.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1149338940434743 / 4000000000000) 3 (IntervalRat.scale (257 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-37070226623 / 1000000000000) (-37070134622 / 1000000000000), orderedInterval (29071424567 / 1000000000000) (29071516568 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (663571146650047 / 4000000000000) 3 (IntervalRat.scale (257 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-10664840722 / 1000000000000) (-10664840721 / 1000000000000), orderedInterval (-60990925628 / 1000000000000) (-60990925627 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1177518644291723 / 4000000000000) 3 (IntervalRat.scale (257 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-6722849794 / 1000000000000) (-6722849780 / 1000000000000), orderedInterval (46026491987 / 1000000000000) (46026492000 / 1000000000000)))) (orderedInterval (-10982411902 / 1000000000000) (-10982227981 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1100190661198487 / 4000000000000) 3 (IntervalRat.scale (257 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-28248241215 / 1000000000000) (-28248233860 / 1000000000000), orderedInterval (38995128391 / 1000000000000) (38995135746 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (785147969068871 / 4000000000000) 3 (IntervalRat.scale (257 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (42732081442 / 1000000000000) (42732164395 / 1000000000000), orderedInterval (-37755606727 / 1000000000000) (-37755523774 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (890274115090209 / 4000000000000) 3 (IntervalRat.scale (257 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-15819670204 / 1000000000000) (-15819670203 / 1000000000000), orderedInterval (-51053359149 / 1000000000000) (-51053359148 / 1000000000000)))) (orderedInterval (18379023048 / 1000000000000) (18379052525 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (742217741419921 / 4000000000000) 3 (IntervalRat.scale (257 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-48814194719 / 1000000000000) (-48814194718 / 1000000000000), orderedInterval (-32242455416 / 1000000000000) (-32242455415 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (655771883750341 / 4000000000000) 3 (IntervalRat.scale (257 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (60997379119 / 1000000000000) (60997379122 / 1000000000000), orderedInterval (12560788736 / 1000000000000) (12560788738 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (190068251847759 / 800000000000) 3 (IntervalRat.scale (257 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-19721081319 / 1000000000000) (-19721080676 / 1000000000000), orderedInterval (47901976249 / 1000000000000) (47901976892 / 1000000000000)))) (orderedInterval (-5204830780 / 1000000000000) (-5204830634 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate253_chunkChecks3_2 :
    compactCertificate253.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (525738787354973 / 4000000000000) 3 (IntervalRat.scale (257 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (18714447289 / 1000000000000) (18714447290 / 1000000000000), orderedInterval (66961783471 / 1000000000000) (66961783472 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (445674592438453 / 4000000000000) 3 (IntervalRat.scale (257 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-58947449799 / 1000000000000) (-58947376399 / 1000000000000), orderedInterval (47582063551 / 1000000000000) (47582136952 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (278882466613159 / 4000000000000) 3 (IntervalRat.scale (257 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (93983573360 / 1000000000000) (93983573362 / 1000000000000), orderedInterval (16585242915 / 1000000000000) (16585242917 / 1000000000000)))) (orderedInterval (13127069220 / 1000000000000) (13127071981 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (149983918065753 / 4000000000000) 3 (IntervalRat.scale (257 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (71288601363 / 1000000000000) (71288601364 / 1000000000000), orderedInterval (108122408446 / 1000000000000) (108122408447 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (407235513576259 / 4000000000000) 3 (IntervalRat.scale (257 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (69723358487 / 1000000000000) (69723371432 / 1000000000000), orderedInterval (-37647882445 / 1000000000000) (-37647869501 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (556045278153443 / 4000000000000) 3 (IntervalRat.scale (257 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (67671846382 / 1000000000000) (67671846422 / 1000000000000), orderedInterval (98655989 / 1000000000000) (98656030 / 1000000000000)))) (orderedInterval (-421424942 / 1000000000000) (-421424775 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (235117533386841 / 4000000000000) 3 (IntervalRat.scale (257 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (13243682581 / 1000000000000) (13243682644 / 1000000000000), orderedInterval (-103338846998 / 1000000000000) (-103338846936 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (955739719882361 / 4000000000000) 3 (IntervalRat.scale (257 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (42248250067 / 1000000000000) (42248250068 / 1000000000000), orderedInterval (29567784979 / 1000000000000) (29567784980 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (638389840018999 / 4000000000000) 3 (IntervalRat.scale (257 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-10115136247 / 1000000000000) (-10115136246 / 1000000000000), orderedInterval (-62311006931 / 1000000000000) (-62311006930 / 1000000000000)))) (orderedInterval (-6934482489 / 1000000000000) (-6934482374 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate253_chunkChecks3 :
    compactCertificate253.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate253.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate253_chunkChecks3_0
    compactCertificate253_chunkChecks3_1 compactCertificate253_chunkChecks3_2

theorem compactCertificate253_chunkChecks4_0 :
    compactCertificate253.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (257 / 2) 4 (IntervalRat.scale (257 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-32448293167 / 1000000000000) (-32448293166 / 1000000000000), orderedInterval (-62334686200 / 1000000000000) (-62334686199 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (378610073610557 / 4000000000000) 4 (IntervalRat.scale (257 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (76100134541 / 1000000000000) (76100134542 / 1000000000000), orderedInterval (30168648840 / 1000000000000) (30168648841 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (122434718770781 / 800000000000) 4 (IntervalRat.scale (257 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (7084097557 / 1000000000000) (7084097581 / 1000000000000), orderedInterval (-64129078518 / 1000000000000) (-64129078494 / 1000000000000)))) (orderedInterval (-12295697183 / 1000000000000) (-12295697163 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (110477475212599 / 4000000000000) 4 (IntervalRat.scale (257 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-19063867110 / 1000000000000) (-19063867108 / 1000000000000), orderedInterval (-150286922549 / 1000000000000) (-150286922547 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (296758038363403 / 4000000000000) 4 (IntervalRat.scale (257 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-38194404204 / 1000000000000) (-38194401717 / 1000000000000), orderedInterval (84651181240 / 1000000000000) (84651183727 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (805755801816351 / 4000000000000) 4 (IntervalRat.scale (257 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (51580207560 / 1000000000000) (51580207561 / 1000000000000), orderedInterval (22228992247 / 1000000000000) (22228992248 / 1000000000000)))) (orderedInterval (-22381751992 / 1000000000000) (-22381751924 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (593516076727063 / 4000000000000) 4 (IntervalRat.scale (257 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-65375538322 / 1000000000000) (-65375538303 / 1000000000000), orderedInterval (-3843206858 / 1000000000000) (-3843206840 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1016999913629299 / 4000000000000) 4 (IntervalRat.scale (257 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-26828886602 / 1000000000000) (-26828886601 / 1000000000000), orderedInterval (-42186151399 / 1000000000000) (-42186151398 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (749117533386841 / 4000000000000) 4 (IntervalRat.scale (257 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-24381570755 / 1000000000000) (-24381569343 / 1000000000000), orderedInterval (53025947026 / 1000000000000) (53025948439 / 1000000000000)))) (orderedInterval (10242151100 / 1000000000000) (10242151332 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate253_chunkChecks4_1 :
    compactCertificate253.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1149338940434743 / 4000000000000) 4 (IntervalRat.scale (257 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-37070226623 / 1000000000000) (-37070134622 / 1000000000000), orderedInterval (29071424567 / 1000000000000) (29071516568 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (663571146650047 / 4000000000000) 4 (IntervalRat.scale (257 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-10664840722 / 1000000000000) (-10664840721 / 1000000000000), orderedInterval (-60990925628 / 1000000000000) (-60990925627 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1177518644291723 / 4000000000000) 4 (IntervalRat.scale (257 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-6722849794 / 1000000000000) (-6722849780 / 1000000000000), orderedInterval (46026491987 / 1000000000000) (46026492000 / 1000000000000)))) (orderedInterval (136324171897 / 1000000000000) (136324584571 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1100190661198487 / 4000000000000) 4 (IntervalRat.scale (257 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-28248241215 / 1000000000000) (-28248233860 / 1000000000000), orderedInterval (38995128391 / 1000000000000) (38995135746 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (785147969068871 / 4000000000000) 4 (IntervalRat.scale (257 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (42732081442 / 1000000000000) (42732164395 / 1000000000000), orderedInterval (-37755606727 / 1000000000000) (-37755523774 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (890274115090209 / 4000000000000) 4 (IntervalRat.scale (257 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-15819670204 / 1000000000000) (-15819670203 / 1000000000000), orderedInterval (-51053359149 / 1000000000000) (-51053359148 / 1000000000000)))) (orderedInterval (33138409500 / 1000000000000) (33138455568 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (742217741419921 / 4000000000000) 4 (IntervalRat.scale (257 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-48814194719 / 1000000000000) (-48814194718 / 1000000000000), orderedInterval (-32242455416 / 1000000000000) (-32242455415 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (655771883750341 / 4000000000000) 4 (IntervalRat.scale (257 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (60997379119 / 1000000000000) (60997379122 / 1000000000000), orderedInterval (12560788736 / 1000000000000) (12560788738 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (190068251847759 / 800000000000) 4 (IntervalRat.scale (257 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-19721081319 / 1000000000000) (-19721080676 / 1000000000000), orderedInterval (47901976249 / 1000000000000) (47901976892 / 1000000000000)))) (orderedInterval (-17518441270 / 1000000000000) (-17518441010 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate253_chunkChecks4_2 :
    compactCertificate253.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (525738787354973 / 4000000000000) 4 (IntervalRat.scale (257 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (18714447289 / 1000000000000) (18714447290 / 1000000000000), orderedInterval (66961783471 / 1000000000000) (66961783472 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (445674592438453 / 4000000000000) 4 (IntervalRat.scale (257 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-58947449799 / 1000000000000) (-58947376399 / 1000000000000), orderedInterval (47582063551 / 1000000000000) (47582136952 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (278882466613159 / 4000000000000) 4 (IntervalRat.scale (257 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (93983573360 / 1000000000000) (93983573362 / 1000000000000), orderedInterval (16585242915 / 1000000000000) (16585242917 / 1000000000000)))) (orderedInterval (-1328501396 / 1000000000000) (-1328498979 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (149983918065753 / 4000000000000) 4 (IntervalRat.scale (257 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (71288601363 / 1000000000000) (71288601364 / 1000000000000), orderedInterval (108122408446 / 1000000000000) (108122408447 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (407235513576259 / 4000000000000) 4 (IntervalRat.scale (257 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (69723358487 / 1000000000000) (69723371432 / 1000000000000), orderedInterval (-37647882445 / 1000000000000) (-37647869501 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (556045278153443 / 4000000000000) 4 (IntervalRat.scale (257 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (67671846382 / 1000000000000) (67671846422 / 1000000000000), orderedInterval (98655989 / 1000000000000) (98656030 / 1000000000000)))) (orderedInterval (-7728885886 / 1000000000000) (-7728885748 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (235117533386841 / 4000000000000) 4 (IntervalRat.scale (257 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (13243682581 / 1000000000000) (13243682644 / 1000000000000), orderedInterval (-103338846998 / 1000000000000) (-103338846936 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (955739719882361 / 4000000000000) 4 (IntervalRat.scale (257 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (42248250067 / 1000000000000) (42248250068 / 1000000000000), orderedInterval (29567784979 / 1000000000000) (29567784980 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (638389840018999 / 4000000000000) 4 (IntervalRat.scale (257 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-10115136247 / 1000000000000) (-10115136246 / 1000000000000), orderedInterval (-62311006931 / 1000000000000) (-62311006930 / 1000000000000)))) (orderedInterval (-36482120278 / 1000000000000) (-36482120093 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate253_chunkChecks4 :
    compactCertificate253.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate253.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate253_chunkChecks4_0
    compactCertificate253_chunkChecks4_1 compactCertificate253_chunkChecks4_2

theorem compactCertificate253_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate253.chunkCheck r b = true :=
  compactCertificate253.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate253_chunkChecks0
    · exact compactCertificate253_chunkChecks1
    · exact compactCertificate253_chunkChecks2
    · exact compactCertificate253_chunkChecks3
    · exact compactCertificate253_chunkChecks4)

theorem compactCertificate253_coefficient0 :
    compactCertificate253.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate253, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate253_coefficient1 :
    compactCertificate253.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate253, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate253_coefficient2 :
    compactCertificate253.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate253, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate253_coefficient3 :
    compactCertificate253.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate253, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate253_coefficient4 :
    compactCertificate253.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate253, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate253_coefficients : ∀ r : Fin 5,
    compactCertificate253.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate253_coefficient0
  · exact compactCertificate253_coefficient1
  · exact compactCertificate253_coefficient2
  · exact compactCertificate253_coefficient3
  · exact compactCertificate253_coefficient4

theorem compactCertificate253_lower : (1 : ℚ) ≤ compactCertificate253.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate253, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate253_proves {t : ℝ} (ht : t ∈ compactCertificate253.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate253.proves compactCertificate253_states compactCertificate253_chunks
    compactCertificate253_coefficients compactCertificate253_lower ht

end Erdos232
