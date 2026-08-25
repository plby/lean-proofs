/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate229 : CompactCertificate where
  left := 106
  right := 107
  center := 213 / 2
  grid := fun i =>
    match i.val with
    | 0 => 34
    | 1 => 25
    | 2 => 40
    | 3 => 7
    | 4 => 20
    | 5 => 53
    | 6 => 39
    | 7 => 67
    | 8 => 49
    | 9 => 76
    | 10 => 44
    | 11 => 78
    | 12 => 73
    | 13 => 52
    | 14 => 59
    | 15 => 49
    | 16 => 43
    | 17 => 63
    | 18 => 35
    | 19 => 29
    | 20 => 18
    | 21 => 10
    | 22 => 27
    | 23 => 37
    | 24 => 16
    | 25 => 63
    | _ => 42
  point := fun i =>
    match i.val with
    | 0 => 213 / 2
    | 1 => 313789671902913 / 4000000000000
    | 2 => 101473132677729 / 800000000000
    | 3 => 91563043658691 / 4000000000000
    | 4 => 245951214674727 / 4000000000000
    | 5 => 667805392166859 / 4000000000000
    | 6 => 491902429349667 / 4000000000000
    | 7 => 842883196898991 / 4000000000000
    | 8 => 620863947904269 / 4000000000000
    | 9 => 952564958414787 / 4000000000000
    | 10 => 549963635161323 / 4000000000000
    | 11 => 975920121533607 / 4000000000000
    | 12 => 911831170565283 / 4000000000000
    | 13 => 650725748683539 / 4000000000000
    | 14 => 737853644024181 / 4000000000000
    | 15 => 615145443277989 / 4000000000000
    | 16 => 543499654625769 / 4000000000000
    | 17 => 157527383827131 / 800000000000
    | 18 => 435729033877857 / 4000000000000
    | 19 => 369372327585177 / 4000000000000
    | 20 => 231136052095731 / 4000000000000
    | 21 => 124305737540877 / 4000000000000
    | 22 => 337514258333631 / 4000000000000
    | 23 => 460846864773087 / 4000000000000
    | 24 => 194863947904269 / 4000000000000
    | 25 => 792111129707949 / 4000000000000
    | _ => 529093524996291 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (35019951529 / 1000000000000) (35019951530 / 1000000000000), orderedInterval (68765209017 / 1000000000000) (68765209018 / 1000000000000))
    | 1 => (orderedInterval (-57439301965 / 1000000000000) (-57439301964 / 1000000000000), orderedInterval (-69031315286 / 1000000000000) (-69031315285 / 1000000000000))
    | 2 => (orderedInterval (65489197772 / 1000000000000) (65489203115 / 1000000000000), orderedInterval (-27279593829 / 1000000000000) (-27279588487 / 1000000000000))
    | 3 => (orderedInterval (-165761894287 / 1000000000000) (-165761894191 / 1000000000000), orderedInterval (21722797121 / 1000000000000) (21722797217 / 1000000000000))
    | 4 => (orderedInterval (-54107639945 / 1000000000000) (-54107628961 / 1000000000000), orderedInterval (86614813499 / 1000000000000) (86614824483 / 1000000000000))
    | 5 => (orderedInterval (-58232321810 / 1000000000000) (-58232321809 / 1000000000000), orderedInterval (-20372834085 / 1000000000000) (-20372834084 / 1000000000000))
    | 6 => (orderedInterval (-67999043370 / 1000000000000) (-67999043369 / 1000000000000), orderedInterval (-23237220399 / 1000000000000) (-23237220398 / 1000000000000))
    | 7 => (orderedInterval (-46804289720 / 1000000000000) (-46804289719 / 1000000000000), orderedInterval (-28707472207 / 1000000000000) (-28707472206 / 1000000000000))
    | 8 => (orderedInterval (-56454492079 / 1000000000000) (-56454475249 / 1000000000000), orderedInterval (30420704142 / 1000000000000) (30420720973 / 1000000000000))
    | 9 => (orderedInterval (8496097366 / 1000000000000) (8496097367 / 1000000000000), orderedInterval (50983224959 / 1000000000000) (50983224960 / 1000000000000))
    | 10 => (orderedInterval (3082855035 / 1000000000000) (3082855038 / 1000000000000), orderedInterval (67965215955 / 1000000000000) (67965215958 / 1000000000000))
    | 11 => (orderedInterval (-14082783627 / 1000000000000) (-14082783483 / 1000000000000), orderedInterval (49130701785 / 1000000000000) (49130701929 / 1000000000000))
    | 12 => (orderedInterval (29560287350 / 1000000000000) (29560293980 / 1000000000000), orderedInterval (-43870098825 / 1000000000000) (-43870092195 / 1000000000000))
    | 13 => (orderedInterval (6447390139 / 1000000000000) (6447390140 / 1000000000000), orderedInterval (62203492166 / 1000000000000) (62203492167 / 1000000000000))
    | 14 => (orderedInterval (6205867411 / 1000000000000) (6205867429 / 1000000000000), orderedInterval (-58435120629 / 1000000000000) (-58435120611 / 1000000000000))
    | 15 => (orderedInterval (-38056408015 / 1000000000000) (-38056408014 / 1000000000000), orderedInterval (-51754529197 / 1000000000000) (-51754529196 / 1000000000000))
    | 16 => (orderedInterval (-68449290086 / 1000000000000) (-68449290043 / 1000000000000), orderedInterval (259508822 / 1000000000000) (259508865 / 1000000000000))
    | 17 => (orderedInterval (12760295935 / 1000000000000) (12760296031 / 1000000000000), orderedInterval (-55442204964 / 1000000000000) (-55442204868 / 1000000000000))
    | 18 => (orderedInterval (18114705908 / 1000000000000) (18114706119 / 1000000000000), orderedInterval (-74353546183 / 1000000000000) (-74353545973 / 1000000000000))
    | 19 => (orderedInterval (-74758895080 / 1000000000000) (-74758886875 / 1000000000000), orderedInterval (36531168820 / 1000000000000) (36531177025 / 1000000000000))
    | 20 => (orderedInterval (94612781050 / 1000000000000) (94612787804 / 1000000000000), orderedInterval (-46265218412 / 1000000000000) (-46265211658 / 1000000000000))
    | 21 => (orderedInterval (61203988720 / 1000000000000) (61203988721 / 1000000000000), orderedInterval (128403938785 / 1000000000000) (128403938786 / 1000000000000))
    | 22 => (orderedInterval (-28924109933 / 1000000000000) (-28924109932 / 1000000000000), orderedInterval (-81732844297 / 1000000000000) (-81732844296 / 1000000000000))
    | 23 => (orderedInterval (17878701757 / 1000000000000) (17878701969 / 1000000000000), orderedInterval (-72230547332 / 1000000000000) (-72230547119 / 1000000000000))
    | 24 => (orderedInterval (-79302514521 / 1000000000000) (-79302437678 / 1000000000000), orderedInterval (83149255434 / 1000000000000) (83149332277 / 1000000000000))
    | 25 => (orderedInterval (-44138122202 / 1000000000000) (-44138122201 / 1000000000000), orderedInterval (-35478221883 / 1000000000000) (-35478221882 / 1000000000000))
    | _ => (orderedInterval (62168055875 / 1000000000000) (62168055876 / 1000000000000), orderedInterval (30554957618 / 1000000000000) (30554957619 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (17188440759 / 1000000000000) (17188441082 / 1000000000000)
      | 1 => orderedInterval (3962549466 / 1000000000000) (3962549881 / 1000000000000)
      | 2 => orderedInterval (79237867 / 1000000000000) (79238280 / 1000000000000)
      | 3 => orderedInterval (-3283190421 / 1000000000000) (-3283190357 / 1000000000000)
      | 4 => orderedInterval (44623890 / 1000000000000) (44624023 / 1000000000000)
      | 5 => orderedInterval (3804376545 / 1000000000000) (3804376561 / 1000000000000)
      | 6 => orderedInterval (4415089824 / 1000000000000) (4415090569 / 1000000000000)
      | 7 => orderedInterval (-1844145045 / 1000000000000) (-1844145015 / 1000000000000)
      | _ => orderedInterval (-8549516418 / 1000000000000) (-8549515924 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (24875766679 / 1000000000000) (24875767062 / 1000000000000)
      | 1 => orderedInterval (4045567971 / 1000000000000) (4045568219 / 1000000000000)
      | 2 => orderedInterval (2823469709 / 1000000000000) (2823470314 / 1000000000000)
      | 3 => orderedInterval (2244334918 / 1000000000000) (2244335054 / 1000000000000)
      | 4 => orderedInterval (11192527237 / 1000000000000) (11192527515 / 1000000000000)
      | 5 => orderedInterval (-3506552159 / 1000000000000) (-3506552135 / 1000000000000)
      | 6 => orderedInterval (9550060774 / 1000000000000) (9550061356 / 1000000000000)
      | 7 => orderedInterval (6765743355 / 1000000000000) (6765743385 / 1000000000000)
      | _ => orderedInterval (-1521047319 / 1000000000000) (-1521047065 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-19275049145 / 1000000000000) (-19275048686 / 1000000000000)
      | 1 => orderedInterval (-9635594796 / 1000000000000) (-9635594639 / 1000000000000)
      | 2 => orderedInterval (-2780019286 / 1000000000000) (-2780018397 / 1000000000000)
      | 3 => orderedInterval (17653118086 / 1000000000000) (17653118383 / 1000000000000)
      | 4 => orderedInterval (1011475164 / 1000000000000) (1011475750 / 1000000000000)
      | 5 => orderedInterval (-6543573669 / 1000000000000) (-6543573633 / 1000000000000)
      | 6 => orderedInterval (-1147391156 / 1000000000000) (-1147390677 / 1000000000000)
      | 7 => orderedInterval (1224328751 / 1000000000000) (1224328783 / 1000000000000)
      | _ => orderedInterval (5685197788 / 1000000000000) (5685197950 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-24111468590 / 1000000000000) (-24111468043 / 1000000000000)
      | 1 => orderedInterval (-6094730944 / 1000000000000) (-6094730834 / 1000000000000)
      | 2 => orderedInterval (-9108298733 / 1000000000000) (-9108297431 / 1000000000000)
      | 3 => orderedInterval (6311785971 / 1000000000000) (6311786632 / 1000000000000)
      | 4 => orderedInterval (-30277033101 / 1000000000000) (-30277031863 / 1000000000000)
      | 5 => orderedInterval (10863611533 / 1000000000000) (10863611589 / 1000000000000)
      | 6 => orderedInterval (-11121803749 / 1000000000000) (-11121803347 / 1000000000000)
      | 7 => orderedInterval (-7882452269 / 1000000000000) (-7882452235 / 1000000000000)
      | _ => orderedInterval (-7684194502 / 1000000000000) (-7684194361 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (21906594928 / 1000000000000) (21906595583 / 1000000000000)
      | 1 => orderedInterval (24897455872 / 1000000000000) (24897455966 / 1000000000000)
      | 2 => orderedInterval (16140181758 / 1000000000000) (16140183680 / 1000000000000)
      | 3 => orderedInterval (-92364514534 / 1000000000000) (-92364513047 / 1000000000000)
      | 4 => orderedInterval (-7596182372 / 1000000000000) (-7596179736 / 1000000000000)
      | 5 => orderedInterval (12080981629 / 1000000000000) (12080981719 / 1000000000000)
      | 6 => orderedInterval (-302864605 / 1000000000000) (-302864256 / 1000000000000)
      | 7 => orderedInterval (-1478108335 / 1000000000000) (-1478108299 / 1000000000000)
      | _ => orderedInterval (15317203587 / 1000000000000) (15317203762 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (15817466467 / 1000000000000) (15817469100 / 1000000000000)
    | 1 => orderedInterval (56469871165 / 1000000000000) (56469873705 / 1000000000000)
    | 2 => orderedInterval (-13807508263 / 1000000000000) (-13807505166 / 1000000000000)
    | 3 => orderedInterval (-79104584384 / 1000000000000) (-79104579893 / 1000000000000)
    | _ => orderedInterval (-11399252072 / 1000000000000) (-11399244628 / 1000000000000)

theorem compactCertificate229_stateChecks0 :
    compactCertificate229.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (213 / 2)) (orderedInterval (35019951529 / 1000000000000) (35019951530 / 1000000000000), orderedInterval (68765209017 / 1000000000000) (68765209018 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (313789671902913 / 4000000000000)) (orderedInterval (-57439301965 / 1000000000000) (-57439301964 / 1000000000000), orderedInterval (-69031315286 / 1000000000000) (-69031315285 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (101473132677729 / 800000000000)) (orderedInterval (65489197772 / 1000000000000) (65489203115 / 1000000000000), orderedInterval (-27279593829 / 1000000000000) (-27279588487 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState016, besselGridState018, besselGridState020, besselGridState025, besselGridState027, besselGridState029, besselGridState034, besselGridState035, besselGridState037, besselGridState039, besselGridState040, besselGridState042, besselGridState043, besselGridState044, besselGridState049, besselGridState052, besselGridState053, besselGridState059, besselGridState063, besselGridState067, besselGridState073, besselGridState076, besselGridState078, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate229_stateChecks1 :
    compactCertificate229.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 7 12 (91563043658691 / 4000000000000)) (orderedInterval (-165761894287 / 1000000000000) (-165761894191 / 1000000000000), orderedInterval (21722797121 / 1000000000000) (21722797217 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 20 12 (245951214674727 / 4000000000000)) (orderedInterval (-54107639945 / 1000000000000) (-54107628961 / 1000000000000), orderedInterval (86614813499 / 1000000000000) (86614824483 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (667805392166859 / 4000000000000)) (orderedInterval (-58232321810 / 1000000000000) (-58232321809 / 1000000000000), orderedInterval (-20372834085 / 1000000000000) (-20372834084 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState016, besselGridState018, besselGridState020, besselGridState025, besselGridState027, besselGridState029, besselGridState034, besselGridState035, besselGridState037, besselGridState039, besselGridState040, besselGridState042, besselGridState043, besselGridState044, besselGridState049, besselGridState052, besselGridState053, besselGridState059, besselGridState063, besselGridState067, besselGridState073, besselGridState076, besselGridState078, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate229_stateChecks2 :
    compactCertificate229.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (491902429349667 / 4000000000000)) (orderedInterval (-67999043370 / 1000000000000) (-67999043369 / 1000000000000), orderedInterval (-23237220399 / 1000000000000) (-23237220398 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (842883196898991 / 4000000000000)) (orderedInterval (-46804289720 / 1000000000000) (-46804289719 / 1000000000000), orderedInterval (-28707472207 / 1000000000000) (-28707472206 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (620863947904269 / 4000000000000)) (orderedInterval (-56454492079 / 1000000000000) (-56454475249 / 1000000000000), orderedInterval (30420704142 / 1000000000000) (30420720973 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState016, besselGridState018, besselGridState020, besselGridState025, besselGridState027, besselGridState029, besselGridState034, besselGridState035, besselGridState037, besselGridState039, besselGridState040, besselGridState042, besselGridState043, besselGridState044, besselGridState049, besselGridState052, besselGridState053, besselGridState059, besselGridState063, besselGridState067, besselGridState073, besselGridState076, besselGridState078, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate229_stateChecks3 :
    compactCertificate229.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (952564958414787 / 4000000000000)) (orderedInterval (8496097366 / 1000000000000) (8496097367 / 1000000000000), orderedInterval (50983224959 / 1000000000000) (50983224960 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (549963635161323 / 4000000000000)) (orderedInterval (3082855035 / 1000000000000) (3082855038 / 1000000000000), orderedInterval (67965215955 / 1000000000000) (67965215958 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (975920121533607 / 4000000000000)) (orderedInterval (-14082783627 / 1000000000000) (-14082783483 / 1000000000000), orderedInterval (49130701785 / 1000000000000) (49130701929 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState016, besselGridState018, besselGridState020, besselGridState025, besselGridState027, besselGridState029, besselGridState034, besselGridState035, besselGridState037, besselGridState039, besselGridState040, besselGridState042, besselGridState043, besselGridState044, besselGridState049, besselGridState052, besselGridState053, besselGridState059, besselGridState063, besselGridState067, besselGridState073, besselGridState076, besselGridState078, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate229_stateChecks4 :
    compactCertificate229.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (911831170565283 / 4000000000000)) (orderedInterval (29560287350 / 1000000000000) (29560293980 / 1000000000000), orderedInterval (-43870098825 / 1000000000000) (-43870092195 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (650725748683539 / 4000000000000)) (orderedInterval (6447390139 / 1000000000000) (6447390140 / 1000000000000), orderedInterval (62203492166 / 1000000000000) (62203492167 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (737853644024181 / 4000000000000)) (orderedInterval (6205867411 / 1000000000000) (6205867429 / 1000000000000), orderedInterval (-58435120629 / 1000000000000) (-58435120611 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState016, besselGridState018, besselGridState020, besselGridState025, besselGridState027, besselGridState029, besselGridState034, besselGridState035, besselGridState037, besselGridState039, besselGridState040, besselGridState042, besselGridState043, besselGridState044, besselGridState049, besselGridState052, besselGridState053, besselGridState059, besselGridState063, besselGridState067, besselGridState073, besselGridState076, besselGridState078, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate229_stateChecks5 :
    compactCertificate229.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (615145443277989 / 4000000000000)) (orderedInterval (-38056408015 / 1000000000000) (-38056408014 / 1000000000000), orderedInterval (-51754529197 / 1000000000000) (-51754529196 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (543499654625769 / 4000000000000)) (orderedInterval (-68449290086 / 1000000000000) (-68449290043 / 1000000000000), orderedInterval (259508822 / 1000000000000) (259508865 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (157527383827131 / 800000000000)) (orderedInterval (12760295935 / 1000000000000) (12760296031 / 1000000000000), orderedInterval (-55442204964 / 1000000000000) (-55442204868 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState016, besselGridState018, besselGridState020, besselGridState025, besselGridState027, besselGridState029, besselGridState034, besselGridState035, besselGridState037, besselGridState039, besselGridState040, besselGridState042, besselGridState043, besselGridState044, besselGridState049, besselGridState052, besselGridState053, besselGridState059, besselGridState063, besselGridState067, besselGridState073, besselGridState076, besselGridState078, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate229_stateChecks6 :
    compactCertificate229.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (435729033877857 / 4000000000000)) (orderedInterval (18114705908 / 1000000000000) (18114706119 / 1000000000000), orderedInterval (-74353546183 / 1000000000000) (-74353545973 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (369372327585177 / 4000000000000)) (orderedInterval (-74758895080 / 1000000000000) (-74758886875 / 1000000000000), orderedInterval (36531168820 / 1000000000000) (36531177025 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 18 12 (231136052095731 / 4000000000000)) (orderedInterval (94612781050 / 1000000000000) (94612787804 / 1000000000000), orderedInterval (-46265218412 / 1000000000000) (-46265211658 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState016, besselGridState018, besselGridState020, besselGridState025, besselGridState027, besselGridState029, besselGridState034, besselGridState035, besselGridState037, besselGridState039, besselGridState040, besselGridState042, besselGridState043, besselGridState044, besselGridState049, besselGridState052, besselGridState053, besselGridState059, besselGridState063, besselGridState067, besselGridState073, besselGridState076, besselGridState078, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate229_stateChecks7 :
    compactCertificate229.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 10 12 (124305737540877 / 4000000000000)) (orderedInterval (61203988720 / 1000000000000) (61203988721 / 1000000000000), orderedInterval (128403938785 / 1000000000000) (128403938786 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (337514258333631 / 4000000000000)) (orderedInterval (-28924109933 / 1000000000000) (-28924109932 / 1000000000000), orderedInterval (-81732844297 / 1000000000000) (-81732844296 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (460846864773087 / 4000000000000)) (orderedInterval (17878701757 / 1000000000000) (17878701969 / 1000000000000), orderedInterval (-72230547332 / 1000000000000) (-72230547119 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState016, besselGridState018, besselGridState020, besselGridState025, besselGridState027, besselGridState029, besselGridState034, besselGridState035, besselGridState037, besselGridState039, besselGridState040, besselGridState042, besselGridState043, besselGridState044, besselGridState049, besselGridState052, besselGridState053, besselGridState059, besselGridState063, besselGridState067, besselGridState073, besselGridState076, besselGridState078, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate229_stateChecks8 :
    compactCertificate229.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 16 12 (194863947904269 / 4000000000000)) (orderedInterval (-79302514521 / 1000000000000) (-79302437678 / 1000000000000), orderedInterval (83149255434 / 1000000000000) (83149332277 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (792111129707949 / 4000000000000)) (orderedInterval (-44138122202 / 1000000000000) (-44138122201 / 1000000000000), orderedInterval (-35478221883 / 1000000000000) (-35478221882 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (529093524996291 / 4000000000000)) (orderedInterval (62168055875 / 1000000000000) (62168055876 / 1000000000000), orderedInterval (30554957618 / 1000000000000) (30554957619 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState016, besselGridState018, besselGridState020, besselGridState025, besselGridState027, besselGridState029, besselGridState034, besselGridState035, besselGridState037, besselGridState039, besselGridState040, besselGridState042, besselGridState043, besselGridState044, besselGridState049, besselGridState052, besselGridState053, besselGridState059, besselGridState063, besselGridState067, besselGridState073, besselGridState076, besselGridState078, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate229_states : ∀ j,
    BesselStateValid (compactCertificate229.point j) (compactCertificate229.state j) :=
  compactCertificate229.statesValid_of_checks3 compactCertificate229_stateChecks0
    compactCertificate229_stateChecks1 compactCertificate229_stateChecks2
    compactCertificate229_stateChecks3 compactCertificate229_stateChecks4
    compactCertificate229_stateChecks5 compactCertificate229_stateChecks6
    compactCertificate229_stateChecks7 compactCertificate229_stateChecks8

theorem compactCertificate229_chunkChecks0_0 :
    compactCertificate229.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (213 / 2) 0 (IntervalRat.scale (213 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (35019951529 / 1000000000000) (35019951530 / 1000000000000), orderedInterval (68765209017 / 1000000000000) (68765209018 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (313789671902913 / 4000000000000) 0 (IntervalRat.scale (213 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-57439301965 / 1000000000000) (-57439301964 / 1000000000000), orderedInterval (-69031315286 / 1000000000000) (-69031315285 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (101473132677729 / 800000000000) 0 (IntervalRat.scale (213 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (65489197772 / 1000000000000) (65489203115 / 1000000000000), orderedInterval (-27279593829 / 1000000000000) (-27279588487 / 1000000000000)))) (orderedInterval (17188440759 / 1000000000000) (17188441082 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (91563043658691 / 4000000000000) 0 (IntervalRat.scale (213 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-165761894287 / 1000000000000) (-165761894191 / 1000000000000), orderedInterval (21722797121 / 1000000000000) (21722797217 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (245951214674727 / 4000000000000) 0 (IntervalRat.scale (213 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-54107639945 / 1000000000000) (-54107628961 / 1000000000000), orderedInterval (86614813499 / 1000000000000) (86614824483 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (667805392166859 / 4000000000000) 0 (IntervalRat.scale (213 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-58232321810 / 1000000000000) (-58232321809 / 1000000000000), orderedInterval (-20372834085 / 1000000000000) (-20372834084 / 1000000000000)))) (orderedInterval (3962549466 / 1000000000000) (3962549881 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (491902429349667 / 4000000000000) 0 (IntervalRat.scale (213 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-67999043370 / 1000000000000) (-67999043369 / 1000000000000), orderedInterval (-23237220399 / 1000000000000) (-23237220398 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (842883196898991 / 4000000000000) 0 (IntervalRat.scale (213 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-46804289720 / 1000000000000) (-46804289719 / 1000000000000), orderedInterval (-28707472207 / 1000000000000) (-28707472206 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (620863947904269 / 4000000000000) 0 (IntervalRat.scale (213 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-56454492079 / 1000000000000) (-56454475249 / 1000000000000), orderedInterval (30420704142 / 1000000000000) (30420720973 / 1000000000000)))) (orderedInterval (79237867 / 1000000000000) (79238280 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate229_chunkChecks0_1 :
    compactCertificate229.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (952564958414787 / 4000000000000) 0 (IntervalRat.scale (213 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (8496097366 / 1000000000000) (8496097367 / 1000000000000), orderedInterval (50983224959 / 1000000000000) (50983224960 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (549963635161323 / 4000000000000) 0 (IntervalRat.scale (213 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (3082855035 / 1000000000000) (3082855038 / 1000000000000), orderedInterval (67965215955 / 1000000000000) (67965215958 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (975920121533607 / 4000000000000) 0 (IntervalRat.scale (213 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-14082783627 / 1000000000000) (-14082783483 / 1000000000000), orderedInterval (49130701785 / 1000000000000) (49130701929 / 1000000000000)))) (orderedInterval (-3283190421 / 1000000000000) (-3283190357 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (911831170565283 / 4000000000000) 0 (IntervalRat.scale (213 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (29560287350 / 1000000000000) (29560293980 / 1000000000000), orderedInterval (-43870098825 / 1000000000000) (-43870092195 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (650725748683539 / 4000000000000) 0 (IntervalRat.scale (213 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (6447390139 / 1000000000000) (6447390140 / 1000000000000), orderedInterval (62203492166 / 1000000000000) (62203492167 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (737853644024181 / 4000000000000) 0 (IntervalRat.scale (213 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (6205867411 / 1000000000000) (6205867429 / 1000000000000), orderedInterval (-58435120629 / 1000000000000) (-58435120611 / 1000000000000)))) (orderedInterval (44623890 / 1000000000000) (44624023 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (615145443277989 / 4000000000000) 0 (IntervalRat.scale (213 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-38056408015 / 1000000000000) (-38056408014 / 1000000000000), orderedInterval (-51754529197 / 1000000000000) (-51754529196 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (543499654625769 / 4000000000000) 0 (IntervalRat.scale (213 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-68449290086 / 1000000000000) (-68449290043 / 1000000000000), orderedInterval (259508822 / 1000000000000) (259508865 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (157527383827131 / 800000000000) 0 (IntervalRat.scale (213 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (12760295935 / 1000000000000) (12760296031 / 1000000000000), orderedInterval (-55442204964 / 1000000000000) (-55442204868 / 1000000000000)))) (orderedInterval (3804376545 / 1000000000000) (3804376561 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate229_chunkChecks0_2 :
    compactCertificate229.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (435729033877857 / 4000000000000) 0 (IntervalRat.scale (213 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (18114705908 / 1000000000000) (18114706119 / 1000000000000), orderedInterval (-74353546183 / 1000000000000) (-74353545973 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (369372327585177 / 4000000000000) 0 (IntervalRat.scale (213 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-74758895080 / 1000000000000) (-74758886875 / 1000000000000), orderedInterval (36531168820 / 1000000000000) (36531177025 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (231136052095731 / 4000000000000) 0 (IntervalRat.scale (213 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (94612781050 / 1000000000000) (94612787804 / 1000000000000), orderedInterval (-46265218412 / 1000000000000) (-46265211658 / 1000000000000)))) (orderedInterval (4415089824 / 1000000000000) (4415090569 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (124305737540877 / 4000000000000) 0 (IntervalRat.scale (213 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (61203988720 / 1000000000000) (61203988721 / 1000000000000), orderedInterval (128403938785 / 1000000000000) (128403938786 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (337514258333631 / 4000000000000) 0 (IntervalRat.scale (213 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-28924109933 / 1000000000000) (-28924109932 / 1000000000000), orderedInterval (-81732844297 / 1000000000000) (-81732844296 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (460846864773087 / 4000000000000) 0 (IntervalRat.scale (213 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (17878701757 / 1000000000000) (17878701969 / 1000000000000), orderedInterval (-72230547332 / 1000000000000) (-72230547119 / 1000000000000)))) (orderedInterval (-1844145045 / 1000000000000) (-1844145015 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (194863947904269 / 4000000000000) 0 (IntervalRat.scale (213 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-79302514521 / 1000000000000) (-79302437678 / 1000000000000), orderedInterval (83149255434 / 1000000000000) (83149332277 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (792111129707949 / 4000000000000) 0 (IntervalRat.scale (213 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-44138122202 / 1000000000000) (-44138122201 / 1000000000000), orderedInterval (-35478221883 / 1000000000000) (-35478221882 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (529093524996291 / 4000000000000) 0 (IntervalRat.scale (213 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (62168055875 / 1000000000000) (62168055876 / 1000000000000), orderedInterval (30554957618 / 1000000000000) (30554957619 / 1000000000000)))) (orderedInterval (-8549516418 / 1000000000000) (-8549515924 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate229_chunkChecks0 :
    compactCertificate229.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate229.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate229_chunkChecks0_0
    compactCertificate229_chunkChecks0_1 compactCertificate229_chunkChecks0_2

theorem compactCertificate229_chunkChecks1_0 :
    compactCertificate229.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (213 / 2) 1 (IntervalRat.scale (213 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (35019951529 / 1000000000000) (35019951530 / 1000000000000), orderedInterval (68765209017 / 1000000000000) (68765209018 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (313789671902913 / 4000000000000) 1 (IntervalRat.scale (213 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-57439301965 / 1000000000000) (-57439301964 / 1000000000000), orderedInterval (-69031315286 / 1000000000000) (-69031315285 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (101473132677729 / 800000000000) 1 (IntervalRat.scale (213 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (65489197772 / 1000000000000) (65489203115 / 1000000000000), orderedInterval (-27279593829 / 1000000000000) (-27279588487 / 1000000000000)))) (orderedInterval (24875766679 / 1000000000000) (24875767062 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (91563043658691 / 4000000000000) 1 (IntervalRat.scale (213 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-165761894287 / 1000000000000) (-165761894191 / 1000000000000), orderedInterval (21722797121 / 1000000000000) (21722797217 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (245951214674727 / 4000000000000) 1 (IntervalRat.scale (213 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-54107639945 / 1000000000000) (-54107628961 / 1000000000000), orderedInterval (86614813499 / 1000000000000) (86614824483 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (667805392166859 / 4000000000000) 1 (IntervalRat.scale (213 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-58232321810 / 1000000000000) (-58232321809 / 1000000000000), orderedInterval (-20372834085 / 1000000000000) (-20372834084 / 1000000000000)))) (orderedInterval (4045567971 / 1000000000000) (4045568219 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (491902429349667 / 4000000000000) 1 (IntervalRat.scale (213 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-67999043370 / 1000000000000) (-67999043369 / 1000000000000), orderedInterval (-23237220399 / 1000000000000) (-23237220398 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (842883196898991 / 4000000000000) 1 (IntervalRat.scale (213 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-46804289720 / 1000000000000) (-46804289719 / 1000000000000), orderedInterval (-28707472207 / 1000000000000) (-28707472206 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (620863947904269 / 4000000000000) 1 (IntervalRat.scale (213 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-56454492079 / 1000000000000) (-56454475249 / 1000000000000), orderedInterval (30420704142 / 1000000000000) (30420720973 / 1000000000000)))) (orderedInterval (2823469709 / 1000000000000) (2823470314 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate229_chunkChecks1_1 :
    compactCertificate229.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (952564958414787 / 4000000000000) 1 (IntervalRat.scale (213 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (8496097366 / 1000000000000) (8496097367 / 1000000000000), orderedInterval (50983224959 / 1000000000000) (50983224960 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (549963635161323 / 4000000000000) 1 (IntervalRat.scale (213 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (3082855035 / 1000000000000) (3082855038 / 1000000000000), orderedInterval (67965215955 / 1000000000000) (67965215958 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (975920121533607 / 4000000000000) 1 (IntervalRat.scale (213 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-14082783627 / 1000000000000) (-14082783483 / 1000000000000), orderedInterval (49130701785 / 1000000000000) (49130701929 / 1000000000000)))) (orderedInterval (2244334918 / 1000000000000) (2244335054 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (911831170565283 / 4000000000000) 1 (IntervalRat.scale (213 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (29560287350 / 1000000000000) (29560293980 / 1000000000000), orderedInterval (-43870098825 / 1000000000000) (-43870092195 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (650725748683539 / 4000000000000) 1 (IntervalRat.scale (213 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (6447390139 / 1000000000000) (6447390140 / 1000000000000), orderedInterval (62203492166 / 1000000000000) (62203492167 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (737853644024181 / 4000000000000) 1 (IntervalRat.scale (213 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (6205867411 / 1000000000000) (6205867429 / 1000000000000), orderedInterval (-58435120629 / 1000000000000) (-58435120611 / 1000000000000)))) (orderedInterval (11192527237 / 1000000000000) (11192527515 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (615145443277989 / 4000000000000) 1 (IntervalRat.scale (213 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-38056408015 / 1000000000000) (-38056408014 / 1000000000000), orderedInterval (-51754529197 / 1000000000000) (-51754529196 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (543499654625769 / 4000000000000) 1 (IntervalRat.scale (213 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-68449290086 / 1000000000000) (-68449290043 / 1000000000000), orderedInterval (259508822 / 1000000000000) (259508865 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (157527383827131 / 800000000000) 1 (IntervalRat.scale (213 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (12760295935 / 1000000000000) (12760296031 / 1000000000000), orderedInterval (-55442204964 / 1000000000000) (-55442204868 / 1000000000000)))) (orderedInterval (-3506552159 / 1000000000000) (-3506552135 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate229_chunkChecks1_2 :
    compactCertificate229.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (435729033877857 / 4000000000000) 1 (IntervalRat.scale (213 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (18114705908 / 1000000000000) (18114706119 / 1000000000000), orderedInterval (-74353546183 / 1000000000000) (-74353545973 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (369372327585177 / 4000000000000) 1 (IntervalRat.scale (213 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-74758895080 / 1000000000000) (-74758886875 / 1000000000000), orderedInterval (36531168820 / 1000000000000) (36531177025 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (231136052095731 / 4000000000000) 1 (IntervalRat.scale (213 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (94612781050 / 1000000000000) (94612787804 / 1000000000000), orderedInterval (-46265218412 / 1000000000000) (-46265211658 / 1000000000000)))) (orderedInterval (9550060774 / 1000000000000) (9550061356 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (124305737540877 / 4000000000000) 1 (IntervalRat.scale (213 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (61203988720 / 1000000000000) (61203988721 / 1000000000000), orderedInterval (128403938785 / 1000000000000) (128403938786 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (337514258333631 / 4000000000000) 1 (IntervalRat.scale (213 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-28924109933 / 1000000000000) (-28924109932 / 1000000000000), orderedInterval (-81732844297 / 1000000000000) (-81732844296 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (460846864773087 / 4000000000000) 1 (IntervalRat.scale (213 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (17878701757 / 1000000000000) (17878701969 / 1000000000000), orderedInterval (-72230547332 / 1000000000000) (-72230547119 / 1000000000000)))) (orderedInterval (6765743355 / 1000000000000) (6765743385 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (194863947904269 / 4000000000000) 1 (IntervalRat.scale (213 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-79302514521 / 1000000000000) (-79302437678 / 1000000000000), orderedInterval (83149255434 / 1000000000000) (83149332277 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (792111129707949 / 4000000000000) 1 (IntervalRat.scale (213 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-44138122202 / 1000000000000) (-44138122201 / 1000000000000), orderedInterval (-35478221883 / 1000000000000) (-35478221882 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (529093524996291 / 4000000000000) 1 (IntervalRat.scale (213 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (62168055875 / 1000000000000) (62168055876 / 1000000000000), orderedInterval (30554957618 / 1000000000000) (30554957619 / 1000000000000)))) (orderedInterval (-1521047319 / 1000000000000) (-1521047065 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate229_chunkChecks1 :
    compactCertificate229.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate229.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate229_chunkChecks1_0
    compactCertificate229_chunkChecks1_1 compactCertificate229_chunkChecks1_2

theorem compactCertificate229_chunkChecks2_0 :
    compactCertificate229.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (213 / 2) 2 (IntervalRat.scale (213 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (35019951529 / 1000000000000) (35019951530 / 1000000000000), orderedInterval (68765209017 / 1000000000000) (68765209018 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (313789671902913 / 4000000000000) 2 (IntervalRat.scale (213 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-57439301965 / 1000000000000) (-57439301964 / 1000000000000), orderedInterval (-69031315286 / 1000000000000) (-69031315285 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (101473132677729 / 800000000000) 2 (IntervalRat.scale (213 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (65489197772 / 1000000000000) (65489203115 / 1000000000000), orderedInterval (-27279593829 / 1000000000000) (-27279588487 / 1000000000000)))) (orderedInterval (-19275049145 / 1000000000000) (-19275048686 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (91563043658691 / 4000000000000) 2 (IntervalRat.scale (213 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-165761894287 / 1000000000000) (-165761894191 / 1000000000000), orderedInterval (21722797121 / 1000000000000) (21722797217 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (245951214674727 / 4000000000000) 2 (IntervalRat.scale (213 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-54107639945 / 1000000000000) (-54107628961 / 1000000000000), orderedInterval (86614813499 / 1000000000000) (86614824483 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (667805392166859 / 4000000000000) 2 (IntervalRat.scale (213 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-58232321810 / 1000000000000) (-58232321809 / 1000000000000), orderedInterval (-20372834085 / 1000000000000) (-20372834084 / 1000000000000)))) (orderedInterval (-9635594796 / 1000000000000) (-9635594639 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (491902429349667 / 4000000000000) 2 (IntervalRat.scale (213 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-67999043370 / 1000000000000) (-67999043369 / 1000000000000), orderedInterval (-23237220399 / 1000000000000) (-23237220398 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (842883196898991 / 4000000000000) 2 (IntervalRat.scale (213 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-46804289720 / 1000000000000) (-46804289719 / 1000000000000), orderedInterval (-28707472207 / 1000000000000) (-28707472206 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (620863947904269 / 4000000000000) 2 (IntervalRat.scale (213 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-56454492079 / 1000000000000) (-56454475249 / 1000000000000), orderedInterval (30420704142 / 1000000000000) (30420720973 / 1000000000000)))) (orderedInterval (-2780019286 / 1000000000000) (-2780018397 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate229_chunkChecks2_1 :
    compactCertificate229.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (952564958414787 / 4000000000000) 2 (IntervalRat.scale (213 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (8496097366 / 1000000000000) (8496097367 / 1000000000000), orderedInterval (50983224959 / 1000000000000) (50983224960 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (549963635161323 / 4000000000000) 2 (IntervalRat.scale (213 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (3082855035 / 1000000000000) (3082855038 / 1000000000000), orderedInterval (67965215955 / 1000000000000) (67965215958 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (975920121533607 / 4000000000000) 2 (IntervalRat.scale (213 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-14082783627 / 1000000000000) (-14082783483 / 1000000000000), orderedInterval (49130701785 / 1000000000000) (49130701929 / 1000000000000)))) (orderedInterval (17653118086 / 1000000000000) (17653118383 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (911831170565283 / 4000000000000) 2 (IntervalRat.scale (213 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (29560287350 / 1000000000000) (29560293980 / 1000000000000), orderedInterval (-43870098825 / 1000000000000) (-43870092195 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (650725748683539 / 4000000000000) 2 (IntervalRat.scale (213 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (6447390139 / 1000000000000) (6447390140 / 1000000000000), orderedInterval (62203492166 / 1000000000000) (62203492167 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (737853644024181 / 4000000000000) 2 (IntervalRat.scale (213 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (6205867411 / 1000000000000) (6205867429 / 1000000000000), orderedInterval (-58435120629 / 1000000000000) (-58435120611 / 1000000000000)))) (orderedInterval (1011475164 / 1000000000000) (1011475750 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (615145443277989 / 4000000000000) 2 (IntervalRat.scale (213 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-38056408015 / 1000000000000) (-38056408014 / 1000000000000), orderedInterval (-51754529197 / 1000000000000) (-51754529196 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (543499654625769 / 4000000000000) 2 (IntervalRat.scale (213 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-68449290086 / 1000000000000) (-68449290043 / 1000000000000), orderedInterval (259508822 / 1000000000000) (259508865 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (157527383827131 / 800000000000) 2 (IntervalRat.scale (213 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (12760295935 / 1000000000000) (12760296031 / 1000000000000), orderedInterval (-55442204964 / 1000000000000) (-55442204868 / 1000000000000)))) (orderedInterval (-6543573669 / 1000000000000) (-6543573633 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate229_chunkChecks2_2 :
    compactCertificate229.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (435729033877857 / 4000000000000) 2 (IntervalRat.scale (213 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (18114705908 / 1000000000000) (18114706119 / 1000000000000), orderedInterval (-74353546183 / 1000000000000) (-74353545973 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (369372327585177 / 4000000000000) 2 (IntervalRat.scale (213 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-74758895080 / 1000000000000) (-74758886875 / 1000000000000), orderedInterval (36531168820 / 1000000000000) (36531177025 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (231136052095731 / 4000000000000) 2 (IntervalRat.scale (213 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (94612781050 / 1000000000000) (94612787804 / 1000000000000), orderedInterval (-46265218412 / 1000000000000) (-46265211658 / 1000000000000)))) (orderedInterval (-1147391156 / 1000000000000) (-1147390677 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (124305737540877 / 4000000000000) 2 (IntervalRat.scale (213 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (61203988720 / 1000000000000) (61203988721 / 1000000000000), orderedInterval (128403938785 / 1000000000000) (128403938786 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (337514258333631 / 4000000000000) 2 (IntervalRat.scale (213 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-28924109933 / 1000000000000) (-28924109932 / 1000000000000), orderedInterval (-81732844297 / 1000000000000) (-81732844296 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (460846864773087 / 4000000000000) 2 (IntervalRat.scale (213 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (17878701757 / 1000000000000) (17878701969 / 1000000000000), orderedInterval (-72230547332 / 1000000000000) (-72230547119 / 1000000000000)))) (orderedInterval (1224328751 / 1000000000000) (1224328783 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (194863947904269 / 4000000000000) 2 (IntervalRat.scale (213 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-79302514521 / 1000000000000) (-79302437678 / 1000000000000), orderedInterval (83149255434 / 1000000000000) (83149332277 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (792111129707949 / 4000000000000) 2 (IntervalRat.scale (213 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-44138122202 / 1000000000000) (-44138122201 / 1000000000000), orderedInterval (-35478221883 / 1000000000000) (-35478221882 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (529093524996291 / 4000000000000) 2 (IntervalRat.scale (213 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (62168055875 / 1000000000000) (62168055876 / 1000000000000), orderedInterval (30554957618 / 1000000000000) (30554957619 / 1000000000000)))) (orderedInterval (5685197788 / 1000000000000) (5685197950 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate229_chunkChecks2 :
    compactCertificate229.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate229.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate229_chunkChecks2_0
    compactCertificate229_chunkChecks2_1 compactCertificate229_chunkChecks2_2

theorem compactCertificate229_chunkChecks3_0 :
    compactCertificate229.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (213 / 2) 3 (IntervalRat.scale (213 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (35019951529 / 1000000000000) (35019951530 / 1000000000000), orderedInterval (68765209017 / 1000000000000) (68765209018 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (313789671902913 / 4000000000000) 3 (IntervalRat.scale (213 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-57439301965 / 1000000000000) (-57439301964 / 1000000000000), orderedInterval (-69031315286 / 1000000000000) (-69031315285 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (101473132677729 / 800000000000) 3 (IntervalRat.scale (213 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (65489197772 / 1000000000000) (65489203115 / 1000000000000), orderedInterval (-27279593829 / 1000000000000) (-27279588487 / 1000000000000)))) (orderedInterval (-24111468590 / 1000000000000) (-24111468043 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (91563043658691 / 4000000000000) 3 (IntervalRat.scale (213 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-165761894287 / 1000000000000) (-165761894191 / 1000000000000), orderedInterval (21722797121 / 1000000000000) (21722797217 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (245951214674727 / 4000000000000) 3 (IntervalRat.scale (213 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-54107639945 / 1000000000000) (-54107628961 / 1000000000000), orderedInterval (86614813499 / 1000000000000) (86614824483 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (667805392166859 / 4000000000000) 3 (IntervalRat.scale (213 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-58232321810 / 1000000000000) (-58232321809 / 1000000000000), orderedInterval (-20372834085 / 1000000000000) (-20372834084 / 1000000000000)))) (orderedInterval (-6094730944 / 1000000000000) (-6094730834 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (491902429349667 / 4000000000000) 3 (IntervalRat.scale (213 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-67999043370 / 1000000000000) (-67999043369 / 1000000000000), orderedInterval (-23237220399 / 1000000000000) (-23237220398 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (842883196898991 / 4000000000000) 3 (IntervalRat.scale (213 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-46804289720 / 1000000000000) (-46804289719 / 1000000000000), orderedInterval (-28707472207 / 1000000000000) (-28707472206 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (620863947904269 / 4000000000000) 3 (IntervalRat.scale (213 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-56454492079 / 1000000000000) (-56454475249 / 1000000000000), orderedInterval (30420704142 / 1000000000000) (30420720973 / 1000000000000)))) (orderedInterval (-9108298733 / 1000000000000) (-9108297431 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate229_chunkChecks3_1 :
    compactCertificate229.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (952564958414787 / 4000000000000) 3 (IntervalRat.scale (213 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (8496097366 / 1000000000000) (8496097367 / 1000000000000), orderedInterval (50983224959 / 1000000000000) (50983224960 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (549963635161323 / 4000000000000) 3 (IntervalRat.scale (213 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (3082855035 / 1000000000000) (3082855038 / 1000000000000), orderedInterval (67965215955 / 1000000000000) (67965215958 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (975920121533607 / 4000000000000) 3 (IntervalRat.scale (213 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-14082783627 / 1000000000000) (-14082783483 / 1000000000000), orderedInterval (49130701785 / 1000000000000) (49130701929 / 1000000000000)))) (orderedInterval (6311785971 / 1000000000000) (6311786632 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (911831170565283 / 4000000000000) 3 (IntervalRat.scale (213 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (29560287350 / 1000000000000) (29560293980 / 1000000000000), orderedInterval (-43870098825 / 1000000000000) (-43870092195 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (650725748683539 / 4000000000000) 3 (IntervalRat.scale (213 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (6447390139 / 1000000000000) (6447390140 / 1000000000000), orderedInterval (62203492166 / 1000000000000) (62203492167 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (737853644024181 / 4000000000000) 3 (IntervalRat.scale (213 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (6205867411 / 1000000000000) (6205867429 / 1000000000000), orderedInterval (-58435120629 / 1000000000000) (-58435120611 / 1000000000000)))) (orderedInterval (-30277033101 / 1000000000000) (-30277031863 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (615145443277989 / 4000000000000) 3 (IntervalRat.scale (213 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-38056408015 / 1000000000000) (-38056408014 / 1000000000000), orderedInterval (-51754529197 / 1000000000000) (-51754529196 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (543499654625769 / 4000000000000) 3 (IntervalRat.scale (213 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-68449290086 / 1000000000000) (-68449290043 / 1000000000000), orderedInterval (259508822 / 1000000000000) (259508865 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (157527383827131 / 800000000000) 3 (IntervalRat.scale (213 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (12760295935 / 1000000000000) (12760296031 / 1000000000000), orderedInterval (-55442204964 / 1000000000000) (-55442204868 / 1000000000000)))) (orderedInterval (10863611533 / 1000000000000) (10863611589 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate229_chunkChecks3_2 :
    compactCertificate229.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (435729033877857 / 4000000000000) 3 (IntervalRat.scale (213 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (18114705908 / 1000000000000) (18114706119 / 1000000000000), orderedInterval (-74353546183 / 1000000000000) (-74353545973 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (369372327585177 / 4000000000000) 3 (IntervalRat.scale (213 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-74758895080 / 1000000000000) (-74758886875 / 1000000000000), orderedInterval (36531168820 / 1000000000000) (36531177025 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (231136052095731 / 4000000000000) 3 (IntervalRat.scale (213 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (94612781050 / 1000000000000) (94612787804 / 1000000000000), orderedInterval (-46265218412 / 1000000000000) (-46265211658 / 1000000000000)))) (orderedInterval (-11121803749 / 1000000000000) (-11121803347 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (124305737540877 / 4000000000000) 3 (IntervalRat.scale (213 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (61203988720 / 1000000000000) (61203988721 / 1000000000000), orderedInterval (128403938785 / 1000000000000) (128403938786 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (337514258333631 / 4000000000000) 3 (IntervalRat.scale (213 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-28924109933 / 1000000000000) (-28924109932 / 1000000000000), orderedInterval (-81732844297 / 1000000000000) (-81732844296 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (460846864773087 / 4000000000000) 3 (IntervalRat.scale (213 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (17878701757 / 1000000000000) (17878701969 / 1000000000000), orderedInterval (-72230547332 / 1000000000000) (-72230547119 / 1000000000000)))) (orderedInterval (-7882452269 / 1000000000000) (-7882452235 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (194863947904269 / 4000000000000) 3 (IntervalRat.scale (213 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-79302514521 / 1000000000000) (-79302437678 / 1000000000000), orderedInterval (83149255434 / 1000000000000) (83149332277 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (792111129707949 / 4000000000000) 3 (IntervalRat.scale (213 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-44138122202 / 1000000000000) (-44138122201 / 1000000000000), orderedInterval (-35478221883 / 1000000000000) (-35478221882 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (529093524996291 / 4000000000000) 3 (IntervalRat.scale (213 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (62168055875 / 1000000000000) (62168055876 / 1000000000000), orderedInterval (30554957618 / 1000000000000) (30554957619 / 1000000000000)))) (orderedInterval (-7684194502 / 1000000000000) (-7684194361 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate229_chunkChecks3 :
    compactCertificate229.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate229.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate229_chunkChecks3_0
    compactCertificate229_chunkChecks3_1 compactCertificate229_chunkChecks3_2

theorem compactCertificate229_chunkChecks4_0 :
    compactCertificate229.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (213 / 2) 4 (IntervalRat.scale (213 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (35019951529 / 1000000000000) (35019951530 / 1000000000000), orderedInterval (68765209017 / 1000000000000) (68765209018 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (313789671902913 / 4000000000000) 4 (IntervalRat.scale (213 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-57439301965 / 1000000000000) (-57439301964 / 1000000000000), orderedInterval (-69031315286 / 1000000000000) (-69031315285 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (101473132677729 / 800000000000) 4 (IntervalRat.scale (213 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (65489197772 / 1000000000000) (65489203115 / 1000000000000), orderedInterval (-27279593829 / 1000000000000) (-27279588487 / 1000000000000)))) (orderedInterval (21906594928 / 1000000000000) (21906595583 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (91563043658691 / 4000000000000) 4 (IntervalRat.scale (213 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-165761894287 / 1000000000000) (-165761894191 / 1000000000000), orderedInterval (21722797121 / 1000000000000) (21722797217 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (245951214674727 / 4000000000000) 4 (IntervalRat.scale (213 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-54107639945 / 1000000000000) (-54107628961 / 1000000000000), orderedInterval (86614813499 / 1000000000000) (86614824483 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (667805392166859 / 4000000000000) 4 (IntervalRat.scale (213 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-58232321810 / 1000000000000) (-58232321809 / 1000000000000), orderedInterval (-20372834085 / 1000000000000) (-20372834084 / 1000000000000)))) (orderedInterval (24897455872 / 1000000000000) (24897455966 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (491902429349667 / 4000000000000) 4 (IntervalRat.scale (213 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-67999043370 / 1000000000000) (-67999043369 / 1000000000000), orderedInterval (-23237220399 / 1000000000000) (-23237220398 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (842883196898991 / 4000000000000) 4 (IntervalRat.scale (213 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-46804289720 / 1000000000000) (-46804289719 / 1000000000000), orderedInterval (-28707472207 / 1000000000000) (-28707472206 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (620863947904269 / 4000000000000) 4 (IntervalRat.scale (213 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-56454492079 / 1000000000000) (-56454475249 / 1000000000000), orderedInterval (30420704142 / 1000000000000) (30420720973 / 1000000000000)))) (orderedInterval (16140181758 / 1000000000000) (16140183680 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate229_chunkChecks4_1 :
    compactCertificate229.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (952564958414787 / 4000000000000) 4 (IntervalRat.scale (213 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (8496097366 / 1000000000000) (8496097367 / 1000000000000), orderedInterval (50983224959 / 1000000000000) (50983224960 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (549963635161323 / 4000000000000) 4 (IntervalRat.scale (213 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (3082855035 / 1000000000000) (3082855038 / 1000000000000), orderedInterval (67965215955 / 1000000000000) (67965215958 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (975920121533607 / 4000000000000) 4 (IntervalRat.scale (213 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-14082783627 / 1000000000000) (-14082783483 / 1000000000000), orderedInterval (49130701785 / 1000000000000) (49130701929 / 1000000000000)))) (orderedInterval (-92364514534 / 1000000000000) (-92364513047 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (911831170565283 / 4000000000000) 4 (IntervalRat.scale (213 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (29560287350 / 1000000000000) (29560293980 / 1000000000000), orderedInterval (-43870098825 / 1000000000000) (-43870092195 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (650725748683539 / 4000000000000) 4 (IntervalRat.scale (213 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (6447390139 / 1000000000000) (6447390140 / 1000000000000), orderedInterval (62203492166 / 1000000000000) (62203492167 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (737853644024181 / 4000000000000) 4 (IntervalRat.scale (213 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (6205867411 / 1000000000000) (6205867429 / 1000000000000), orderedInterval (-58435120629 / 1000000000000) (-58435120611 / 1000000000000)))) (orderedInterval (-7596182372 / 1000000000000) (-7596179736 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (615145443277989 / 4000000000000) 4 (IntervalRat.scale (213 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-38056408015 / 1000000000000) (-38056408014 / 1000000000000), orderedInterval (-51754529197 / 1000000000000) (-51754529196 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (543499654625769 / 4000000000000) 4 (IntervalRat.scale (213 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-68449290086 / 1000000000000) (-68449290043 / 1000000000000), orderedInterval (259508822 / 1000000000000) (259508865 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (157527383827131 / 800000000000) 4 (IntervalRat.scale (213 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (12760295935 / 1000000000000) (12760296031 / 1000000000000), orderedInterval (-55442204964 / 1000000000000) (-55442204868 / 1000000000000)))) (orderedInterval (12080981629 / 1000000000000) (12080981719 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate229_chunkChecks4_2 :
    compactCertificate229.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (435729033877857 / 4000000000000) 4 (IntervalRat.scale (213 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (18114705908 / 1000000000000) (18114706119 / 1000000000000), orderedInterval (-74353546183 / 1000000000000) (-74353545973 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (369372327585177 / 4000000000000) 4 (IntervalRat.scale (213 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-74758895080 / 1000000000000) (-74758886875 / 1000000000000), orderedInterval (36531168820 / 1000000000000) (36531177025 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (231136052095731 / 4000000000000) 4 (IntervalRat.scale (213 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (94612781050 / 1000000000000) (94612787804 / 1000000000000), orderedInterval (-46265218412 / 1000000000000) (-46265211658 / 1000000000000)))) (orderedInterval (-302864605 / 1000000000000) (-302864256 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (124305737540877 / 4000000000000) 4 (IntervalRat.scale (213 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (61203988720 / 1000000000000) (61203988721 / 1000000000000), orderedInterval (128403938785 / 1000000000000) (128403938786 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (337514258333631 / 4000000000000) 4 (IntervalRat.scale (213 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-28924109933 / 1000000000000) (-28924109932 / 1000000000000), orderedInterval (-81732844297 / 1000000000000) (-81732844296 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (460846864773087 / 4000000000000) 4 (IntervalRat.scale (213 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (17878701757 / 1000000000000) (17878701969 / 1000000000000), orderedInterval (-72230547332 / 1000000000000) (-72230547119 / 1000000000000)))) (orderedInterval (-1478108335 / 1000000000000) (-1478108299 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (194863947904269 / 4000000000000) 4 (IntervalRat.scale (213 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-79302514521 / 1000000000000) (-79302437678 / 1000000000000), orderedInterval (83149255434 / 1000000000000) (83149332277 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (792111129707949 / 4000000000000) 4 (IntervalRat.scale (213 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-44138122202 / 1000000000000) (-44138122201 / 1000000000000), orderedInterval (-35478221883 / 1000000000000) (-35478221882 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (529093524996291 / 4000000000000) 4 (IntervalRat.scale (213 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (62168055875 / 1000000000000) (62168055876 / 1000000000000), orderedInterval (30554957618 / 1000000000000) (30554957619 / 1000000000000)))) (orderedInterval (15317203587 / 1000000000000) (15317203762 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate229_chunkChecks4 :
    compactCertificate229.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate229.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate229_chunkChecks4_0
    compactCertificate229_chunkChecks4_1 compactCertificate229_chunkChecks4_2

theorem compactCertificate229_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate229.chunkCheck r b = true :=
  compactCertificate229.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate229_chunkChecks0
    · exact compactCertificate229_chunkChecks1
    · exact compactCertificate229_chunkChecks2
    · exact compactCertificate229_chunkChecks3
    · exact compactCertificate229_chunkChecks4)

theorem compactCertificate229_coefficient0 :
    compactCertificate229.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate229, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate229_coefficient1 :
    compactCertificate229.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate229, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate229_coefficient2 :
    compactCertificate229.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate229, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate229_coefficient3 :
    compactCertificate229.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate229, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate229_coefficient4 :
    compactCertificate229.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate229, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate229_coefficients : ∀ r : Fin 5,
    compactCertificate229.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate229_coefficient0
  · exact compactCertificate229_coefficient1
  · exact compactCertificate229_coefficient2
  · exact compactCertificate229_coefficient3
  · exact compactCertificate229_coefficient4

theorem compactCertificate229_lower : (1 : ℚ) ≤ compactCertificate229.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate229, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate229_proves {t : ℝ} (ht : t ∈ compactCertificate229.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate229.proves compactCertificate229_states compactCertificate229_chunks
    compactCertificate229_coefficients compactCertificate229_lower ht

end Erdos232
