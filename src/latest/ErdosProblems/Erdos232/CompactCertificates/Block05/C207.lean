/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate207 : CompactCertificate where
  left := 185 / 2
  right := 2961 / 32
  center := 5921 / 64
  grid := fun i =>
    match i.val with
    | 0 => 29
    | 1 => 22
    | 2 => 35
    | 3 => 6
    | 4 => 17
    | 5 => 46
    | 6 => 34
    | 7 => 58
    | 8 => 43
    | 9 => 66
    | 10 => 38
    | 11 => 67
    | 12 => 63
    | 13 => 45
    | 14 => 51
    | 15 => 43
    | 16 => 38
    | 17 => 54
    | 18 => 30
    | 19 => 26
    | 20 => 16
    | 21 => 9
    | 22 => 23
    | 23 => 32
    | 24 => 13
    | 25 => 55
    | _ => 37
  point := fun i =>
    match i.val with
    | 0 => 5921 / 64
    | 1 => 8722763602521821 / 128000000000000
    | 2 => 2820762528567293 / 25600000000000
    | 3 => 2545280664333847 / 128000000000000
    | 4 => 6836981887742059 / 128000000000000
    | 5 => 18563735807605503 / 128000000000000
    | 6 => 13673963775490039 / 128000000000000
    | 7 => 23430569994548947 / 128000000000000
    | 8 => 17258851810052473 / 128000000000000
    | 9 => 26479516989549079 / 128000000000000
    | 10 => 15287956261925791 / 128000000000000
    | 11 => 27128746664791019 / 128000000000000
    | 12 => 25347194182709111 / 128000000000000
    | 13 => 18088953793217063 / 128000000000000
    | 14 => 20510945663226177 / 128000000000000
    | 15 => 17099888120417713 / 128000000000000
    | 16 => 15108269741967973 / 128000000000000
    | 17 => 4378965444321327 / 25600000000000
    | 18 => 12112448871318269 / 128000000000000
    | 19 => 10267857049914709 / 128000000000000
    | 20 => 6425148189947527 / 128000000000000
    | 21 => 3455466065631609 / 128000000000000
    | 22 => 9382262552081827 / 128000000000000
    | 23 => 12810677400570179 / 128000000000000
    | 24 => 5416851810052473 / 128000000000000
    | 25 => 22019201873243033 / 128000000000000
    | _ => 14707806392033047 / 128000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-67383410742 / 1000000000000) (-67383368436 / 1000000000000), orderedInterval (48744508716 / 1000000000000) (48744551022 / 1000000000000))
    | 1 => (orderedInterval (-17767799849 / 1000000000000) (-17767799717 / 1000000000000), orderedInterval (95138022204 / 1000000000000) (95138022337 / 1000000000000))
    | 2 => (orderedInterval (-64551817521 / 1000000000000) (-64551817520 / 1000000000000), orderedInterval (-39840830196 / 1000000000000) (-39840830195 / 1000000000000))
    | 3 => (orderedInterval (173610072636 / 1000000000000) (173610073206 / 1000000000000), orderedInterval (-47556431075 / 1000000000000) (-47556430505 / 1000000000000))
    | 4 => (orderedInterval (-77541912396 / 1000000000000) (-77541912395 / 1000000000000), orderedInterval (-76123789255 / 1000000000000) (-76123789254 / 1000000000000))
    | 5 => (orderedInterval (63847581240 / 1000000000000) (63847581241 / 1000000000000), orderedInterval (17473430940 / 1000000000000) (17473430941 / 1000000000000))
    | 6 => (orderedInterval (55265109999 / 1000000000000) (55265110000 / 1000000000000), orderedInterval (53640058606 / 1000000000000) (53640058607 / 1000000000000))
    | 7 => (orderedInterval (58890531707 / 1000000000000) (58890531836 / 1000000000000), orderedInterval (-3277501346 / 1000000000000) (-3277501218 / 1000000000000))
    | 8 => (orderedInterval (-34782057637 / 1000000000000) (-34782057636 / 1000000000000), orderedInterval (-59130659606 / 1000000000000) (-59130659605 / 1000000000000))
    | 9 => (orderedInterval (16970637370 / 1000000000000) (16970637371 / 1000000000000), orderedInterval (52773536013 / 1000000000000) (52773536014 / 1000000000000))
    | 10 => (orderedInterval (54412823070 / 1000000000000) (54412823071 / 1000000000000), orderedInterval (48448745772 / 1000000000000) (48448745773 / 1000000000000))
    | 11 => (orderedInterval (-42936618771 / 1000000000000) (-42936511761 / 1000000000000), orderedInterval (34162587293 / 1000000000000) (34162694303 / 1000000000000))
    | 12 => (orderedInterval (-44037617173 / 1000000000000) (-44037617172 / 1000000000000), orderedInterval (-35603404466 / 1000000000000) (-35603404465 / 1000000000000))
    | 13 => (orderedInterval (-44898398920 / 1000000000000) (-44898398919 / 1000000000000), orderedInterval (-49730510313 / 1000000000000) (-49730510312 / 1000000000000))
    | 14 => (orderedInterval (-45441161715 / 1000000000000) (-45441161714 / 1000000000000), orderedInterval (-43538534269 / 1000000000000) (-43538534268 / 1000000000000))
    | 15 => (orderedInterval (45056948524 / 1000000000000) (45056981241 / 1000000000000), orderedInterval (-52468236990 / 1000000000000) (-52468204274 / 1000000000000))
    | 16 => (orderedInterval (-39186173702 / 1000000000000) (-39186165195 / 1000000000000), orderedInterval (62278974939 / 1000000000000) (62278983446 / 1000000000000))
    | 17 => (orderedInterval (49608765125 / 1000000000000) (49608824119 / 1000000000000), orderedInterval (-35651712320 / 1000000000000) (-35651653325 / 1000000000000))
    | 18 => (orderedInterval (75353776044 / 1000000000000) (75353776045 / 1000000000000), orderedInterval (31994947862 / 1000000000000) (31994947863 / 1000000000000))
    | 19 => (orderedInterval (-56011119020 / 1000000000000) (-56011087693 / 1000000000000), orderedInterval (69623514583 / 1000000000000) (69623545909 / 1000000000000))
    | 20 => (orderedInterval (73737852137 / 1000000000000) (73737852138 / 1000000000000), orderedInterval (84385374330 / 1000000000000) (84385374331 / 1000000000000))
    | 21 => (orderedInterval (73311068152 / 1000000000000) (73311074917 / 1000000000000), orderedInterval (-136301188544 / 1000000000000) (-136301181779 / 1000000000000))
    | 22 => (orderedInterval (-90175539947 / 1000000000000) (-90175539084 / 1000000000000), orderedInterval (24140601099 / 1000000000000) (24140601962 / 1000000000000))
    | 23 => (orderedInterval (26341483456 / 1000000000000) (26341483457 / 1000000000000), orderedInterval (75148415914 / 1000000000000) (75148415915 / 1000000000000))
    | 24 => (orderedInterval (-94583183115 / 1000000000000) (-94583121063 / 1000000000000), orderedInterval (79201423183 / 1000000000000) (79201485236 / 1000000000000))
    | 25 => (orderedInterval (-1343718077 / 1000000000000) (-1343718074 / 1000000000000), orderedInterval (-60815084662 / 1000000000000) (-60815084659 / 1000000000000))
    | _ => (orderedInterval (38897899500 / 1000000000000) (38897907079 / 1000000000000), orderedInterval (-63630986818 / 1000000000000) (-63630979239 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-30661960797 / 1000000000000) (-30661944020 / 1000000000000)
      | 1 => orderedInterval (-9253638450 / 1000000000000) (-9253638431 / 1000000000000)
      | 2 => orderedInterval (-2657033334 / 1000000000000) (-2657033324 / 1000000000000)
      | 3 => orderedInterval (-5087628291 / 1000000000000) (-5087613041 / 1000000000000)
      | 4 => orderedInterval (-3220747944 / 1000000000000) (-3220747932 / 1000000000000)
      | 5 => orderedInterval (4032977128 / 1000000000000) (4032979513 / 1000000000000)
      | 6 => orderedInterval (-6477718420 / 1000000000000) (-6477716622 / 1000000000000)
      | 7 => orderedInterval (-1326679097 / 1000000000000) (-1326678941 / 1000000000000)
      | _ => orderedInterval (-7759076638 / 1000000000000) (-7759074815 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (17189166659 / 1000000000000) (17189183437 / 1000000000000)
      | 1 => orderedInterval (-3441061156 / 1000000000000) (-3441061141 / 1000000000000)
      | 2 => orderedInterval (-1882748317 / 1000000000000) (-1882748299 / 1000000000000)
      | 3 => orderedInterval (-5208359851 / 1000000000000) (-5208324925 / 1000000000000)
      | 4 => orderedInterval (-5426032047 / 1000000000000) (-5426032028 / 1000000000000)
      | 5 => orderedInterval (-7109684483 / 1000000000000) (-7109680510 / 1000000000000)
      | 6 => orderedInterval (-7158892737 / 1000000000000) (-7158891177 / 1000000000000)
      | 7 => orderedInterval (-5929914839 / 1000000000000) (-5929914776 / 1000000000000)
      | _ => orderedInterval (24251461974 / 1000000000000) (24251463948 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (31985602229 / 1000000000000) (31985619189 / 1000000000000)
      | 1 => orderedInterval (12221960155 / 1000000000000) (12221960174 / 1000000000000)
      | 2 => orderedInterval (8916910936 / 1000000000000) (8916910968 / 1000000000000)
      | 3 => orderedInterval (40447693590 / 1000000000000) (40447773968 / 1000000000000)
      | 4 => orderedInterval (5633080194 / 1000000000000) (5633080225 / 1000000000000)
      | 5 => orderedInterval (-9000299828 / 1000000000000) (-9000293021 / 1000000000000)
      | 6 => orderedInterval (9592389229 / 1000000000000) (9592390600 / 1000000000000)
      | 7 => orderedInterval (1257734097 / 1000000000000) (1257734132 / 1000000000000)
      | _ => orderedInterval (10737118583 / 1000000000000) (10737120931 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-16068979012 / 1000000000000) (-16068962055 / 1000000000000)
      | 1 => orderedInterval (5182525232 / 1000000000000) (5182525259 / 1000000000000)
      | 2 => orderedInterval (3544344988 / 1000000000000) (3544345049 / 1000000000000)
      | 3 => orderedInterval (38290001339 / 1000000000000) (38290185450 / 1000000000000)
      | 4 => orderedInterval (9251801249 / 1000000000000) (9251801301 / 1000000000000)
      | 5 => orderedInterval (15091537534 / 1000000000000) (15091549332 / 1000000000000)
      | 6 => orderedInterval (7499837306 / 1000000000000) (7499838497 / 1000000000000)
      | 7 => orderedInterval (7486943095 / 1000000000000) (7486943120 / 1000000000000)
      | _ => orderedInterval (-54857824067 / 1000000000000) (-54857821198 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-34027788946 / 1000000000000) (-34027771809 / 1000000000000)
      | 1 => orderedInterval (-27839390944 / 1000000000000) (-27839390903 / 1000000000000)
      | 2 => orderedInterval (-31706835634 / 1000000000000) (-31706835518 / 1000000000000)
      | 3 => orderedInterval (-233128139139 / 1000000000000) (-233127715421 / 1000000000000)
      | 4 => orderedInterval (-4557680031 / 1000000000000) (-4557679942 / 1000000000000)
      | 5 => orderedInterval (22719641449 / 1000000000000) (22719662331 / 1000000000000)
      | 6 => orderedInterval (-11348523764 / 1000000000000) (-11348522717 / 1000000000000)
      | 7 => orderedInterval (-2130291598 / 1000000000000) (-2130291578 / 1000000000000)
      | _ => orderedInterval (-14896787853 / 1000000000000) (-14896784259 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-62411505843 / 1000000000000) (-62411467613 / 1000000000000)
    | 1 => orderedInterval (5283935203 / 1000000000000) (5283994529 / 1000000000000)
    | 2 => orderedInterval (111792189185 / 1000000000000) (111792297166 / 1000000000000)
    | 3 => orderedInterval (15420187664 / 1000000000000) (15420404755 / 1000000000000)
    | _ => orderedInterval (-336915796460 / 1000000000000) (-336915329816 / 1000000000000)

theorem compactCertificate207_stateChecks0 :
    compactCertificate207.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (5921 / 64)) (orderedInterval (-67383410742 / 1000000000000) (-67383368436 / 1000000000000), orderedInterval (48744508716 / 1000000000000) (48744551022 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 22 12 (8722763602521821 / 128000000000000)) (orderedInterval (-17767799849 / 1000000000000) (-17767799717 / 1000000000000), orderedInterval (95138022204 / 1000000000000) (95138022337 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (2820762528567293 / 25600000000000)) (orderedInterval (-64551817521 / 1000000000000) (-64551817520 / 1000000000000), orderedInterval (-39840830196 / 1000000000000) (-39840830195 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate207_stateChecks1 :
    compactCertificate207.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 6 12 (2545280664333847 / 128000000000000)) (orderedInterval (173610072636 / 1000000000000) (173610073206 / 1000000000000), orderedInterval (-47556431075 / 1000000000000) (-47556430505 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 17 12 (6836981887742059 / 128000000000000)) (orderedInterval (-77541912396 / 1000000000000) (-77541912395 / 1000000000000), orderedInterval (-76123789255 / 1000000000000) (-76123789254 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (18563735807605503 / 128000000000000)) (orderedInterval (63847581240 / 1000000000000) (63847581241 / 1000000000000), orderedInterval (17473430940 / 1000000000000) (17473430941 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate207_stateChecks2 :
    compactCertificate207.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (13673963775490039 / 128000000000000)) (orderedInterval (55265109999 / 1000000000000) (55265110000 / 1000000000000), orderedInterval (53640058606 / 1000000000000) (53640058607 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (23430569994548947 / 128000000000000)) (orderedInterval (58890531707 / 1000000000000) (58890531836 / 1000000000000), orderedInterval (-3277501346 / 1000000000000) (-3277501218 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (17258851810052473 / 128000000000000)) (orderedInterval (-34782057637 / 1000000000000) (-34782057636 / 1000000000000), orderedInterval (-59130659606 / 1000000000000) (-59130659605 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate207_stateChecks3 :
    compactCertificate207.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (26479516989549079 / 128000000000000)) (orderedInterval (16970637370 / 1000000000000) (16970637371 / 1000000000000), orderedInterval (52773536013 / 1000000000000) (52773536014 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (15287956261925791 / 128000000000000)) (orderedInterval (54412823070 / 1000000000000) (54412823071 / 1000000000000), orderedInterval (48448745772 / 1000000000000) (48448745773 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (27128746664791019 / 128000000000000)) (orderedInterval (-42936618771 / 1000000000000) (-42936511761 / 1000000000000), orderedInterval (34162587293 / 1000000000000) (34162694303 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate207_stateChecks4 :
    compactCertificate207.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (25347194182709111 / 128000000000000)) (orderedInterval (-44037617173 / 1000000000000) (-44037617172 / 1000000000000), orderedInterval (-35603404466 / 1000000000000) (-35603404465 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (18088953793217063 / 128000000000000)) (orderedInterval (-44898398920 / 1000000000000) (-44898398919 / 1000000000000), orderedInterval (-49730510313 / 1000000000000) (-49730510312 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (20510945663226177 / 128000000000000)) (orderedInterval (-45441161715 / 1000000000000) (-45441161714 / 1000000000000), orderedInterval (-43538534269 / 1000000000000) (-43538534268 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate207_stateChecks5 :
    compactCertificate207.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (17099888120417713 / 128000000000000)) (orderedInterval (45056948524 / 1000000000000) (45056981241 / 1000000000000), orderedInterval (-52468236990 / 1000000000000) (-52468204274 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (15108269741967973 / 128000000000000)) (orderedInterval (-39186173702 / 1000000000000) (-39186165195 / 1000000000000), orderedInterval (62278974939 / 1000000000000) (62278983446 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (4378965444321327 / 25600000000000)) (orderedInterval (49608765125 / 1000000000000) (49608824119 / 1000000000000), orderedInterval (-35651712320 / 1000000000000) (-35651653325 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate207_stateChecks6 :
    compactCertificate207.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (12112448871318269 / 128000000000000)) (orderedInterval (75353776044 / 1000000000000) (75353776045 / 1000000000000), orderedInterval (31994947862 / 1000000000000) (31994947863 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (10267857049914709 / 128000000000000)) (orderedInterval (-56011119020 / 1000000000000) (-56011087693 / 1000000000000), orderedInterval (69623514583 / 1000000000000) (69623545909 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 16 12 (6425148189947527 / 128000000000000)) (orderedInterval (73737852137 / 1000000000000) (73737852138 / 1000000000000), orderedInterval (84385374330 / 1000000000000) (84385374331 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate207_stateChecks7 :
    compactCertificate207.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 9 12 (3455466065631609 / 128000000000000)) (orderedInterval (73311068152 / 1000000000000) (73311074917 / 1000000000000), orderedInterval (-136301188544 / 1000000000000) (-136301181779 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (9382262552081827 / 128000000000000)) (orderedInterval (-90175539947 / 1000000000000) (-90175539084 / 1000000000000), orderedInterval (24140601099 / 1000000000000) (24140601962 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (12810677400570179 / 128000000000000)) (orderedInterval (26341483456 / 1000000000000) (26341483457 / 1000000000000), orderedInterval (75148415914 / 1000000000000) (75148415915 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate207_stateChecks8 :
    compactCertificate207.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 13 12 (5416851810052473 / 128000000000000)) (orderedInterval (-94583183115 / 1000000000000) (-94583121063 / 1000000000000), orderedInterval (79201423183 / 1000000000000) (79201485236 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (22019201873243033 / 128000000000000)) (orderedInterval (-1343718077 / 1000000000000) (-1343718074 / 1000000000000), orderedInterval (-60815084662 / 1000000000000) (-60815084659 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (14707806392033047 / 128000000000000)) (orderedInterval (38897899500 / 1000000000000) (38897907079 / 1000000000000), orderedInterval (-63630986818 / 1000000000000) (-63630979239 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState006, besselGridState009, besselGridState013, besselGridState016, besselGridState017, besselGridState022, besselGridState023, besselGridState026, besselGridState029, besselGridState030, besselGridState032, besselGridState034, besselGridState035, besselGridState037, besselGridState038, besselGridState043, besselGridState045, besselGridState046, besselGridState051, besselGridState054, besselGridState055, besselGridState058, besselGridState063, besselGridState066, besselGridState067, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate207_states : ∀ j,
    BesselStateValid (compactCertificate207.point j) (compactCertificate207.state j) :=
  compactCertificate207.statesValid_of_checks3 compactCertificate207_stateChecks0
    compactCertificate207_stateChecks1 compactCertificate207_stateChecks2
    compactCertificate207_stateChecks3 compactCertificate207_stateChecks4
    compactCertificate207_stateChecks5 compactCertificate207_stateChecks6
    compactCertificate207_stateChecks7 compactCertificate207_stateChecks8

theorem compactCertificate207_chunkChecks0_0 :
    compactCertificate207.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (5921 / 64) 0 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-67383410742 / 1000000000000) (-67383368436 / 1000000000000), orderedInterval (48744508716 / 1000000000000) (48744551022 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (8722763602521821 / 128000000000000) 0 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-17767799849 / 1000000000000) (-17767799717 / 1000000000000), orderedInterval (95138022204 / 1000000000000) (95138022337 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (2820762528567293 / 25600000000000) 0 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-64551817521 / 1000000000000) (-64551817520 / 1000000000000), orderedInterval (-39840830196 / 1000000000000) (-39840830195 / 1000000000000)))) (orderedInterval (-30661960797 / 1000000000000) (-30661944020 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (2545280664333847 / 128000000000000) 0 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (173610072636 / 1000000000000) (173610073206 / 1000000000000), orderedInterval (-47556431075 / 1000000000000) (-47556430505 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (6836981887742059 / 128000000000000) 0 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-77541912396 / 1000000000000) (-77541912395 / 1000000000000), orderedInterval (-76123789255 / 1000000000000) (-76123789254 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (18563735807605503 / 128000000000000) 0 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (63847581240 / 1000000000000) (63847581241 / 1000000000000), orderedInterval (17473430940 / 1000000000000) (17473430941 / 1000000000000)))) (orderedInterval (-9253638450 / 1000000000000) (-9253638431 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (13673963775490039 / 128000000000000) 0 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (55265109999 / 1000000000000) (55265110000 / 1000000000000), orderedInterval (53640058606 / 1000000000000) (53640058607 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (23430569994548947 / 128000000000000) 0 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (58890531707 / 1000000000000) (58890531836 / 1000000000000), orderedInterval (-3277501346 / 1000000000000) (-3277501218 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (17258851810052473 / 128000000000000) 0 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-34782057637 / 1000000000000) (-34782057636 / 1000000000000), orderedInterval (-59130659606 / 1000000000000) (-59130659605 / 1000000000000)))) (orderedInterval (-2657033334 / 1000000000000) (-2657033324 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate207_chunkChecks0_1 :
    compactCertificate207.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (26479516989549079 / 128000000000000) 0 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (16970637370 / 1000000000000) (16970637371 / 1000000000000), orderedInterval (52773536013 / 1000000000000) (52773536014 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (15287956261925791 / 128000000000000) 0 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (54412823070 / 1000000000000) (54412823071 / 1000000000000), orderedInterval (48448745772 / 1000000000000) (48448745773 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (27128746664791019 / 128000000000000) 0 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-42936618771 / 1000000000000) (-42936511761 / 1000000000000), orderedInterval (34162587293 / 1000000000000) (34162694303 / 1000000000000)))) (orderedInterval (-5087628291 / 1000000000000) (-5087613041 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (25347194182709111 / 128000000000000) 0 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-44037617173 / 1000000000000) (-44037617172 / 1000000000000), orderedInterval (-35603404466 / 1000000000000) (-35603404465 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (18088953793217063 / 128000000000000) 0 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-44898398920 / 1000000000000) (-44898398919 / 1000000000000), orderedInterval (-49730510313 / 1000000000000) (-49730510312 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (20510945663226177 / 128000000000000) 0 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-45441161715 / 1000000000000) (-45441161714 / 1000000000000), orderedInterval (-43538534269 / 1000000000000) (-43538534268 / 1000000000000)))) (orderedInterval (-3220747944 / 1000000000000) (-3220747932 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (17099888120417713 / 128000000000000) 0 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (45056948524 / 1000000000000) (45056981241 / 1000000000000), orderedInterval (-52468236990 / 1000000000000) (-52468204274 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (15108269741967973 / 128000000000000) 0 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-39186173702 / 1000000000000) (-39186165195 / 1000000000000), orderedInterval (62278974939 / 1000000000000) (62278983446 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (4378965444321327 / 25600000000000) 0 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (49608765125 / 1000000000000) (49608824119 / 1000000000000), orderedInterval (-35651712320 / 1000000000000) (-35651653325 / 1000000000000)))) (orderedInterval (4032977128 / 1000000000000) (4032979513 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate207_chunkChecks0_2 :
    compactCertificate207.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (12112448871318269 / 128000000000000) 0 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (75353776044 / 1000000000000) (75353776045 / 1000000000000), orderedInterval (31994947862 / 1000000000000) (31994947863 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (10267857049914709 / 128000000000000) 0 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-56011119020 / 1000000000000) (-56011087693 / 1000000000000), orderedInterval (69623514583 / 1000000000000) (69623545909 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (6425148189947527 / 128000000000000) 0 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (73737852137 / 1000000000000) (73737852138 / 1000000000000), orderedInterval (84385374330 / 1000000000000) (84385374331 / 1000000000000)))) (orderedInterval (-6477718420 / 1000000000000) (-6477716622 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (3455466065631609 / 128000000000000) 0 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (73311068152 / 1000000000000) (73311074917 / 1000000000000), orderedInterval (-136301188544 / 1000000000000) (-136301181779 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (9382262552081827 / 128000000000000) 0 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-90175539947 / 1000000000000) (-90175539084 / 1000000000000), orderedInterval (24140601099 / 1000000000000) (24140601962 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (12810677400570179 / 128000000000000) 0 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (26341483456 / 1000000000000) (26341483457 / 1000000000000), orderedInterval (75148415914 / 1000000000000) (75148415915 / 1000000000000)))) (orderedInterval (-1326679097 / 1000000000000) (-1326678941 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (5416851810052473 / 128000000000000) 0 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-94583183115 / 1000000000000) (-94583121063 / 1000000000000), orderedInterval (79201423183 / 1000000000000) (79201485236 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (22019201873243033 / 128000000000000) 0 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-1343718077 / 1000000000000) (-1343718074 / 1000000000000), orderedInterval (-60815084662 / 1000000000000) (-60815084659 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (14707806392033047 / 128000000000000) 0 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (38897899500 / 1000000000000) (38897907079 / 1000000000000), orderedInterval (-63630986818 / 1000000000000) (-63630979239 / 1000000000000)))) (orderedInterval (-7759076638 / 1000000000000) (-7759074815 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate207_chunkChecks0 :
    compactCertificate207.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate207.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate207_chunkChecks0_0
    compactCertificate207_chunkChecks0_1 compactCertificate207_chunkChecks0_2

theorem compactCertificate207_chunkChecks1_0 :
    compactCertificate207.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (5921 / 64) 1 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-67383410742 / 1000000000000) (-67383368436 / 1000000000000), orderedInterval (48744508716 / 1000000000000) (48744551022 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (8722763602521821 / 128000000000000) 1 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-17767799849 / 1000000000000) (-17767799717 / 1000000000000), orderedInterval (95138022204 / 1000000000000) (95138022337 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (2820762528567293 / 25600000000000) 1 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-64551817521 / 1000000000000) (-64551817520 / 1000000000000), orderedInterval (-39840830196 / 1000000000000) (-39840830195 / 1000000000000)))) (orderedInterval (17189166659 / 1000000000000) (17189183437 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (2545280664333847 / 128000000000000) 1 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (173610072636 / 1000000000000) (173610073206 / 1000000000000), orderedInterval (-47556431075 / 1000000000000) (-47556430505 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (6836981887742059 / 128000000000000) 1 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-77541912396 / 1000000000000) (-77541912395 / 1000000000000), orderedInterval (-76123789255 / 1000000000000) (-76123789254 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (18563735807605503 / 128000000000000) 1 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (63847581240 / 1000000000000) (63847581241 / 1000000000000), orderedInterval (17473430940 / 1000000000000) (17473430941 / 1000000000000)))) (orderedInterval (-3441061156 / 1000000000000) (-3441061141 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (13673963775490039 / 128000000000000) 1 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (55265109999 / 1000000000000) (55265110000 / 1000000000000), orderedInterval (53640058606 / 1000000000000) (53640058607 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (23430569994548947 / 128000000000000) 1 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (58890531707 / 1000000000000) (58890531836 / 1000000000000), orderedInterval (-3277501346 / 1000000000000) (-3277501218 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (17258851810052473 / 128000000000000) 1 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-34782057637 / 1000000000000) (-34782057636 / 1000000000000), orderedInterval (-59130659606 / 1000000000000) (-59130659605 / 1000000000000)))) (orderedInterval (-1882748317 / 1000000000000) (-1882748299 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate207_chunkChecks1_1 :
    compactCertificate207.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (26479516989549079 / 128000000000000) 1 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (16970637370 / 1000000000000) (16970637371 / 1000000000000), orderedInterval (52773536013 / 1000000000000) (52773536014 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (15287956261925791 / 128000000000000) 1 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (54412823070 / 1000000000000) (54412823071 / 1000000000000), orderedInterval (48448745772 / 1000000000000) (48448745773 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (27128746664791019 / 128000000000000) 1 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-42936618771 / 1000000000000) (-42936511761 / 1000000000000), orderedInterval (34162587293 / 1000000000000) (34162694303 / 1000000000000)))) (orderedInterval (-5208359851 / 1000000000000) (-5208324925 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (25347194182709111 / 128000000000000) 1 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-44037617173 / 1000000000000) (-44037617172 / 1000000000000), orderedInterval (-35603404466 / 1000000000000) (-35603404465 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (18088953793217063 / 128000000000000) 1 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-44898398920 / 1000000000000) (-44898398919 / 1000000000000), orderedInterval (-49730510313 / 1000000000000) (-49730510312 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (20510945663226177 / 128000000000000) 1 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-45441161715 / 1000000000000) (-45441161714 / 1000000000000), orderedInterval (-43538534269 / 1000000000000) (-43538534268 / 1000000000000)))) (orderedInterval (-5426032047 / 1000000000000) (-5426032028 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (17099888120417713 / 128000000000000) 1 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (45056948524 / 1000000000000) (45056981241 / 1000000000000), orderedInterval (-52468236990 / 1000000000000) (-52468204274 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (15108269741967973 / 128000000000000) 1 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-39186173702 / 1000000000000) (-39186165195 / 1000000000000), orderedInterval (62278974939 / 1000000000000) (62278983446 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (4378965444321327 / 25600000000000) 1 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (49608765125 / 1000000000000) (49608824119 / 1000000000000), orderedInterval (-35651712320 / 1000000000000) (-35651653325 / 1000000000000)))) (orderedInterval (-7109684483 / 1000000000000) (-7109680510 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate207_chunkChecks1_2 :
    compactCertificate207.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (12112448871318269 / 128000000000000) 1 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (75353776044 / 1000000000000) (75353776045 / 1000000000000), orderedInterval (31994947862 / 1000000000000) (31994947863 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (10267857049914709 / 128000000000000) 1 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-56011119020 / 1000000000000) (-56011087693 / 1000000000000), orderedInterval (69623514583 / 1000000000000) (69623545909 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (6425148189947527 / 128000000000000) 1 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (73737852137 / 1000000000000) (73737852138 / 1000000000000), orderedInterval (84385374330 / 1000000000000) (84385374331 / 1000000000000)))) (orderedInterval (-7158892737 / 1000000000000) (-7158891177 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (3455466065631609 / 128000000000000) 1 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (73311068152 / 1000000000000) (73311074917 / 1000000000000), orderedInterval (-136301188544 / 1000000000000) (-136301181779 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (9382262552081827 / 128000000000000) 1 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-90175539947 / 1000000000000) (-90175539084 / 1000000000000), orderedInterval (24140601099 / 1000000000000) (24140601962 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (12810677400570179 / 128000000000000) 1 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (26341483456 / 1000000000000) (26341483457 / 1000000000000), orderedInterval (75148415914 / 1000000000000) (75148415915 / 1000000000000)))) (orderedInterval (-5929914839 / 1000000000000) (-5929914776 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (5416851810052473 / 128000000000000) 1 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-94583183115 / 1000000000000) (-94583121063 / 1000000000000), orderedInterval (79201423183 / 1000000000000) (79201485236 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (22019201873243033 / 128000000000000) 1 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-1343718077 / 1000000000000) (-1343718074 / 1000000000000), orderedInterval (-60815084662 / 1000000000000) (-60815084659 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (14707806392033047 / 128000000000000) 1 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (38897899500 / 1000000000000) (38897907079 / 1000000000000), orderedInterval (-63630986818 / 1000000000000) (-63630979239 / 1000000000000)))) (orderedInterval (24251461974 / 1000000000000) (24251463948 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate207_chunkChecks1 :
    compactCertificate207.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate207.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate207_chunkChecks1_0
    compactCertificate207_chunkChecks1_1 compactCertificate207_chunkChecks1_2

theorem compactCertificate207_chunkChecks2_0 :
    compactCertificate207.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (5921 / 64) 2 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-67383410742 / 1000000000000) (-67383368436 / 1000000000000), orderedInterval (48744508716 / 1000000000000) (48744551022 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (8722763602521821 / 128000000000000) 2 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-17767799849 / 1000000000000) (-17767799717 / 1000000000000), orderedInterval (95138022204 / 1000000000000) (95138022337 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (2820762528567293 / 25600000000000) 2 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-64551817521 / 1000000000000) (-64551817520 / 1000000000000), orderedInterval (-39840830196 / 1000000000000) (-39840830195 / 1000000000000)))) (orderedInterval (31985602229 / 1000000000000) (31985619189 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (2545280664333847 / 128000000000000) 2 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (173610072636 / 1000000000000) (173610073206 / 1000000000000), orderedInterval (-47556431075 / 1000000000000) (-47556430505 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (6836981887742059 / 128000000000000) 2 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-77541912396 / 1000000000000) (-77541912395 / 1000000000000), orderedInterval (-76123789255 / 1000000000000) (-76123789254 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (18563735807605503 / 128000000000000) 2 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (63847581240 / 1000000000000) (63847581241 / 1000000000000), orderedInterval (17473430940 / 1000000000000) (17473430941 / 1000000000000)))) (orderedInterval (12221960155 / 1000000000000) (12221960174 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (13673963775490039 / 128000000000000) 2 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (55265109999 / 1000000000000) (55265110000 / 1000000000000), orderedInterval (53640058606 / 1000000000000) (53640058607 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (23430569994548947 / 128000000000000) 2 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (58890531707 / 1000000000000) (58890531836 / 1000000000000), orderedInterval (-3277501346 / 1000000000000) (-3277501218 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (17258851810052473 / 128000000000000) 2 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-34782057637 / 1000000000000) (-34782057636 / 1000000000000), orderedInterval (-59130659606 / 1000000000000) (-59130659605 / 1000000000000)))) (orderedInterval (8916910936 / 1000000000000) (8916910968 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate207_chunkChecks2_1 :
    compactCertificate207.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (26479516989549079 / 128000000000000) 2 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (16970637370 / 1000000000000) (16970637371 / 1000000000000), orderedInterval (52773536013 / 1000000000000) (52773536014 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (15287956261925791 / 128000000000000) 2 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (54412823070 / 1000000000000) (54412823071 / 1000000000000), orderedInterval (48448745772 / 1000000000000) (48448745773 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (27128746664791019 / 128000000000000) 2 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-42936618771 / 1000000000000) (-42936511761 / 1000000000000), orderedInterval (34162587293 / 1000000000000) (34162694303 / 1000000000000)))) (orderedInterval (40447693590 / 1000000000000) (40447773968 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (25347194182709111 / 128000000000000) 2 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-44037617173 / 1000000000000) (-44037617172 / 1000000000000), orderedInterval (-35603404466 / 1000000000000) (-35603404465 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (18088953793217063 / 128000000000000) 2 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-44898398920 / 1000000000000) (-44898398919 / 1000000000000), orderedInterval (-49730510313 / 1000000000000) (-49730510312 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (20510945663226177 / 128000000000000) 2 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-45441161715 / 1000000000000) (-45441161714 / 1000000000000), orderedInterval (-43538534269 / 1000000000000) (-43538534268 / 1000000000000)))) (orderedInterval (5633080194 / 1000000000000) (5633080225 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (17099888120417713 / 128000000000000) 2 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (45056948524 / 1000000000000) (45056981241 / 1000000000000), orderedInterval (-52468236990 / 1000000000000) (-52468204274 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (15108269741967973 / 128000000000000) 2 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-39186173702 / 1000000000000) (-39186165195 / 1000000000000), orderedInterval (62278974939 / 1000000000000) (62278983446 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (4378965444321327 / 25600000000000) 2 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (49608765125 / 1000000000000) (49608824119 / 1000000000000), orderedInterval (-35651712320 / 1000000000000) (-35651653325 / 1000000000000)))) (orderedInterval (-9000299828 / 1000000000000) (-9000293021 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate207_chunkChecks2_2 :
    compactCertificate207.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (12112448871318269 / 128000000000000) 2 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (75353776044 / 1000000000000) (75353776045 / 1000000000000), orderedInterval (31994947862 / 1000000000000) (31994947863 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (10267857049914709 / 128000000000000) 2 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-56011119020 / 1000000000000) (-56011087693 / 1000000000000), orderedInterval (69623514583 / 1000000000000) (69623545909 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (6425148189947527 / 128000000000000) 2 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (73737852137 / 1000000000000) (73737852138 / 1000000000000), orderedInterval (84385374330 / 1000000000000) (84385374331 / 1000000000000)))) (orderedInterval (9592389229 / 1000000000000) (9592390600 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (3455466065631609 / 128000000000000) 2 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (73311068152 / 1000000000000) (73311074917 / 1000000000000), orderedInterval (-136301188544 / 1000000000000) (-136301181779 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (9382262552081827 / 128000000000000) 2 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-90175539947 / 1000000000000) (-90175539084 / 1000000000000), orderedInterval (24140601099 / 1000000000000) (24140601962 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (12810677400570179 / 128000000000000) 2 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (26341483456 / 1000000000000) (26341483457 / 1000000000000), orderedInterval (75148415914 / 1000000000000) (75148415915 / 1000000000000)))) (orderedInterval (1257734097 / 1000000000000) (1257734132 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (5416851810052473 / 128000000000000) 2 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-94583183115 / 1000000000000) (-94583121063 / 1000000000000), orderedInterval (79201423183 / 1000000000000) (79201485236 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (22019201873243033 / 128000000000000) 2 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-1343718077 / 1000000000000) (-1343718074 / 1000000000000), orderedInterval (-60815084662 / 1000000000000) (-60815084659 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (14707806392033047 / 128000000000000) 2 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (38897899500 / 1000000000000) (38897907079 / 1000000000000), orderedInterval (-63630986818 / 1000000000000) (-63630979239 / 1000000000000)))) (orderedInterval (10737118583 / 1000000000000) (10737120931 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate207_chunkChecks2 :
    compactCertificate207.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate207.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate207_chunkChecks2_0
    compactCertificate207_chunkChecks2_1 compactCertificate207_chunkChecks2_2

theorem compactCertificate207_chunkChecks3_0 :
    compactCertificate207.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (5921 / 64) 3 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-67383410742 / 1000000000000) (-67383368436 / 1000000000000), orderedInterval (48744508716 / 1000000000000) (48744551022 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (8722763602521821 / 128000000000000) 3 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-17767799849 / 1000000000000) (-17767799717 / 1000000000000), orderedInterval (95138022204 / 1000000000000) (95138022337 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (2820762528567293 / 25600000000000) 3 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-64551817521 / 1000000000000) (-64551817520 / 1000000000000), orderedInterval (-39840830196 / 1000000000000) (-39840830195 / 1000000000000)))) (orderedInterval (-16068979012 / 1000000000000) (-16068962055 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (2545280664333847 / 128000000000000) 3 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (173610072636 / 1000000000000) (173610073206 / 1000000000000), orderedInterval (-47556431075 / 1000000000000) (-47556430505 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (6836981887742059 / 128000000000000) 3 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-77541912396 / 1000000000000) (-77541912395 / 1000000000000), orderedInterval (-76123789255 / 1000000000000) (-76123789254 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (18563735807605503 / 128000000000000) 3 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (63847581240 / 1000000000000) (63847581241 / 1000000000000), orderedInterval (17473430940 / 1000000000000) (17473430941 / 1000000000000)))) (orderedInterval (5182525232 / 1000000000000) (5182525259 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (13673963775490039 / 128000000000000) 3 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (55265109999 / 1000000000000) (55265110000 / 1000000000000), orderedInterval (53640058606 / 1000000000000) (53640058607 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (23430569994548947 / 128000000000000) 3 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (58890531707 / 1000000000000) (58890531836 / 1000000000000), orderedInterval (-3277501346 / 1000000000000) (-3277501218 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (17258851810052473 / 128000000000000) 3 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-34782057637 / 1000000000000) (-34782057636 / 1000000000000), orderedInterval (-59130659606 / 1000000000000) (-59130659605 / 1000000000000)))) (orderedInterval (3544344988 / 1000000000000) (3544345049 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate207_chunkChecks3_1 :
    compactCertificate207.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (26479516989549079 / 128000000000000) 3 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (16970637370 / 1000000000000) (16970637371 / 1000000000000), orderedInterval (52773536013 / 1000000000000) (52773536014 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (15287956261925791 / 128000000000000) 3 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (54412823070 / 1000000000000) (54412823071 / 1000000000000), orderedInterval (48448745772 / 1000000000000) (48448745773 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (27128746664791019 / 128000000000000) 3 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-42936618771 / 1000000000000) (-42936511761 / 1000000000000), orderedInterval (34162587293 / 1000000000000) (34162694303 / 1000000000000)))) (orderedInterval (38290001339 / 1000000000000) (38290185450 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (25347194182709111 / 128000000000000) 3 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-44037617173 / 1000000000000) (-44037617172 / 1000000000000), orderedInterval (-35603404466 / 1000000000000) (-35603404465 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (18088953793217063 / 128000000000000) 3 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-44898398920 / 1000000000000) (-44898398919 / 1000000000000), orderedInterval (-49730510313 / 1000000000000) (-49730510312 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (20510945663226177 / 128000000000000) 3 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-45441161715 / 1000000000000) (-45441161714 / 1000000000000), orderedInterval (-43538534269 / 1000000000000) (-43538534268 / 1000000000000)))) (orderedInterval (9251801249 / 1000000000000) (9251801301 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (17099888120417713 / 128000000000000) 3 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (45056948524 / 1000000000000) (45056981241 / 1000000000000), orderedInterval (-52468236990 / 1000000000000) (-52468204274 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (15108269741967973 / 128000000000000) 3 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-39186173702 / 1000000000000) (-39186165195 / 1000000000000), orderedInterval (62278974939 / 1000000000000) (62278983446 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (4378965444321327 / 25600000000000) 3 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (49608765125 / 1000000000000) (49608824119 / 1000000000000), orderedInterval (-35651712320 / 1000000000000) (-35651653325 / 1000000000000)))) (orderedInterval (15091537534 / 1000000000000) (15091549332 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate207_chunkChecks3_2 :
    compactCertificate207.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (12112448871318269 / 128000000000000) 3 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (75353776044 / 1000000000000) (75353776045 / 1000000000000), orderedInterval (31994947862 / 1000000000000) (31994947863 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (10267857049914709 / 128000000000000) 3 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-56011119020 / 1000000000000) (-56011087693 / 1000000000000), orderedInterval (69623514583 / 1000000000000) (69623545909 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (6425148189947527 / 128000000000000) 3 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (73737852137 / 1000000000000) (73737852138 / 1000000000000), orderedInterval (84385374330 / 1000000000000) (84385374331 / 1000000000000)))) (orderedInterval (7499837306 / 1000000000000) (7499838497 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (3455466065631609 / 128000000000000) 3 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (73311068152 / 1000000000000) (73311074917 / 1000000000000), orderedInterval (-136301188544 / 1000000000000) (-136301181779 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (9382262552081827 / 128000000000000) 3 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-90175539947 / 1000000000000) (-90175539084 / 1000000000000), orderedInterval (24140601099 / 1000000000000) (24140601962 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (12810677400570179 / 128000000000000) 3 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (26341483456 / 1000000000000) (26341483457 / 1000000000000), orderedInterval (75148415914 / 1000000000000) (75148415915 / 1000000000000)))) (orderedInterval (7486943095 / 1000000000000) (7486943120 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (5416851810052473 / 128000000000000) 3 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-94583183115 / 1000000000000) (-94583121063 / 1000000000000), orderedInterval (79201423183 / 1000000000000) (79201485236 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (22019201873243033 / 128000000000000) 3 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-1343718077 / 1000000000000) (-1343718074 / 1000000000000), orderedInterval (-60815084662 / 1000000000000) (-60815084659 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (14707806392033047 / 128000000000000) 3 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (38897899500 / 1000000000000) (38897907079 / 1000000000000), orderedInterval (-63630986818 / 1000000000000) (-63630979239 / 1000000000000)))) (orderedInterval (-54857824067 / 1000000000000) (-54857821198 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate207_chunkChecks3 :
    compactCertificate207.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate207.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate207_chunkChecks3_0
    compactCertificate207_chunkChecks3_1 compactCertificate207_chunkChecks3_2

theorem compactCertificate207_chunkChecks4_0 :
    compactCertificate207.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (5921 / 64) 4 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-67383410742 / 1000000000000) (-67383368436 / 1000000000000), orderedInterval (48744508716 / 1000000000000) (48744551022 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (8722763602521821 / 128000000000000) 4 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-17767799849 / 1000000000000) (-17767799717 / 1000000000000), orderedInterval (95138022204 / 1000000000000) (95138022337 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (2820762528567293 / 25600000000000) 4 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-64551817521 / 1000000000000) (-64551817520 / 1000000000000), orderedInterval (-39840830196 / 1000000000000) (-39840830195 / 1000000000000)))) (orderedInterval (-34027788946 / 1000000000000) (-34027771809 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (2545280664333847 / 128000000000000) 4 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (173610072636 / 1000000000000) (173610073206 / 1000000000000), orderedInterval (-47556431075 / 1000000000000) (-47556430505 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (6836981887742059 / 128000000000000) 4 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-77541912396 / 1000000000000) (-77541912395 / 1000000000000), orderedInterval (-76123789255 / 1000000000000) (-76123789254 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (18563735807605503 / 128000000000000) 4 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (63847581240 / 1000000000000) (63847581241 / 1000000000000), orderedInterval (17473430940 / 1000000000000) (17473430941 / 1000000000000)))) (orderedInterval (-27839390944 / 1000000000000) (-27839390903 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (13673963775490039 / 128000000000000) 4 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (55265109999 / 1000000000000) (55265110000 / 1000000000000), orderedInterval (53640058606 / 1000000000000) (53640058607 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (23430569994548947 / 128000000000000) 4 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (58890531707 / 1000000000000) (58890531836 / 1000000000000), orderedInterval (-3277501346 / 1000000000000) (-3277501218 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (17258851810052473 / 128000000000000) 4 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-34782057637 / 1000000000000) (-34782057636 / 1000000000000), orderedInterval (-59130659606 / 1000000000000) (-59130659605 / 1000000000000)))) (orderedInterval (-31706835634 / 1000000000000) (-31706835518 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate207_chunkChecks4_1 :
    compactCertificate207.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (26479516989549079 / 128000000000000) 4 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (16970637370 / 1000000000000) (16970637371 / 1000000000000), orderedInterval (52773536013 / 1000000000000) (52773536014 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (15287956261925791 / 128000000000000) 4 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (54412823070 / 1000000000000) (54412823071 / 1000000000000), orderedInterval (48448745772 / 1000000000000) (48448745773 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (27128746664791019 / 128000000000000) 4 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-42936618771 / 1000000000000) (-42936511761 / 1000000000000), orderedInterval (34162587293 / 1000000000000) (34162694303 / 1000000000000)))) (orderedInterval (-233128139139 / 1000000000000) (-233127715421 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (25347194182709111 / 128000000000000) 4 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-44037617173 / 1000000000000) (-44037617172 / 1000000000000), orderedInterval (-35603404466 / 1000000000000) (-35603404465 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (18088953793217063 / 128000000000000) 4 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-44898398920 / 1000000000000) (-44898398919 / 1000000000000), orderedInterval (-49730510313 / 1000000000000) (-49730510312 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (20510945663226177 / 128000000000000) 4 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-45441161715 / 1000000000000) (-45441161714 / 1000000000000), orderedInterval (-43538534269 / 1000000000000) (-43538534268 / 1000000000000)))) (orderedInterval (-4557680031 / 1000000000000) (-4557679942 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (17099888120417713 / 128000000000000) 4 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (45056948524 / 1000000000000) (45056981241 / 1000000000000), orderedInterval (-52468236990 / 1000000000000) (-52468204274 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (15108269741967973 / 128000000000000) 4 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-39186173702 / 1000000000000) (-39186165195 / 1000000000000), orderedInterval (62278974939 / 1000000000000) (62278983446 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (4378965444321327 / 25600000000000) 4 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (49608765125 / 1000000000000) (49608824119 / 1000000000000), orderedInterval (-35651712320 / 1000000000000) (-35651653325 / 1000000000000)))) (orderedInterval (22719641449 / 1000000000000) (22719662331 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate207_chunkChecks4_2 :
    compactCertificate207.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (12112448871318269 / 128000000000000) 4 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (75353776044 / 1000000000000) (75353776045 / 1000000000000), orderedInterval (31994947862 / 1000000000000) (31994947863 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (10267857049914709 / 128000000000000) 4 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-56011119020 / 1000000000000) (-56011087693 / 1000000000000), orderedInterval (69623514583 / 1000000000000) (69623545909 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (6425148189947527 / 128000000000000) 4 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (73737852137 / 1000000000000) (73737852138 / 1000000000000), orderedInterval (84385374330 / 1000000000000) (84385374331 / 1000000000000)))) (orderedInterval (-11348523764 / 1000000000000) (-11348522717 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (3455466065631609 / 128000000000000) 4 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (73311068152 / 1000000000000) (73311074917 / 1000000000000), orderedInterval (-136301188544 / 1000000000000) (-136301181779 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (9382262552081827 / 128000000000000) 4 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-90175539947 / 1000000000000) (-90175539084 / 1000000000000), orderedInterval (24140601099 / 1000000000000) (24140601962 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (12810677400570179 / 128000000000000) 4 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (26341483456 / 1000000000000) (26341483457 / 1000000000000), orderedInterval (75148415914 / 1000000000000) (75148415915 / 1000000000000)))) (orderedInterval (-2130291598 / 1000000000000) (-2130291578 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (5416851810052473 / 128000000000000) 4 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-94583183115 / 1000000000000) (-94583121063 / 1000000000000), orderedInterval (79201423183 / 1000000000000) (79201485236 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (22019201873243033 / 128000000000000) 4 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-1343718077 / 1000000000000) (-1343718074 / 1000000000000), orderedInterval (-60815084662 / 1000000000000) (-60815084659 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (14707806392033047 / 128000000000000) 4 (IntervalRat.scale (5921 / 64) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (38897899500 / 1000000000000) (38897907079 / 1000000000000), orderedInterval (-63630986818 / 1000000000000) (-63630979239 / 1000000000000)))) (orderedInterval (-14896787853 / 1000000000000) (-14896784259 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate207_chunkChecks4 :
    compactCertificate207.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate207.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate207_chunkChecks4_0
    compactCertificate207_chunkChecks4_1 compactCertificate207_chunkChecks4_2

theorem compactCertificate207_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate207.chunkCheck r b = true :=
  compactCertificate207.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate207_chunkChecks0
    · exact compactCertificate207_chunkChecks1
    · exact compactCertificate207_chunkChecks2
    · exact compactCertificate207_chunkChecks3
    · exact compactCertificate207_chunkChecks4)

theorem compactCertificate207_coefficient0 :
    compactCertificate207.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate207, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate207_coefficient1 :
    compactCertificate207.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate207, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate207_coefficient2 :
    compactCertificate207.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate207, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate207_coefficient3 :
    compactCertificate207.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate207, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate207_coefficient4 :
    compactCertificate207.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate207, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate207_coefficients : ∀ r : Fin 5,
    compactCertificate207.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate207_coefficient0
  · exact compactCertificate207_coefficient1
  · exact compactCertificate207_coefficient2
  · exact compactCertificate207_coefficient3
  · exact compactCertificate207_coefficient4

theorem compactCertificate207_lower : (1 : ℚ) ≤ compactCertificate207.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate207, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate207_proves {t : ℝ} (ht : t ∈ compactCertificate207.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate207.proves compactCertificate207_states compactCertificate207_chunks
    compactCertificate207_coefficients compactCertificate207_lower ht

end Erdos232
