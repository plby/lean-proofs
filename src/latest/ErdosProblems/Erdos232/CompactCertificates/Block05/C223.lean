/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate223 : CompactCertificate where
  left := 102
  right := 103
  center := 205 / 2
  grid := fun i =>
    match i.val with
    | 0 => 33
    | 1 => 24
    | 2 => 39
    | 3 => 7
    | 4 => 19
    | 5 => 51
    | 6 => 38
    | 7 => 65
    | 8 => 48
    | 9 => 73
    | 10 => 42
    | 11 => 75
    | 12 => 70
    | 13 => 50
    | 14 => 57
    | 15 => 47
    | 16 => 42
    | 17 => 60
    | 18 => 33
    | 19 => 28
    | 20 => 18
    | 21 => 10
    | 22 => 26
    | 23 => 35
    | 24 => 15
    | 25 => 61
    | _ => 41
  point := fun i =>
    match i.val with
    | 0 => 205 / 2
    | 1 => 60400828863941 / 800000000000
    | 2 => 19532387041253 / 160000000000
    | 3 => 17624811220687 / 800000000000
    | 4 => 47342722073539 / 800000000000
    | 5 => 128544699900663 / 800000000000
    | 6 => 94685444147119 / 800000000000
    | 7 => 162245122407787 / 800000000000
    | 8 => 119509022836033 / 800000000000
    | 9 => 183357574154959 / 800000000000
    | 10 => 105861544796311 / 800000000000
    | 11 => 187853168933699 / 800000000000
    | 12 => 175516798090031 / 800000000000
    | 13 => 125257068995423 / 800000000000
    | 14 => 142028166220617 / 800000000000
    | 15 => 118408277814073 / 800000000000
    | 16 => 104617304411533 / 800000000000
    | 17 => 30322172473767 / 160000000000
    | 18 => 83872724830949 / 800000000000
    | 19 => 71099837704189 / 800000000000
    | 20 => 44490977163967 / 800000000000
    | 21 => 23927395489089 / 800000000000
    | 22 => 64967533294267 / 800000000000
    | 23 => 88707612468059 / 800000000000
    | 24 => 37509022836033 / 800000000000
    | 25 => 152472095389793 / 800000000000
    | _ => 101844293543887 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (29844043106 / 1000000000000) (29844044509 / 1000000000000), orderedInterval (-73086035464 / 1000000000000) (-73086034062 / 1000000000000))
    | 1 => (orderedInterval (71154747041 / 1000000000000) (71154747042 / 1000000000000), orderedInterval (57571021780 / 1000000000000) (57571021781 / 1000000000000))
    | 2 => (orderedInterval (-24060588782 / 1000000000000) (-24060588781 / 1000000000000), orderedInterval (-67989689707 / 1000000000000) (-67989689706 / 1000000000000))
    | 3 => (orderedInterval (-124224495744 / 1000000000000) (-124224495743 / 1000000000000), orderedInterval (-113217881087 / 1000000000000) (-113217881086 / 1000000000000))
    | 4 => (orderedInterval (-27807385542 / 1000000000000) (-27807385541 / 1000000000000), orderedInterval (-99688616738 / 1000000000000) (-99688616737 / 1000000000000))
    | 5 => (orderedInterval (-59618530387 / 1000000000000) (-59618530386 / 1000000000000), orderedInterval (-20004306456 / 1000000000000) (-20004306455 / 1000000000000))
    | 6 => (orderedInterval (-17388506408 / 1000000000000) (-17388506210 / 1000000000000), orderedInterval (71323024546 / 1000000000000) (71323024744 / 1000000000000))
    | 7 => (orderedInterval (32203392458 / 1000000000000) (32203401582 / 1000000000000), orderedInterval (-45926929214 / 1000000000000) (-45926920090 / 1000000000000))
    | 8 => (orderedInterval (-38227599452 / 1000000000000) (-38227585881 / 1000000000000), orderedInterval (53045107210 / 1000000000000) (53045120781 / 1000000000000))
    | 9 => (orderedInterval (-31708388142 / 1000000000000) (-31708388141 / 1000000000000), orderedInterval (-42028213104 / 1000000000000) (-42028213103 / 1000000000000))
    | 10 => (orderedInterval (63714050797 / 1000000000000) (63714050798 / 1000000000000), orderedInterval (27171986173 / 1000000000000) (27171986174 / 1000000000000))
    | 11 => (orderedInterval (943534963 / 1000000000000) (943534966 / 1000000000000), orderedInterval (-52062105457 / 1000000000000) (-52062105454 / 1000000000000))
    | 12 => (orderedInterval (14333847595 / 1000000000000) (14333847596 / 1000000000000), orderedInterval (51892664719 / 1000000000000) (51892664720 / 1000000000000))
    | 13 => (orderedInterval (17395181793 / 1000000000000) (17395181794 / 1000000000000), orderedInterval (61291250382 / 1000000000000) (61291250383 / 1000000000000))
    | 14 => (orderedInterval (40856448580 / 1000000000000) (40856486971 / 1000000000000), orderedInterval (-43894404364 / 1000000000000) (-43894365973 / 1000000000000))
    | 15 => (orderedInterval (-59592382191 / 1000000000000) (-59592382190 / 1000000000000), orderedInterval (-27183289298 / 1000000000000) (-27183289297 / 1000000000000))
    | 16 => (orderedInterval (-26579357474 / 1000000000000) (-26579356249 / 1000000000000), orderedInterval (64613192098 / 1000000000000) (64613193323 / 1000000000000))
    | 17 => (orderedInterval (56406483484 / 1000000000000) (56406484785 / 1000000000000), orderedInterval (-13472800452 / 1000000000000) (-13472799150 / 1000000000000))
    | 18 => (orderedInterval (-72314500272 / 1000000000000) (-72314495969 / 1000000000000), orderedInterval (29376048144 / 1000000000000) (29376052447 / 1000000000000))
    | 19 => (orderedInterval (83990923714 / 1000000000000) (83990923891 / 1000000000000), orderedInterval (-10889938649 / 1000000000000) (-10889938472 / 1000000000000))
    | 20 => (orderedInterval (-16178187281 / 1000000000000) (-16178187191 / 1000000000000), orderedInterval (105908752681 / 1000000000000) (105908752771 / 1000000000000))
    | 21 => (orderedInterval (-96791058203 / 1000000000000) (-96791000521 / 1000000000000), orderedInterval (110782159082 / 1000000000000) (110782216764 / 1000000000000))
    | 22 => (orderedInterval (27166818918 / 1000000000000) (27166818919 / 1000000000000), orderedInterval (84102074898 / 1000000000000) (84102074899 / 1000000000000))
    | 23 => (orderedInterval (-75005599077 / 1000000000000) (-75005598814 / 1000000000000), orderedInterval (11080210121 / 1000000000000) (11080210384 / 1000000000000))
    | 24 => (orderedInterval (-60418790004 / 1000000000000) (-60418790003 / 1000000000000), orderedInterval (-98994515145 / 1000000000000) (-98994515144 / 1000000000000))
    | 25 => (orderedInterval (14985811762 / 1000000000000) (14985811927 / 1000000000000), orderedInterval (-55857691873 / 1000000000000) (-55857691707 / 1000000000000))
    | _ => (orderedInterval (46389862438 / 1000000000000) (46389897465 / 1000000000000), orderedInterval (-53555561952 / 1000000000000) (-53555526926 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (11080255356 / 1000000000000) (11080255920 / 1000000000000)
      | 1 => orderedInterval (4570711421 / 1000000000000) (4570711435 / 1000000000000)
      | 2 => orderedInterval (-1917167410 / 1000000000000) (-1917166794 / 1000000000000)
      | 3 => orderedInterval (10489013620 / 1000000000000) (10489013662 / 1000000000000)
      | 4 => orderedInterval (1179410698 / 1000000000000) (1179410905 / 1000000000000)
      | 5 => orderedInterval (2277123848 / 1000000000000) (2277123962 / 1000000000000)
      | 6 => orderedInterval (6281973471 / 1000000000000) (6281974199 / 1000000000000)
      | 7 => orderedInterval (6919271608 / 1000000000000) (6919272706 / 1000000000000)
      | _ => orderedInterval (-10288071368 / 1000000000000) (-10288064753 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-33325343560 / 1000000000000) (-33325342995 / 1000000000000)
      | 1 => orderedInterval (391879711 / 1000000000000) (391879725 / 1000000000000)
      | 2 => orderedInterval (4671239110 / 1000000000000) (4671240156 / 1000000000000)
      | 3 => orderedInterval (2343056929 / 1000000000000) (2343057015 / 1000000000000)
      | 4 => orderedInterval (7232867993 / 1000000000000) (7232868351 / 1000000000000)
      | 5 => orderedInterval (-5808546070 / 1000000000000) (-5808545904 / 1000000000000)
      | 6 => orderedInterval (-2399112220 / 1000000000000) (-2399111481 / 1000000000000)
      | 7 => orderedInterval (-3027233559 / 1000000000000) (-3027233214 / 1000000000000)
      | _ => orderedInterval (20661822188 / 1000000000000) (20661830416 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-9860993551 / 1000000000000) (-9860992980 / 1000000000000)
      | 1 => orderedInterval (-10142868955 / 1000000000000) (-10142868934 / 1000000000000)
      | 2 => orderedInterval (5805398136 / 1000000000000) (5805399963 / 1000000000000)
      | 3 => orderedInterval (-36765593682 / 1000000000000) (-36765593498 / 1000000000000)
      | 4 => orderedInterval (-2102921336 / 1000000000000) (-2102920716 / 1000000000000)
      | 5 => orderedInterval (-5921336385 / 1000000000000) (-5921336133 / 1000000000000)
      | 6 => orderedInterval (-8344223485 / 1000000000000) (-8344222726 / 1000000000000)
      | 7 => orderedInterval (-6463000691 / 1000000000000) (-6463000562 / 1000000000000)
      | _ => orderedInterval (17518755065 / 1000000000000) (17518765388 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (35587632533 / 1000000000000) (35587633106 / 1000000000000)
      | 1 => orderedInterval (-4691086644 / 1000000000000) (-4691086614 / 1000000000000)
      | 2 => orderedInterval (-14997532913 / 1000000000000) (-14997529667 / 1000000000000)
      | 3 => orderedInterval (1515105269 / 1000000000000) (1515105673 / 1000000000000)
      | 4 => orderedInterval (-12603869802 / 1000000000000) (-12603868730 / 1000000000000)
      | 5 => orderedInterval (10861375013 / 1000000000000) (10861375405 / 1000000000000)
      | 6 => orderedInterval (4154892769 / 1000000000000) (4154893542 / 1000000000000)
      | 7 => orderedInterval (2137580944 / 1000000000000) (2137581009 / 1000000000000)
      | _ => orderedInterval (-48594638718 / 1000000000000) (-48594625851 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (8488152469 / 1000000000000) (8488153050 / 1000000000000)
      | 1 => orderedInterval (25575264559 / 1000000000000) (25575264605 / 1000000000000)
      | 2 => orderedInterval (-19098299768 / 1000000000000) (-19098293853 / 1000000000000)
      | 3 => orderedInterval (157629277072 / 1000000000000) (157629277968 / 1000000000000)
      | 4 => orderedInterval (1909008422 / 1000000000000) (1909010288 / 1000000000000)
      | 5 => orderedInterval (17702763060 / 1000000000000) (17702763695 / 1000000000000)
      | 6 => orderedInterval (9841040444 / 1000000000000) (9841041240 / 1000000000000)
      | 7 => orderedInterval (7600614083 / 1000000000000) (7600614132 / 1000000000000)
      | _ => orderedInterval (-34359595692 / 1000000000000) (-34359579503 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (30592521244 / 1000000000000) (30592531242 / 1000000000000)
    | 1 => orderedInterval (-9259369478 / 1000000000000) (-9259357931 / 1000000000000)
    | 2 => orderedInterval (-56276784884 / 1000000000000) (-56276770198 / 1000000000000)
    | 3 => orderedInterval (-26630541549 / 1000000000000) (-26630522127 / 1000000000000)
    | _ => orderedInterval (175288224649 / 1000000000000) (175288251622 / 1000000000000)

theorem compactCertificate223_stateChecks0 :
    compactCertificate223.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (205 / 2)) (orderedInterval (29844043106 / 1000000000000) (29844044509 / 1000000000000), orderedInterval (-73086035464 / 1000000000000) (-73086034062 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 24 12 (60400828863941 / 800000000000)) (orderedInterval (71154747041 / 1000000000000) (71154747042 / 1000000000000), orderedInterval (57571021780 / 1000000000000) (57571021781 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (19532387041253 / 160000000000)) (orderedInterval (-24060588782 / 1000000000000) (-24060588781 / 1000000000000), orderedInterval (-67989689707 / 1000000000000) (-67989689706 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState015, besselGridState018, besselGridState019, besselGridState024, besselGridState026, besselGridState028, besselGridState033, besselGridState035, besselGridState038, besselGridState039, besselGridState041, besselGridState042, besselGridState047, besselGridState048, besselGridState050, besselGridState051, besselGridState057, besselGridState060, besselGridState061, besselGridState065, besselGridState070, besselGridState073, besselGridState075, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate223_stateChecks1 :
    compactCertificate223.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 7 12 (17624811220687 / 800000000000)) (orderedInterval (-124224495744 / 1000000000000) (-124224495743 / 1000000000000), orderedInterval (-113217881087 / 1000000000000) (-113217881086 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 19 12 (47342722073539 / 800000000000)) (orderedInterval (-27807385542 / 1000000000000) (-27807385541 / 1000000000000), orderedInterval (-99688616738 / 1000000000000) (-99688616737 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (128544699900663 / 800000000000)) (orderedInterval (-59618530387 / 1000000000000) (-59618530386 / 1000000000000), orderedInterval (-20004306456 / 1000000000000) (-20004306455 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState015, besselGridState018, besselGridState019, besselGridState024, besselGridState026, besselGridState028, besselGridState033, besselGridState035, besselGridState038, besselGridState039, besselGridState041, besselGridState042, besselGridState047, besselGridState048, besselGridState050, besselGridState051, besselGridState057, besselGridState060, besselGridState061, besselGridState065, besselGridState070, besselGridState073, besselGridState075, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate223_stateChecks2 :
    compactCertificate223.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (94685444147119 / 800000000000)) (orderedInterval (-17388506408 / 1000000000000) (-17388506210 / 1000000000000), orderedInterval (71323024546 / 1000000000000) (71323024744 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (162245122407787 / 800000000000)) (orderedInterval (32203392458 / 1000000000000) (32203401582 / 1000000000000), orderedInterval (-45926929214 / 1000000000000) (-45926920090 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (119509022836033 / 800000000000)) (orderedInterval (-38227599452 / 1000000000000) (-38227585881 / 1000000000000), orderedInterval (53045107210 / 1000000000000) (53045120781 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState015, besselGridState018, besselGridState019, besselGridState024, besselGridState026, besselGridState028, besselGridState033, besselGridState035, besselGridState038, besselGridState039, besselGridState041, besselGridState042, besselGridState047, besselGridState048, besselGridState050, besselGridState051, besselGridState057, besselGridState060, besselGridState061, besselGridState065, besselGridState070, besselGridState073, besselGridState075, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate223_stateChecks3 :
    compactCertificate223.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (183357574154959 / 800000000000)) (orderedInterval (-31708388142 / 1000000000000) (-31708388141 / 1000000000000), orderedInterval (-42028213104 / 1000000000000) (-42028213103 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (105861544796311 / 800000000000)) (orderedInterval (63714050797 / 1000000000000) (63714050798 / 1000000000000), orderedInterval (27171986173 / 1000000000000) (27171986174 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (187853168933699 / 800000000000)) (orderedInterval (943534963 / 1000000000000) (943534966 / 1000000000000), orderedInterval (-52062105457 / 1000000000000) (-52062105454 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState015, besselGridState018, besselGridState019, besselGridState024, besselGridState026, besselGridState028, besselGridState033, besselGridState035, besselGridState038, besselGridState039, besselGridState041, besselGridState042, besselGridState047, besselGridState048, besselGridState050, besselGridState051, besselGridState057, besselGridState060, besselGridState061, besselGridState065, besselGridState070, besselGridState073, besselGridState075, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate223_stateChecks4 :
    compactCertificate223.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (175516798090031 / 800000000000)) (orderedInterval (14333847595 / 1000000000000) (14333847596 / 1000000000000), orderedInterval (51892664719 / 1000000000000) (51892664720 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (125257068995423 / 800000000000)) (orderedInterval (17395181793 / 1000000000000) (17395181794 / 1000000000000), orderedInterval (61291250382 / 1000000000000) (61291250383 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (142028166220617 / 800000000000)) (orderedInterval (40856448580 / 1000000000000) (40856486971 / 1000000000000), orderedInterval (-43894404364 / 1000000000000) (-43894365973 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState015, besselGridState018, besselGridState019, besselGridState024, besselGridState026, besselGridState028, besselGridState033, besselGridState035, besselGridState038, besselGridState039, besselGridState041, besselGridState042, besselGridState047, besselGridState048, besselGridState050, besselGridState051, besselGridState057, besselGridState060, besselGridState061, besselGridState065, besselGridState070, besselGridState073, besselGridState075, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate223_stateChecks5 :
    compactCertificate223.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (118408277814073 / 800000000000)) (orderedInterval (-59592382191 / 1000000000000) (-59592382190 / 1000000000000), orderedInterval (-27183289298 / 1000000000000) (-27183289297 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (104617304411533 / 800000000000)) (orderedInterval (-26579357474 / 1000000000000) (-26579356249 / 1000000000000), orderedInterval (64613192098 / 1000000000000) (64613193323 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (30322172473767 / 160000000000)) (orderedInterval (56406483484 / 1000000000000) (56406484785 / 1000000000000), orderedInterval (-13472800452 / 1000000000000) (-13472799150 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState015, besselGridState018, besselGridState019, besselGridState024, besselGridState026, besselGridState028, besselGridState033, besselGridState035, besselGridState038, besselGridState039, besselGridState041, besselGridState042, besselGridState047, besselGridState048, besselGridState050, besselGridState051, besselGridState057, besselGridState060, besselGridState061, besselGridState065, besselGridState070, besselGridState073, besselGridState075, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate223_stateChecks6 :
    compactCertificate223.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (83872724830949 / 800000000000)) (orderedInterval (-72314500272 / 1000000000000) (-72314495969 / 1000000000000), orderedInterval (29376048144 / 1000000000000) (29376052447 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 28 12 (71099837704189 / 800000000000)) (orderedInterval (83990923714 / 1000000000000) (83990923891 / 1000000000000), orderedInterval (-10889938649 / 1000000000000) (-10889938472 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 18 12 (44490977163967 / 800000000000)) (orderedInterval (-16178187281 / 1000000000000) (-16178187191 / 1000000000000), orderedInterval (105908752681 / 1000000000000) (105908752771 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState015, besselGridState018, besselGridState019, besselGridState024, besselGridState026, besselGridState028, besselGridState033, besselGridState035, besselGridState038, besselGridState039, besselGridState041, besselGridState042, besselGridState047, besselGridState048, besselGridState050, besselGridState051, besselGridState057, besselGridState060, besselGridState061, besselGridState065, besselGridState070, besselGridState073, besselGridState075, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate223_stateChecks7 :
    compactCertificate223.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 10 12 (23927395489089 / 800000000000)) (orderedInterval (-96791058203 / 1000000000000) (-96791000521 / 1000000000000), orderedInterval (110782159082 / 1000000000000) (110782216764 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (64967533294267 / 800000000000)) (orderedInterval (27166818918 / 1000000000000) (27166818919 / 1000000000000), orderedInterval (84102074898 / 1000000000000) (84102074899 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (88707612468059 / 800000000000)) (orderedInterval (-75005599077 / 1000000000000) (-75005598814 / 1000000000000), orderedInterval (11080210121 / 1000000000000) (11080210384 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState015, besselGridState018, besselGridState019, besselGridState024, besselGridState026, besselGridState028, besselGridState033, besselGridState035, besselGridState038, besselGridState039, besselGridState041, besselGridState042, besselGridState047, besselGridState048, besselGridState050, besselGridState051, besselGridState057, besselGridState060, besselGridState061, besselGridState065, besselGridState070, besselGridState073, besselGridState075, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate223_stateChecks8 :
    compactCertificate223.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 15 12 (37509022836033 / 800000000000)) (orderedInterval (-60418790004 / 1000000000000) (-60418790003 / 1000000000000), orderedInterval (-98994515145 / 1000000000000) (-98994515144 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (152472095389793 / 800000000000)) (orderedInterval (14985811762 / 1000000000000) (14985811927 / 1000000000000), orderedInterval (-55857691873 / 1000000000000) (-55857691707 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (101844293543887 / 800000000000)) (orderedInterval (46389862438 / 1000000000000) (46389897465 / 1000000000000), orderedInterval (-53555561952 / 1000000000000) (-53555526926 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState015, besselGridState018, besselGridState019, besselGridState024, besselGridState026, besselGridState028, besselGridState033, besselGridState035, besselGridState038, besselGridState039, besselGridState041, besselGridState042, besselGridState047, besselGridState048, besselGridState050, besselGridState051, besselGridState057, besselGridState060, besselGridState061, besselGridState065, besselGridState070, besselGridState073, besselGridState075, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate223_states : ∀ j,
    BesselStateValid (compactCertificate223.point j) (compactCertificate223.state j) :=
  compactCertificate223.statesValid_of_checks3 compactCertificate223_stateChecks0
    compactCertificate223_stateChecks1 compactCertificate223_stateChecks2
    compactCertificate223_stateChecks3 compactCertificate223_stateChecks4
    compactCertificate223_stateChecks5 compactCertificate223_stateChecks6
    compactCertificate223_stateChecks7 compactCertificate223_stateChecks8

theorem compactCertificate223_chunkChecks0_0 :
    compactCertificate223.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (205 / 2) 0 (IntervalRat.scale (205 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (29844043106 / 1000000000000) (29844044509 / 1000000000000), orderedInterval (-73086035464 / 1000000000000) (-73086034062 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (60400828863941 / 800000000000) 0 (IntervalRat.scale (205 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (71154747041 / 1000000000000) (71154747042 / 1000000000000), orderedInterval (57571021780 / 1000000000000) (57571021781 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (19532387041253 / 160000000000) 0 (IntervalRat.scale (205 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-24060588782 / 1000000000000) (-24060588781 / 1000000000000), orderedInterval (-67989689707 / 1000000000000) (-67989689706 / 1000000000000)))) (orderedInterval (11080255356 / 1000000000000) (11080255920 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (17624811220687 / 800000000000) 0 (IntervalRat.scale (205 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-124224495744 / 1000000000000) (-124224495743 / 1000000000000), orderedInterval (-113217881087 / 1000000000000) (-113217881086 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (47342722073539 / 800000000000) 0 (IntervalRat.scale (205 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-27807385542 / 1000000000000) (-27807385541 / 1000000000000), orderedInterval (-99688616738 / 1000000000000) (-99688616737 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (128544699900663 / 800000000000) 0 (IntervalRat.scale (205 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-59618530387 / 1000000000000) (-59618530386 / 1000000000000), orderedInterval (-20004306456 / 1000000000000) (-20004306455 / 1000000000000)))) (orderedInterval (4570711421 / 1000000000000) (4570711435 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (94685444147119 / 800000000000) 0 (IntervalRat.scale (205 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-17388506408 / 1000000000000) (-17388506210 / 1000000000000), orderedInterval (71323024546 / 1000000000000) (71323024744 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (162245122407787 / 800000000000) 0 (IntervalRat.scale (205 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (32203392458 / 1000000000000) (32203401582 / 1000000000000), orderedInterval (-45926929214 / 1000000000000) (-45926920090 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (119509022836033 / 800000000000) 0 (IntervalRat.scale (205 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-38227599452 / 1000000000000) (-38227585881 / 1000000000000), orderedInterval (53045107210 / 1000000000000) (53045120781 / 1000000000000)))) (orderedInterval (-1917167410 / 1000000000000) (-1917166794 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate223_chunkChecks0_1 :
    compactCertificate223.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (183357574154959 / 800000000000) 0 (IntervalRat.scale (205 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-31708388142 / 1000000000000) (-31708388141 / 1000000000000), orderedInterval (-42028213104 / 1000000000000) (-42028213103 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (105861544796311 / 800000000000) 0 (IntervalRat.scale (205 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (63714050797 / 1000000000000) (63714050798 / 1000000000000), orderedInterval (27171986173 / 1000000000000) (27171986174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (187853168933699 / 800000000000) 0 (IntervalRat.scale (205 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (943534963 / 1000000000000) (943534966 / 1000000000000), orderedInterval (-52062105457 / 1000000000000) (-52062105454 / 1000000000000)))) (orderedInterval (10489013620 / 1000000000000) (10489013662 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (175516798090031 / 800000000000) 0 (IntervalRat.scale (205 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (14333847595 / 1000000000000) (14333847596 / 1000000000000), orderedInterval (51892664719 / 1000000000000) (51892664720 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (125257068995423 / 800000000000) 0 (IntervalRat.scale (205 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17395181793 / 1000000000000) (17395181794 / 1000000000000), orderedInterval (61291250382 / 1000000000000) (61291250383 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (142028166220617 / 800000000000) 0 (IntervalRat.scale (205 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (40856448580 / 1000000000000) (40856486971 / 1000000000000), orderedInterval (-43894404364 / 1000000000000) (-43894365973 / 1000000000000)))) (orderedInterval (1179410698 / 1000000000000) (1179410905 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (118408277814073 / 800000000000) 0 (IntervalRat.scale (205 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-59592382191 / 1000000000000) (-59592382190 / 1000000000000), orderedInterval (-27183289298 / 1000000000000) (-27183289297 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (104617304411533 / 800000000000) 0 (IntervalRat.scale (205 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-26579357474 / 1000000000000) (-26579356249 / 1000000000000), orderedInterval (64613192098 / 1000000000000) (64613193323 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (30322172473767 / 160000000000) 0 (IntervalRat.scale (205 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (56406483484 / 1000000000000) (56406484785 / 1000000000000), orderedInterval (-13472800452 / 1000000000000) (-13472799150 / 1000000000000)))) (orderedInterval (2277123848 / 1000000000000) (2277123962 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate223_chunkChecks0_2 :
    compactCertificate223.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (83872724830949 / 800000000000) 0 (IntervalRat.scale (205 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-72314500272 / 1000000000000) (-72314495969 / 1000000000000), orderedInterval (29376048144 / 1000000000000) (29376052447 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (71099837704189 / 800000000000) 0 (IntervalRat.scale (205 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (83990923714 / 1000000000000) (83990923891 / 1000000000000), orderedInterval (-10889938649 / 1000000000000) (-10889938472 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (44490977163967 / 800000000000) 0 (IntervalRat.scale (205 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-16178187281 / 1000000000000) (-16178187191 / 1000000000000), orderedInterval (105908752681 / 1000000000000) (105908752771 / 1000000000000)))) (orderedInterval (6281973471 / 1000000000000) (6281974199 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (23927395489089 / 800000000000) 0 (IntervalRat.scale (205 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-96791058203 / 1000000000000) (-96791000521 / 1000000000000), orderedInterval (110782159082 / 1000000000000) (110782216764 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (64967533294267 / 800000000000) 0 (IntervalRat.scale (205 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (27166818918 / 1000000000000) (27166818919 / 1000000000000), orderedInterval (84102074898 / 1000000000000) (84102074899 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (88707612468059 / 800000000000) 0 (IntervalRat.scale (205 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-75005599077 / 1000000000000) (-75005598814 / 1000000000000), orderedInterval (11080210121 / 1000000000000) (11080210384 / 1000000000000)))) (orderedInterval (6919271608 / 1000000000000) (6919272706 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (37509022836033 / 800000000000) 0 (IntervalRat.scale (205 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-60418790004 / 1000000000000) (-60418790003 / 1000000000000), orderedInterval (-98994515145 / 1000000000000) (-98994515144 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (152472095389793 / 800000000000) 0 (IntervalRat.scale (205 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (14985811762 / 1000000000000) (14985811927 / 1000000000000), orderedInterval (-55857691873 / 1000000000000) (-55857691707 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (101844293543887 / 800000000000) 0 (IntervalRat.scale (205 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (46389862438 / 1000000000000) (46389897465 / 1000000000000), orderedInterval (-53555561952 / 1000000000000) (-53555526926 / 1000000000000)))) (orderedInterval (-10288071368 / 1000000000000) (-10288064753 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate223_chunkChecks0 :
    compactCertificate223.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate223.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate223_chunkChecks0_0
    compactCertificate223_chunkChecks0_1 compactCertificate223_chunkChecks0_2

theorem compactCertificate223_chunkChecks1_0 :
    compactCertificate223.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (205 / 2) 1 (IntervalRat.scale (205 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (29844043106 / 1000000000000) (29844044509 / 1000000000000), orderedInterval (-73086035464 / 1000000000000) (-73086034062 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (60400828863941 / 800000000000) 1 (IntervalRat.scale (205 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (71154747041 / 1000000000000) (71154747042 / 1000000000000), orderedInterval (57571021780 / 1000000000000) (57571021781 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (19532387041253 / 160000000000) 1 (IntervalRat.scale (205 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-24060588782 / 1000000000000) (-24060588781 / 1000000000000), orderedInterval (-67989689707 / 1000000000000) (-67989689706 / 1000000000000)))) (orderedInterval (-33325343560 / 1000000000000) (-33325342995 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (17624811220687 / 800000000000) 1 (IntervalRat.scale (205 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-124224495744 / 1000000000000) (-124224495743 / 1000000000000), orderedInterval (-113217881087 / 1000000000000) (-113217881086 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (47342722073539 / 800000000000) 1 (IntervalRat.scale (205 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-27807385542 / 1000000000000) (-27807385541 / 1000000000000), orderedInterval (-99688616738 / 1000000000000) (-99688616737 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (128544699900663 / 800000000000) 1 (IntervalRat.scale (205 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-59618530387 / 1000000000000) (-59618530386 / 1000000000000), orderedInterval (-20004306456 / 1000000000000) (-20004306455 / 1000000000000)))) (orderedInterval (391879711 / 1000000000000) (391879725 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (94685444147119 / 800000000000) 1 (IntervalRat.scale (205 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-17388506408 / 1000000000000) (-17388506210 / 1000000000000), orderedInterval (71323024546 / 1000000000000) (71323024744 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (162245122407787 / 800000000000) 1 (IntervalRat.scale (205 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (32203392458 / 1000000000000) (32203401582 / 1000000000000), orderedInterval (-45926929214 / 1000000000000) (-45926920090 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (119509022836033 / 800000000000) 1 (IntervalRat.scale (205 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-38227599452 / 1000000000000) (-38227585881 / 1000000000000), orderedInterval (53045107210 / 1000000000000) (53045120781 / 1000000000000)))) (orderedInterval (4671239110 / 1000000000000) (4671240156 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate223_chunkChecks1_1 :
    compactCertificate223.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (183357574154959 / 800000000000) 1 (IntervalRat.scale (205 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-31708388142 / 1000000000000) (-31708388141 / 1000000000000), orderedInterval (-42028213104 / 1000000000000) (-42028213103 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (105861544796311 / 800000000000) 1 (IntervalRat.scale (205 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (63714050797 / 1000000000000) (63714050798 / 1000000000000), orderedInterval (27171986173 / 1000000000000) (27171986174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (187853168933699 / 800000000000) 1 (IntervalRat.scale (205 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (943534963 / 1000000000000) (943534966 / 1000000000000), orderedInterval (-52062105457 / 1000000000000) (-52062105454 / 1000000000000)))) (orderedInterval (2343056929 / 1000000000000) (2343057015 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (175516798090031 / 800000000000) 1 (IntervalRat.scale (205 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (14333847595 / 1000000000000) (14333847596 / 1000000000000), orderedInterval (51892664719 / 1000000000000) (51892664720 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (125257068995423 / 800000000000) 1 (IntervalRat.scale (205 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17395181793 / 1000000000000) (17395181794 / 1000000000000), orderedInterval (61291250382 / 1000000000000) (61291250383 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (142028166220617 / 800000000000) 1 (IntervalRat.scale (205 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (40856448580 / 1000000000000) (40856486971 / 1000000000000), orderedInterval (-43894404364 / 1000000000000) (-43894365973 / 1000000000000)))) (orderedInterval (7232867993 / 1000000000000) (7232868351 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (118408277814073 / 800000000000) 1 (IntervalRat.scale (205 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-59592382191 / 1000000000000) (-59592382190 / 1000000000000), orderedInterval (-27183289298 / 1000000000000) (-27183289297 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (104617304411533 / 800000000000) 1 (IntervalRat.scale (205 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-26579357474 / 1000000000000) (-26579356249 / 1000000000000), orderedInterval (64613192098 / 1000000000000) (64613193323 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (30322172473767 / 160000000000) 1 (IntervalRat.scale (205 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (56406483484 / 1000000000000) (56406484785 / 1000000000000), orderedInterval (-13472800452 / 1000000000000) (-13472799150 / 1000000000000)))) (orderedInterval (-5808546070 / 1000000000000) (-5808545904 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate223_chunkChecks1_2 :
    compactCertificate223.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (83872724830949 / 800000000000) 1 (IntervalRat.scale (205 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-72314500272 / 1000000000000) (-72314495969 / 1000000000000), orderedInterval (29376048144 / 1000000000000) (29376052447 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (71099837704189 / 800000000000) 1 (IntervalRat.scale (205 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (83990923714 / 1000000000000) (83990923891 / 1000000000000), orderedInterval (-10889938649 / 1000000000000) (-10889938472 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (44490977163967 / 800000000000) 1 (IntervalRat.scale (205 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-16178187281 / 1000000000000) (-16178187191 / 1000000000000), orderedInterval (105908752681 / 1000000000000) (105908752771 / 1000000000000)))) (orderedInterval (-2399112220 / 1000000000000) (-2399111481 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (23927395489089 / 800000000000) 1 (IntervalRat.scale (205 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-96791058203 / 1000000000000) (-96791000521 / 1000000000000), orderedInterval (110782159082 / 1000000000000) (110782216764 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (64967533294267 / 800000000000) 1 (IntervalRat.scale (205 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (27166818918 / 1000000000000) (27166818919 / 1000000000000), orderedInterval (84102074898 / 1000000000000) (84102074899 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (88707612468059 / 800000000000) 1 (IntervalRat.scale (205 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-75005599077 / 1000000000000) (-75005598814 / 1000000000000), orderedInterval (11080210121 / 1000000000000) (11080210384 / 1000000000000)))) (orderedInterval (-3027233559 / 1000000000000) (-3027233214 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (37509022836033 / 800000000000) 1 (IntervalRat.scale (205 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-60418790004 / 1000000000000) (-60418790003 / 1000000000000), orderedInterval (-98994515145 / 1000000000000) (-98994515144 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (152472095389793 / 800000000000) 1 (IntervalRat.scale (205 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (14985811762 / 1000000000000) (14985811927 / 1000000000000), orderedInterval (-55857691873 / 1000000000000) (-55857691707 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (101844293543887 / 800000000000) 1 (IntervalRat.scale (205 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (46389862438 / 1000000000000) (46389897465 / 1000000000000), orderedInterval (-53555561952 / 1000000000000) (-53555526926 / 1000000000000)))) (orderedInterval (20661822188 / 1000000000000) (20661830416 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate223_chunkChecks1 :
    compactCertificate223.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate223.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate223_chunkChecks1_0
    compactCertificate223_chunkChecks1_1 compactCertificate223_chunkChecks1_2

theorem compactCertificate223_chunkChecks2_0 :
    compactCertificate223.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (205 / 2) 2 (IntervalRat.scale (205 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (29844043106 / 1000000000000) (29844044509 / 1000000000000), orderedInterval (-73086035464 / 1000000000000) (-73086034062 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (60400828863941 / 800000000000) 2 (IntervalRat.scale (205 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (71154747041 / 1000000000000) (71154747042 / 1000000000000), orderedInterval (57571021780 / 1000000000000) (57571021781 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (19532387041253 / 160000000000) 2 (IntervalRat.scale (205 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-24060588782 / 1000000000000) (-24060588781 / 1000000000000), orderedInterval (-67989689707 / 1000000000000) (-67989689706 / 1000000000000)))) (orderedInterval (-9860993551 / 1000000000000) (-9860992980 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (17624811220687 / 800000000000) 2 (IntervalRat.scale (205 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-124224495744 / 1000000000000) (-124224495743 / 1000000000000), orderedInterval (-113217881087 / 1000000000000) (-113217881086 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (47342722073539 / 800000000000) 2 (IntervalRat.scale (205 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-27807385542 / 1000000000000) (-27807385541 / 1000000000000), orderedInterval (-99688616738 / 1000000000000) (-99688616737 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (128544699900663 / 800000000000) 2 (IntervalRat.scale (205 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-59618530387 / 1000000000000) (-59618530386 / 1000000000000), orderedInterval (-20004306456 / 1000000000000) (-20004306455 / 1000000000000)))) (orderedInterval (-10142868955 / 1000000000000) (-10142868934 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (94685444147119 / 800000000000) 2 (IntervalRat.scale (205 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-17388506408 / 1000000000000) (-17388506210 / 1000000000000), orderedInterval (71323024546 / 1000000000000) (71323024744 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (162245122407787 / 800000000000) 2 (IntervalRat.scale (205 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (32203392458 / 1000000000000) (32203401582 / 1000000000000), orderedInterval (-45926929214 / 1000000000000) (-45926920090 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (119509022836033 / 800000000000) 2 (IntervalRat.scale (205 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-38227599452 / 1000000000000) (-38227585881 / 1000000000000), orderedInterval (53045107210 / 1000000000000) (53045120781 / 1000000000000)))) (orderedInterval (5805398136 / 1000000000000) (5805399963 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate223_chunkChecks2_1 :
    compactCertificate223.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (183357574154959 / 800000000000) 2 (IntervalRat.scale (205 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-31708388142 / 1000000000000) (-31708388141 / 1000000000000), orderedInterval (-42028213104 / 1000000000000) (-42028213103 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (105861544796311 / 800000000000) 2 (IntervalRat.scale (205 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (63714050797 / 1000000000000) (63714050798 / 1000000000000), orderedInterval (27171986173 / 1000000000000) (27171986174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (187853168933699 / 800000000000) 2 (IntervalRat.scale (205 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (943534963 / 1000000000000) (943534966 / 1000000000000), orderedInterval (-52062105457 / 1000000000000) (-52062105454 / 1000000000000)))) (orderedInterval (-36765593682 / 1000000000000) (-36765593498 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (175516798090031 / 800000000000) 2 (IntervalRat.scale (205 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (14333847595 / 1000000000000) (14333847596 / 1000000000000), orderedInterval (51892664719 / 1000000000000) (51892664720 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (125257068995423 / 800000000000) 2 (IntervalRat.scale (205 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17395181793 / 1000000000000) (17395181794 / 1000000000000), orderedInterval (61291250382 / 1000000000000) (61291250383 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (142028166220617 / 800000000000) 2 (IntervalRat.scale (205 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (40856448580 / 1000000000000) (40856486971 / 1000000000000), orderedInterval (-43894404364 / 1000000000000) (-43894365973 / 1000000000000)))) (orderedInterval (-2102921336 / 1000000000000) (-2102920716 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (118408277814073 / 800000000000) 2 (IntervalRat.scale (205 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-59592382191 / 1000000000000) (-59592382190 / 1000000000000), orderedInterval (-27183289298 / 1000000000000) (-27183289297 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (104617304411533 / 800000000000) 2 (IntervalRat.scale (205 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-26579357474 / 1000000000000) (-26579356249 / 1000000000000), orderedInterval (64613192098 / 1000000000000) (64613193323 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (30322172473767 / 160000000000) 2 (IntervalRat.scale (205 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (56406483484 / 1000000000000) (56406484785 / 1000000000000), orderedInterval (-13472800452 / 1000000000000) (-13472799150 / 1000000000000)))) (orderedInterval (-5921336385 / 1000000000000) (-5921336133 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate223_chunkChecks2_2 :
    compactCertificate223.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (83872724830949 / 800000000000) 2 (IntervalRat.scale (205 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-72314500272 / 1000000000000) (-72314495969 / 1000000000000), orderedInterval (29376048144 / 1000000000000) (29376052447 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (71099837704189 / 800000000000) 2 (IntervalRat.scale (205 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (83990923714 / 1000000000000) (83990923891 / 1000000000000), orderedInterval (-10889938649 / 1000000000000) (-10889938472 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (44490977163967 / 800000000000) 2 (IntervalRat.scale (205 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-16178187281 / 1000000000000) (-16178187191 / 1000000000000), orderedInterval (105908752681 / 1000000000000) (105908752771 / 1000000000000)))) (orderedInterval (-8344223485 / 1000000000000) (-8344222726 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (23927395489089 / 800000000000) 2 (IntervalRat.scale (205 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-96791058203 / 1000000000000) (-96791000521 / 1000000000000), orderedInterval (110782159082 / 1000000000000) (110782216764 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (64967533294267 / 800000000000) 2 (IntervalRat.scale (205 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (27166818918 / 1000000000000) (27166818919 / 1000000000000), orderedInterval (84102074898 / 1000000000000) (84102074899 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (88707612468059 / 800000000000) 2 (IntervalRat.scale (205 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-75005599077 / 1000000000000) (-75005598814 / 1000000000000), orderedInterval (11080210121 / 1000000000000) (11080210384 / 1000000000000)))) (orderedInterval (-6463000691 / 1000000000000) (-6463000562 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (37509022836033 / 800000000000) 2 (IntervalRat.scale (205 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-60418790004 / 1000000000000) (-60418790003 / 1000000000000), orderedInterval (-98994515145 / 1000000000000) (-98994515144 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (152472095389793 / 800000000000) 2 (IntervalRat.scale (205 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (14985811762 / 1000000000000) (14985811927 / 1000000000000), orderedInterval (-55857691873 / 1000000000000) (-55857691707 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (101844293543887 / 800000000000) 2 (IntervalRat.scale (205 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (46389862438 / 1000000000000) (46389897465 / 1000000000000), orderedInterval (-53555561952 / 1000000000000) (-53555526926 / 1000000000000)))) (orderedInterval (17518755065 / 1000000000000) (17518765388 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate223_chunkChecks2 :
    compactCertificate223.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate223.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate223_chunkChecks2_0
    compactCertificate223_chunkChecks2_1 compactCertificate223_chunkChecks2_2

theorem compactCertificate223_chunkChecks3_0 :
    compactCertificate223.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (205 / 2) 3 (IntervalRat.scale (205 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (29844043106 / 1000000000000) (29844044509 / 1000000000000), orderedInterval (-73086035464 / 1000000000000) (-73086034062 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (60400828863941 / 800000000000) 3 (IntervalRat.scale (205 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (71154747041 / 1000000000000) (71154747042 / 1000000000000), orderedInterval (57571021780 / 1000000000000) (57571021781 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (19532387041253 / 160000000000) 3 (IntervalRat.scale (205 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-24060588782 / 1000000000000) (-24060588781 / 1000000000000), orderedInterval (-67989689707 / 1000000000000) (-67989689706 / 1000000000000)))) (orderedInterval (35587632533 / 1000000000000) (35587633106 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (17624811220687 / 800000000000) 3 (IntervalRat.scale (205 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-124224495744 / 1000000000000) (-124224495743 / 1000000000000), orderedInterval (-113217881087 / 1000000000000) (-113217881086 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (47342722073539 / 800000000000) 3 (IntervalRat.scale (205 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-27807385542 / 1000000000000) (-27807385541 / 1000000000000), orderedInterval (-99688616738 / 1000000000000) (-99688616737 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (128544699900663 / 800000000000) 3 (IntervalRat.scale (205 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-59618530387 / 1000000000000) (-59618530386 / 1000000000000), orderedInterval (-20004306456 / 1000000000000) (-20004306455 / 1000000000000)))) (orderedInterval (-4691086644 / 1000000000000) (-4691086614 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (94685444147119 / 800000000000) 3 (IntervalRat.scale (205 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-17388506408 / 1000000000000) (-17388506210 / 1000000000000), orderedInterval (71323024546 / 1000000000000) (71323024744 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (162245122407787 / 800000000000) 3 (IntervalRat.scale (205 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (32203392458 / 1000000000000) (32203401582 / 1000000000000), orderedInterval (-45926929214 / 1000000000000) (-45926920090 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (119509022836033 / 800000000000) 3 (IntervalRat.scale (205 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-38227599452 / 1000000000000) (-38227585881 / 1000000000000), orderedInterval (53045107210 / 1000000000000) (53045120781 / 1000000000000)))) (orderedInterval (-14997532913 / 1000000000000) (-14997529667 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate223_chunkChecks3_1 :
    compactCertificate223.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (183357574154959 / 800000000000) 3 (IntervalRat.scale (205 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-31708388142 / 1000000000000) (-31708388141 / 1000000000000), orderedInterval (-42028213104 / 1000000000000) (-42028213103 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (105861544796311 / 800000000000) 3 (IntervalRat.scale (205 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (63714050797 / 1000000000000) (63714050798 / 1000000000000), orderedInterval (27171986173 / 1000000000000) (27171986174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (187853168933699 / 800000000000) 3 (IntervalRat.scale (205 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (943534963 / 1000000000000) (943534966 / 1000000000000), orderedInterval (-52062105457 / 1000000000000) (-52062105454 / 1000000000000)))) (orderedInterval (1515105269 / 1000000000000) (1515105673 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (175516798090031 / 800000000000) 3 (IntervalRat.scale (205 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (14333847595 / 1000000000000) (14333847596 / 1000000000000), orderedInterval (51892664719 / 1000000000000) (51892664720 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (125257068995423 / 800000000000) 3 (IntervalRat.scale (205 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17395181793 / 1000000000000) (17395181794 / 1000000000000), orderedInterval (61291250382 / 1000000000000) (61291250383 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (142028166220617 / 800000000000) 3 (IntervalRat.scale (205 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (40856448580 / 1000000000000) (40856486971 / 1000000000000), orderedInterval (-43894404364 / 1000000000000) (-43894365973 / 1000000000000)))) (orderedInterval (-12603869802 / 1000000000000) (-12603868730 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (118408277814073 / 800000000000) 3 (IntervalRat.scale (205 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-59592382191 / 1000000000000) (-59592382190 / 1000000000000), orderedInterval (-27183289298 / 1000000000000) (-27183289297 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (104617304411533 / 800000000000) 3 (IntervalRat.scale (205 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-26579357474 / 1000000000000) (-26579356249 / 1000000000000), orderedInterval (64613192098 / 1000000000000) (64613193323 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (30322172473767 / 160000000000) 3 (IntervalRat.scale (205 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (56406483484 / 1000000000000) (56406484785 / 1000000000000), orderedInterval (-13472800452 / 1000000000000) (-13472799150 / 1000000000000)))) (orderedInterval (10861375013 / 1000000000000) (10861375405 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate223_chunkChecks3_2 :
    compactCertificate223.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (83872724830949 / 800000000000) 3 (IntervalRat.scale (205 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-72314500272 / 1000000000000) (-72314495969 / 1000000000000), orderedInterval (29376048144 / 1000000000000) (29376052447 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (71099837704189 / 800000000000) 3 (IntervalRat.scale (205 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (83990923714 / 1000000000000) (83990923891 / 1000000000000), orderedInterval (-10889938649 / 1000000000000) (-10889938472 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (44490977163967 / 800000000000) 3 (IntervalRat.scale (205 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-16178187281 / 1000000000000) (-16178187191 / 1000000000000), orderedInterval (105908752681 / 1000000000000) (105908752771 / 1000000000000)))) (orderedInterval (4154892769 / 1000000000000) (4154893542 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (23927395489089 / 800000000000) 3 (IntervalRat.scale (205 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-96791058203 / 1000000000000) (-96791000521 / 1000000000000), orderedInterval (110782159082 / 1000000000000) (110782216764 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (64967533294267 / 800000000000) 3 (IntervalRat.scale (205 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (27166818918 / 1000000000000) (27166818919 / 1000000000000), orderedInterval (84102074898 / 1000000000000) (84102074899 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (88707612468059 / 800000000000) 3 (IntervalRat.scale (205 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-75005599077 / 1000000000000) (-75005598814 / 1000000000000), orderedInterval (11080210121 / 1000000000000) (11080210384 / 1000000000000)))) (orderedInterval (2137580944 / 1000000000000) (2137581009 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (37509022836033 / 800000000000) 3 (IntervalRat.scale (205 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-60418790004 / 1000000000000) (-60418790003 / 1000000000000), orderedInterval (-98994515145 / 1000000000000) (-98994515144 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (152472095389793 / 800000000000) 3 (IntervalRat.scale (205 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (14985811762 / 1000000000000) (14985811927 / 1000000000000), orderedInterval (-55857691873 / 1000000000000) (-55857691707 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (101844293543887 / 800000000000) 3 (IntervalRat.scale (205 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (46389862438 / 1000000000000) (46389897465 / 1000000000000), orderedInterval (-53555561952 / 1000000000000) (-53555526926 / 1000000000000)))) (orderedInterval (-48594638718 / 1000000000000) (-48594625851 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate223_chunkChecks3 :
    compactCertificate223.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate223.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate223_chunkChecks3_0
    compactCertificate223_chunkChecks3_1 compactCertificate223_chunkChecks3_2

theorem compactCertificate223_chunkChecks4_0 :
    compactCertificate223.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (205 / 2) 4 (IntervalRat.scale (205 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (29844043106 / 1000000000000) (29844044509 / 1000000000000), orderedInterval (-73086035464 / 1000000000000) (-73086034062 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (60400828863941 / 800000000000) 4 (IntervalRat.scale (205 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (71154747041 / 1000000000000) (71154747042 / 1000000000000), orderedInterval (57571021780 / 1000000000000) (57571021781 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (19532387041253 / 160000000000) 4 (IntervalRat.scale (205 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-24060588782 / 1000000000000) (-24060588781 / 1000000000000), orderedInterval (-67989689707 / 1000000000000) (-67989689706 / 1000000000000)))) (orderedInterval (8488152469 / 1000000000000) (8488153050 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (17624811220687 / 800000000000) 4 (IntervalRat.scale (205 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-124224495744 / 1000000000000) (-124224495743 / 1000000000000), orderedInterval (-113217881087 / 1000000000000) (-113217881086 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (47342722073539 / 800000000000) 4 (IntervalRat.scale (205 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-27807385542 / 1000000000000) (-27807385541 / 1000000000000), orderedInterval (-99688616738 / 1000000000000) (-99688616737 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (128544699900663 / 800000000000) 4 (IntervalRat.scale (205 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-59618530387 / 1000000000000) (-59618530386 / 1000000000000), orderedInterval (-20004306456 / 1000000000000) (-20004306455 / 1000000000000)))) (orderedInterval (25575264559 / 1000000000000) (25575264605 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (94685444147119 / 800000000000) 4 (IntervalRat.scale (205 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-17388506408 / 1000000000000) (-17388506210 / 1000000000000), orderedInterval (71323024546 / 1000000000000) (71323024744 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (162245122407787 / 800000000000) 4 (IntervalRat.scale (205 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (32203392458 / 1000000000000) (32203401582 / 1000000000000), orderedInterval (-45926929214 / 1000000000000) (-45926920090 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (119509022836033 / 800000000000) 4 (IntervalRat.scale (205 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-38227599452 / 1000000000000) (-38227585881 / 1000000000000), orderedInterval (53045107210 / 1000000000000) (53045120781 / 1000000000000)))) (orderedInterval (-19098299768 / 1000000000000) (-19098293853 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate223_chunkChecks4_1 :
    compactCertificate223.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (183357574154959 / 800000000000) 4 (IntervalRat.scale (205 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-31708388142 / 1000000000000) (-31708388141 / 1000000000000), orderedInterval (-42028213104 / 1000000000000) (-42028213103 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (105861544796311 / 800000000000) 4 (IntervalRat.scale (205 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (63714050797 / 1000000000000) (63714050798 / 1000000000000), orderedInterval (27171986173 / 1000000000000) (27171986174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (187853168933699 / 800000000000) 4 (IntervalRat.scale (205 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (943534963 / 1000000000000) (943534966 / 1000000000000), orderedInterval (-52062105457 / 1000000000000) (-52062105454 / 1000000000000)))) (orderedInterval (157629277072 / 1000000000000) (157629277968 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (175516798090031 / 800000000000) 4 (IntervalRat.scale (205 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (14333847595 / 1000000000000) (14333847596 / 1000000000000), orderedInterval (51892664719 / 1000000000000) (51892664720 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (125257068995423 / 800000000000) 4 (IntervalRat.scale (205 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17395181793 / 1000000000000) (17395181794 / 1000000000000), orderedInterval (61291250382 / 1000000000000) (61291250383 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (142028166220617 / 800000000000) 4 (IntervalRat.scale (205 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (40856448580 / 1000000000000) (40856486971 / 1000000000000), orderedInterval (-43894404364 / 1000000000000) (-43894365973 / 1000000000000)))) (orderedInterval (1909008422 / 1000000000000) (1909010288 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (118408277814073 / 800000000000) 4 (IntervalRat.scale (205 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-59592382191 / 1000000000000) (-59592382190 / 1000000000000), orderedInterval (-27183289298 / 1000000000000) (-27183289297 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (104617304411533 / 800000000000) 4 (IntervalRat.scale (205 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-26579357474 / 1000000000000) (-26579356249 / 1000000000000), orderedInterval (64613192098 / 1000000000000) (64613193323 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (30322172473767 / 160000000000) 4 (IntervalRat.scale (205 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (56406483484 / 1000000000000) (56406484785 / 1000000000000), orderedInterval (-13472800452 / 1000000000000) (-13472799150 / 1000000000000)))) (orderedInterval (17702763060 / 1000000000000) (17702763695 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate223_chunkChecks4_2 :
    compactCertificate223.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (83872724830949 / 800000000000) 4 (IntervalRat.scale (205 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-72314500272 / 1000000000000) (-72314495969 / 1000000000000), orderedInterval (29376048144 / 1000000000000) (29376052447 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (71099837704189 / 800000000000) 4 (IntervalRat.scale (205 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (83990923714 / 1000000000000) (83990923891 / 1000000000000), orderedInterval (-10889938649 / 1000000000000) (-10889938472 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (44490977163967 / 800000000000) 4 (IntervalRat.scale (205 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-16178187281 / 1000000000000) (-16178187191 / 1000000000000), orderedInterval (105908752681 / 1000000000000) (105908752771 / 1000000000000)))) (orderedInterval (9841040444 / 1000000000000) (9841041240 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (23927395489089 / 800000000000) 4 (IntervalRat.scale (205 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-96791058203 / 1000000000000) (-96791000521 / 1000000000000), orderedInterval (110782159082 / 1000000000000) (110782216764 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (64967533294267 / 800000000000) 4 (IntervalRat.scale (205 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (27166818918 / 1000000000000) (27166818919 / 1000000000000), orderedInterval (84102074898 / 1000000000000) (84102074899 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (88707612468059 / 800000000000) 4 (IntervalRat.scale (205 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-75005599077 / 1000000000000) (-75005598814 / 1000000000000), orderedInterval (11080210121 / 1000000000000) (11080210384 / 1000000000000)))) (orderedInterval (7600614083 / 1000000000000) (7600614132 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (37509022836033 / 800000000000) 4 (IntervalRat.scale (205 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-60418790004 / 1000000000000) (-60418790003 / 1000000000000), orderedInterval (-98994515145 / 1000000000000) (-98994515144 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (152472095389793 / 800000000000) 4 (IntervalRat.scale (205 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (14985811762 / 1000000000000) (14985811927 / 1000000000000), orderedInterval (-55857691873 / 1000000000000) (-55857691707 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (101844293543887 / 800000000000) 4 (IntervalRat.scale (205 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (46389862438 / 1000000000000) (46389897465 / 1000000000000), orderedInterval (-53555561952 / 1000000000000) (-53555526926 / 1000000000000)))) (orderedInterval (-34359595692 / 1000000000000) (-34359579503 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate223_chunkChecks4 :
    compactCertificate223.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate223.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate223_chunkChecks4_0
    compactCertificate223_chunkChecks4_1 compactCertificate223_chunkChecks4_2

theorem compactCertificate223_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate223.chunkCheck r b = true :=
  compactCertificate223.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate223_chunkChecks0
    · exact compactCertificate223_chunkChecks1
    · exact compactCertificate223_chunkChecks2
    · exact compactCertificate223_chunkChecks3
    · exact compactCertificate223_chunkChecks4)

theorem compactCertificate223_coefficient0 :
    compactCertificate223.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate223, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate223_coefficient1 :
    compactCertificate223.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate223, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate223_coefficient2 :
    compactCertificate223.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate223, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate223_coefficient3 :
    compactCertificate223.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate223, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate223_coefficient4 :
    compactCertificate223.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate223, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate223_coefficients : ∀ r : Fin 5,
    compactCertificate223.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate223_coefficient0
  · exact compactCertificate223_coefficient1
  · exact compactCertificate223_coefficient2
  · exact compactCertificate223_coefficient3
  · exact compactCertificate223_coefficient4

theorem compactCertificate223_lower : (1 : ℚ) ≤ compactCertificate223.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate223, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate223_proves {t : ℝ} (ht : t ∈ compactCertificate223.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate223.proves compactCertificate223_states compactCertificate223_chunks
    compactCertificate223_coefficients compactCertificate223_lower ht

end Erdos232
