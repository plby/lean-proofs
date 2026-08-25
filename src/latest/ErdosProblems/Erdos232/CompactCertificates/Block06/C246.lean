/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate246 : CompactCertificate where
  left := 121
  right := 122
  center := 243 / 2
  grid := fun i =>
    match i.val with
    | 0 => 39
    | 1 => 29
    | 2 => 46
    | 3 => 8
    | 4 => 22
    | 5 => 61
    | 6 => 45
    | 7 => 77
    | 8 => 56
    | 9 => 87
    | 10 => 50
    | 11 => 89
    | 12 => 83
    | 13 => 59
    | 14 => 67
    | 15 => 56
    | 16 => 49
    | 17 => 72
    | 18 => 40
    | 19 => 34
    | 20 => 21
    | 21 => 11
    | 22 => 31
    | 23 => 42
    | 24 => 18
    | 25 => 72
    | _ => 48
  point := fun i =>
    match i.val with
    | 0 => 243 / 2
    | 1 => 357985400339943 / 4000000000000
    | 2 => 115765123195719 / 800000000000
    | 3 => 104459246990901 / 4000000000000
    | 4 => 280592230826097 / 4000000000000
    | 5 => 761862489655149 / 4000000000000
    | 6 => 561184461652437 / 4000000000000
    | 7 => 961599140124201 / 4000000000000
    | 8 => 708309574369659 / 4000000000000
    | 9 => 1086729037064757 / 4000000000000
    | 10 => 627423302085453 / 4000000000000
    | 11 => 1113373659777777 / 4000000000000
    | 12 => 1040258095997013 / 4000000000000
    | 13 => 742377262582629 / 4000000000000
    | 14 => 841776692478291 / 4000000000000
    | 15 => 701785646556579 / 4000000000000
    | 16 => 620048901756159 / 4000000000000
    | 17 => 179714339295741 / 800000000000
    | 18 => 497099320339527 / 4000000000000
    | 19 => 421396599076047 / 4000000000000
    | 20 => 263690425630341 / 4000000000000
    | 21 => 141813587898747 / 4000000000000
    | 22 => 385051477817241 / 4000000000000
    | 23 => 525754873896057 / 4000000000000
    | 24 => 222309574369659 / 4000000000000
    | 25 => 903676077554139 / 4000000000000
    | _ => 603613739784501 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (17047506731 / 1000000000000) (17047506921 / 1000000000000), orderedInterval (-70419928379 / 1000000000000) (-70419928189 / 1000000000000))
    | 1 => (orderedInterval (61999545419 / 1000000000000) (61999652711 / 1000000000000), orderedInterval (-57525092321 / 1000000000000) (-57524985029 / 1000000000000))
    | 2 => (orderedInterval (54998974092 / 1000000000000) (54998974093 / 1000000000000), orderedInterval (36884108715 / 1000000000000) (36884108716 / 1000000000000))
    | 3 => (orderedInterval (153253940145 / 1000000000000) (153253940446 / 1000000000000), orderedInterval (-32712764871 / 1000000000000) (-32712764570 / 1000000000000))
    | 4 => (orderedInterval (92399288189 / 1000000000000) (92399288946 / 1000000000000), orderedInterval (-23843500842 / 1000000000000) (-23843500085 / 1000000000000))
    | 5 => (orderedInterval (21808221460 / 1000000000000) (21808222277 / 1000000000000), orderedInterval (-53600213335 / 1000000000000) (-53600212518 / 1000000000000))
    | 6 => (orderedInterval (19329911598 / 1000000000000) (19329911937 / 1000000000000), orderedInterval (-64598455552 / 1000000000000) (-64598455214 / 1000000000000))
    | 7 => (orderedInterval (33853576365 / 1000000000000) (33853597552 / 1000000000000), orderedInterval (-38827440085 / 1000000000000) (-38827418898 / 1000000000000))
    | 8 => (orderedInterval (56071355396 / 1000000000000) (56071360518 / 1000000000000), orderedInterval (-21398428317 / 1000000000000) (-21398423195 / 1000000000000))
    | 9 => (orderedInterval (36410800745 / 1000000000000) (36410862041 / 1000000000000), orderedInterval (-31965345444 / 1000000000000) (-31965284147 / 1000000000000))
    | 10 => (orderedInterval (33883246768 / 1000000000000) (33883246769 / 1000000000000), orderedInterval (53841642476 / 1000000000000) (53841642477 / 1000000000000))
    | 11 => (orderedInterval (21803085517 / 1000000000000) (21803086865 / 1000000000000), orderedInterval (-42604426935 / 1000000000000) (-42604425587 / 1000000000000))
    | 12 => (orderedInterval (-4804072835 / 1000000000000) (-4804072834 / 1000000000000), orderedInterval (-49233584605 / 1000000000000) (-49233584603 / 1000000000000))
    | 13 => (orderedInterval (-50060744236 / 1000000000000) (-50060744235 / 1000000000000), orderedInterval (-30263895267 / 1000000000000) (-30263895266 / 1000000000000))
    | 14 => (orderedInterval (-37178628846 / 1000000000000) (-37178628845 / 1000000000000), orderedInterval (-40444055659 / 1000000000000) (-40444055658 / 1000000000000))
    | 15 => (orderedInterval (17911208484 / 1000000000000) (17911208485 / 1000000000000), orderedInterval (57462187287 / 1000000000000) (57462187288 / 1000000000000))
    | 16 => (orderedInterval (-61445874249 / 1000000000000) (-61445872221 / 1000000000000), orderedInterval (18399489065 / 1000000000000) (18399491092 / 1000000000000))
    | 17 => (orderedInterval (-36939973304 / 1000000000000) (-36939937494 / 1000000000000), orderedInterval (38414413350 / 1000000000000) (38414449160 / 1000000000000))
    | 18 => (orderedInterval (-40677379601 / 1000000000000) (-40677367118 / 1000000000000), orderedInterval (59053739011 / 1000000000000) (59053751494 / 1000000000000))
    | 19 => (orderedInterval (-48927519498 / 1000000000000) (-48927491313 / 1000000000000), orderedInterval (60639682895 / 1000000000000) (60639711080 / 1000000000000))
    | 20 => (orderedInterval (-65727392505 / 1000000000000) (-65727392504 / 1000000000000), orderedInterval (-72556402473 / 1000000000000) (-72556402472 / 1000000000000))
    | 21 => (orderedInterval (-133229615425 / 1000000000000) (-133229615325 / 1000000000000), orderedInterval (16184190328 / 1000000000000) (16184190428 / 1000000000000))
    | 22 => (orderedInterval (27303975876 / 1000000000000) (27303976721 / 1000000000000), orderedInterval (-76744095150 / 1000000000000) (-76744094306 / 1000000000000))
    | 23 => (orderedInterval (18983586976 / 1000000000000) (18983586977 / 1000000000000), orderedInterval (66883931819 / 1000000000000) (66883931820 / 1000000000000))
    | 24 => (orderedInterval (-20015360163 / 1000000000000) (-20015360013 / 1000000000000), orderedInterval (105320290221 / 1000000000000) (105320290371 / 1000000000000))
    | 25 => (orderedInterval (25876984388 / 1000000000000) (25876984389 / 1000000000000), orderedInterval (46292451103 / 1000000000000) (46292451104 / 1000000000000))
    | _ => (orderedInterval (50535597479 / 1000000000000) (50535597480 / 1000000000000), orderedInterval (40635393773 / 1000000000000) (40635393774 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (10562152864 / 1000000000000) (10562153949 / 1000000000000)
      | 1 => orderedInterval (160624044 / 1000000000000) (160624148 / 1000000000000)
      | 2 => orderedInterval (310953631 / 1000000000000) (310954416 / 1000000000000)
      | 3 => orderedInterval (-859863754 / 1000000000000) (-859852622 / 1000000000000)
      | 4 => orderedInterval (-4459013840 / 1000000000000) (-4459013824 / 1000000000000)
      | 5 => orderedInterval (2777366572 / 1000000000000) (2777367617 / 1000000000000)
      | 6 => orderedInterval (7133524327 / 1000000000000) (7133527950 / 1000000000000)
      | 7 => orderedInterval (385778221 / 1000000000000) (385778257 / 1000000000000)
      | _ => orderedInterval (-11708910331 / 1000000000000) (-11708910295 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-25729025464 / 1000000000000) (-25729024641 / 1000000000000)
      | 1 => orderedInterval (5546944547 / 1000000000000) (5546944672 / 1000000000000)
      | 2 => orderedInterval (1615836479 / 1000000000000) (1615837965 / 1000000000000)
      | 3 => orderedInterval (3975862627 / 1000000000000) (3975887521 / 1000000000000)
      | 4 => orderedInterval (-2114564957 / 1000000000000) (-2114564932 / 1000000000000)
      | 5 => orderedInterval (1433327964 / 1000000000000) (1433329825 / 1000000000000)
      | 6 => orderedInterval (-13915465518 / 1000000000000) (-13915462064 / 1000000000000)
      | 7 => orderedInterval (-4252973572 / 1000000000000) (-4252973543 / 1000000000000)
      | _ => orderedInterval (-16185771310 / 1000000000000) (-16185771261 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-11436729800 / 1000000000000) (-11436729164 / 1000000000000)
      | 1 => orderedInterval (2716450102 / 1000000000000) (2716450279 / 1000000000000)
      | 2 => orderedInterval (1196080359 / 1000000000000) (1196083214 / 1000000000000)
      | 3 => orderedInterval (11865530569 / 1000000000000) (11865586451 / 1000000000000)
      | 4 => orderedInterval (10101357656 / 1000000000000) (10101357696 / 1000000000000)
      | 5 => orderedInterval (-2933464883 / 1000000000000) (-2933461518 / 1000000000000)
      | 6 => orderedInterval (-8142018702 / 1000000000000) (-8142015359 / 1000000000000)
      | 7 => orderedInterval (1917006292 / 1000000000000) (1917006318 / 1000000000000)
      | _ => orderedInterval (22067696138 / 1000000000000) (22067696209 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (24562049185 / 1000000000000) (24562049678 / 1000000000000)
      | 1 => orderedInterval (-14536875095 / 1000000000000) (-14536874830 / 1000000000000)
      | 2 => orderedInterval (-7685236168 / 1000000000000) (-7685230661 / 1000000000000)
      | 3 => orderedInterval (633586503 / 1000000000000) (633711504 / 1000000000000)
      | 4 => orderedInterval (337261400 / 1000000000000) (337261468 / 1000000000000)
      | 5 => orderedInterval (-6003645444 / 1000000000000) (-6003639341 / 1000000000000)
      | 6 => orderedInterval (12784786459 / 1000000000000) (12784789688 / 1000000000000)
      | 7 => orderedInterval (5614971885 / 1000000000000) (5614971909 / 1000000000000)
      | _ => orderedInterval (38589265911 / 1000000000000) (38589266020 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (13015833618 / 1000000000000) (13015834011 / 1000000000000)
      | 1 => orderedInterval (-8751641266 / 1000000000000) (-8751640854 / 1000000000000)
      | 2 => orderedInterval (-9762551059 / 1000000000000) (-9762540324 / 1000000000000)
      | 3 => orderedInterval (-69411107447 / 1000000000000) (-69410826807 / 1000000000000)
      | 4 => orderedInterval (-22264489180 / 1000000000000) (-22264489063 / 1000000000000)
      | 5 => orderedInterval (-738387439 / 1000000000000) (-738376257 / 1000000000000)
      | 6 => orderedInterval (8287660002 / 1000000000000) (8287663166 / 1000000000000)
      | 7 => orderedInterval (-2311117937 / 1000000000000) (-2311117915 / 1000000000000)
      | _ => orderedInterval (-48381153276 / 1000000000000) (-48381153101 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (4302611734 / 1000000000000) (4302629596 / 1000000000000)
    | 1 => orderedInterval (-49625829204 / 1000000000000) (-49625796458 / 1000000000000)
    | 2 => orderedInterval (27351907731 / 1000000000000) (27351974126 / 1000000000000)
    | 3 => orderedInterval (54296164636 / 1000000000000) (54296305435 / 1000000000000)
    | _ => orderedInterval (-140316953984 / 1000000000000) (-140316647144 / 1000000000000)

theorem compactCertificate246_stateChecks0 :
    compactCertificate246.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (243 / 2)) (orderedInterval (17047506731 / 1000000000000) (17047506921 / 1000000000000), orderedInterval (-70419928379 / 1000000000000) (-70419928189 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (357985400339943 / 4000000000000)) (orderedInterval (61999545419 / 1000000000000) (61999652711 / 1000000000000), orderedInterval (-57525092321 / 1000000000000) (-57524985029 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (115765123195719 / 800000000000)) (orderedInterval (54998974092 / 1000000000000) (54998974093 / 1000000000000), orderedInterval (36884108715 / 1000000000000) (36884108716 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState018, besselGridState021, besselGridState022, besselGridState029, besselGridState031, besselGridState034, besselGridState039, besselGridState040, besselGridState042, besselGridState045, besselGridState046, besselGridState048, besselGridState049, besselGridState050, besselGridState056, besselGridState059, besselGridState061, besselGridState067, besselGridState072, besselGridState077, besselGridState083, besselGridState087, besselGridState089, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate246_stateChecks1 :
    compactCertificate246.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 8 12 (104459246990901 / 4000000000000)) (orderedInterval (153253940145 / 1000000000000) (153253940446 / 1000000000000), orderedInterval (-32712764871 / 1000000000000) (-32712764570 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 22 12 (280592230826097 / 4000000000000)) (orderedInterval (92399288189 / 1000000000000) (92399288946 / 1000000000000), orderedInterval (-23843500842 / 1000000000000) (-23843500085 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (761862489655149 / 4000000000000)) (orderedInterval (21808221460 / 1000000000000) (21808222277 / 1000000000000), orderedInterval (-53600213335 / 1000000000000) (-53600212518 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState018, besselGridState021, besselGridState022, besselGridState029, besselGridState031, besselGridState034, besselGridState039, besselGridState040, besselGridState042, besselGridState045, besselGridState046, besselGridState048, besselGridState049, besselGridState050, besselGridState056, besselGridState059, besselGridState061, besselGridState067, besselGridState072, besselGridState077, besselGridState083, besselGridState087, besselGridState089, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate246_stateChecks2 :
    compactCertificate246.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (561184461652437 / 4000000000000)) (orderedInterval (19329911598 / 1000000000000) (19329911937 / 1000000000000), orderedInterval (-64598455552 / 1000000000000) (-64598455214 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (961599140124201 / 4000000000000)) (orderedInterval (33853576365 / 1000000000000) (33853597552 / 1000000000000), orderedInterval (-38827440085 / 1000000000000) (-38827418898 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (708309574369659 / 4000000000000)) (orderedInterval (56071355396 / 1000000000000) (56071360518 / 1000000000000), orderedInterval (-21398428317 / 1000000000000) (-21398423195 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState018, besselGridState021, besselGridState022, besselGridState029, besselGridState031, besselGridState034, besselGridState039, besselGridState040, besselGridState042, besselGridState045, besselGridState046, besselGridState048, besselGridState049, besselGridState050, besselGridState056, besselGridState059, besselGridState061, besselGridState067, besselGridState072, besselGridState077, besselGridState083, besselGridState087, besselGridState089, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate246_stateChecks3 :
    compactCertificate246.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (1086729037064757 / 4000000000000)) (orderedInterval (36410800745 / 1000000000000) (36410862041 / 1000000000000), orderedInterval (-31965345444 / 1000000000000) (-31965284147 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (627423302085453 / 4000000000000)) (orderedInterval (33883246768 / 1000000000000) (33883246769 / 1000000000000), orderedInterval (53841642476 / 1000000000000) (53841642477 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (1113373659777777 / 4000000000000)) (orderedInterval (21803085517 / 1000000000000) (21803086865 / 1000000000000), orderedInterval (-42604426935 / 1000000000000) (-42604425587 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState018, besselGridState021, besselGridState022, besselGridState029, besselGridState031, besselGridState034, besselGridState039, besselGridState040, besselGridState042, besselGridState045, besselGridState046, besselGridState048, besselGridState049, besselGridState050, besselGridState056, besselGridState059, besselGridState061, besselGridState067, besselGridState072, besselGridState077, besselGridState083, besselGridState087, besselGridState089, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate246_stateChecks4 :
    compactCertificate246.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (1040258095997013 / 4000000000000)) (orderedInterval (-4804072835 / 1000000000000) (-4804072834 / 1000000000000), orderedInterval (-49233584605 / 1000000000000) (-49233584603 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (742377262582629 / 4000000000000)) (orderedInterval (-50060744236 / 1000000000000) (-50060744235 / 1000000000000), orderedInterval (-30263895267 / 1000000000000) (-30263895266 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (841776692478291 / 4000000000000)) (orderedInterval (-37178628846 / 1000000000000) (-37178628845 / 1000000000000), orderedInterval (-40444055659 / 1000000000000) (-40444055658 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState018, besselGridState021, besselGridState022, besselGridState029, besselGridState031, besselGridState034, besselGridState039, besselGridState040, besselGridState042, besselGridState045, besselGridState046, besselGridState048, besselGridState049, besselGridState050, besselGridState056, besselGridState059, besselGridState061, besselGridState067, besselGridState072, besselGridState077, besselGridState083, besselGridState087, besselGridState089, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate246_stateChecks5 :
    compactCertificate246.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (701785646556579 / 4000000000000)) (orderedInterval (17911208484 / 1000000000000) (17911208485 / 1000000000000), orderedInterval (57462187287 / 1000000000000) (57462187288 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (620048901756159 / 4000000000000)) (orderedInterval (-61445874249 / 1000000000000) (-61445872221 / 1000000000000), orderedInterval (18399489065 / 1000000000000) (18399491092 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (179714339295741 / 800000000000)) (orderedInterval (-36939973304 / 1000000000000) (-36939937494 / 1000000000000), orderedInterval (38414413350 / 1000000000000) (38414449160 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState018, besselGridState021, besselGridState022, besselGridState029, besselGridState031, besselGridState034, besselGridState039, besselGridState040, besselGridState042, besselGridState045, besselGridState046, besselGridState048, besselGridState049, besselGridState050, besselGridState056, besselGridState059, besselGridState061, besselGridState067, besselGridState072, besselGridState077, besselGridState083, besselGridState087, besselGridState089, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate246_stateChecks6 :
    compactCertificate246.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (497099320339527 / 4000000000000)) (orderedInterval (-40677379601 / 1000000000000) (-40677367118 / 1000000000000), orderedInterval (59053739011 / 1000000000000) (59053751494 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (421396599076047 / 4000000000000)) (orderedInterval (-48927519498 / 1000000000000) (-48927491313 / 1000000000000), orderedInterval (60639682895 / 1000000000000) (60639711080 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 21 12 (263690425630341 / 4000000000000)) (orderedInterval (-65727392505 / 1000000000000) (-65727392504 / 1000000000000), orderedInterval (-72556402473 / 1000000000000) (-72556402472 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState018, besselGridState021, besselGridState022, besselGridState029, besselGridState031, besselGridState034, besselGridState039, besselGridState040, besselGridState042, besselGridState045, besselGridState046, besselGridState048, besselGridState049, besselGridState050, besselGridState056, besselGridState059, besselGridState061, besselGridState067, besselGridState072, besselGridState077, besselGridState083, besselGridState087, besselGridState089, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate246_stateChecks7 :
    compactCertificate246.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 11 12 (141813587898747 / 4000000000000)) (orderedInterval (-133229615425 / 1000000000000) (-133229615325 / 1000000000000), orderedInterval (16184190328 / 1000000000000) (16184190428 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (385051477817241 / 4000000000000)) (orderedInterval (27303975876 / 1000000000000) (27303976721 / 1000000000000), orderedInterval (-76744095150 / 1000000000000) (-76744094306 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (525754873896057 / 4000000000000)) (orderedInterval (18983586976 / 1000000000000) (18983586977 / 1000000000000), orderedInterval (66883931819 / 1000000000000) (66883931820 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState018, besselGridState021, besselGridState022, besselGridState029, besselGridState031, besselGridState034, besselGridState039, besselGridState040, besselGridState042, besselGridState045, besselGridState046, besselGridState048, besselGridState049, besselGridState050, besselGridState056, besselGridState059, besselGridState061, besselGridState067, besselGridState072, besselGridState077, besselGridState083, besselGridState087, besselGridState089, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate246_stateChecks8 :
    compactCertificate246.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 18 12 (222309574369659 / 4000000000000)) (orderedInterval (-20015360163 / 1000000000000) (-20015360013 / 1000000000000), orderedInterval (105320290221 / 1000000000000) (105320290371 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (903676077554139 / 4000000000000)) (orderedInterval (25876984388 / 1000000000000) (25876984389 / 1000000000000), orderedInterval (46292451103 / 1000000000000) (46292451104 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (603613739784501 / 4000000000000)) (orderedInterval (50535597479 / 1000000000000) (50535597480 / 1000000000000), orderedInterval (40635393773 / 1000000000000) (40635393774 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState018, besselGridState021, besselGridState022, besselGridState029, besselGridState031, besselGridState034, besselGridState039, besselGridState040, besselGridState042, besselGridState045, besselGridState046, besselGridState048, besselGridState049, besselGridState050, besselGridState056, besselGridState059, besselGridState061, besselGridState067, besselGridState072, besselGridState077, besselGridState083, besselGridState087, besselGridState089, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate246_states : ∀ j,
    BesselStateValid (compactCertificate246.point j) (compactCertificate246.state j) :=
  compactCertificate246.statesValid_of_checks3 compactCertificate246_stateChecks0
    compactCertificate246_stateChecks1 compactCertificate246_stateChecks2
    compactCertificate246_stateChecks3 compactCertificate246_stateChecks4
    compactCertificate246_stateChecks5 compactCertificate246_stateChecks6
    compactCertificate246_stateChecks7 compactCertificate246_stateChecks8

theorem compactCertificate246_chunkChecks0_0 :
    compactCertificate246.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (243 / 2) 0 (IntervalRat.scale (243 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (17047506731 / 1000000000000) (17047506921 / 1000000000000), orderedInterval (-70419928379 / 1000000000000) (-70419928189 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (357985400339943 / 4000000000000) 0 (IntervalRat.scale (243 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (61999545419 / 1000000000000) (61999652711 / 1000000000000), orderedInterval (-57525092321 / 1000000000000) (-57524985029 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (115765123195719 / 800000000000) 0 (IntervalRat.scale (243 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (54998974092 / 1000000000000) (54998974093 / 1000000000000), orderedInterval (36884108715 / 1000000000000) (36884108716 / 1000000000000)))) (orderedInterval (10562152864 / 1000000000000) (10562153949 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (104459246990901 / 4000000000000) 0 (IntervalRat.scale (243 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (153253940145 / 1000000000000) (153253940446 / 1000000000000), orderedInterval (-32712764871 / 1000000000000) (-32712764570 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (280592230826097 / 4000000000000) 0 (IntervalRat.scale (243 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (92399288189 / 1000000000000) (92399288946 / 1000000000000), orderedInterval (-23843500842 / 1000000000000) (-23843500085 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (761862489655149 / 4000000000000) 0 (IntervalRat.scale (243 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (21808221460 / 1000000000000) (21808222277 / 1000000000000), orderedInterval (-53600213335 / 1000000000000) (-53600212518 / 1000000000000)))) (orderedInterval (160624044 / 1000000000000) (160624148 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (561184461652437 / 4000000000000) 0 (IntervalRat.scale (243 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (19329911598 / 1000000000000) (19329911937 / 1000000000000), orderedInterval (-64598455552 / 1000000000000) (-64598455214 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (961599140124201 / 4000000000000) 0 (IntervalRat.scale (243 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (33853576365 / 1000000000000) (33853597552 / 1000000000000), orderedInterval (-38827440085 / 1000000000000) (-38827418898 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (708309574369659 / 4000000000000) 0 (IntervalRat.scale (243 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (56071355396 / 1000000000000) (56071360518 / 1000000000000), orderedInterval (-21398428317 / 1000000000000) (-21398423195 / 1000000000000)))) (orderedInterval (310953631 / 1000000000000) (310954416 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate246_chunkChecks0_1 :
    compactCertificate246.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1086729037064757 / 4000000000000) 0 (IntervalRat.scale (243 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (36410800745 / 1000000000000) (36410862041 / 1000000000000), orderedInterval (-31965345444 / 1000000000000) (-31965284147 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (627423302085453 / 4000000000000) 0 (IntervalRat.scale (243 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (33883246768 / 1000000000000) (33883246769 / 1000000000000), orderedInterval (53841642476 / 1000000000000) (53841642477 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1113373659777777 / 4000000000000) 0 (IntervalRat.scale (243 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (21803085517 / 1000000000000) (21803086865 / 1000000000000), orderedInterval (-42604426935 / 1000000000000) (-42604425587 / 1000000000000)))) (orderedInterval (-859863754 / 1000000000000) (-859852622 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1040258095997013 / 4000000000000) 0 (IntervalRat.scale (243 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-4804072835 / 1000000000000) (-4804072834 / 1000000000000), orderedInterval (-49233584605 / 1000000000000) (-49233584603 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (742377262582629 / 4000000000000) 0 (IntervalRat.scale (243 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-50060744236 / 1000000000000) (-50060744235 / 1000000000000), orderedInterval (-30263895267 / 1000000000000) (-30263895266 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (841776692478291 / 4000000000000) 0 (IntervalRat.scale (243 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-37178628846 / 1000000000000) (-37178628845 / 1000000000000), orderedInterval (-40444055659 / 1000000000000) (-40444055658 / 1000000000000)))) (orderedInterval (-4459013840 / 1000000000000) (-4459013824 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (701785646556579 / 4000000000000) 0 (IntervalRat.scale (243 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (17911208484 / 1000000000000) (17911208485 / 1000000000000), orderedInterval (57462187287 / 1000000000000) (57462187288 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (620048901756159 / 4000000000000) 0 (IntervalRat.scale (243 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-61445874249 / 1000000000000) (-61445872221 / 1000000000000), orderedInterval (18399489065 / 1000000000000) (18399491092 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (179714339295741 / 800000000000) 0 (IntervalRat.scale (243 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-36939973304 / 1000000000000) (-36939937494 / 1000000000000), orderedInterval (38414413350 / 1000000000000) (38414449160 / 1000000000000)))) (orderedInterval (2777366572 / 1000000000000) (2777367617 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate246_chunkChecks0_2 :
    compactCertificate246.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (497099320339527 / 4000000000000) 0 (IntervalRat.scale (243 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-40677379601 / 1000000000000) (-40677367118 / 1000000000000), orderedInterval (59053739011 / 1000000000000) (59053751494 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (421396599076047 / 4000000000000) 0 (IntervalRat.scale (243 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-48927519498 / 1000000000000) (-48927491313 / 1000000000000), orderedInterval (60639682895 / 1000000000000) (60639711080 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (263690425630341 / 4000000000000) 0 (IntervalRat.scale (243 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-65727392505 / 1000000000000) (-65727392504 / 1000000000000), orderedInterval (-72556402473 / 1000000000000) (-72556402472 / 1000000000000)))) (orderedInterval (7133524327 / 1000000000000) (7133527950 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (141813587898747 / 4000000000000) 0 (IntervalRat.scale (243 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-133229615425 / 1000000000000) (-133229615325 / 1000000000000), orderedInterval (16184190328 / 1000000000000) (16184190428 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (385051477817241 / 4000000000000) 0 (IntervalRat.scale (243 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (27303975876 / 1000000000000) (27303976721 / 1000000000000), orderedInterval (-76744095150 / 1000000000000) (-76744094306 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (525754873896057 / 4000000000000) 0 (IntervalRat.scale (243 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (18983586976 / 1000000000000) (18983586977 / 1000000000000), orderedInterval (66883931819 / 1000000000000) (66883931820 / 1000000000000)))) (orderedInterval (385778221 / 1000000000000) (385778257 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (222309574369659 / 4000000000000) 0 (IntervalRat.scale (243 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-20015360163 / 1000000000000) (-20015360013 / 1000000000000), orderedInterval (105320290221 / 1000000000000) (105320290371 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (903676077554139 / 4000000000000) 0 (IntervalRat.scale (243 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (25876984388 / 1000000000000) (25876984389 / 1000000000000), orderedInterval (46292451103 / 1000000000000) (46292451104 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (603613739784501 / 4000000000000) 0 (IntervalRat.scale (243 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (50535597479 / 1000000000000) (50535597480 / 1000000000000), orderedInterval (40635393773 / 1000000000000) (40635393774 / 1000000000000)))) (orderedInterval (-11708910331 / 1000000000000) (-11708910295 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate246_chunkChecks0 :
    compactCertificate246.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate246.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate246_chunkChecks0_0
    compactCertificate246_chunkChecks0_1 compactCertificate246_chunkChecks0_2

theorem compactCertificate246_chunkChecks1_0 :
    compactCertificate246.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (243 / 2) 1 (IntervalRat.scale (243 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (17047506731 / 1000000000000) (17047506921 / 1000000000000), orderedInterval (-70419928379 / 1000000000000) (-70419928189 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (357985400339943 / 4000000000000) 1 (IntervalRat.scale (243 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (61999545419 / 1000000000000) (61999652711 / 1000000000000), orderedInterval (-57525092321 / 1000000000000) (-57524985029 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (115765123195719 / 800000000000) 1 (IntervalRat.scale (243 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (54998974092 / 1000000000000) (54998974093 / 1000000000000), orderedInterval (36884108715 / 1000000000000) (36884108716 / 1000000000000)))) (orderedInterval (-25729025464 / 1000000000000) (-25729024641 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (104459246990901 / 4000000000000) 1 (IntervalRat.scale (243 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (153253940145 / 1000000000000) (153253940446 / 1000000000000), orderedInterval (-32712764871 / 1000000000000) (-32712764570 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (280592230826097 / 4000000000000) 1 (IntervalRat.scale (243 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (92399288189 / 1000000000000) (92399288946 / 1000000000000), orderedInterval (-23843500842 / 1000000000000) (-23843500085 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (761862489655149 / 4000000000000) 1 (IntervalRat.scale (243 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (21808221460 / 1000000000000) (21808222277 / 1000000000000), orderedInterval (-53600213335 / 1000000000000) (-53600212518 / 1000000000000)))) (orderedInterval (5546944547 / 1000000000000) (5546944672 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (561184461652437 / 4000000000000) 1 (IntervalRat.scale (243 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (19329911598 / 1000000000000) (19329911937 / 1000000000000), orderedInterval (-64598455552 / 1000000000000) (-64598455214 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (961599140124201 / 4000000000000) 1 (IntervalRat.scale (243 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (33853576365 / 1000000000000) (33853597552 / 1000000000000), orderedInterval (-38827440085 / 1000000000000) (-38827418898 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (708309574369659 / 4000000000000) 1 (IntervalRat.scale (243 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (56071355396 / 1000000000000) (56071360518 / 1000000000000), orderedInterval (-21398428317 / 1000000000000) (-21398423195 / 1000000000000)))) (orderedInterval (1615836479 / 1000000000000) (1615837965 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate246_chunkChecks1_1 :
    compactCertificate246.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1086729037064757 / 4000000000000) 1 (IntervalRat.scale (243 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (36410800745 / 1000000000000) (36410862041 / 1000000000000), orderedInterval (-31965345444 / 1000000000000) (-31965284147 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (627423302085453 / 4000000000000) 1 (IntervalRat.scale (243 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (33883246768 / 1000000000000) (33883246769 / 1000000000000), orderedInterval (53841642476 / 1000000000000) (53841642477 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1113373659777777 / 4000000000000) 1 (IntervalRat.scale (243 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (21803085517 / 1000000000000) (21803086865 / 1000000000000), orderedInterval (-42604426935 / 1000000000000) (-42604425587 / 1000000000000)))) (orderedInterval (3975862627 / 1000000000000) (3975887521 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1040258095997013 / 4000000000000) 1 (IntervalRat.scale (243 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-4804072835 / 1000000000000) (-4804072834 / 1000000000000), orderedInterval (-49233584605 / 1000000000000) (-49233584603 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (742377262582629 / 4000000000000) 1 (IntervalRat.scale (243 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-50060744236 / 1000000000000) (-50060744235 / 1000000000000), orderedInterval (-30263895267 / 1000000000000) (-30263895266 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (841776692478291 / 4000000000000) 1 (IntervalRat.scale (243 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-37178628846 / 1000000000000) (-37178628845 / 1000000000000), orderedInterval (-40444055659 / 1000000000000) (-40444055658 / 1000000000000)))) (orderedInterval (-2114564957 / 1000000000000) (-2114564932 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (701785646556579 / 4000000000000) 1 (IntervalRat.scale (243 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (17911208484 / 1000000000000) (17911208485 / 1000000000000), orderedInterval (57462187287 / 1000000000000) (57462187288 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (620048901756159 / 4000000000000) 1 (IntervalRat.scale (243 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-61445874249 / 1000000000000) (-61445872221 / 1000000000000), orderedInterval (18399489065 / 1000000000000) (18399491092 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (179714339295741 / 800000000000) 1 (IntervalRat.scale (243 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-36939973304 / 1000000000000) (-36939937494 / 1000000000000), orderedInterval (38414413350 / 1000000000000) (38414449160 / 1000000000000)))) (orderedInterval (1433327964 / 1000000000000) (1433329825 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate246_chunkChecks1_2 :
    compactCertificate246.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (497099320339527 / 4000000000000) 1 (IntervalRat.scale (243 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-40677379601 / 1000000000000) (-40677367118 / 1000000000000), orderedInterval (59053739011 / 1000000000000) (59053751494 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (421396599076047 / 4000000000000) 1 (IntervalRat.scale (243 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-48927519498 / 1000000000000) (-48927491313 / 1000000000000), orderedInterval (60639682895 / 1000000000000) (60639711080 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (263690425630341 / 4000000000000) 1 (IntervalRat.scale (243 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-65727392505 / 1000000000000) (-65727392504 / 1000000000000), orderedInterval (-72556402473 / 1000000000000) (-72556402472 / 1000000000000)))) (orderedInterval (-13915465518 / 1000000000000) (-13915462064 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (141813587898747 / 4000000000000) 1 (IntervalRat.scale (243 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-133229615425 / 1000000000000) (-133229615325 / 1000000000000), orderedInterval (16184190328 / 1000000000000) (16184190428 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (385051477817241 / 4000000000000) 1 (IntervalRat.scale (243 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (27303975876 / 1000000000000) (27303976721 / 1000000000000), orderedInterval (-76744095150 / 1000000000000) (-76744094306 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (525754873896057 / 4000000000000) 1 (IntervalRat.scale (243 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (18983586976 / 1000000000000) (18983586977 / 1000000000000), orderedInterval (66883931819 / 1000000000000) (66883931820 / 1000000000000)))) (orderedInterval (-4252973572 / 1000000000000) (-4252973543 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (222309574369659 / 4000000000000) 1 (IntervalRat.scale (243 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-20015360163 / 1000000000000) (-20015360013 / 1000000000000), orderedInterval (105320290221 / 1000000000000) (105320290371 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (903676077554139 / 4000000000000) 1 (IntervalRat.scale (243 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (25876984388 / 1000000000000) (25876984389 / 1000000000000), orderedInterval (46292451103 / 1000000000000) (46292451104 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (603613739784501 / 4000000000000) 1 (IntervalRat.scale (243 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (50535597479 / 1000000000000) (50535597480 / 1000000000000), orderedInterval (40635393773 / 1000000000000) (40635393774 / 1000000000000)))) (orderedInterval (-16185771310 / 1000000000000) (-16185771261 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate246_chunkChecks1 :
    compactCertificate246.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate246.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate246_chunkChecks1_0
    compactCertificate246_chunkChecks1_1 compactCertificate246_chunkChecks1_2

theorem compactCertificate246_chunkChecks2_0 :
    compactCertificate246.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (243 / 2) 2 (IntervalRat.scale (243 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (17047506731 / 1000000000000) (17047506921 / 1000000000000), orderedInterval (-70419928379 / 1000000000000) (-70419928189 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (357985400339943 / 4000000000000) 2 (IntervalRat.scale (243 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (61999545419 / 1000000000000) (61999652711 / 1000000000000), orderedInterval (-57525092321 / 1000000000000) (-57524985029 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (115765123195719 / 800000000000) 2 (IntervalRat.scale (243 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (54998974092 / 1000000000000) (54998974093 / 1000000000000), orderedInterval (36884108715 / 1000000000000) (36884108716 / 1000000000000)))) (orderedInterval (-11436729800 / 1000000000000) (-11436729164 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (104459246990901 / 4000000000000) 2 (IntervalRat.scale (243 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (153253940145 / 1000000000000) (153253940446 / 1000000000000), orderedInterval (-32712764871 / 1000000000000) (-32712764570 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (280592230826097 / 4000000000000) 2 (IntervalRat.scale (243 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (92399288189 / 1000000000000) (92399288946 / 1000000000000), orderedInterval (-23843500842 / 1000000000000) (-23843500085 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (761862489655149 / 4000000000000) 2 (IntervalRat.scale (243 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (21808221460 / 1000000000000) (21808222277 / 1000000000000), orderedInterval (-53600213335 / 1000000000000) (-53600212518 / 1000000000000)))) (orderedInterval (2716450102 / 1000000000000) (2716450279 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (561184461652437 / 4000000000000) 2 (IntervalRat.scale (243 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (19329911598 / 1000000000000) (19329911937 / 1000000000000), orderedInterval (-64598455552 / 1000000000000) (-64598455214 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (961599140124201 / 4000000000000) 2 (IntervalRat.scale (243 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (33853576365 / 1000000000000) (33853597552 / 1000000000000), orderedInterval (-38827440085 / 1000000000000) (-38827418898 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (708309574369659 / 4000000000000) 2 (IntervalRat.scale (243 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (56071355396 / 1000000000000) (56071360518 / 1000000000000), orderedInterval (-21398428317 / 1000000000000) (-21398423195 / 1000000000000)))) (orderedInterval (1196080359 / 1000000000000) (1196083214 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate246_chunkChecks2_1 :
    compactCertificate246.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1086729037064757 / 4000000000000) 2 (IntervalRat.scale (243 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (36410800745 / 1000000000000) (36410862041 / 1000000000000), orderedInterval (-31965345444 / 1000000000000) (-31965284147 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (627423302085453 / 4000000000000) 2 (IntervalRat.scale (243 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (33883246768 / 1000000000000) (33883246769 / 1000000000000), orderedInterval (53841642476 / 1000000000000) (53841642477 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1113373659777777 / 4000000000000) 2 (IntervalRat.scale (243 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (21803085517 / 1000000000000) (21803086865 / 1000000000000), orderedInterval (-42604426935 / 1000000000000) (-42604425587 / 1000000000000)))) (orderedInterval (11865530569 / 1000000000000) (11865586451 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1040258095997013 / 4000000000000) 2 (IntervalRat.scale (243 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-4804072835 / 1000000000000) (-4804072834 / 1000000000000), orderedInterval (-49233584605 / 1000000000000) (-49233584603 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (742377262582629 / 4000000000000) 2 (IntervalRat.scale (243 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-50060744236 / 1000000000000) (-50060744235 / 1000000000000), orderedInterval (-30263895267 / 1000000000000) (-30263895266 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (841776692478291 / 4000000000000) 2 (IntervalRat.scale (243 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-37178628846 / 1000000000000) (-37178628845 / 1000000000000), orderedInterval (-40444055659 / 1000000000000) (-40444055658 / 1000000000000)))) (orderedInterval (10101357656 / 1000000000000) (10101357696 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (701785646556579 / 4000000000000) 2 (IntervalRat.scale (243 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (17911208484 / 1000000000000) (17911208485 / 1000000000000), orderedInterval (57462187287 / 1000000000000) (57462187288 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (620048901756159 / 4000000000000) 2 (IntervalRat.scale (243 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-61445874249 / 1000000000000) (-61445872221 / 1000000000000), orderedInterval (18399489065 / 1000000000000) (18399491092 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (179714339295741 / 800000000000) 2 (IntervalRat.scale (243 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-36939973304 / 1000000000000) (-36939937494 / 1000000000000), orderedInterval (38414413350 / 1000000000000) (38414449160 / 1000000000000)))) (orderedInterval (-2933464883 / 1000000000000) (-2933461518 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate246_chunkChecks2_2 :
    compactCertificate246.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (497099320339527 / 4000000000000) 2 (IntervalRat.scale (243 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-40677379601 / 1000000000000) (-40677367118 / 1000000000000), orderedInterval (59053739011 / 1000000000000) (59053751494 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (421396599076047 / 4000000000000) 2 (IntervalRat.scale (243 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-48927519498 / 1000000000000) (-48927491313 / 1000000000000), orderedInterval (60639682895 / 1000000000000) (60639711080 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (263690425630341 / 4000000000000) 2 (IntervalRat.scale (243 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-65727392505 / 1000000000000) (-65727392504 / 1000000000000), orderedInterval (-72556402473 / 1000000000000) (-72556402472 / 1000000000000)))) (orderedInterval (-8142018702 / 1000000000000) (-8142015359 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (141813587898747 / 4000000000000) 2 (IntervalRat.scale (243 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-133229615425 / 1000000000000) (-133229615325 / 1000000000000), orderedInterval (16184190328 / 1000000000000) (16184190428 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (385051477817241 / 4000000000000) 2 (IntervalRat.scale (243 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (27303975876 / 1000000000000) (27303976721 / 1000000000000), orderedInterval (-76744095150 / 1000000000000) (-76744094306 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (525754873896057 / 4000000000000) 2 (IntervalRat.scale (243 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (18983586976 / 1000000000000) (18983586977 / 1000000000000), orderedInterval (66883931819 / 1000000000000) (66883931820 / 1000000000000)))) (orderedInterval (1917006292 / 1000000000000) (1917006318 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (222309574369659 / 4000000000000) 2 (IntervalRat.scale (243 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-20015360163 / 1000000000000) (-20015360013 / 1000000000000), orderedInterval (105320290221 / 1000000000000) (105320290371 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (903676077554139 / 4000000000000) 2 (IntervalRat.scale (243 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (25876984388 / 1000000000000) (25876984389 / 1000000000000), orderedInterval (46292451103 / 1000000000000) (46292451104 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (603613739784501 / 4000000000000) 2 (IntervalRat.scale (243 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (50535597479 / 1000000000000) (50535597480 / 1000000000000), orderedInterval (40635393773 / 1000000000000) (40635393774 / 1000000000000)))) (orderedInterval (22067696138 / 1000000000000) (22067696209 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate246_chunkChecks2 :
    compactCertificate246.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate246.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate246_chunkChecks2_0
    compactCertificate246_chunkChecks2_1 compactCertificate246_chunkChecks2_2

theorem compactCertificate246_chunkChecks3_0 :
    compactCertificate246.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (243 / 2) 3 (IntervalRat.scale (243 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (17047506731 / 1000000000000) (17047506921 / 1000000000000), orderedInterval (-70419928379 / 1000000000000) (-70419928189 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (357985400339943 / 4000000000000) 3 (IntervalRat.scale (243 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (61999545419 / 1000000000000) (61999652711 / 1000000000000), orderedInterval (-57525092321 / 1000000000000) (-57524985029 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (115765123195719 / 800000000000) 3 (IntervalRat.scale (243 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (54998974092 / 1000000000000) (54998974093 / 1000000000000), orderedInterval (36884108715 / 1000000000000) (36884108716 / 1000000000000)))) (orderedInterval (24562049185 / 1000000000000) (24562049678 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (104459246990901 / 4000000000000) 3 (IntervalRat.scale (243 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (153253940145 / 1000000000000) (153253940446 / 1000000000000), orderedInterval (-32712764871 / 1000000000000) (-32712764570 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (280592230826097 / 4000000000000) 3 (IntervalRat.scale (243 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (92399288189 / 1000000000000) (92399288946 / 1000000000000), orderedInterval (-23843500842 / 1000000000000) (-23843500085 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (761862489655149 / 4000000000000) 3 (IntervalRat.scale (243 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (21808221460 / 1000000000000) (21808222277 / 1000000000000), orderedInterval (-53600213335 / 1000000000000) (-53600212518 / 1000000000000)))) (orderedInterval (-14536875095 / 1000000000000) (-14536874830 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (561184461652437 / 4000000000000) 3 (IntervalRat.scale (243 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (19329911598 / 1000000000000) (19329911937 / 1000000000000), orderedInterval (-64598455552 / 1000000000000) (-64598455214 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (961599140124201 / 4000000000000) 3 (IntervalRat.scale (243 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (33853576365 / 1000000000000) (33853597552 / 1000000000000), orderedInterval (-38827440085 / 1000000000000) (-38827418898 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (708309574369659 / 4000000000000) 3 (IntervalRat.scale (243 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (56071355396 / 1000000000000) (56071360518 / 1000000000000), orderedInterval (-21398428317 / 1000000000000) (-21398423195 / 1000000000000)))) (orderedInterval (-7685236168 / 1000000000000) (-7685230661 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate246_chunkChecks3_1 :
    compactCertificate246.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1086729037064757 / 4000000000000) 3 (IntervalRat.scale (243 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (36410800745 / 1000000000000) (36410862041 / 1000000000000), orderedInterval (-31965345444 / 1000000000000) (-31965284147 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (627423302085453 / 4000000000000) 3 (IntervalRat.scale (243 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (33883246768 / 1000000000000) (33883246769 / 1000000000000), orderedInterval (53841642476 / 1000000000000) (53841642477 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1113373659777777 / 4000000000000) 3 (IntervalRat.scale (243 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (21803085517 / 1000000000000) (21803086865 / 1000000000000), orderedInterval (-42604426935 / 1000000000000) (-42604425587 / 1000000000000)))) (orderedInterval (633586503 / 1000000000000) (633711504 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1040258095997013 / 4000000000000) 3 (IntervalRat.scale (243 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-4804072835 / 1000000000000) (-4804072834 / 1000000000000), orderedInterval (-49233584605 / 1000000000000) (-49233584603 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (742377262582629 / 4000000000000) 3 (IntervalRat.scale (243 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-50060744236 / 1000000000000) (-50060744235 / 1000000000000), orderedInterval (-30263895267 / 1000000000000) (-30263895266 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (841776692478291 / 4000000000000) 3 (IntervalRat.scale (243 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-37178628846 / 1000000000000) (-37178628845 / 1000000000000), orderedInterval (-40444055659 / 1000000000000) (-40444055658 / 1000000000000)))) (orderedInterval (337261400 / 1000000000000) (337261468 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (701785646556579 / 4000000000000) 3 (IntervalRat.scale (243 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (17911208484 / 1000000000000) (17911208485 / 1000000000000), orderedInterval (57462187287 / 1000000000000) (57462187288 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (620048901756159 / 4000000000000) 3 (IntervalRat.scale (243 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-61445874249 / 1000000000000) (-61445872221 / 1000000000000), orderedInterval (18399489065 / 1000000000000) (18399491092 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (179714339295741 / 800000000000) 3 (IntervalRat.scale (243 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-36939973304 / 1000000000000) (-36939937494 / 1000000000000), orderedInterval (38414413350 / 1000000000000) (38414449160 / 1000000000000)))) (orderedInterval (-6003645444 / 1000000000000) (-6003639341 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate246_chunkChecks3_2 :
    compactCertificate246.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (497099320339527 / 4000000000000) 3 (IntervalRat.scale (243 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-40677379601 / 1000000000000) (-40677367118 / 1000000000000), orderedInterval (59053739011 / 1000000000000) (59053751494 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (421396599076047 / 4000000000000) 3 (IntervalRat.scale (243 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-48927519498 / 1000000000000) (-48927491313 / 1000000000000), orderedInterval (60639682895 / 1000000000000) (60639711080 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (263690425630341 / 4000000000000) 3 (IntervalRat.scale (243 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-65727392505 / 1000000000000) (-65727392504 / 1000000000000), orderedInterval (-72556402473 / 1000000000000) (-72556402472 / 1000000000000)))) (orderedInterval (12784786459 / 1000000000000) (12784789688 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (141813587898747 / 4000000000000) 3 (IntervalRat.scale (243 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-133229615425 / 1000000000000) (-133229615325 / 1000000000000), orderedInterval (16184190328 / 1000000000000) (16184190428 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (385051477817241 / 4000000000000) 3 (IntervalRat.scale (243 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (27303975876 / 1000000000000) (27303976721 / 1000000000000), orderedInterval (-76744095150 / 1000000000000) (-76744094306 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (525754873896057 / 4000000000000) 3 (IntervalRat.scale (243 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (18983586976 / 1000000000000) (18983586977 / 1000000000000), orderedInterval (66883931819 / 1000000000000) (66883931820 / 1000000000000)))) (orderedInterval (5614971885 / 1000000000000) (5614971909 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (222309574369659 / 4000000000000) 3 (IntervalRat.scale (243 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-20015360163 / 1000000000000) (-20015360013 / 1000000000000), orderedInterval (105320290221 / 1000000000000) (105320290371 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (903676077554139 / 4000000000000) 3 (IntervalRat.scale (243 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (25876984388 / 1000000000000) (25876984389 / 1000000000000), orderedInterval (46292451103 / 1000000000000) (46292451104 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (603613739784501 / 4000000000000) 3 (IntervalRat.scale (243 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (50535597479 / 1000000000000) (50535597480 / 1000000000000), orderedInterval (40635393773 / 1000000000000) (40635393774 / 1000000000000)))) (orderedInterval (38589265911 / 1000000000000) (38589266020 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate246_chunkChecks3 :
    compactCertificate246.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate246.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate246_chunkChecks3_0
    compactCertificate246_chunkChecks3_1 compactCertificate246_chunkChecks3_2

theorem compactCertificate246_chunkChecks4_0 :
    compactCertificate246.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (243 / 2) 4 (IntervalRat.scale (243 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (17047506731 / 1000000000000) (17047506921 / 1000000000000), orderedInterval (-70419928379 / 1000000000000) (-70419928189 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (357985400339943 / 4000000000000) 4 (IntervalRat.scale (243 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (61999545419 / 1000000000000) (61999652711 / 1000000000000), orderedInterval (-57525092321 / 1000000000000) (-57524985029 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (115765123195719 / 800000000000) 4 (IntervalRat.scale (243 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (54998974092 / 1000000000000) (54998974093 / 1000000000000), orderedInterval (36884108715 / 1000000000000) (36884108716 / 1000000000000)))) (orderedInterval (13015833618 / 1000000000000) (13015834011 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (104459246990901 / 4000000000000) 4 (IntervalRat.scale (243 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (153253940145 / 1000000000000) (153253940446 / 1000000000000), orderedInterval (-32712764871 / 1000000000000) (-32712764570 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (280592230826097 / 4000000000000) 4 (IntervalRat.scale (243 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (92399288189 / 1000000000000) (92399288946 / 1000000000000), orderedInterval (-23843500842 / 1000000000000) (-23843500085 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (761862489655149 / 4000000000000) 4 (IntervalRat.scale (243 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (21808221460 / 1000000000000) (21808222277 / 1000000000000), orderedInterval (-53600213335 / 1000000000000) (-53600212518 / 1000000000000)))) (orderedInterval (-8751641266 / 1000000000000) (-8751640854 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (561184461652437 / 4000000000000) 4 (IntervalRat.scale (243 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (19329911598 / 1000000000000) (19329911937 / 1000000000000), orderedInterval (-64598455552 / 1000000000000) (-64598455214 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (961599140124201 / 4000000000000) 4 (IntervalRat.scale (243 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (33853576365 / 1000000000000) (33853597552 / 1000000000000), orderedInterval (-38827440085 / 1000000000000) (-38827418898 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (708309574369659 / 4000000000000) 4 (IntervalRat.scale (243 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (56071355396 / 1000000000000) (56071360518 / 1000000000000), orderedInterval (-21398428317 / 1000000000000) (-21398423195 / 1000000000000)))) (orderedInterval (-9762551059 / 1000000000000) (-9762540324 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate246_chunkChecks4_1 :
    compactCertificate246.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1086729037064757 / 4000000000000) 4 (IntervalRat.scale (243 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (36410800745 / 1000000000000) (36410862041 / 1000000000000), orderedInterval (-31965345444 / 1000000000000) (-31965284147 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (627423302085453 / 4000000000000) 4 (IntervalRat.scale (243 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (33883246768 / 1000000000000) (33883246769 / 1000000000000), orderedInterval (53841642476 / 1000000000000) (53841642477 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1113373659777777 / 4000000000000) 4 (IntervalRat.scale (243 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (21803085517 / 1000000000000) (21803086865 / 1000000000000), orderedInterval (-42604426935 / 1000000000000) (-42604425587 / 1000000000000)))) (orderedInterval (-69411107447 / 1000000000000) (-69410826807 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1040258095997013 / 4000000000000) 4 (IntervalRat.scale (243 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-4804072835 / 1000000000000) (-4804072834 / 1000000000000), orderedInterval (-49233584605 / 1000000000000) (-49233584603 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (742377262582629 / 4000000000000) 4 (IntervalRat.scale (243 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-50060744236 / 1000000000000) (-50060744235 / 1000000000000), orderedInterval (-30263895267 / 1000000000000) (-30263895266 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (841776692478291 / 4000000000000) 4 (IntervalRat.scale (243 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-37178628846 / 1000000000000) (-37178628845 / 1000000000000), orderedInterval (-40444055659 / 1000000000000) (-40444055658 / 1000000000000)))) (orderedInterval (-22264489180 / 1000000000000) (-22264489063 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (701785646556579 / 4000000000000) 4 (IntervalRat.scale (243 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (17911208484 / 1000000000000) (17911208485 / 1000000000000), orderedInterval (57462187287 / 1000000000000) (57462187288 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (620048901756159 / 4000000000000) 4 (IntervalRat.scale (243 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-61445874249 / 1000000000000) (-61445872221 / 1000000000000), orderedInterval (18399489065 / 1000000000000) (18399491092 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (179714339295741 / 800000000000) 4 (IntervalRat.scale (243 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-36939973304 / 1000000000000) (-36939937494 / 1000000000000), orderedInterval (38414413350 / 1000000000000) (38414449160 / 1000000000000)))) (orderedInterval (-738387439 / 1000000000000) (-738376257 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate246_chunkChecks4_2 :
    compactCertificate246.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (497099320339527 / 4000000000000) 4 (IntervalRat.scale (243 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-40677379601 / 1000000000000) (-40677367118 / 1000000000000), orderedInterval (59053739011 / 1000000000000) (59053751494 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (421396599076047 / 4000000000000) 4 (IntervalRat.scale (243 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-48927519498 / 1000000000000) (-48927491313 / 1000000000000), orderedInterval (60639682895 / 1000000000000) (60639711080 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (263690425630341 / 4000000000000) 4 (IntervalRat.scale (243 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-65727392505 / 1000000000000) (-65727392504 / 1000000000000), orderedInterval (-72556402473 / 1000000000000) (-72556402472 / 1000000000000)))) (orderedInterval (8287660002 / 1000000000000) (8287663166 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (141813587898747 / 4000000000000) 4 (IntervalRat.scale (243 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-133229615425 / 1000000000000) (-133229615325 / 1000000000000), orderedInterval (16184190328 / 1000000000000) (16184190428 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (385051477817241 / 4000000000000) 4 (IntervalRat.scale (243 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (27303975876 / 1000000000000) (27303976721 / 1000000000000), orderedInterval (-76744095150 / 1000000000000) (-76744094306 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (525754873896057 / 4000000000000) 4 (IntervalRat.scale (243 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (18983586976 / 1000000000000) (18983586977 / 1000000000000), orderedInterval (66883931819 / 1000000000000) (66883931820 / 1000000000000)))) (orderedInterval (-2311117937 / 1000000000000) (-2311117915 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (222309574369659 / 4000000000000) 4 (IntervalRat.scale (243 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-20015360163 / 1000000000000) (-20015360013 / 1000000000000), orderedInterval (105320290221 / 1000000000000) (105320290371 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (903676077554139 / 4000000000000) 4 (IntervalRat.scale (243 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (25876984388 / 1000000000000) (25876984389 / 1000000000000), orderedInterval (46292451103 / 1000000000000) (46292451104 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (603613739784501 / 4000000000000) 4 (IntervalRat.scale (243 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (50535597479 / 1000000000000) (50535597480 / 1000000000000), orderedInterval (40635393773 / 1000000000000) (40635393774 / 1000000000000)))) (orderedInterval (-48381153276 / 1000000000000) (-48381153101 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate246_chunkChecks4 :
    compactCertificate246.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate246.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate246_chunkChecks4_0
    compactCertificate246_chunkChecks4_1 compactCertificate246_chunkChecks4_2

theorem compactCertificate246_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate246.chunkCheck r b = true :=
  compactCertificate246.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate246_chunkChecks0
    · exact compactCertificate246_chunkChecks1
    · exact compactCertificate246_chunkChecks2
    · exact compactCertificate246_chunkChecks3
    · exact compactCertificate246_chunkChecks4)

theorem compactCertificate246_coefficient0 :
    compactCertificate246.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate246, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate246_coefficient1 :
    compactCertificate246.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate246, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate246_coefficient2 :
    compactCertificate246.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate246, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate246_coefficient3 :
    compactCertificate246.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate246, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate246_coefficient4 :
    compactCertificate246.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate246, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate246_coefficients : ∀ r : Fin 5,
    compactCertificate246.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate246_coefficient0
  · exact compactCertificate246_coefficient1
  · exact compactCertificate246_coefficient2
  · exact compactCertificate246_coefficient3
  · exact compactCertificate246_coefficient4

theorem compactCertificate246_lower : (1 : ℚ) ≤ compactCertificate246.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate246, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate246_proves {t : ℝ} (ht : t ∈ compactCertificate246.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate246.proves compactCertificate246_states compactCertificate246_chunks
    compactCertificate246_coefficients compactCertificate246_lower ht

end Erdos232
