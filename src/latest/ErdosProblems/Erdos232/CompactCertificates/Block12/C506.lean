/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate506 : CompactCertificate where
  left := 377
  right := 378
  center := 755 / 2
  grid := fun i =>
    match i.val with
    | 0 => 120
    | 1 => 89
    | 2 => 143
    | 3 => 26
    | 4 => 69
    | 5 => 188
    | 6 => 139
    | 7 => 238
    | 8 => 175
    | 9 => 269
    | 10 => 155
    | 11 => 275
    | 12 => 257
    | 13 => 184
    | 14 => 208
    | 15 => 174
    | 16 => 153
    | 17 => 222
    | 18 => 123
    | 19 => 104
    | 20 => 65
    | 21 => 35
    | 22 => 95
    | 23 => 130
    | 24 => 55
    | 25 => 224
    | _ => 149
  point := fun i =>
    match i.val with
    | 0 => 755 / 2
    | 1 => 222451833133051 / 800000000000
    | 2 => 71936352273883 / 160000000000
    | 3 => 64910890105457 / 800000000000
    | 4 => 174359781295229 / 800000000000
    | 5 => 473420724024393 / 800000000000
    | 6 => 348719562590609 / 800000000000
    | 7 => 597536914233557 / 800000000000
    | 8 => 440142986542463 / 800000000000
    | 9 => 675292529204849 / 800000000000
    | 10 => 389880323518121 / 800000000000
    | 11 => 691849475828989 / 800000000000
    | 12 => 646415524673041 / 800000000000
    | 13 => 461312619958753 / 800000000000
    | 14 => 523079343885687 / 800000000000
    | 15 => 436089023168903 / 800000000000
    | 16 => 385297877222963 / 800000000000
    | 17 => 111674342525337 / 160000000000
    | 18 => 308897108523739 / 800000000000
    | 19 => 261855499837379 / 800000000000
    | 20 => 163857013457537 / 800000000000
    | 21 => 88122846801279 / 800000000000
    | 22 => 239270671400837 / 800000000000
    | 23 => 326703645918949 / 800000000000
    | 24 => 138142986542463 / 800000000000
    | 25 => 561543570825823 / 800000000000
    | _ => 375085081100657 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (39502189309 / 1000000000000) (39502189313 / 1000000000000), orderedInterval (11172017796 / 1000000000000) (11172017800 / 1000000000000))
    | 1 => (orderedInterval (32685426837 / 1000000000000) (32685451219 / 1000000000000), orderedInterval (-35003425013 / 1000000000000) (-35003400631 / 1000000000000))
    | 2 => (orderedInterval (-34184486301 / 1000000000000) (-34184486300 / 1000000000000), orderedInterval (-15690385928 / 1000000000000) (-15690385926 / 1000000000000))
    | 3 => (orderedInterval (21146347958 / 1000000000000) (21146347959 / 1000000000000), orderedInterval (85887370780 / 1000000000000) (85887370781 / 1000000000000))
    | 4 => (orderedInterval (-49907658589 / 1000000000000) (-49907649813 / 1000000000000), orderedInterval (20854989871 / 1000000000000) (20854998646 / 1000000000000))
    | 5 => (orderedInterval (30569024339 / 1000000000000) (30569066751 / 1000000000000), orderedInterval (-11913304486 / 1000000000000) (-11913262074 / 1000000000000))
    | 6 => (orderedInterval (-121748377 / 1000000000000) (-121748376 / 1000000000000), orderedInterval (-38215826034 / 1000000000000) (-38215826033 / 1000000000000))
    | 7 => (orderedInterval (213762389 / 1000000000000) (213762390 / 1000000000000), orderedInterval (29193688048 / 1000000000000) (29193688049 / 1000000000000))
    | 8 => (orderedInterval (-31518571340 / 1000000000000) (-31518571337 / 1000000000000), orderedInterval (-12765643350 / 1000000000000) (-12765643347 / 1000000000000))
    | 9 => (orderedInterval (5119418428 / 1000000000000) (5119418429 / 1000000000000), orderedInterval (-26984084183 / 1000000000000) (-26984084182 / 1000000000000))
    | 10 => (orderedInterval (-33535963554 / 1000000000000) (-33535963552 / 1000000000000), orderedInterval (-13442470700 / 1000000000000) (-13442470698 / 1000000000000))
    | 11 => (orderedInterval (-27026086302 / 1000000000000) (-27026075356 / 1000000000000), orderedInterval (2408853445 / 1000000000000) (2408864391 / 1000000000000))
    | 12 => (orderedInterval (-27730643481 / 1000000000000) (-27730642949 / 1000000000000), orderedInterval (-4328886916 / 1000000000000) (-4328886384 / 1000000000000))
    | 13 => (orderedInterval (-19497182059 / 1000000000000) (-19497180669 / 1000000000000), orderedInterval (26921821755 / 1000000000000) (26921823145 / 1000000000000))
    | 14 => (orderedInterval (28887688006 / 1000000000000) (28887688012 / 1000000000000), orderedInterval (11774118309 / 1000000000000) (11774118315 / 1000000000000))
    | 15 => (orderedInterval (-23060203163 / 1000000000000) (-23060197397 / 1000000000000), orderedInterval (25242140523 / 1000000000000) (25242146289 / 1000000000000))
    | 16 => (orderedInterval (-35814096386 / 1000000000000) (-35814092860 / 1000000000000), orderedInterval (6296054825 / 1000000000000) (6296058351 / 1000000000000))
    | 17 => (orderedInterval (29228294885 / 1000000000000) (29228294952 / 1000000000000), orderedInterval (7582711419 / 1000000000000) (7582711485 / 1000000000000))
    | 18 => (orderedInterval (-19129887867 / 1000000000000) (-19129887866 / 1000000000000), orderedInterval (-35791477226 / 1000000000000) (-35791477225 / 1000000000000))
    | 19 => (orderedInterval (43290827112 / 1000000000000) (43290827122 / 1000000000000), orderedInterval (8351236444 / 1000000000000) (8351236454 / 1000000000000))
    | 20 => (orderedInterval (-54963529057 / 1000000000000) (-54963529051 / 1000000000000), orderedInterval (-9202525869 / 1000000000000) (-9202525863 / 1000000000000))
    | 21 => (orderedInterval (-63223867780 / 1000000000000) (-63223867779 / 1000000000000), orderedInterval (-41928002038 / 1000000000000) (-41928002037 / 1000000000000))
    | 22 => (orderedInterval (-45626335339 / 1000000000000) (-45626335323 / 1000000000000), orderedInterval (-6762505540 / 1000000000000) (-6762505525 / 1000000000000))
    | 23 => (orderedInterval (27131911511 / 1000000000000) (27131911512 / 1000000000000), orderedInterval (28650431518 / 1000000000000) (28650431519 / 1000000000000))
    | 24 => (orderedInterval (-37981169401 / 1000000000000) (-37981169400 / 1000000000000), orderedInterval (-47262628309 / 1000000000000) (-47262628308 / 1000000000000))
    | 25 => (orderedInterval (-25375162782 / 1000000000000) (-25375129034 / 1000000000000), orderedInterval (16237144283 / 1000000000000) (16237178031 / 1000000000000))
    | _ => (orderedInterval (-36835465125 / 1000000000000) (-36835464818 / 1000000000000), orderedInterval (-941465224 / 1000000000000) (-941464917 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (13955865118 / 1000000000000) (13955865373 / 1000000000000)
      | 1 => orderedInterval (-4224782640 / 1000000000000) (-4224779259 / 1000000000000)
      | 2 => orderedInterval (-768334981 / 1000000000000) (-768334960 / 1000000000000)
      | 3 => orderedInterval (-7236315255 / 1000000000000) (-7236313549 / 1000000000000)
      | 4 => orderedInterval (-1489274096 / 1000000000000) (-1489273909 / 1000000000000)
      | 5 => orderedInterval (2531589690 / 1000000000000) (2531589997 / 1000000000000)
      | 6 => orderedInterval (-1180887055 / 1000000000000) (-1180886959 / 1000000000000)
      | 7 => orderedInterval (123195427 / 1000000000000) (123195473 / 1000000000000)
      | _ => orderedInterval (8747927930 / 1000000000000) (8747930839 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (3091357419 / 1000000000000) (3091357618 / 1000000000000)
      | 1 => orderedInterval (1566973697 / 1000000000000) (1566978661 / 1000000000000)
      | 2 => orderedInterval (-2231275834 / 1000000000000) (-2231275796 / 1000000000000)
      | 3 => orderedInterval (10220054110 / 1000000000000) (10220057985 / 1000000000000)
      | 4 => orderedInterval (3952854108 / 1000000000000) (3952854403 / 1000000000000)
      | 5 => orderedInterval (320189663 / 1000000000000) (320190072 / 1000000000000)
      | 6 => orderedInterval (5281087588 / 1000000000000) (5281087677 / 1000000000000)
      | 7 => orderedInterval (-2027884396 / 1000000000000) (-2027884354 / 1000000000000)
      | _ => orderedInterval (-2368590733 / 1000000000000) (-2368585406 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-12985275442 / 1000000000000) (-12985275282 / 1000000000000)
      | 1 => orderedInterval (5954188522 / 1000000000000) (5954196123 / 1000000000000)
      | 2 => orderedInterval (1649733157 / 1000000000000) (1649733223 / 1000000000000)
      | 3 => orderedInterval (28825547359 / 1000000000000) (28825556200 / 1000000000000)
      | 4 => orderedInterval (2436464254 / 1000000000000) (2436464726 / 1000000000000)
      | 5 => orderedInterval (-5339888672 / 1000000000000) (-5339888119 / 1000000000000)
      | 6 => orderedInterval (-845126158 / 1000000000000) (-845126074 / 1000000000000)
      | 7 => orderedInterval (1689662812 / 1000000000000) (1689662853 / 1000000000000)
      | _ => orderedInterval (-17748621505 / 1000000000000) (-17748611687 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-2707935725 / 1000000000000) (-2707935592 / 1000000000000)
      | 1 => orderedInterval (-3415618456 / 1000000000000) (-3415606653 / 1000000000000)
      | 2 => orderedInterval (7925525366 / 1000000000000) (7925525485 / 1000000000000)
      | 3 => orderedInterval (-55657275698 / 1000000000000) (-55657255509 / 1000000000000)
      | 4 => orderedInterval (-9537018822 / 1000000000000) (-9537018053 / 1000000000000)
      | 5 => orderedInterval (-1342381401 / 1000000000000) (-1342380649 / 1000000000000)
      | 6 => orderedInterval (-5765646353 / 1000000000000) (-5765646271 / 1000000000000)
      | 7 => orderedInterval (2679823616 / 1000000000000) (2679823658 / 1000000000000)
      | _ => orderedInterval (8232986581 / 1000000000000) (8233004712 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (11724992290 / 1000000000000) (11724992405 / 1000000000000)
      | 1 => orderedInterval (-13308323936 / 1000000000000) (-13308305466 / 1000000000000)
      | 2 => orderedInterval (-3579833901 / 1000000000000) (-3579833679 / 1000000000000)
      | 3 => orderedInterval (-135168196904 / 1000000000000) (-135168150707 / 1000000000000)
      | 4 => orderedInterval (-794866360 / 1000000000000) (-794865084 / 1000000000000)
      | 5 => orderedInterval (13024757039 / 1000000000000) (13024758076 / 1000000000000)
      | 6 => orderedInterval (1838395251 / 1000000000000) (1838395331 / 1000000000000)
      | 7 => orderedInterval (-2445707182 / 1000000000000) (-2445707138 / 1000000000000)
      | _ => orderedInterval (41083452338 / 1000000000000) (41083485945 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (10458984138 / 1000000000000) (10458993046 / 1000000000000)
    | 1 => orderedInterval (17804765622 / 1000000000000) (17804780860 / 1000000000000)
    | 2 => orderedInterval (3636684327 / 1000000000000) (3636711963 / 1000000000000)
    | 3 => orderedInterval (-59587540892 / 1000000000000) (-59587488872 / 1000000000000)
    | _ => orderedInterval (-87625331365 / 1000000000000) (-87625230317 / 1000000000000)

theorem compactCertificate506_stateChecks0 :
    compactCertificate506.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 120 12 (755 / 2)) (orderedInterval (39502189309 / 1000000000000) (39502189313 / 1000000000000), orderedInterval (11172017796 / 1000000000000) (11172017800 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (222451833133051 / 800000000000)) (orderedInterval (32685426837 / 1000000000000) (32685451219 / 1000000000000), orderedInterval (-35003425013 / 1000000000000) (-35003400631 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 143 12 (71936352273883 / 160000000000)) (orderedInterval (-34184486301 / 1000000000000) (-34184486300 / 1000000000000), orderedInterval (-15690385928 / 1000000000000) (-15690385926 / 1000000000000))) = true
  rfl'

theorem compactCertificate506_stateChecks1 :
    compactCertificate506.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (64910890105457 / 800000000000)) (orderedInterval (21146347958 / 1000000000000) (21146347959 / 1000000000000), orderedInterval (85887370780 / 1000000000000) (85887370781 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (174359781295229 / 800000000000)) (orderedInterval (-49907658589 / 1000000000000) (-49907649813 / 1000000000000), orderedInterval (20854989871 / 1000000000000) (20854998646 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 188 12 (473420724024393 / 800000000000)) (orderedInterval (30569024339 / 1000000000000) (30569066751 / 1000000000000), orderedInterval (-11913304486 / 1000000000000) (-11913262074 / 1000000000000))) = true
  rfl'

theorem compactCertificate506_stateChecks2 :
    compactCertificate506.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 139 12 (348719562590609 / 800000000000)) (orderedInterval (-121748377 / 1000000000000) (-121748376 / 1000000000000), orderedInterval (-38215826034 / 1000000000000) (-38215826033 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 238 12 (597536914233557 / 800000000000)) (orderedInterval (213762389 / 1000000000000) (213762390 / 1000000000000), orderedInterval (29193688048 / 1000000000000) (29193688049 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 175 12 (440142986542463 / 800000000000)) (orderedInterval (-31518571340 / 1000000000000) (-31518571337 / 1000000000000), orderedInterval (-12765643350 / 1000000000000) (-12765643347 / 1000000000000))) = true
  rfl'

theorem compactCertificate506_stateChecks3 :
    compactCertificate506.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 269 12 (675292529204849 / 800000000000)) (orderedInterval (5119418428 / 1000000000000) (5119418429 / 1000000000000), orderedInterval (-26984084183 / 1000000000000) (-26984084182 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 155 12 (389880323518121 / 800000000000)) (orderedInterval (-33535963554 / 1000000000000) (-33535963552 / 1000000000000), orderedInterval (-13442470700 / 1000000000000) (-13442470698 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 275 12 (691849475828989 / 800000000000)) (orderedInterval (-27026086302 / 1000000000000) (-27026075356 / 1000000000000), orderedInterval (2408853445 / 1000000000000) (2408864391 / 1000000000000))) = true
  rfl'

theorem compactCertificate506_stateChecks4 :
    compactCertificate506.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 257 12 (646415524673041 / 800000000000)) (orderedInterval (-27730643481 / 1000000000000) (-27730642949 / 1000000000000), orderedInterval (-4328886916 / 1000000000000) (-4328886384 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 184 12 (461312619958753 / 800000000000)) (orderedInterval (-19497182059 / 1000000000000) (-19497180669 / 1000000000000), orderedInterval (26921821755 / 1000000000000) (26921823145 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 208 12 (523079343885687 / 800000000000)) (orderedInterval (28887688006 / 1000000000000) (28887688012 / 1000000000000), orderedInterval (11774118309 / 1000000000000) (11774118315 / 1000000000000))) = true
  rfl'

theorem compactCertificate506_stateChecks5 :
    compactCertificate506.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 174 12 (436089023168903 / 800000000000)) (orderedInterval (-23060203163 / 1000000000000) (-23060197397 / 1000000000000), orderedInterval (25242140523 / 1000000000000) (25242146289 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 153 12 (385297877222963 / 800000000000)) (orderedInterval (-35814096386 / 1000000000000) (-35814092860 / 1000000000000), orderedInterval (6296054825 / 1000000000000) (6296058351 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 222 12 (111674342525337 / 160000000000)) (orderedInterval (29228294885 / 1000000000000) (29228294952 / 1000000000000), orderedInterval (7582711419 / 1000000000000) (7582711485 / 1000000000000))) = true
  rfl'

theorem compactCertificate506_stateChecks6 :
    compactCertificate506.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 123 12 (308897108523739 / 800000000000)) (orderedInterval (-19129887867 / 1000000000000) (-19129887866 / 1000000000000), orderedInterval (-35791477226 / 1000000000000) (-35791477225 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 104 12 (261855499837379 / 800000000000)) (orderedInterval (43290827112 / 1000000000000) (43290827122 / 1000000000000), orderedInterval (8351236444 / 1000000000000) (8351236454 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (163857013457537 / 800000000000)) (orderedInterval (-54963529057 / 1000000000000) (-54963529051 / 1000000000000), orderedInterval (-9202525869 / 1000000000000) (-9202525863 / 1000000000000))) = true
  rfl'

theorem compactCertificate506_stateChecks7 :
    compactCertificate506.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (88122846801279 / 800000000000)) (orderedInterval (-63223867780 / 1000000000000) (-63223867779 / 1000000000000), orderedInterval (-41928002038 / 1000000000000) (-41928002037 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 95 12 (239270671400837 / 800000000000)) (orderedInterval (-45626335339 / 1000000000000) (-45626335323 / 1000000000000), orderedInterval (-6762505540 / 1000000000000) (-6762505525 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 130 12 (326703645918949 / 800000000000)) (orderedInterval (27131911511 / 1000000000000) (27131911512 / 1000000000000), orderedInterval (28650431518 / 1000000000000) (28650431519 / 1000000000000))) = true
  rfl'

theorem compactCertificate506_stateChecks8 :
    compactCertificate506.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (138142986542463 / 800000000000)) (orderedInterval (-37981169401 / 1000000000000) (-37981169400 / 1000000000000), orderedInterval (-47262628309 / 1000000000000) (-47262628308 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 224 12 (561543570825823 / 800000000000)) (orderedInterval (-25375162782 / 1000000000000) (-25375129034 / 1000000000000), orderedInterval (16237144283 / 1000000000000) (16237178031 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 149 12 (375085081100657 / 800000000000)) (orderedInterval (-36835465125 / 1000000000000) (-36835464818 / 1000000000000), orderedInterval (-941465224 / 1000000000000) (-941464917 / 1000000000000))) = true
  rfl'

theorem compactCertificate506_states : ∀ j,
    BesselStateValid (compactCertificate506.point j) (compactCertificate506.state j) :=
  compactCertificate506.statesValid_of_checks3 compactCertificate506_stateChecks0
    compactCertificate506_stateChecks1 compactCertificate506_stateChecks2
    compactCertificate506_stateChecks3 compactCertificate506_stateChecks4
    compactCertificate506_stateChecks5 compactCertificate506_stateChecks6
    compactCertificate506_stateChecks7 compactCertificate506_stateChecks8

theorem compactCertificate506_chunkChecks0_0 :
    compactCertificate506.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (755 / 2) 0 (IntervalRat.scale (755 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (39502189309 / 1000000000000) (39502189313 / 1000000000000), orderedInterval (11172017796 / 1000000000000) (11172017800 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (222451833133051 / 800000000000) 0 (IntervalRat.scale (755 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (32685426837 / 1000000000000) (32685451219 / 1000000000000), orderedInterval (-35003425013 / 1000000000000) (-35003400631 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (71936352273883 / 160000000000) 0 (IntervalRat.scale (755 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34184486301 / 1000000000000) (-34184486300 / 1000000000000), orderedInterval (-15690385928 / 1000000000000) (-15690385926 / 1000000000000)))) (orderedInterval (13955865118 / 1000000000000) (13955865373 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (64910890105457 / 800000000000) 0 (IntervalRat.scale (755 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (21146347958 / 1000000000000) (21146347959 / 1000000000000), orderedInterval (85887370780 / 1000000000000) (85887370781 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (174359781295229 / 800000000000) 0 (IntervalRat.scale (755 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-49907658589 / 1000000000000) (-49907649813 / 1000000000000), orderedInterval (20854989871 / 1000000000000) (20854998646 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (473420724024393 / 800000000000) 0 (IntervalRat.scale (755 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30569024339 / 1000000000000) (30569066751 / 1000000000000), orderedInterval (-11913304486 / 1000000000000) (-11913262074 / 1000000000000)))) (orderedInterval (-4224782640 / 1000000000000) (-4224779259 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (348719562590609 / 800000000000) 0 (IntervalRat.scale (755 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-121748377 / 1000000000000) (-121748376 / 1000000000000), orderedInterval (-38215826034 / 1000000000000) (-38215826033 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (597536914233557 / 800000000000) 0 (IntervalRat.scale (755 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (213762389 / 1000000000000) (213762390 / 1000000000000), orderedInterval (29193688048 / 1000000000000) (29193688049 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (440142986542463 / 800000000000) 0 (IntervalRat.scale (755 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-31518571340 / 1000000000000) (-31518571337 / 1000000000000), orderedInterval (-12765643350 / 1000000000000) (-12765643347 / 1000000000000)))) (orderedInterval (-768334981 / 1000000000000) (-768334960 / 1000000000000))) = true
  rfl'

theorem compactCertificate506_chunkChecks0_1 :
    compactCertificate506.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (675292529204849 / 800000000000) 0 (IntervalRat.scale (755 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (5119418428 / 1000000000000) (5119418429 / 1000000000000), orderedInterval (-26984084183 / 1000000000000) (-26984084182 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (389880323518121 / 800000000000) 0 (IntervalRat.scale (755 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-33535963554 / 1000000000000) (-33535963552 / 1000000000000), orderedInterval (-13442470700 / 1000000000000) (-13442470698 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (691849475828989 / 800000000000) 0 (IntervalRat.scale (755 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-27026086302 / 1000000000000) (-27026075356 / 1000000000000), orderedInterval (2408853445 / 1000000000000) (2408864391 / 1000000000000)))) (orderedInterval (-7236315255 / 1000000000000) (-7236313549 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (646415524673041 / 800000000000) 0 (IntervalRat.scale (755 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-27730643481 / 1000000000000) (-27730642949 / 1000000000000), orderedInterval (-4328886916 / 1000000000000) (-4328886384 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (461312619958753 / 800000000000) 0 (IntervalRat.scale (755 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-19497182059 / 1000000000000) (-19497180669 / 1000000000000), orderedInterval (26921821755 / 1000000000000) (26921823145 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (523079343885687 / 800000000000) 0 (IntervalRat.scale (755 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (28887688006 / 1000000000000) (28887688012 / 1000000000000), orderedInterval (11774118309 / 1000000000000) (11774118315 / 1000000000000)))) (orderedInterval (-1489274096 / 1000000000000) (-1489273909 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (436089023168903 / 800000000000) 0 (IntervalRat.scale (755 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-23060203163 / 1000000000000) (-23060197397 / 1000000000000), orderedInterval (25242140523 / 1000000000000) (25242146289 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (385297877222963 / 800000000000) 0 (IntervalRat.scale (755 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-35814096386 / 1000000000000) (-35814092860 / 1000000000000), orderedInterval (6296054825 / 1000000000000) (6296058351 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (111674342525337 / 160000000000) 0 (IntervalRat.scale (755 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (29228294885 / 1000000000000) (29228294952 / 1000000000000), orderedInterval (7582711419 / 1000000000000) (7582711485 / 1000000000000)))) (orderedInterval (2531589690 / 1000000000000) (2531589997 / 1000000000000))) = true
  rfl'

theorem compactCertificate506_chunkChecks0_2 :
    compactCertificate506.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (308897108523739 / 800000000000) 0 (IntervalRat.scale (755 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-19129887867 / 1000000000000) (-19129887866 / 1000000000000), orderedInterval (-35791477226 / 1000000000000) (-35791477225 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (261855499837379 / 800000000000) 0 (IntervalRat.scale (755 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (43290827112 / 1000000000000) (43290827122 / 1000000000000), orderedInterval (8351236444 / 1000000000000) (8351236454 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (163857013457537 / 800000000000) 0 (IntervalRat.scale (755 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-54963529057 / 1000000000000) (-54963529051 / 1000000000000), orderedInterval (-9202525869 / 1000000000000) (-9202525863 / 1000000000000)))) (orderedInterval (-1180887055 / 1000000000000) (-1180886959 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (88122846801279 / 800000000000) 0 (IntervalRat.scale (755 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-63223867780 / 1000000000000) (-63223867779 / 1000000000000), orderedInterval (-41928002038 / 1000000000000) (-41928002037 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (239270671400837 / 800000000000) 0 (IntervalRat.scale (755 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-45626335339 / 1000000000000) (-45626335323 / 1000000000000), orderedInterval (-6762505540 / 1000000000000) (-6762505525 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (326703645918949 / 800000000000) 0 (IntervalRat.scale (755 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (27131911511 / 1000000000000) (27131911512 / 1000000000000), orderedInterval (28650431518 / 1000000000000) (28650431519 / 1000000000000)))) (orderedInterval (123195427 / 1000000000000) (123195473 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (138142986542463 / 800000000000) 0 (IntervalRat.scale (755 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-37981169401 / 1000000000000) (-37981169400 / 1000000000000), orderedInterval (-47262628309 / 1000000000000) (-47262628308 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (561543570825823 / 800000000000) 0 (IntervalRat.scale (755 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25375162782 / 1000000000000) (-25375129034 / 1000000000000), orderedInterval (16237144283 / 1000000000000) (16237178031 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (375085081100657 / 800000000000) 0 (IntervalRat.scale (755 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-36835465125 / 1000000000000) (-36835464818 / 1000000000000), orderedInterval (-941465224 / 1000000000000) (-941464917 / 1000000000000)))) (orderedInterval (8747927930 / 1000000000000) (8747930839 / 1000000000000))) = true
  rfl'

theorem compactCertificate506_chunkChecks0 :
    compactCertificate506.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate506.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate506_chunkChecks0_0
    compactCertificate506_chunkChecks0_1 compactCertificate506_chunkChecks0_2

theorem compactCertificate506_chunkChecks1_0 :
    compactCertificate506.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (755 / 2) 1 (IntervalRat.scale (755 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (39502189309 / 1000000000000) (39502189313 / 1000000000000), orderedInterval (11172017796 / 1000000000000) (11172017800 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (222451833133051 / 800000000000) 1 (IntervalRat.scale (755 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (32685426837 / 1000000000000) (32685451219 / 1000000000000), orderedInterval (-35003425013 / 1000000000000) (-35003400631 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (71936352273883 / 160000000000) 1 (IntervalRat.scale (755 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34184486301 / 1000000000000) (-34184486300 / 1000000000000), orderedInterval (-15690385928 / 1000000000000) (-15690385926 / 1000000000000)))) (orderedInterval (3091357419 / 1000000000000) (3091357618 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (64910890105457 / 800000000000) 1 (IntervalRat.scale (755 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (21146347958 / 1000000000000) (21146347959 / 1000000000000), orderedInterval (85887370780 / 1000000000000) (85887370781 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (174359781295229 / 800000000000) 1 (IntervalRat.scale (755 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-49907658589 / 1000000000000) (-49907649813 / 1000000000000), orderedInterval (20854989871 / 1000000000000) (20854998646 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (473420724024393 / 800000000000) 1 (IntervalRat.scale (755 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30569024339 / 1000000000000) (30569066751 / 1000000000000), orderedInterval (-11913304486 / 1000000000000) (-11913262074 / 1000000000000)))) (orderedInterval (1566973697 / 1000000000000) (1566978661 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (348719562590609 / 800000000000) 1 (IntervalRat.scale (755 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-121748377 / 1000000000000) (-121748376 / 1000000000000), orderedInterval (-38215826034 / 1000000000000) (-38215826033 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (597536914233557 / 800000000000) 1 (IntervalRat.scale (755 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (213762389 / 1000000000000) (213762390 / 1000000000000), orderedInterval (29193688048 / 1000000000000) (29193688049 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (440142986542463 / 800000000000) 1 (IntervalRat.scale (755 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-31518571340 / 1000000000000) (-31518571337 / 1000000000000), orderedInterval (-12765643350 / 1000000000000) (-12765643347 / 1000000000000)))) (orderedInterval (-2231275834 / 1000000000000) (-2231275796 / 1000000000000))) = true
  rfl'

theorem compactCertificate506_chunkChecks1_1 :
    compactCertificate506.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (675292529204849 / 800000000000) 1 (IntervalRat.scale (755 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (5119418428 / 1000000000000) (5119418429 / 1000000000000), orderedInterval (-26984084183 / 1000000000000) (-26984084182 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (389880323518121 / 800000000000) 1 (IntervalRat.scale (755 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-33535963554 / 1000000000000) (-33535963552 / 1000000000000), orderedInterval (-13442470700 / 1000000000000) (-13442470698 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (691849475828989 / 800000000000) 1 (IntervalRat.scale (755 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-27026086302 / 1000000000000) (-27026075356 / 1000000000000), orderedInterval (2408853445 / 1000000000000) (2408864391 / 1000000000000)))) (orderedInterval (10220054110 / 1000000000000) (10220057985 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (646415524673041 / 800000000000) 1 (IntervalRat.scale (755 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-27730643481 / 1000000000000) (-27730642949 / 1000000000000), orderedInterval (-4328886916 / 1000000000000) (-4328886384 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (461312619958753 / 800000000000) 1 (IntervalRat.scale (755 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-19497182059 / 1000000000000) (-19497180669 / 1000000000000), orderedInterval (26921821755 / 1000000000000) (26921823145 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (523079343885687 / 800000000000) 1 (IntervalRat.scale (755 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (28887688006 / 1000000000000) (28887688012 / 1000000000000), orderedInterval (11774118309 / 1000000000000) (11774118315 / 1000000000000)))) (orderedInterval (3952854108 / 1000000000000) (3952854403 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (436089023168903 / 800000000000) 1 (IntervalRat.scale (755 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-23060203163 / 1000000000000) (-23060197397 / 1000000000000), orderedInterval (25242140523 / 1000000000000) (25242146289 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (385297877222963 / 800000000000) 1 (IntervalRat.scale (755 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-35814096386 / 1000000000000) (-35814092860 / 1000000000000), orderedInterval (6296054825 / 1000000000000) (6296058351 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (111674342525337 / 160000000000) 1 (IntervalRat.scale (755 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (29228294885 / 1000000000000) (29228294952 / 1000000000000), orderedInterval (7582711419 / 1000000000000) (7582711485 / 1000000000000)))) (orderedInterval (320189663 / 1000000000000) (320190072 / 1000000000000))) = true
  rfl'

theorem compactCertificate506_chunkChecks1_2 :
    compactCertificate506.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (308897108523739 / 800000000000) 1 (IntervalRat.scale (755 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-19129887867 / 1000000000000) (-19129887866 / 1000000000000), orderedInterval (-35791477226 / 1000000000000) (-35791477225 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (261855499837379 / 800000000000) 1 (IntervalRat.scale (755 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (43290827112 / 1000000000000) (43290827122 / 1000000000000), orderedInterval (8351236444 / 1000000000000) (8351236454 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (163857013457537 / 800000000000) 1 (IntervalRat.scale (755 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-54963529057 / 1000000000000) (-54963529051 / 1000000000000), orderedInterval (-9202525869 / 1000000000000) (-9202525863 / 1000000000000)))) (orderedInterval (5281087588 / 1000000000000) (5281087677 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (88122846801279 / 800000000000) 1 (IntervalRat.scale (755 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-63223867780 / 1000000000000) (-63223867779 / 1000000000000), orderedInterval (-41928002038 / 1000000000000) (-41928002037 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (239270671400837 / 800000000000) 1 (IntervalRat.scale (755 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-45626335339 / 1000000000000) (-45626335323 / 1000000000000), orderedInterval (-6762505540 / 1000000000000) (-6762505525 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (326703645918949 / 800000000000) 1 (IntervalRat.scale (755 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (27131911511 / 1000000000000) (27131911512 / 1000000000000), orderedInterval (28650431518 / 1000000000000) (28650431519 / 1000000000000)))) (orderedInterval (-2027884396 / 1000000000000) (-2027884354 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (138142986542463 / 800000000000) 1 (IntervalRat.scale (755 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-37981169401 / 1000000000000) (-37981169400 / 1000000000000), orderedInterval (-47262628309 / 1000000000000) (-47262628308 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (561543570825823 / 800000000000) 1 (IntervalRat.scale (755 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25375162782 / 1000000000000) (-25375129034 / 1000000000000), orderedInterval (16237144283 / 1000000000000) (16237178031 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (375085081100657 / 800000000000) 1 (IntervalRat.scale (755 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-36835465125 / 1000000000000) (-36835464818 / 1000000000000), orderedInterval (-941465224 / 1000000000000) (-941464917 / 1000000000000)))) (orderedInterval (-2368590733 / 1000000000000) (-2368585406 / 1000000000000))) = true
  rfl'

theorem compactCertificate506_chunkChecks1 :
    compactCertificate506.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate506.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate506_chunkChecks1_0
    compactCertificate506_chunkChecks1_1 compactCertificate506_chunkChecks1_2

theorem compactCertificate506_chunkChecks2_0 :
    compactCertificate506.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (755 / 2) 2 (IntervalRat.scale (755 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (39502189309 / 1000000000000) (39502189313 / 1000000000000), orderedInterval (11172017796 / 1000000000000) (11172017800 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (222451833133051 / 800000000000) 2 (IntervalRat.scale (755 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (32685426837 / 1000000000000) (32685451219 / 1000000000000), orderedInterval (-35003425013 / 1000000000000) (-35003400631 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (71936352273883 / 160000000000) 2 (IntervalRat.scale (755 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34184486301 / 1000000000000) (-34184486300 / 1000000000000), orderedInterval (-15690385928 / 1000000000000) (-15690385926 / 1000000000000)))) (orderedInterval (-12985275442 / 1000000000000) (-12985275282 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (64910890105457 / 800000000000) 2 (IntervalRat.scale (755 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (21146347958 / 1000000000000) (21146347959 / 1000000000000), orderedInterval (85887370780 / 1000000000000) (85887370781 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (174359781295229 / 800000000000) 2 (IntervalRat.scale (755 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-49907658589 / 1000000000000) (-49907649813 / 1000000000000), orderedInterval (20854989871 / 1000000000000) (20854998646 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (473420724024393 / 800000000000) 2 (IntervalRat.scale (755 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30569024339 / 1000000000000) (30569066751 / 1000000000000), orderedInterval (-11913304486 / 1000000000000) (-11913262074 / 1000000000000)))) (orderedInterval (5954188522 / 1000000000000) (5954196123 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (348719562590609 / 800000000000) 2 (IntervalRat.scale (755 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-121748377 / 1000000000000) (-121748376 / 1000000000000), orderedInterval (-38215826034 / 1000000000000) (-38215826033 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (597536914233557 / 800000000000) 2 (IntervalRat.scale (755 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (213762389 / 1000000000000) (213762390 / 1000000000000), orderedInterval (29193688048 / 1000000000000) (29193688049 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (440142986542463 / 800000000000) 2 (IntervalRat.scale (755 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-31518571340 / 1000000000000) (-31518571337 / 1000000000000), orderedInterval (-12765643350 / 1000000000000) (-12765643347 / 1000000000000)))) (orderedInterval (1649733157 / 1000000000000) (1649733223 / 1000000000000))) = true
  rfl'

theorem compactCertificate506_chunkChecks2_1 :
    compactCertificate506.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (675292529204849 / 800000000000) 2 (IntervalRat.scale (755 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (5119418428 / 1000000000000) (5119418429 / 1000000000000), orderedInterval (-26984084183 / 1000000000000) (-26984084182 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (389880323518121 / 800000000000) 2 (IntervalRat.scale (755 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-33535963554 / 1000000000000) (-33535963552 / 1000000000000), orderedInterval (-13442470700 / 1000000000000) (-13442470698 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (691849475828989 / 800000000000) 2 (IntervalRat.scale (755 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-27026086302 / 1000000000000) (-27026075356 / 1000000000000), orderedInterval (2408853445 / 1000000000000) (2408864391 / 1000000000000)))) (orderedInterval (28825547359 / 1000000000000) (28825556200 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (646415524673041 / 800000000000) 2 (IntervalRat.scale (755 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-27730643481 / 1000000000000) (-27730642949 / 1000000000000), orderedInterval (-4328886916 / 1000000000000) (-4328886384 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (461312619958753 / 800000000000) 2 (IntervalRat.scale (755 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-19497182059 / 1000000000000) (-19497180669 / 1000000000000), orderedInterval (26921821755 / 1000000000000) (26921823145 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (523079343885687 / 800000000000) 2 (IntervalRat.scale (755 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (28887688006 / 1000000000000) (28887688012 / 1000000000000), orderedInterval (11774118309 / 1000000000000) (11774118315 / 1000000000000)))) (orderedInterval (2436464254 / 1000000000000) (2436464726 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (436089023168903 / 800000000000) 2 (IntervalRat.scale (755 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-23060203163 / 1000000000000) (-23060197397 / 1000000000000), orderedInterval (25242140523 / 1000000000000) (25242146289 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (385297877222963 / 800000000000) 2 (IntervalRat.scale (755 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-35814096386 / 1000000000000) (-35814092860 / 1000000000000), orderedInterval (6296054825 / 1000000000000) (6296058351 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (111674342525337 / 160000000000) 2 (IntervalRat.scale (755 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (29228294885 / 1000000000000) (29228294952 / 1000000000000), orderedInterval (7582711419 / 1000000000000) (7582711485 / 1000000000000)))) (orderedInterval (-5339888672 / 1000000000000) (-5339888119 / 1000000000000))) = true
  rfl'

theorem compactCertificate506_chunkChecks2_2 :
    compactCertificate506.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (308897108523739 / 800000000000) 2 (IntervalRat.scale (755 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-19129887867 / 1000000000000) (-19129887866 / 1000000000000), orderedInterval (-35791477226 / 1000000000000) (-35791477225 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (261855499837379 / 800000000000) 2 (IntervalRat.scale (755 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (43290827112 / 1000000000000) (43290827122 / 1000000000000), orderedInterval (8351236444 / 1000000000000) (8351236454 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (163857013457537 / 800000000000) 2 (IntervalRat.scale (755 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-54963529057 / 1000000000000) (-54963529051 / 1000000000000), orderedInterval (-9202525869 / 1000000000000) (-9202525863 / 1000000000000)))) (orderedInterval (-845126158 / 1000000000000) (-845126074 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (88122846801279 / 800000000000) 2 (IntervalRat.scale (755 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-63223867780 / 1000000000000) (-63223867779 / 1000000000000), orderedInterval (-41928002038 / 1000000000000) (-41928002037 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (239270671400837 / 800000000000) 2 (IntervalRat.scale (755 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-45626335339 / 1000000000000) (-45626335323 / 1000000000000), orderedInterval (-6762505540 / 1000000000000) (-6762505525 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (326703645918949 / 800000000000) 2 (IntervalRat.scale (755 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (27131911511 / 1000000000000) (27131911512 / 1000000000000), orderedInterval (28650431518 / 1000000000000) (28650431519 / 1000000000000)))) (orderedInterval (1689662812 / 1000000000000) (1689662853 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (138142986542463 / 800000000000) 2 (IntervalRat.scale (755 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-37981169401 / 1000000000000) (-37981169400 / 1000000000000), orderedInterval (-47262628309 / 1000000000000) (-47262628308 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (561543570825823 / 800000000000) 2 (IntervalRat.scale (755 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25375162782 / 1000000000000) (-25375129034 / 1000000000000), orderedInterval (16237144283 / 1000000000000) (16237178031 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (375085081100657 / 800000000000) 2 (IntervalRat.scale (755 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-36835465125 / 1000000000000) (-36835464818 / 1000000000000), orderedInterval (-941465224 / 1000000000000) (-941464917 / 1000000000000)))) (orderedInterval (-17748621505 / 1000000000000) (-17748611687 / 1000000000000))) = true
  rfl'

theorem compactCertificate506_chunkChecks2 :
    compactCertificate506.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate506.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate506_chunkChecks2_0
    compactCertificate506_chunkChecks2_1 compactCertificate506_chunkChecks2_2

theorem compactCertificate506_chunkChecks3_0 :
    compactCertificate506.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (755 / 2) 3 (IntervalRat.scale (755 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (39502189309 / 1000000000000) (39502189313 / 1000000000000), orderedInterval (11172017796 / 1000000000000) (11172017800 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (222451833133051 / 800000000000) 3 (IntervalRat.scale (755 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (32685426837 / 1000000000000) (32685451219 / 1000000000000), orderedInterval (-35003425013 / 1000000000000) (-35003400631 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (71936352273883 / 160000000000) 3 (IntervalRat.scale (755 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34184486301 / 1000000000000) (-34184486300 / 1000000000000), orderedInterval (-15690385928 / 1000000000000) (-15690385926 / 1000000000000)))) (orderedInterval (-2707935725 / 1000000000000) (-2707935592 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (64910890105457 / 800000000000) 3 (IntervalRat.scale (755 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (21146347958 / 1000000000000) (21146347959 / 1000000000000), orderedInterval (85887370780 / 1000000000000) (85887370781 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (174359781295229 / 800000000000) 3 (IntervalRat.scale (755 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-49907658589 / 1000000000000) (-49907649813 / 1000000000000), orderedInterval (20854989871 / 1000000000000) (20854998646 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (473420724024393 / 800000000000) 3 (IntervalRat.scale (755 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30569024339 / 1000000000000) (30569066751 / 1000000000000), orderedInterval (-11913304486 / 1000000000000) (-11913262074 / 1000000000000)))) (orderedInterval (-3415618456 / 1000000000000) (-3415606653 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (348719562590609 / 800000000000) 3 (IntervalRat.scale (755 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-121748377 / 1000000000000) (-121748376 / 1000000000000), orderedInterval (-38215826034 / 1000000000000) (-38215826033 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (597536914233557 / 800000000000) 3 (IntervalRat.scale (755 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (213762389 / 1000000000000) (213762390 / 1000000000000), orderedInterval (29193688048 / 1000000000000) (29193688049 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (440142986542463 / 800000000000) 3 (IntervalRat.scale (755 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-31518571340 / 1000000000000) (-31518571337 / 1000000000000), orderedInterval (-12765643350 / 1000000000000) (-12765643347 / 1000000000000)))) (orderedInterval (7925525366 / 1000000000000) (7925525485 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate506_chunkChecks3_1 :
    compactCertificate506.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (675292529204849 / 800000000000) 3 (IntervalRat.scale (755 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (5119418428 / 1000000000000) (5119418429 / 1000000000000), orderedInterval (-26984084183 / 1000000000000) (-26984084182 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (389880323518121 / 800000000000) 3 (IntervalRat.scale (755 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-33535963554 / 1000000000000) (-33535963552 / 1000000000000), orderedInterval (-13442470700 / 1000000000000) (-13442470698 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (691849475828989 / 800000000000) 3 (IntervalRat.scale (755 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-27026086302 / 1000000000000) (-27026075356 / 1000000000000), orderedInterval (2408853445 / 1000000000000) (2408864391 / 1000000000000)))) (orderedInterval (-55657275698 / 1000000000000) (-55657255509 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (646415524673041 / 800000000000) 3 (IntervalRat.scale (755 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-27730643481 / 1000000000000) (-27730642949 / 1000000000000), orderedInterval (-4328886916 / 1000000000000) (-4328886384 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (461312619958753 / 800000000000) 3 (IntervalRat.scale (755 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-19497182059 / 1000000000000) (-19497180669 / 1000000000000), orderedInterval (26921821755 / 1000000000000) (26921823145 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (523079343885687 / 800000000000) 3 (IntervalRat.scale (755 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (28887688006 / 1000000000000) (28887688012 / 1000000000000), orderedInterval (11774118309 / 1000000000000) (11774118315 / 1000000000000)))) (orderedInterval (-9537018822 / 1000000000000) (-9537018053 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (436089023168903 / 800000000000) 3 (IntervalRat.scale (755 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-23060203163 / 1000000000000) (-23060197397 / 1000000000000), orderedInterval (25242140523 / 1000000000000) (25242146289 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (385297877222963 / 800000000000) 3 (IntervalRat.scale (755 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-35814096386 / 1000000000000) (-35814092860 / 1000000000000), orderedInterval (6296054825 / 1000000000000) (6296058351 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (111674342525337 / 160000000000) 3 (IntervalRat.scale (755 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (29228294885 / 1000000000000) (29228294952 / 1000000000000), orderedInterval (7582711419 / 1000000000000) (7582711485 / 1000000000000)))) (orderedInterval (-1342381401 / 1000000000000) (-1342380649 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate506_chunkChecks3_2 :
    compactCertificate506.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (308897108523739 / 800000000000) 3 (IntervalRat.scale (755 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-19129887867 / 1000000000000) (-19129887866 / 1000000000000), orderedInterval (-35791477226 / 1000000000000) (-35791477225 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (261855499837379 / 800000000000) 3 (IntervalRat.scale (755 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (43290827112 / 1000000000000) (43290827122 / 1000000000000), orderedInterval (8351236444 / 1000000000000) (8351236454 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (163857013457537 / 800000000000) 3 (IntervalRat.scale (755 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-54963529057 / 1000000000000) (-54963529051 / 1000000000000), orderedInterval (-9202525869 / 1000000000000) (-9202525863 / 1000000000000)))) (orderedInterval (-5765646353 / 1000000000000) (-5765646271 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (88122846801279 / 800000000000) 3 (IntervalRat.scale (755 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-63223867780 / 1000000000000) (-63223867779 / 1000000000000), orderedInterval (-41928002038 / 1000000000000) (-41928002037 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (239270671400837 / 800000000000) 3 (IntervalRat.scale (755 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-45626335339 / 1000000000000) (-45626335323 / 1000000000000), orderedInterval (-6762505540 / 1000000000000) (-6762505525 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (326703645918949 / 800000000000) 3 (IntervalRat.scale (755 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (27131911511 / 1000000000000) (27131911512 / 1000000000000), orderedInterval (28650431518 / 1000000000000) (28650431519 / 1000000000000)))) (orderedInterval (2679823616 / 1000000000000) (2679823658 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (138142986542463 / 800000000000) 3 (IntervalRat.scale (755 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-37981169401 / 1000000000000) (-37981169400 / 1000000000000), orderedInterval (-47262628309 / 1000000000000) (-47262628308 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (561543570825823 / 800000000000) 3 (IntervalRat.scale (755 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25375162782 / 1000000000000) (-25375129034 / 1000000000000), orderedInterval (16237144283 / 1000000000000) (16237178031 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (375085081100657 / 800000000000) 3 (IntervalRat.scale (755 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-36835465125 / 1000000000000) (-36835464818 / 1000000000000), orderedInterval (-941465224 / 1000000000000) (-941464917 / 1000000000000)))) (orderedInterval (8232986581 / 1000000000000) (8233004712 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate506_chunkChecks3 :
    compactCertificate506.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate506.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate506_chunkChecks3_0
    compactCertificate506_chunkChecks3_1 compactCertificate506_chunkChecks3_2

theorem compactCertificate506_chunkChecks4_0 :
    compactCertificate506.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (755 / 2) 4 (IntervalRat.scale (755 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (39502189309 / 1000000000000) (39502189313 / 1000000000000), orderedInterval (11172017796 / 1000000000000) (11172017800 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (222451833133051 / 800000000000) 4 (IntervalRat.scale (755 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (32685426837 / 1000000000000) (32685451219 / 1000000000000), orderedInterval (-35003425013 / 1000000000000) (-35003400631 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (71936352273883 / 160000000000) 4 (IntervalRat.scale (755 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34184486301 / 1000000000000) (-34184486300 / 1000000000000), orderedInterval (-15690385928 / 1000000000000) (-15690385926 / 1000000000000)))) (orderedInterval (11724992290 / 1000000000000) (11724992405 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (64910890105457 / 800000000000) 4 (IntervalRat.scale (755 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (21146347958 / 1000000000000) (21146347959 / 1000000000000), orderedInterval (85887370780 / 1000000000000) (85887370781 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (174359781295229 / 800000000000) 4 (IntervalRat.scale (755 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-49907658589 / 1000000000000) (-49907649813 / 1000000000000), orderedInterval (20854989871 / 1000000000000) (20854998646 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (473420724024393 / 800000000000) 4 (IntervalRat.scale (755 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30569024339 / 1000000000000) (30569066751 / 1000000000000), orderedInterval (-11913304486 / 1000000000000) (-11913262074 / 1000000000000)))) (orderedInterval (-13308323936 / 1000000000000) (-13308305466 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (348719562590609 / 800000000000) 4 (IntervalRat.scale (755 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-121748377 / 1000000000000) (-121748376 / 1000000000000), orderedInterval (-38215826034 / 1000000000000) (-38215826033 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (597536914233557 / 800000000000) 4 (IntervalRat.scale (755 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (213762389 / 1000000000000) (213762390 / 1000000000000), orderedInterval (29193688048 / 1000000000000) (29193688049 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (440142986542463 / 800000000000) 4 (IntervalRat.scale (755 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-31518571340 / 1000000000000) (-31518571337 / 1000000000000), orderedInterval (-12765643350 / 1000000000000) (-12765643347 / 1000000000000)))) (orderedInterval (-3579833901 / 1000000000000) (-3579833679 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate506_chunkChecks4_1 :
    compactCertificate506.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (675292529204849 / 800000000000) 4 (IntervalRat.scale (755 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (5119418428 / 1000000000000) (5119418429 / 1000000000000), orderedInterval (-26984084183 / 1000000000000) (-26984084182 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (389880323518121 / 800000000000) 4 (IntervalRat.scale (755 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-33535963554 / 1000000000000) (-33535963552 / 1000000000000), orderedInterval (-13442470700 / 1000000000000) (-13442470698 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (691849475828989 / 800000000000) 4 (IntervalRat.scale (755 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-27026086302 / 1000000000000) (-27026075356 / 1000000000000), orderedInterval (2408853445 / 1000000000000) (2408864391 / 1000000000000)))) (orderedInterval (-135168196904 / 1000000000000) (-135168150707 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (646415524673041 / 800000000000) 4 (IntervalRat.scale (755 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-27730643481 / 1000000000000) (-27730642949 / 1000000000000), orderedInterval (-4328886916 / 1000000000000) (-4328886384 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (461312619958753 / 800000000000) 4 (IntervalRat.scale (755 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-19497182059 / 1000000000000) (-19497180669 / 1000000000000), orderedInterval (26921821755 / 1000000000000) (26921823145 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (523079343885687 / 800000000000) 4 (IntervalRat.scale (755 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (28887688006 / 1000000000000) (28887688012 / 1000000000000), orderedInterval (11774118309 / 1000000000000) (11774118315 / 1000000000000)))) (orderedInterval (-794866360 / 1000000000000) (-794865084 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (436089023168903 / 800000000000) 4 (IntervalRat.scale (755 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-23060203163 / 1000000000000) (-23060197397 / 1000000000000), orderedInterval (25242140523 / 1000000000000) (25242146289 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (385297877222963 / 800000000000) 4 (IntervalRat.scale (755 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-35814096386 / 1000000000000) (-35814092860 / 1000000000000), orderedInterval (6296054825 / 1000000000000) (6296058351 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (111674342525337 / 160000000000) 4 (IntervalRat.scale (755 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (29228294885 / 1000000000000) (29228294952 / 1000000000000), orderedInterval (7582711419 / 1000000000000) (7582711485 / 1000000000000)))) (orderedInterval (13024757039 / 1000000000000) (13024758076 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate506_chunkChecks4_2 :
    compactCertificate506.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (308897108523739 / 800000000000) 4 (IntervalRat.scale (755 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-19129887867 / 1000000000000) (-19129887866 / 1000000000000), orderedInterval (-35791477226 / 1000000000000) (-35791477225 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (261855499837379 / 800000000000) 4 (IntervalRat.scale (755 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (43290827112 / 1000000000000) (43290827122 / 1000000000000), orderedInterval (8351236444 / 1000000000000) (8351236454 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (163857013457537 / 800000000000) 4 (IntervalRat.scale (755 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-54963529057 / 1000000000000) (-54963529051 / 1000000000000), orderedInterval (-9202525869 / 1000000000000) (-9202525863 / 1000000000000)))) (orderedInterval (1838395251 / 1000000000000) (1838395331 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (88122846801279 / 800000000000) 4 (IntervalRat.scale (755 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-63223867780 / 1000000000000) (-63223867779 / 1000000000000), orderedInterval (-41928002038 / 1000000000000) (-41928002037 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (239270671400837 / 800000000000) 4 (IntervalRat.scale (755 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-45626335339 / 1000000000000) (-45626335323 / 1000000000000), orderedInterval (-6762505540 / 1000000000000) (-6762505525 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (326703645918949 / 800000000000) 4 (IntervalRat.scale (755 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (27131911511 / 1000000000000) (27131911512 / 1000000000000), orderedInterval (28650431518 / 1000000000000) (28650431519 / 1000000000000)))) (orderedInterval (-2445707182 / 1000000000000) (-2445707138 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (138142986542463 / 800000000000) 4 (IntervalRat.scale (755 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-37981169401 / 1000000000000) (-37981169400 / 1000000000000), orderedInterval (-47262628309 / 1000000000000) (-47262628308 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (561543570825823 / 800000000000) 4 (IntervalRat.scale (755 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25375162782 / 1000000000000) (-25375129034 / 1000000000000), orderedInterval (16237144283 / 1000000000000) (16237178031 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (375085081100657 / 800000000000) 4 (IntervalRat.scale (755 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-36835465125 / 1000000000000) (-36835464818 / 1000000000000), orderedInterval (-941465224 / 1000000000000) (-941464917 / 1000000000000)))) (orderedInterval (41083452338 / 1000000000000) (41083485945 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate506_chunkChecks4 :
    compactCertificate506.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate506.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate506_chunkChecks4_0
    compactCertificate506_chunkChecks4_1 compactCertificate506_chunkChecks4_2

theorem compactCertificate506_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate506.chunkCheck r b = true :=
  compactCertificate506.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate506_chunkChecks0
    · exact compactCertificate506_chunkChecks1
    · exact compactCertificate506_chunkChecks2
    · exact compactCertificate506_chunkChecks3
    · exact compactCertificate506_chunkChecks4)

theorem compactCertificate506_coefficient0 :
    compactCertificate506.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate506_coefficient1 :
    compactCertificate506.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate506_coefficient2 :
    compactCertificate506.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate506_coefficient3 :
    compactCertificate506.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate506_coefficient4 :
    compactCertificate506.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate506_coefficients : ∀ r : Fin 5,
    compactCertificate506.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate506_coefficient0
  · exact compactCertificate506_coefficient1
  · exact compactCertificate506_coefficient2
  · exact compactCertificate506_coefficient3
  · exact compactCertificate506_coefficient4

theorem compactCertificate506_lower : (1 : ℚ) ≤ compactCertificate506.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate506, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate506_proves {t : ℝ} (ht : t ∈ compactCertificate506.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate506.proves compactCertificate506_states compactCertificate506_chunks
    compactCertificate506_coefficients compactCertificate506_lower ht

end Erdos232
