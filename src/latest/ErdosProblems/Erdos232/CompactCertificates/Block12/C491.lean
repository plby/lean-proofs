/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate491 : CompactCertificate where
  left := 362
  right := 363
  center := 725 / 2
  grid := fun i =>
    match i.val with
    | 0 => 115
    | 1 => 85
    | 2 => 137
    | 3 => 25
    | 4 => 67
    | 5 => 181
    | 6 => 133
    | 7 => 228
    | 8 => 168
    | 9 => 258
    | 10 => 149
    | 11 => 264
    | 12 => 247
    | 13 => 176
    | 14 => 200
    | 15 => 167
    | 16 => 147
    | 17 => 213
    | 18 => 118
    | 19 => 100
    | 20 => 63
    | 21 => 34
    | 22 => 91
    | 23 => 125
    | 24 => 53
    | 25 => 215
    | _ => 143
  point := fun i =>
    match i.val with
    | 0 => 725 / 2
    | 1 => 42722537489129 / 160000000000
    | 2 => 13815590834057 / 32000000000
    | 3 => 12466329887803 / 160000000000
    | 4 => 33486315612991 / 160000000000
    | 5 => 90921860905347 / 160000000000
    | 6 => 66972631226011 / 160000000000
    | 7 => 114758745117703 / 160000000000
    | 8 => 84530772249877 / 160000000000
    | 9 => 129691942694971 / 160000000000
    | 10 => 74877678026659 / 160000000000
    | 11 => 132871753636031 / 160000000000
    | 12 => 124146027917339 / 160000000000
    | 13 => 88596463435787 / 160000000000
    | 14 => 100458946838973 / 160000000000
    | 15 => 83752196502637 / 160000000000
    | 16 => 73997605559377 / 160000000000
    | 17 => 21447390286323 / 32000000000
    | 18 => 59324610246281 / 160000000000
    | 19 => 50290129107841 / 160000000000
    | 20 => 31469227750123 / 160000000000
    | 21 => 16924255345941 / 160000000000
    | 22 => 45952645500823 / 160000000000
    | 23 => 62744408818871 / 160000000000
    | 24 => 26530772249877 / 160000000000
    | 25 => 107846116251317 / 160000000000
    | _ => 72036207628603 / 160000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-38072704490 / 1000000000000) (-38072678996 / 1000000000000), orderedInterval (17564254093 / 1000000000000) (17564279586 / 1000000000000))
    | 1 => (orderedInterval (-33829941230 / 1000000000000) (-33829941229 / 1000000000000), orderedInterval (-35146556082 / 1000000000000) (-35146556081 / 1000000000000))
    | 2 => (orderedInterval (-32669846458 / 1000000000000) (-32669744767 / 1000000000000), orderedInterval (20217916159 / 1000000000000) (20218017850 / 1000000000000))
    | 3 => (orderedInterval (-14270616993 / 1000000000000) (-14270616991 / 1000000000000), orderedInterval (-89167885005 / 1000000000000) (-89167885004 / 1000000000000))
    | 4 => (orderedInterval (22107393462 / 1000000000000) (22107394454 / 1000000000000), orderedInterval (-50580863362 / 1000000000000) (-50580862370 / 1000000000000))
    | 5 => (orderedInterval (-13603380716 / 1000000000000) (-13603380715 / 1000000000000), orderedInterval (-30569753285 / 1000000000000) (-30569753284 / 1000000000000))
    | 6 => (orderedInterval (-38969786232 / 1000000000000) (-38969786045 / 1000000000000), orderedInterval (-1457439413 / 1000000000000) (-1457439226 / 1000000000000))
    | 7 => (orderedInterval (29345425595 / 1000000000000) (29345437713 / 1000000000000), orderedInterval (-5162383123 / 1000000000000) (-5162371004 / 1000000000000))
    | 8 => (orderedInterval (33582860269 / 1000000000000) (33582860287 / 1000000000000), orderedInterval (8753778741 / 1000000000000) (8753778759 / 1000000000000))
    | 9 => (orderedInterval (20661146131 / 1000000000000) (20661146132 / 1000000000000), orderedInterval (18921620276 / 1000000000000) (18921620277 / 1000000000000))
    | 10 => (orderedInterval (-22999355939 / 1000000000000) (-22999355938 / 1000000000000), orderedInterval (-28808925898 / 1000000000000) (-28808925897 / 1000000000000))
    | 11 => (orderedInterval (26590355679 / 1000000000000) (26590412217 / 1000000000000), orderedInterval (-7732830820 / 1000000000000) (-7732774282 / 1000000000000))
    | 12 => (orderedInterval (-18984686135 / 1000000000000) (-18984686134 / 1000000000000), orderedInterval (-21436783653 / 1000000000000) (-21436783652 / 1000000000000))
    | 13 => (orderedInterval (33899007745 / 1000000000000) (33899008706 / 1000000000000), orderedInterval (-775340228 / 1000000000000) (-775339266 / 1000000000000))
    | 14 => (orderedInterval (10471385794 / 1000000000000) (10471385795 / 1000000000000), orderedInterval (30063051723 / 1000000000000) (30063051724 / 1000000000000))
    | 15 => (orderedInterval (13887850620 / 1000000000000) (13887850744 / 1000000000000), orderedInterval (-32002715594 / 1000000000000) (-32002715470 / 1000000000000))
    | 16 => (orderedInterval (-36857451871 / 1000000000000) (-36857451782 / 1000000000000), orderedInterval (-4208350808 / 1000000000000) (-4208350719 / 1000000000000))
    | 17 => (orderedInterval (-29566673437 / 1000000000000) (-29566645227 / 1000000000000), orderedInterval (8720534925 / 1000000000000) (8720563135 / 1000000000000))
    | 18 => (orderedInterval (31292329593 / 1000000000000) (31292329594 / 1000000000000), orderedInterval (27119720026 / 1000000000000) (27119720027 / 1000000000000))
    | 19 => (orderedInterval (36318510431 / 1000000000000) (36318510432 / 1000000000000), orderedInterval (26520328963 / 1000000000000) (26520328964 / 1000000000000))
    | 20 => (orderedInterval (24894865291 / 1000000000000) (24894867003 / 1000000000000), orderedInterval (-51220284259 / 1000000000000) (-51220282547 / 1000000000000))
    | 21 => (orderedInterval (-19444080073 / 1000000000000) (-19444079814 / 1000000000000), orderedInterval (75195291082 / 1000000000000) (75195291341 / 1000000000000))
    | 22 => (orderedInterval (-40543693661 / 1000000000000) (-40543648065 / 1000000000000), orderedInterval (24004230307 / 1000000000000) (24004275903 / 1000000000000))
    | 23 => (orderedInterval (-9520724389 / 1000000000000) (-9520724388 / 1000000000000), orderedInterval (-39138278981 / 1000000000000) (-39138278980 / 1000000000000))
    | 24 => (orderedInterval (-6035425637 / 1000000000000) (-6035425635 / 1000000000000), orderedInterval (-61649252365 / 1000000000000) (-61649252363 / 1000000000000))
    | 25 => (orderedInterval (17831165368 / 1000000000000) (17831166069 / 1000000000000), orderedInterval (-25043923968 / 1000000000000) (-25043923267 / 1000000000000))
    | _ => (orderedInterval (-36905926082 / 1000000000000) (-36905922403 / 1000000000000), orderedInterval (7248720979 / 1000000000000) (7248724659 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-17323020517 / 1000000000000) (-17323004420 / 1000000000000)
      | 1 => orderedInterval (1929065041 / 1000000000000) (1929065121 / 1000000000000)
      | 2 => orderedInterval (-93499247 / 1000000000000) (-93498852 / 1000000000000)
      | 3 => orderedInterval (-1595323560 / 1000000000000) (-1595315379 / 1000000000000)
      | 4 => orderedInterval (3495328233 / 1000000000000) (3495328367 / 1000000000000)
      | 5 => orderedInterval (1512578158 / 1000000000000) (1512578922 / 1000000000000)
      | 6 => orderedInterval (-6248574047 / 1000000000000) (-6248573899 / 1000000000000)
      | 7 => orderedInterval (2008502894 / 1000000000000) (2008503977 / 1000000000000)
      | _ => orderedInterval (5436657866 / 1000000000000) (5436658715 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (8133635911 / 1000000000000) (8133653151 / 1000000000000)
      | 1 => orderedInterval (2548420357 / 1000000000000) (2548420428 / 1000000000000)
      | 2 => orderedInterval (623384255 / 1000000000000) (623385031 / 1000000000000)
      | 3 => orderedInterval (-12791918109 / 1000000000000) (-12791899398 / 1000000000000)
      | 4 => orderedInterval (452850247 / 1000000000000) (452850456 / 1000000000000)
      | 5 => orderedInterval (186440076 / 1000000000000) (186441471 / 1000000000000)
      | 6 => orderedInterval (-6641521517 / 1000000000000) (-6641521402 / 1000000000000)
      | 7 => orderedInterval (2408251245 / 1000000000000) (2408252105 / 1000000000000)
      | _ => orderedInterval (1931452075 / 1000000000000) (1931453180 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (17958637693 / 1000000000000) (17958656343 / 1000000000000)
      | 1 => orderedInterval (-2659720751 / 1000000000000) (-2659720670 / 1000000000000)
      | 2 => orderedInterval (1817752237 / 1000000000000) (1817753767 / 1000000000000)
      | 3 => orderedInterval (1393509983 / 1000000000000) (1393552854 / 1000000000000)
      | 4 => orderedInterval (-8892214145 / 1000000000000) (-8892213816 / 1000000000000)
      | 5 => orderedInterval (-1180279264 / 1000000000000) (-1180276705 / 1000000000000)
      | 6 => orderedInterval (6559732759 / 1000000000000) (6559732857 / 1000000000000)
      | 7 => orderedInterval (-1468507471 / 1000000000000) (-1468506780 / 1000000000000)
      | _ => orderedInterval (-5660892935 / 1000000000000) (-5660891462 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-8884798795 / 1000000000000) (-8884778520 / 1000000000000)
      | 1 => orderedInterval (-8018640769 / 1000000000000) (-8018640659 / 1000000000000)
      | 2 => orderedInterval (-1893316140 / 1000000000000) (-1893313125 / 1000000000000)
      | 3 => orderedInterval (55395118197 / 1000000000000) (55395216345 / 1000000000000)
      | 4 => orderedInterval (-2718740335 / 1000000000000) (-2718739813 / 1000000000000)
      | 5 => orderedInterval (-795388989 / 1000000000000) (-795384287 / 1000000000000)
      | 6 => orderedInterval (5866860225 / 1000000000000) (5866860313 / 1000000000000)
      | 7 => orderedInterval (-3488043876 / 1000000000000) (-3488043319 / 1000000000000)
      | _ => orderedInterval (-10448968820 / 1000000000000) (-10448966805 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-18991702278 / 1000000000000) (-18991680011 / 1000000000000)
      | 1 => orderedInterval (5974259184 / 1000000000000) (5974259347 / 1000000000000)
      | 2 => orderedInterval (-10199751214 / 1000000000000) (-10199745255 / 1000000000000)
      | 3 => orderedInterval (7293624805 / 1000000000000) (7293849820 / 1000000000000)
      | 4 => orderedInterval (24184715627 / 1000000000000) (24184716466 / 1000000000000)
      | 5 => orderedInterval (-2556590213 / 1000000000000) (-2556581545 / 1000000000000)
      | 6 => orderedInterval (-6600345463 / 1000000000000) (-6600345381 / 1000000000000)
      | 7 => orderedInterval (1383594881 / 1000000000000) (1383595334 / 1000000000000)
      | _ => orderedInterval (-817659704 / 1000000000000) (-817656854 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-10878285179 / 1000000000000) (-10878257448 / 1000000000000)
    | 1 => orderedInterval (-3149005460 / 1000000000000) (-3148964978 / 1000000000000)
    | 2 => orderedInterval (7868018106 / 1000000000000) (7868086388 / 1000000000000)
    | 3 => orderedInterval (25014080698 / 1000000000000) (25014210130 / 1000000000000)
    | _ => orderedInterval (-329854375 / 1000000000000) (-329588079 / 1000000000000)

theorem compactCertificate491_stateChecks0 :
    compactCertificate491.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 115 12 (725 / 2)) (orderedInterval (-38072704490 / 1000000000000) (-38072678996 / 1000000000000), orderedInterval (17564254093 / 1000000000000) (17564279586 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (42722537489129 / 160000000000)) (orderedInterval (-33829941230 / 1000000000000) (-33829941229 / 1000000000000), orderedInterval (-35146556082 / 1000000000000) (-35146556081 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 137 12 (13815590834057 / 32000000000)) (orderedInterval (-32669846458 / 1000000000000) (-32669744767 / 1000000000000), orderedInterval (20217916159 / 1000000000000) (20218017850 / 1000000000000))) = true
  rfl'

theorem compactCertificate491_stateChecks1 :
    compactCertificate491.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (12466329887803 / 160000000000)) (orderedInterval (-14270616993 / 1000000000000) (-14270616991 / 1000000000000), orderedInterval (-89167885005 / 1000000000000) (-89167885004 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (33486315612991 / 160000000000)) (orderedInterval (22107393462 / 1000000000000) (22107394454 / 1000000000000), orderedInterval (-50580863362 / 1000000000000) (-50580862370 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 181 12 (90921860905347 / 160000000000)) (orderedInterval (-13603380716 / 1000000000000) (-13603380715 / 1000000000000), orderedInterval (-30569753285 / 1000000000000) (-30569753284 / 1000000000000))) = true
  rfl'

theorem compactCertificate491_stateChecks2 :
    compactCertificate491.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 133 12 (66972631226011 / 160000000000)) (orderedInterval (-38969786232 / 1000000000000) (-38969786045 / 1000000000000), orderedInterval (-1457439413 / 1000000000000) (-1457439226 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 228 12 (114758745117703 / 160000000000)) (orderedInterval (29345425595 / 1000000000000) (29345437713 / 1000000000000), orderedInterval (-5162383123 / 1000000000000) (-5162371004 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 168 12 (84530772249877 / 160000000000)) (orderedInterval (33582860269 / 1000000000000) (33582860287 / 1000000000000), orderedInterval (8753778741 / 1000000000000) (8753778759 / 1000000000000))) = true
  rfl'

theorem compactCertificate491_stateChecks3 :
    compactCertificate491.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 258 12 (129691942694971 / 160000000000)) (orderedInterval (20661146131 / 1000000000000) (20661146132 / 1000000000000), orderedInterval (18921620276 / 1000000000000) (18921620277 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 149 12 (74877678026659 / 160000000000)) (orderedInterval (-22999355939 / 1000000000000) (-22999355938 / 1000000000000), orderedInterval (-28808925898 / 1000000000000) (-28808925897 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 264 12 (132871753636031 / 160000000000)) (orderedInterval (26590355679 / 1000000000000) (26590412217 / 1000000000000), orderedInterval (-7732830820 / 1000000000000) (-7732774282 / 1000000000000))) = true
  rfl'

theorem compactCertificate491_stateChecks4 :
    compactCertificate491.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 247 12 (124146027917339 / 160000000000)) (orderedInterval (-18984686135 / 1000000000000) (-18984686134 / 1000000000000), orderedInterval (-21436783653 / 1000000000000) (-21436783652 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 176 12 (88596463435787 / 160000000000)) (orderedInterval (33899007745 / 1000000000000) (33899008706 / 1000000000000), orderedInterval (-775340228 / 1000000000000) (-775339266 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 200 12 (100458946838973 / 160000000000)) (orderedInterval (10471385794 / 1000000000000) (10471385795 / 1000000000000), orderedInterval (30063051723 / 1000000000000) (30063051724 / 1000000000000))) = true
  rfl'

theorem compactCertificate491_stateChecks5 :
    compactCertificate491.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 167 12 (83752196502637 / 160000000000)) (orderedInterval (13887850620 / 1000000000000) (13887850744 / 1000000000000), orderedInterval (-32002715594 / 1000000000000) (-32002715470 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 147 12 (73997605559377 / 160000000000)) (orderedInterval (-36857451871 / 1000000000000) (-36857451782 / 1000000000000), orderedInterval (-4208350808 / 1000000000000) (-4208350719 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 213 12 (21447390286323 / 32000000000)) (orderedInterval (-29566673437 / 1000000000000) (-29566645227 / 1000000000000), orderedInterval (8720534925 / 1000000000000) (8720563135 / 1000000000000))) = true
  rfl'

theorem compactCertificate491_stateChecks6 :
    compactCertificate491.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 118 12 (59324610246281 / 160000000000)) (orderedInterval (31292329593 / 1000000000000) (31292329594 / 1000000000000), orderedInterval (27119720026 / 1000000000000) (27119720027 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 100 12 (50290129107841 / 160000000000)) (orderedInterval (36318510431 / 1000000000000) (36318510432 / 1000000000000), orderedInterval (26520328963 / 1000000000000) (26520328964 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (31469227750123 / 160000000000)) (orderedInterval (24894865291 / 1000000000000) (24894867003 / 1000000000000), orderedInterval (-51220284259 / 1000000000000) (-51220282547 / 1000000000000))) = true
  rfl'

theorem compactCertificate491_stateChecks7 :
    compactCertificate491.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (16924255345941 / 160000000000)) (orderedInterval (-19444080073 / 1000000000000) (-19444079814 / 1000000000000), orderedInterval (75195291082 / 1000000000000) (75195291341 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 91 12 (45952645500823 / 160000000000)) (orderedInterval (-40543693661 / 1000000000000) (-40543648065 / 1000000000000), orderedInterval (24004230307 / 1000000000000) (24004275903 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 125 12 (62744408818871 / 160000000000)) (orderedInterval (-9520724389 / 1000000000000) (-9520724388 / 1000000000000), orderedInterval (-39138278981 / 1000000000000) (-39138278980 / 1000000000000))) = true
  rfl'

theorem compactCertificate491_stateChecks8 :
    compactCertificate491.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (26530772249877 / 160000000000)) (orderedInterval (-6035425637 / 1000000000000) (-6035425635 / 1000000000000), orderedInterval (-61649252365 / 1000000000000) (-61649252363 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 215 12 (107846116251317 / 160000000000)) (orderedInterval (17831165368 / 1000000000000) (17831166069 / 1000000000000), orderedInterval (-25043923968 / 1000000000000) (-25043923267 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 143 12 (72036207628603 / 160000000000)) (orderedInterval (-36905926082 / 1000000000000) (-36905922403 / 1000000000000), orderedInterval (7248720979 / 1000000000000) (7248724659 / 1000000000000))) = true
  rfl'

theorem compactCertificate491_states : ∀ j,
    BesselStateValid (compactCertificate491.point j) (compactCertificate491.state j) :=
  compactCertificate491.statesValid_of_checks3 compactCertificate491_stateChecks0
    compactCertificate491_stateChecks1 compactCertificate491_stateChecks2
    compactCertificate491_stateChecks3 compactCertificate491_stateChecks4
    compactCertificate491_stateChecks5 compactCertificate491_stateChecks6
    compactCertificate491_stateChecks7 compactCertificate491_stateChecks8

theorem compactCertificate491_chunkChecks0_0 :
    compactCertificate491.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (725 / 2) 0 (IntervalRat.scale (725 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-38072704490 / 1000000000000) (-38072678996 / 1000000000000), orderedInterval (17564254093 / 1000000000000) (17564279586 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (42722537489129 / 160000000000) 0 (IntervalRat.scale (725 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-33829941230 / 1000000000000) (-33829941229 / 1000000000000), orderedInterval (-35146556082 / 1000000000000) (-35146556081 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (13815590834057 / 32000000000) 0 (IntervalRat.scale (725 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-32669846458 / 1000000000000) (-32669744767 / 1000000000000), orderedInterval (20217916159 / 1000000000000) (20218017850 / 1000000000000)))) (orderedInterval (-17323020517 / 1000000000000) (-17323004420 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (12466329887803 / 160000000000) 0 (IntervalRat.scale (725 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-14270616993 / 1000000000000) (-14270616991 / 1000000000000), orderedInterval (-89167885005 / 1000000000000) (-89167885004 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (33486315612991 / 160000000000) 0 (IntervalRat.scale (725 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (22107393462 / 1000000000000) (22107394454 / 1000000000000), orderedInterval (-50580863362 / 1000000000000) (-50580862370 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (90921860905347 / 160000000000) 0 (IntervalRat.scale (725 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-13603380716 / 1000000000000) (-13603380715 / 1000000000000), orderedInterval (-30569753285 / 1000000000000) (-30569753284 / 1000000000000)))) (orderedInterval (1929065041 / 1000000000000) (1929065121 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (66972631226011 / 160000000000) 0 (IntervalRat.scale (725 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-38969786232 / 1000000000000) (-38969786045 / 1000000000000), orderedInterval (-1457439413 / 1000000000000) (-1457439226 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (114758745117703 / 160000000000) 0 (IntervalRat.scale (725 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (29345425595 / 1000000000000) (29345437713 / 1000000000000), orderedInterval (-5162383123 / 1000000000000) (-5162371004 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (84530772249877 / 160000000000) 0 (IntervalRat.scale (725 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (33582860269 / 1000000000000) (33582860287 / 1000000000000), orderedInterval (8753778741 / 1000000000000) (8753778759 / 1000000000000)))) (orderedInterval (-93499247 / 1000000000000) (-93498852 / 1000000000000))) = true
  rfl'

theorem compactCertificate491_chunkChecks0_1 :
    compactCertificate491.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (129691942694971 / 160000000000) 0 (IntervalRat.scale (725 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (20661146131 / 1000000000000) (20661146132 / 1000000000000), orderedInterval (18921620276 / 1000000000000) (18921620277 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (74877678026659 / 160000000000) 0 (IntervalRat.scale (725 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-22999355939 / 1000000000000) (-22999355938 / 1000000000000), orderedInterval (-28808925898 / 1000000000000) (-28808925897 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (132871753636031 / 160000000000) 0 (IntervalRat.scale (725 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (26590355679 / 1000000000000) (26590412217 / 1000000000000), orderedInterval (-7732830820 / 1000000000000) (-7732774282 / 1000000000000)))) (orderedInterval (-1595323560 / 1000000000000) (-1595315379 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (124146027917339 / 160000000000) 0 (IntervalRat.scale (725 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-18984686135 / 1000000000000) (-18984686134 / 1000000000000), orderedInterval (-21436783653 / 1000000000000) (-21436783652 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (88596463435787 / 160000000000) 0 (IntervalRat.scale (725 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (33899007745 / 1000000000000) (33899008706 / 1000000000000), orderedInterval (-775340228 / 1000000000000) (-775339266 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (100458946838973 / 160000000000) 0 (IntervalRat.scale (725 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (10471385794 / 1000000000000) (10471385795 / 1000000000000), orderedInterval (30063051723 / 1000000000000) (30063051724 / 1000000000000)))) (orderedInterval (3495328233 / 1000000000000) (3495328367 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (83752196502637 / 160000000000) 0 (IntervalRat.scale (725 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (13887850620 / 1000000000000) (13887850744 / 1000000000000), orderedInterval (-32002715594 / 1000000000000) (-32002715470 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (73997605559377 / 160000000000) 0 (IntervalRat.scale (725 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-36857451871 / 1000000000000) (-36857451782 / 1000000000000), orderedInterval (-4208350808 / 1000000000000) (-4208350719 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (21447390286323 / 32000000000) 0 (IntervalRat.scale (725 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-29566673437 / 1000000000000) (-29566645227 / 1000000000000), orderedInterval (8720534925 / 1000000000000) (8720563135 / 1000000000000)))) (orderedInterval (1512578158 / 1000000000000) (1512578922 / 1000000000000))) = true
  rfl'

theorem compactCertificate491_chunkChecks0_2 :
    compactCertificate491.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (59324610246281 / 160000000000) 0 (IntervalRat.scale (725 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (31292329593 / 1000000000000) (31292329594 / 1000000000000), orderedInterval (27119720026 / 1000000000000) (27119720027 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (50290129107841 / 160000000000) 0 (IntervalRat.scale (725 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (36318510431 / 1000000000000) (36318510432 / 1000000000000), orderedInterval (26520328963 / 1000000000000) (26520328964 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (31469227750123 / 160000000000) 0 (IntervalRat.scale (725 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (24894865291 / 1000000000000) (24894867003 / 1000000000000), orderedInterval (-51220284259 / 1000000000000) (-51220282547 / 1000000000000)))) (orderedInterval (-6248574047 / 1000000000000) (-6248573899 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (16924255345941 / 160000000000) 0 (IntervalRat.scale (725 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-19444080073 / 1000000000000) (-19444079814 / 1000000000000), orderedInterval (75195291082 / 1000000000000) (75195291341 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (45952645500823 / 160000000000) 0 (IntervalRat.scale (725 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-40543693661 / 1000000000000) (-40543648065 / 1000000000000), orderedInterval (24004230307 / 1000000000000) (24004275903 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (62744408818871 / 160000000000) 0 (IntervalRat.scale (725 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-9520724389 / 1000000000000) (-9520724388 / 1000000000000), orderedInterval (-39138278981 / 1000000000000) (-39138278980 / 1000000000000)))) (orderedInterval (2008502894 / 1000000000000) (2008503977 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (26530772249877 / 160000000000) 0 (IntervalRat.scale (725 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-6035425637 / 1000000000000) (-6035425635 / 1000000000000), orderedInterval (-61649252365 / 1000000000000) (-61649252363 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (107846116251317 / 160000000000) 0 (IntervalRat.scale (725 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (17831165368 / 1000000000000) (17831166069 / 1000000000000), orderedInterval (-25043923968 / 1000000000000) (-25043923267 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (72036207628603 / 160000000000) 0 (IntervalRat.scale (725 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-36905926082 / 1000000000000) (-36905922403 / 1000000000000), orderedInterval (7248720979 / 1000000000000) (7248724659 / 1000000000000)))) (orderedInterval (5436657866 / 1000000000000) (5436658715 / 1000000000000))) = true
  rfl'

theorem compactCertificate491_chunkChecks0 :
    compactCertificate491.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate491.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate491_chunkChecks0_0
    compactCertificate491_chunkChecks0_1 compactCertificate491_chunkChecks0_2

theorem compactCertificate491_chunkChecks1_0 :
    compactCertificate491.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (725 / 2) 1 (IntervalRat.scale (725 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-38072704490 / 1000000000000) (-38072678996 / 1000000000000), orderedInterval (17564254093 / 1000000000000) (17564279586 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (42722537489129 / 160000000000) 1 (IntervalRat.scale (725 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-33829941230 / 1000000000000) (-33829941229 / 1000000000000), orderedInterval (-35146556082 / 1000000000000) (-35146556081 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (13815590834057 / 32000000000) 1 (IntervalRat.scale (725 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-32669846458 / 1000000000000) (-32669744767 / 1000000000000), orderedInterval (20217916159 / 1000000000000) (20218017850 / 1000000000000)))) (orderedInterval (8133635911 / 1000000000000) (8133653151 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (12466329887803 / 160000000000) 1 (IntervalRat.scale (725 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-14270616993 / 1000000000000) (-14270616991 / 1000000000000), orderedInterval (-89167885005 / 1000000000000) (-89167885004 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (33486315612991 / 160000000000) 1 (IntervalRat.scale (725 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (22107393462 / 1000000000000) (22107394454 / 1000000000000), orderedInterval (-50580863362 / 1000000000000) (-50580862370 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (90921860905347 / 160000000000) 1 (IntervalRat.scale (725 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-13603380716 / 1000000000000) (-13603380715 / 1000000000000), orderedInterval (-30569753285 / 1000000000000) (-30569753284 / 1000000000000)))) (orderedInterval (2548420357 / 1000000000000) (2548420428 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (66972631226011 / 160000000000) 1 (IntervalRat.scale (725 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-38969786232 / 1000000000000) (-38969786045 / 1000000000000), orderedInterval (-1457439413 / 1000000000000) (-1457439226 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (114758745117703 / 160000000000) 1 (IntervalRat.scale (725 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (29345425595 / 1000000000000) (29345437713 / 1000000000000), orderedInterval (-5162383123 / 1000000000000) (-5162371004 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (84530772249877 / 160000000000) 1 (IntervalRat.scale (725 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (33582860269 / 1000000000000) (33582860287 / 1000000000000), orderedInterval (8753778741 / 1000000000000) (8753778759 / 1000000000000)))) (orderedInterval (623384255 / 1000000000000) (623385031 / 1000000000000))) = true
  rfl'

theorem compactCertificate491_chunkChecks1_1 :
    compactCertificate491.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (129691942694971 / 160000000000) 1 (IntervalRat.scale (725 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (20661146131 / 1000000000000) (20661146132 / 1000000000000), orderedInterval (18921620276 / 1000000000000) (18921620277 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (74877678026659 / 160000000000) 1 (IntervalRat.scale (725 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-22999355939 / 1000000000000) (-22999355938 / 1000000000000), orderedInterval (-28808925898 / 1000000000000) (-28808925897 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (132871753636031 / 160000000000) 1 (IntervalRat.scale (725 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (26590355679 / 1000000000000) (26590412217 / 1000000000000), orderedInterval (-7732830820 / 1000000000000) (-7732774282 / 1000000000000)))) (orderedInterval (-12791918109 / 1000000000000) (-12791899398 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (124146027917339 / 160000000000) 1 (IntervalRat.scale (725 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-18984686135 / 1000000000000) (-18984686134 / 1000000000000), orderedInterval (-21436783653 / 1000000000000) (-21436783652 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (88596463435787 / 160000000000) 1 (IntervalRat.scale (725 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (33899007745 / 1000000000000) (33899008706 / 1000000000000), orderedInterval (-775340228 / 1000000000000) (-775339266 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (100458946838973 / 160000000000) 1 (IntervalRat.scale (725 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (10471385794 / 1000000000000) (10471385795 / 1000000000000), orderedInterval (30063051723 / 1000000000000) (30063051724 / 1000000000000)))) (orderedInterval (452850247 / 1000000000000) (452850456 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (83752196502637 / 160000000000) 1 (IntervalRat.scale (725 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (13887850620 / 1000000000000) (13887850744 / 1000000000000), orderedInterval (-32002715594 / 1000000000000) (-32002715470 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (73997605559377 / 160000000000) 1 (IntervalRat.scale (725 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-36857451871 / 1000000000000) (-36857451782 / 1000000000000), orderedInterval (-4208350808 / 1000000000000) (-4208350719 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (21447390286323 / 32000000000) 1 (IntervalRat.scale (725 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-29566673437 / 1000000000000) (-29566645227 / 1000000000000), orderedInterval (8720534925 / 1000000000000) (8720563135 / 1000000000000)))) (orderedInterval (186440076 / 1000000000000) (186441471 / 1000000000000))) = true
  rfl'

theorem compactCertificate491_chunkChecks1_2 :
    compactCertificate491.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (59324610246281 / 160000000000) 1 (IntervalRat.scale (725 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (31292329593 / 1000000000000) (31292329594 / 1000000000000), orderedInterval (27119720026 / 1000000000000) (27119720027 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (50290129107841 / 160000000000) 1 (IntervalRat.scale (725 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (36318510431 / 1000000000000) (36318510432 / 1000000000000), orderedInterval (26520328963 / 1000000000000) (26520328964 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (31469227750123 / 160000000000) 1 (IntervalRat.scale (725 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (24894865291 / 1000000000000) (24894867003 / 1000000000000), orderedInterval (-51220284259 / 1000000000000) (-51220282547 / 1000000000000)))) (orderedInterval (-6641521517 / 1000000000000) (-6641521402 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (16924255345941 / 160000000000) 1 (IntervalRat.scale (725 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-19444080073 / 1000000000000) (-19444079814 / 1000000000000), orderedInterval (75195291082 / 1000000000000) (75195291341 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (45952645500823 / 160000000000) 1 (IntervalRat.scale (725 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-40543693661 / 1000000000000) (-40543648065 / 1000000000000), orderedInterval (24004230307 / 1000000000000) (24004275903 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (62744408818871 / 160000000000) 1 (IntervalRat.scale (725 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-9520724389 / 1000000000000) (-9520724388 / 1000000000000), orderedInterval (-39138278981 / 1000000000000) (-39138278980 / 1000000000000)))) (orderedInterval (2408251245 / 1000000000000) (2408252105 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (26530772249877 / 160000000000) 1 (IntervalRat.scale (725 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-6035425637 / 1000000000000) (-6035425635 / 1000000000000), orderedInterval (-61649252365 / 1000000000000) (-61649252363 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (107846116251317 / 160000000000) 1 (IntervalRat.scale (725 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (17831165368 / 1000000000000) (17831166069 / 1000000000000), orderedInterval (-25043923968 / 1000000000000) (-25043923267 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (72036207628603 / 160000000000) 1 (IntervalRat.scale (725 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-36905926082 / 1000000000000) (-36905922403 / 1000000000000), orderedInterval (7248720979 / 1000000000000) (7248724659 / 1000000000000)))) (orderedInterval (1931452075 / 1000000000000) (1931453180 / 1000000000000))) = true
  rfl'

theorem compactCertificate491_chunkChecks1 :
    compactCertificate491.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate491.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate491_chunkChecks1_0
    compactCertificate491_chunkChecks1_1 compactCertificate491_chunkChecks1_2

theorem compactCertificate491_chunkChecks2_0 :
    compactCertificate491.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (725 / 2) 2 (IntervalRat.scale (725 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-38072704490 / 1000000000000) (-38072678996 / 1000000000000), orderedInterval (17564254093 / 1000000000000) (17564279586 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (42722537489129 / 160000000000) 2 (IntervalRat.scale (725 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-33829941230 / 1000000000000) (-33829941229 / 1000000000000), orderedInterval (-35146556082 / 1000000000000) (-35146556081 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (13815590834057 / 32000000000) 2 (IntervalRat.scale (725 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-32669846458 / 1000000000000) (-32669744767 / 1000000000000), orderedInterval (20217916159 / 1000000000000) (20218017850 / 1000000000000)))) (orderedInterval (17958637693 / 1000000000000) (17958656343 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (12466329887803 / 160000000000) 2 (IntervalRat.scale (725 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-14270616993 / 1000000000000) (-14270616991 / 1000000000000), orderedInterval (-89167885005 / 1000000000000) (-89167885004 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (33486315612991 / 160000000000) 2 (IntervalRat.scale (725 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (22107393462 / 1000000000000) (22107394454 / 1000000000000), orderedInterval (-50580863362 / 1000000000000) (-50580862370 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (90921860905347 / 160000000000) 2 (IntervalRat.scale (725 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-13603380716 / 1000000000000) (-13603380715 / 1000000000000), orderedInterval (-30569753285 / 1000000000000) (-30569753284 / 1000000000000)))) (orderedInterval (-2659720751 / 1000000000000) (-2659720670 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (66972631226011 / 160000000000) 2 (IntervalRat.scale (725 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-38969786232 / 1000000000000) (-38969786045 / 1000000000000), orderedInterval (-1457439413 / 1000000000000) (-1457439226 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (114758745117703 / 160000000000) 2 (IntervalRat.scale (725 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (29345425595 / 1000000000000) (29345437713 / 1000000000000), orderedInterval (-5162383123 / 1000000000000) (-5162371004 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (84530772249877 / 160000000000) 2 (IntervalRat.scale (725 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (33582860269 / 1000000000000) (33582860287 / 1000000000000), orderedInterval (8753778741 / 1000000000000) (8753778759 / 1000000000000)))) (orderedInterval (1817752237 / 1000000000000) (1817753767 / 1000000000000))) = true
  rfl'

theorem compactCertificate491_chunkChecks2_1 :
    compactCertificate491.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (129691942694971 / 160000000000) 2 (IntervalRat.scale (725 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (20661146131 / 1000000000000) (20661146132 / 1000000000000), orderedInterval (18921620276 / 1000000000000) (18921620277 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (74877678026659 / 160000000000) 2 (IntervalRat.scale (725 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-22999355939 / 1000000000000) (-22999355938 / 1000000000000), orderedInterval (-28808925898 / 1000000000000) (-28808925897 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (132871753636031 / 160000000000) 2 (IntervalRat.scale (725 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (26590355679 / 1000000000000) (26590412217 / 1000000000000), orderedInterval (-7732830820 / 1000000000000) (-7732774282 / 1000000000000)))) (orderedInterval (1393509983 / 1000000000000) (1393552854 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (124146027917339 / 160000000000) 2 (IntervalRat.scale (725 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-18984686135 / 1000000000000) (-18984686134 / 1000000000000), orderedInterval (-21436783653 / 1000000000000) (-21436783652 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (88596463435787 / 160000000000) 2 (IntervalRat.scale (725 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (33899007745 / 1000000000000) (33899008706 / 1000000000000), orderedInterval (-775340228 / 1000000000000) (-775339266 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (100458946838973 / 160000000000) 2 (IntervalRat.scale (725 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (10471385794 / 1000000000000) (10471385795 / 1000000000000), orderedInterval (30063051723 / 1000000000000) (30063051724 / 1000000000000)))) (orderedInterval (-8892214145 / 1000000000000) (-8892213816 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (83752196502637 / 160000000000) 2 (IntervalRat.scale (725 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (13887850620 / 1000000000000) (13887850744 / 1000000000000), orderedInterval (-32002715594 / 1000000000000) (-32002715470 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (73997605559377 / 160000000000) 2 (IntervalRat.scale (725 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-36857451871 / 1000000000000) (-36857451782 / 1000000000000), orderedInterval (-4208350808 / 1000000000000) (-4208350719 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (21447390286323 / 32000000000) 2 (IntervalRat.scale (725 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-29566673437 / 1000000000000) (-29566645227 / 1000000000000), orderedInterval (8720534925 / 1000000000000) (8720563135 / 1000000000000)))) (orderedInterval (-1180279264 / 1000000000000) (-1180276705 / 1000000000000))) = true
  rfl'

theorem compactCertificate491_chunkChecks2_2 :
    compactCertificate491.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (59324610246281 / 160000000000) 2 (IntervalRat.scale (725 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (31292329593 / 1000000000000) (31292329594 / 1000000000000), orderedInterval (27119720026 / 1000000000000) (27119720027 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (50290129107841 / 160000000000) 2 (IntervalRat.scale (725 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (36318510431 / 1000000000000) (36318510432 / 1000000000000), orderedInterval (26520328963 / 1000000000000) (26520328964 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (31469227750123 / 160000000000) 2 (IntervalRat.scale (725 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (24894865291 / 1000000000000) (24894867003 / 1000000000000), orderedInterval (-51220284259 / 1000000000000) (-51220282547 / 1000000000000)))) (orderedInterval (6559732759 / 1000000000000) (6559732857 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (16924255345941 / 160000000000) 2 (IntervalRat.scale (725 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-19444080073 / 1000000000000) (-19444079814 / 1000000000000), orderedInterval (75195291082 / 1000000000000) (75195291341 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (45952645500823 / 160000000000) 2 (IntervalRat.scale (725 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-40543693661 / 1000000000000) (-40543648065 / 1000000000000), orderedInterval (24004230307 / 1000000000000) (24004275903 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (62744408818871 / 160000000000) 2 (IntervalRat.scale (725 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-9520724389 / 1000000000000) (-9520724388 / 1000000000000), orderedInterval (-39138278981 / 1000000000000) (-39138278980 / 1000000000000)))) (orderedInterval (-1468507471 / 1000000000000) (-1468506780 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (26530772249877 / 160000000000) 2 (IntervalRat.scale (725 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-6035425637 / 1000000000000) (-6035425635 / 1000000000000), orderedInterval (-61649252365 / 1000000000000) (-61649252363 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (107846116251317 / 160000000000) 2 (IntervalRat.scale (725 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (17831165368 / 1000000000000) (17831166069 / 1000000000000), orderedInterval (-25043923968 / 1000000000000) (-25043923267 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (72036207628603 / 160000000000) 2 (IntervalRat.scale (725 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-36905926082 / 1000000000000) (-36905922403 / 1000000000000), orderedInterval (7248720979 / 1000000000000) (7248724659 / 1000000000000)))) (orderedInterval (-5660892935 / 1000000000000) (-5660891462 / 1000000000000))) = true
  rfl'

theorem compactCertificate491_chunkChecks2 :
    compactCertificate491.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate491.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate491_chunkChecks2_0
    compactCertificate491_chunkChecks2_1 compactCertificate491_chunkChecks2_2

theorem compactCertificate491_chunkChecks3_0 :
    compactCertificate491.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (725 / 2) 3 (IntervalRat.scale (725 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-38072704490 / 1000000000000) (-38072678996 / 1000000000000), orderedInterval (17564254093 / 1000000000000) (17564279586 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (42722537489129 / 160000000000) 3 (IntervalRat.scale (725 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-33829941230 / 1000000000000) (-33829941229 / 1000000000000), orderedInterval (-35146556082 / 1000000000000) (-35146556081 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (13815590834057 / 32000000000) 3 (IntervalRat.scale (725 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-32669846458 / 1000000000000) (-32669744767 / 1000000000000), orderedInterval (20217916159 / 1000000000000) (20218017850 / 1000000000000)))) (orderedInterval (-8884798795 / 1000000000000) (-8884778520 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (12466329887803 / 160000000000) 3 (IntervalRat.scale (725 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-14270616993 / 1000000000000) (-14270616991 / 1000000000000), orderedInterval (-89167885005 / 1000000000000) (-89167885004 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (33486315612991 / 160000000000) 3 (IntervalRat.scale (725 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (22107393462 / 1000000000000) (22107394454 / 1000000000000), orderedInterval (-50580863362 / 1000000000000) (-50580862370 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (90921860905347 / 160000000000) 3 (IntervalRat.scale (725 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-13603380716 / 1000000000000) (-13603380715 / 1000000000000), orderedInterval (-30569753285 / 1000000000000) (-30569753284 / 1000000000000)))) (orderedInterval (-8018640769 / 1000000000000) (-8018640659 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (66972631226011 / 160000000000) 3 (IntervalRat.scale (725 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-38969786232 / 1000000000000) (-38969786045 / 1000000000000), orderedInterval (-1457439413 / 1000000000000) (-1457439226 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (114758745117703 / 160000000000) 3 (IntervalRat.scale (725 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (29345425595 / 1000000000000) (29345437713 / 1000000000000), orderedInterval (-5162383123 / 1000000000000) (-5162371004 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (84530772249877 / 160000000000) 3 (IntervalRat.scale (725 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (33582860269 / 1000000000000) (33582860287 / 1000000000000), orderedInterval (8753778741 / 1000000000000) (8753778759 / 1000000000000)))) (orderedInterval (-1893316140 / 1000000000000) (-1893313125 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate491_chunkChecks3_1 :
    compactCertificate491.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (129691942694971 / 160000000000) 3 (IntervalRat.scale (725 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (20661146131 / 1000000000000) (20661146132 / 1000000000000), orderedInterval (18921620276 / 1000000000000) (18921620277 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (74877678026659 / 160000000000) 3 (IntervalRat.scale (725 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-22999355939 / 1000000000000) (-22999355938 / 1000000000000), orderedInterval (-28808925898 / 1000000000000) (-28808925897 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (132871753636031 / 160000000000) 3 (IntervalRat.scale (725 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (26590355679 / 1000000000000) (26590412217 / 1000000000000), orderedInterval (-7732830820 / 1000000000000) (-7732774282 / 1000000000000)))) (orderedInterval (55395118197 / 1000000000000) (55395216345 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (124146027917339 / 160000000000) 3 (IntervalRat.scale (725 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-18984686135 / 1000000000000) (-18984686134 / 1000000000000), orderedInterval (-21436783653 / 1000000000000) (-21436783652 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (88596463435787 / 160000000000) 3 (IntervalRat.scale (725 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (33899007745 / 1000000000000) (33899008706 / 1000000000000), orderedInterval (-775340228 / 1000000000000) (-775339266 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (100458946838973 / 160000000000) 3 (IntervalRat.scale (725 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (10471385794 / 1000000000000) (10471385795 / 1000000000000), orderedInterval (30063051723 / 1000000000000) (30063051724 / 1000000000000)))) (orderedInterval (-2718740335 / 1000000000000) (-2718739813 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (83752196502637 / 160000000000) 3 (IntervalRat.scale (725 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (13887850620 / 1000000000000) (13887850744 / 1000000000000), orderedInterval (-32002715594 / 1000000000000) (-32002715470 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (73997605559377 / 160000000000) 3 (IntervalRat.scale (725 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-36857451871 / 1000000000000) (-36857451782 / 1000000000000), orderedInterval (-4208350808 / 1000000000000) (-4208350719 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (21447390286323 / 32000000000) 3 (IntervalRat.scale (725 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-29566673437 / 1000000000000) (-29566645227 / 1000000000000), orderedInterval (8720534925 / 1000000000000) (8720563135 / 1000000000000)))) (orderedInterval (-795388989 / 1000000000000) (-795384287 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate491_chunkChecks3_2 :
    compactCertificate491.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (59324610246281 / 160000000000) 3 (IntervalRat.scale (725 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (31292329593 / 1000000000000) (31292329594 / 1000000000000), orderedInterval (27119720026 / 1000000000000) (27119720027 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (50290129107841 / 160000000000) 3 (IntervalRat.scale (725 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (36318510431 / 1000000000000) (36318510432 / 1000000000000), orderedInterval (26520328963 / 1000000000000) (26520328964 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (31469227750123 / 160000000000) 3 (IntervalRat.scale (725 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (24894865291 / 1000000000000) (24894867003 / 1000000000000), orderedInterval (-51220284259 / 1000000000000) (-51220282547 / 1000000000000)))) (orderedInterval (5866860225 / 1000000000000) (5866860313 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (16924255345941 / 160000000000) 3 (IntervalRat.scale (725 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-19444080073 / 1000000000000) (-19444079814 / 1000000000000), orderedInterval (75195291082 / 1000000000000) (75195291341 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (45952645500823 / 160000000000) 3 (IntervalRat.scale (725 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-40543693661 / 1000000000000) (-40543648065 / 1000000000000), orderedInterval (24004230307 / 1000000000000) (24004275903 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (62744408818871 / 160000000000) 3 (IntervalRat.scale (725 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-9520724389 / 1000000000000) (-9520724388 / 1000000000000), orderedInterval (-39138278981 / 1000000000000) (-39138278980 / 1000000000000)))) (orderedInterval (-3488043876 / 1000000000000) (-3488043319 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (26530772249877 / 160000000000) 3 (IntervalRat.scale (725 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-6035425637 / 1000000000000) (-6035425635 / 1000000000000), orderedInterval (-61649252365 / 1000000000000) (-61649252363 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (107846116251317 / 160000000000) 3 (IntervalRat.scale (725 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (17831165368 / 1000000000000) (17831166069 / 1000000000000), orderedInterval (-25043923968 / 1000000000000) (-25043923267 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (72036207628603 / 160000000000) 3 (IntervalRat.scale (725 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-36905926082 / 1000000000000) (-36905922403 / 1000000000000), orderedInterval (7248720979 / 1000000000000) (7248724659 / 1000000000000)))) (orderedInterval (-10448968820 / 1000000000000) (-10448966805 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate491_chunkChecks3 :
    compactCertificate491.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate491.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate491_chunkChecks3_0
    compactCertificate491_chunkChecks3_1 compactCertificate491_chunkChecks3_2

theorem compactCertificate491_chunkChecks4_0 :
    compactCertificate491.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (725 / 2) 4 (IntervalRat.scale (725 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-38072704490 / 1000000000000) (-38072678996 / 1000000000000), orderedInterval (17564254093 / 1000000000000) (17564279586 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (42722537489129 / 160000000000) 4 (IntervalRat.scale (725 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-33829941230 / 1000000000000) (-33829941229 / 1000000000000), orderedInterval (-35146556082 / 1000000000000) (-35146556081 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (13815590834057 / 32000000000) 4 (IntervalRat.scale (725 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-32669846458 / 1000000000000) (-32669744767 / 1000000000000), orderedInterval (20217916159 / 1000000000000) (20218017850 / 1000000000000)))) (orderedInterval (-18991702278 / 1000000000000) (-18991680011 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (12466329887803 / 160000000000) 4 (IntervalRat.scale (725 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-14270616993 / 1000000000000) (-14270616991 / 1000000000000), orderedInterval (-89167885005 / 1000000000000) (-89167885004 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (33486315612991 / 160000000000) 4 (IntervalRat.scale (725 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (22107393462 / 1000000000000) (22107394454 / 1000000000000), orderedInterval (-50580863362 / 1000000000000) (-50580862370 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (90921860905347 / 160000000000) 4 (IntervalRat.scale (725 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-13603380716 / 1000000000000) (-13603380715 / 1000000000000), orderedInterval (-30569753285 / 1000000000000) (-30569753284 / 1000000000000)))) (orderedInterval (5974259184 / 1000000000000) (5974259347 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (66972631226011 / 160000000000) 4 (IntervalRat.scale (725 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-38969786232 / 1000000000000) (-38969786045 / 1000000000000), orderedInterval (-1457439413 / 1000000000000) (-1457439226 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (114758745117703 / 160000000000) 4 (IntervalRat.scale (725 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (29345425595 / 1000000000000) (29345437713 / 1000000000000), orderedInterval (-5162383123 / 1000000000000) (-5162371004 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (84530772249877 / 160000000000) 4 (IntervalRat.scale (725 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (33582860269 / 1000000000000) (33582860287 / 1000000000000), orderedInterval (8753778741 / 1000000000000) (8753778759 / 1000000000000)))) (orderedInterval (-10199751214 / 1000000000000) (-10199745255 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate491_chunkChecks4_1 :
    compactCertificate491.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (129691942694971 / 160000000000) 4 (IntervalRat.scale (725 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (20661146131 / 1000000000000) (20661146132 / 1000000000000), orderedInterval (18921620276 / 1000000000000) (18921620277 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (74877678026659 / 160000000000) 4 (IntervalRat.scale (725 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-22999355939 / 1000000000000) (-22999355938 / 1000000000000), orderedInterval (-28808925898 / 1000000000000) (-28808925897 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (132871753636031 / 160000000000) 4 (IntervalRat.scale (725 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (26590355679 / 1000000000000) (26590412217 / 1000000000000), orderedInterval (-7732830820 / 1000000000000) (-7732774282 / 1000000000000)))) (orderedInterval (7293624805 / 1000000000000) (7293849820 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (124146027917339 / 160000000000) 4 (IntervalRat.scale (725 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-18984686135 / 1000000000000) (-18984686134 / 1000000000000), orderedInterval (-21436783653 / 1000000000000) (-21436783652 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (88596463435787 / 160000000000) 4 (IntervalRat.scale (725 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (33899007745 / 1000000000000) (33899008706 / 1000000000000), orderedInterval (-775340228 / 1000000000000) (-775339266 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (100458946838973 / 160000000000) 4 (IntervalRat.scale (725 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (10471385794 / 1000000000000) (10471385795 / 1000000000000), orderedInterval (30063051723 / 1000000000000) (30063051724 / 1000000000000)))) (orderedInterval (24184715627 / 1000000000000) (24184716466 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (83752196502637 / 160000000000) 4 (IntervalRat.scale (725 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (13887850620 / 1000000000000) (13887850744 / 1000000000000), orderedInterval (-32002715594 / 1000000000000) (-32002715470 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (73997605559377 / 160000000000) 4 (IntervalRat.scale (725 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-36857451871 / 1000000000000) (-36857451782 / 1000000000000), orderedInterval (-4208350808 / 1000000000000) (-4208350719 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (21447390286323 / 32000000000) 4 (IntervalRat.scale (725 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-29566673437 / 1000000000000) (-29566645227 / 1000000000000), orderedInterval (8720534925 / 1000000000000) (8720563135 / 1000000000000)))) (orderedInterval (-2556590213 / 1000000000000) (-2556581545 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate491_chunkChecks4_2 :
    compactCertificate491.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (59324610246281 / 160000000000) 4 (IntervalRat.scale (725 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (31292329593 / 1000000000000) (31292329594 / 1000000000000), orderedInterval (27119720026 / 1000000000000) (27119720027 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (50290129107841 / 160000000000) 4 (IntervalRat.scale (725 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (36318510431 / 1000000000000) (36318510432 / 1000000000000), orderedInterval (26520328963 / 1000000000000) (26520328964 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (31469227750123 / 160000000000) 4 (IntervalRat.scale (725 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (24894865291 / 1000000000000) (24894867003 / 1000000000000), orderedInterval (-51220284259 / 1000000000000) (-51220282547 / 1000000000000)))) (orderedInterval (-6600345463 / 1000000000000) (-6600345381 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (16924255345941 / 160000000000) 4 (IntervalRat.scale (725 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-19444080073 / 1000000000000) (-19444079814 / 1000000000000), orderedInterval (75195291082 / 1000000000000) (75195291341 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (45952645500823 / 160000000000) 4 (IntervalRat.scale (725 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-40543693661 / 1000000000000) (-40543648065 / 1000000000000), orderedInterval (24004230307 / 1000000000000) (24004275903 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (62744408818871 / 160000000000) 4 (IntervalRat.scale (725 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-9520724389 / 1000000000000) (-9520724388 / 1000000000000), orderedInterval (-39138278981 / 1000000000000) (-39138278980 / 1000000000000)))) (orderedInterval (1383594881 / 1000000000000) (1383595334 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (26530772249877 / 160000000000) 4 (IntervalRat.scale (725 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-6035425637 / 1000000000000) (-6035425635 / 1000000000000), orderedInterval (-61649252365 / 1000000000000) (-61649252363 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (107846116251317 / 160000000000) 4 (IntervalRat.scale (725 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (17831165368 / 1000000000000) (17831166069 / 1000000000000), orderedInterval (-25043923968 / 1000000000000) (-25043923267 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (72036207628603 / 160000000000) 4 (IntervalRat.scale (725 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-36905926082 / 1000000000000) (-36905922403 / 1000000000000), orderedInterval (7248720979 / 1000000000000) (7248724659 / 1000000000000)))) (orderedInterval (-817659704 / 1000000000000) (-817656854 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate491_chunkChecks4 :
    compactCertificate491.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate491.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate491_chunkChecks4_0
    compactCertificate491_chunkChecks4_1 compactCertificate491_chunkChecks4_2

theorem compactCertificate491_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate491.chunkCheck r b = true :=
  compactCertificate491.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate491_chunkChecks0
    · exact compactCertificate491_chunkChecks1
    · exact compactCertificate491_chunkChecks2
    · exact compactCertificate491_chunkChecks3
    · exact compactCertificate491_chunkChecks4)

theorem compactCertificate491_coefficient0 :
    compactCertificate491.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate491_coefficient1 :
    compactCertificate491.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate491_coefficient2 :
    compactCertificate491.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate491_coefficient3 :
    compactCertificate491.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate491_coefficient4 :
    compactCertificate491.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate491_coefficients : ∀ r : Fin 5,
    compactCertificate491.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate491_coefficient0
  · exact compactCertificate491_coefficient1
  · exact compactCertificate491_coefficient2
  · exact compactCertificate491_coefficient3
  · exact compactCertificate491_coefficient4

theorem compactCertificate491_lower : (1 : ℚ) ≤ compactCertificate491.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate491, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate491_proves {t : ℝ} (ht : t ∈ compactCertificate491.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate491.proves compactCertificate491_states compactCertificate491_chunks
    compactCertificate491_coefficients compactCertificate491_lower ht

end Erdos232
