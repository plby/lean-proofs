/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate405 : CompactCertificate where
  left := 276
  right := 277
  center := 553 / 2
  grid := fun i =>
    match i.val with
    | 0 => 88
    | 1 => 65
    | 2 => 105
    | 3 => 19
    | 4 => 51
    | 5 => 138
    | 6 => 102
    | 7 => 174
    | 8 => 128
    | 9 => 197
    | 10 => 114
    | 11 => 202
    | 12 => 188
    | 13 => 135
    | 14 => 153
    | 15 => 127
    | 16 => 112
    | 17 => 163
    | 18 => 90
    | 19 => 76
    | 20 => 48
    | 21 => 26
    | 22 => 70
    | 23 => 95
    | 24 => 40
    | 25 => 164
    | _ => 109
  point := fun i =>
    match i.val with
    | 0 => 553 / 2
    | 1 => 814674594189253 / 4000000000000
    | 2 => 263449025214949 / 800000000000
    | 3 => 237720014757071 / 4000000000000
    | 4 => 638549397723587 / 4000000000000
    | 5 => 1733785830367479 / 4000000000000
    | 6 => 1277098795447727 / 4000000000000
    | 7 => 2188330553451371 / 4000000000000
    | 8 => 1611914381178689 / 4000000000000
    | 9 => 2473091183114447 / 4000000000000
    | 10 => 1427839860301463 / 4000000000000
    | 11 => 2533726888300867 / 4000000000000
    | 12 => 2367336325458223 / 4000000000000
    | 13 => 1689442906206559 / 4000000000000
    | 14 => 1915648193170761 / 4000000000000
    | 15 => 1597067747102009 / 4000000000000
    | 16 => 1411057788770189 / 4000000000000
    | 17 => 408979545804711 / 800000000000
    | 18 => 1131258947110117 / 4000000000000
    | 19 => 958980737815037 / 4000000000000
    | 20 => 600085618821311 / 4000000000000
    | 21 => 322728041596737 / 4000000000000
    | 22 => 876269412481211 / 4000000000000
    | 23 => 1196470968166747 / 4000000000000
    | 24 => 505914381178689 / 4000000000000
    | 25 => 2056513871964769 / 4000000000000
    | _ => 1373655959262671 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (35239436457 / 1000000000000) (35239436458 / 1000000000000), orderedInterval (32503194046 / 1000000000000) (32503194047 / 1000000000000))
    | 1 => (orderedInterval (-13827118885 / 1000000000000) (-13827118884 / 1000000000000), orderedInterval (-54137830899 / 1000000000000) (-54137830898 / 1000000000000))
    | 2 => (orderedInterval (-9983956516 / 1000000000000) (-9983956515 / 1000000000000), orderedInterval (-42804323251 / 1000000000000) (-42804323250 / 1000000000000))
    | 3 => (orderedInterval (-51698474609 / 1000000000000) (-51698474608 / 1000000000000), orderedInterval (-89228623329 / 1000000000000) (-89228623328 / 1000000000000))
    | 4 => (orderedInterval (-12591671277 / 1000000000000) (-12591671276 / 1000000000000), orderedInterval (-61842548605 / 1000000000000) (-61842548604 / 1000000000000))
    | 5 => (orderedInterval (24447335194 / 1000000000000) (24447335195 / 1000000000000), orderedInterval (29485645046 / 1000000000000) (29485645047 / 1000000000000))
    | 6 => (orderedInterval (-16676749336 / 1000000000000) (-16676748991 / 1000000000000), orderedInterval (41448864017 / 1000000000000) (41448864362 / 1000000000000))
    | 7 => (orderedInterval (32158463579 / 1000000000000) (32158463585 / 1000000000000), orderedInterval (11350228986 / 1000000000000) (11350228992 / 1000000000000))
    | 8 => (orderedInterval (39651847093 / 1000000000000) (39651847768 / 1000000000000), orderedInterval (-2790615546 / 1000000000000) (-2790614872 / 1000000000000))
    | 9 => (orderedInterval (-5246528096 / 1000000000000) (-5246528095 / 1000000000000), orderedInterval (-31652491422 / 1000000000000) (-31652491421 / 1000000000000))
    | 10 => (orderedInterval (-16311163522 / 1000000000000) (-16311163199 / 1000000000000), orderedInterval (38976612533 / 1000000000000) (38976612856 / 1000000000000))
    | 11 => (orderedInterval (-11899991141 / 1000000000000) (-11899991103 / 1000000000000), orderedInterval (29393460661 / 1000000000000) (29393460700 / 1000000000000))
    | 12 => (orderedInterval (29824649666 / 1000000000000) (29824720248 / 1000000000000), orderedInterval (-13669298780 / 1000000000000) (-13669228197 / 1000000000000))
    | 13 => (orderedInterval (32007141479 / 1000000000000) (32007228949 / 1000000000000), orderedInterval (-22011300437 / 1000000000000) (-22011212967 / 1000000000000))
    | 14 => (orderedInterval (30002462880 / 1000000000000) (30002529836 / 1000000000000), orderedInterval (-20747389875 / 1000000000000) (-20747322919 / 1000000000000))
    | 15 => (orderedInterval (-35022633706 / 1000000000000) (-35022633705 / 1000000000000), orderedInterval (-19136496116 / 1000000000000) (-19136496115 / 1000000000000))
    | 16 => (orderedInterval (42174149408 / 1000000000000) (42174150330 / 1000000000000), orderedInterval (-5158697971 / 1000000000000) (-5158697048 / 1000000000000))
    | 17 => (orderedInterval (2468768900 / 1000000000000) (2468768901 / 1000000000000), orderedInterval (-35204546537 / 1000000000000) (-35204546536 / 1000000000000))
    | 18 => (orderedInterval (35842600159 / 1000000000000) (35842600160 / 1000000000000), orderedInterval (31022335907 / 1000000000000) (31022335908 / 1000000000000))
    | 19 => (orderedInterval (50521463461 / 1000000000000) (50521464640 / 1000000000000), orderedInterval (-10253175116 / 1000000000000) (-10253173936 / 1000000000000))
    | 20 => (orderedInterval (620294020 / 1000000000000) (620294024 / 1000000000000), orderedInterval (65137514114 / 1000000000000) (65137514118 / 1000000000000))
    | 21 => (orderedInterval (-18998815688 / 1000000000000) (-18998815504 / 1000000000000), orderedInterval (86891361660 / 1000000000000) (86891361844 / 1000000000000))
    | 22 => (orderedInterval (-3195124799 / 1000000000000) (-3195124792 / 1000000000000), orderedInterval (53820344314 / 1000000000000) (53820344321 / 1000000000000))
    | 23 => (orderedInterval (-45805412991 / 1000000000000) (-45805412967 / 1000000000000), orderedInterval (-5417635661 / 1000000000000) (-5417635636 / 1000000000000))
    | 24 => (orderedInterval (70917499224 / 1000000000000) (70917499285 / 1000000000000), orderedInterval (-2302253704 / 1000000000000) (-2302253643 / 1000000000000))
    | 25 => (orderedInterval (-10653247472 / 1000000000000) (-10653247442 / 1000000000000), orderedInterval (33547790001 / 1000000000000) (33547790031 / 1000000000000))
    | _ => (orderedInterval (-42242810253 / 1000000000000) (-42242808184 / 1000000000000), orderedInterval (8388573208 / 1000000000000) (8388575276 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (13252967101 / 1000000000000) (13252967122 / 1000000000000)
      | 1 => orderedInterval (-1636804407 / 1000000000000) (-1636804374 / 1000000000000)
      | 2 => orderedInterval (-33588780 / 1000000000000) (-33588747 / 1000000000000)
      | 3 => orderedInterval (-1967932207 / 1000000000000) (-1967932067 / 1000000000000)
      | 4 => orderedInterval (2336428692 / 1000000000000) (2336438610 / 1000000000000)
      | 5 => orderedInterval (-2754706073 / 1000000000000) (-2754705993 / 1000000000000)
      | 6 => orderedInterval (-8570279738 / 1000000000000) (-8570279601 / 1000000000000)
      | 7 => orderedInterval (3933777779 / 1000000000000) (3933777818 / 1000000000000)
      | _ => orderedInterval (9220578571 / 1000000000000) (9220579039 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (9519986104 / 1000000000000) (9519986127 / 1000000000000)
      | 1 => orderedInterval (-4381494036 / 1000000000000) (-4381493998 / 1000000000000)
      | 2 => orderedInterval (-790975016 / 1000000000000) (-790974965 / 1000000000000)
      | 3 => orderedInterval (25876820704 / 1000000000000) (25876820975 / 1000000000000)
      | 4 => orderedInterval (-2469413745 / 1000000000000) (-2469397742 / 1000000000000)
      | 5 => orderedInterval (-1609021891 / 1000000000000) (-1609021785 / 1000000000000)
      | 6 => orderedInterval (-3419769294 / 1000000000000) (-3419769171 / 1000000000000)
      | 7 => orderedInterval (-986406263 / 1000000000000) (-986406229 / 1000000000000)
      | _ => orderedInterval (-7038947019 / 1000000000000) (-7038946424 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-13101158902 / 1000000000000) (-13101158876 / 1000000000000)
      | 1 => orderedInterval (4414073299 / 1000000000000) (4414073352 / 1000000000000)
      | 2 => orderedInterval (1850453861 / 1000000000000) (1850453945 / 1000000000000)
      | 3 => orderedInterval (6137510841 / 1000000000000) (6137511397 / 1000000000000)
      | 4 => orderedInterval (-4131054553 / 1000000000000) (-4131028252 / 1000000000000)
      | 5 => orderedInterval (4561508407 / 1000000000000) (4561508551 / 1000000000000)
      | 6 => orderedInterval (8151959064 / 1000000000000) (8151959177 / 1000000000000)
      | 7 => orderedInterval (-4180084060 / 1000000000000) (-4180084028 / 1000000000000)
      | _ => orderedInterval (-15288488088 / 1000000000000) (-15288487320 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-8390546248 / 1000000000000) (-8390546218 / 1000000000000)
      | 1 => orderedInterval (8483828659 / 1000000000000) (8483828738 / 1000000000000)
      | 2 => orderedInterval (2913827533 / 1000000000000) (2913827673 / 1000000000000)
      | 3 => orderedInterval (-119354399152 / 1000000000000) (-119354397964 / 1000000000000)
      | 4 => orderedInterval (4468095905 / 1000000000000) (4468139887 / 1000000000000)
      | 5 => orderedInterval (5732899036 / 1000000000000) (5732899235 / 1000000000000)
      | 6 => orderedInterval (4561366333 / 1000000000000) (4561366437 / 1000000000000)
      | 7 => orderedInterval (136565539 / 1000000000000) (136565572 / 1000000000000)
      | _ => orderedInterval (20628042279 / 1000000000000) (20628043285 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (12811450120 / 1000000000000) (12811450155 / 1000000000000)
      | 1 => orderedInterval (-10606596989 / 1000000000000) (-10606596868 / 1000000000000)
      | 2 => orderedInterval (-10899263886 / 1000000000000) (-10899263648 / 1000000000000)
      | 3 => orderedInterval (-25781511617 / 1000000000000) (-25781509028 / 1000000000000)
      | 4 => orderedInterval (3777996961 / 1000000000000) (3778072366 / 1000000000000)
      | 5 => orderedInterval (-7455581867 / 1000000000000) (-7455581587 / 1000000000000)
      | 6 => orderedInterval (-7920103756 / 1000000000000) (-7920103659 / 1000000000000)
      | 7 => orderedInterval (4837947873 / 1000000000000) (4837947908 / 1000000000000)
      | _ => orderedInterval (29095423507 / 1000000000000) (29095424859 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (13780440938 / 1000000000000) (13780451807 / 1000000000000)
    | 1 => orderedInterval (14700779544 / 1000000000000) (14700796788 / 1000000000000)
    | 2 => orderedInterval (-11585280131 / 1000000000000) (-11585252054 / 1000000000000)
    | 3 => orderedInterval (-80820320116 / 1000000000000) (-80820273355 / 1000000000000)
    | _ => orderedInterval (-12140239654 / 1000000000000) (-12140159502 / 1000000000000)

theorem compactCertificate405_stateChecks0 :
    compactCertificate405.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 88 12 (553 / 2)) (orderedInterval (35239436457 / 1000000000000) (35239436458 / 1000000000000), orderedInterval (32503194046 / 1000000000000) (32503194047 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (814674594189253 / 4000000000000)) (orderedInterval (-13827118885 / 1000000000000) (-13827118884 / 1000000000000), orderedInterval (-54137830899 / 1000000000000) (-54137830898 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 105 12 (263449025214949 / 800000000000)) (orderedInterval (-9983956516 / 1000000000000) (-9983956515 / 1000000000000), orderedInterval (-42804323251 / 1000000000000) (-42804323250 / 1000000000000))) = true
  rfl'

theorem compactCertificate405_stateChecks1 :
    compactCertificate405.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 19 12 (237720014757071 / 4000000000000)) (orderedInterval (-51698474609 / 1000000000000) (-51698474608 / 1000000000000), orderedInterval (-89228623329 / 1000000000000) (-89228623328 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (638549397723587 / 4000000000000)) (orderedInterval (-12591671277 / 1000000000000) (-12591671276 / 1000000000000), orderedInterval (-61842548605 / 1000000000000) (-61842548604 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 138 12 (1733785830367479 / 4000000000000)) (orderedInterval (24447335194 / 1000000000000) (24447335195 / 1000000000000), orderedInterval (29485645046 / 1000000000000) (29485645047 / 1000000000000))) = true
  rfl'

theorem compactCertificate405_stateChecks2 :
    compactCertificate405.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 102 12 (1277098795447727 / 4000000000000)) (orderedInterval (-16676749336 / 1000000000000) (-16676748991 / 1000000000000), orderedInterval (41448864017 / 1000000000000) (41448864362 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 174 12 (2188330553451371 / 4000000000000)) (orderedInterval (32158463579 / 1000000000000) (32158463585 / 1000000000000), orderedInterval (11350228986 / 1000000000000) (11350228992 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 128 12 (1611914381178689 / 4000000000000)) (orderedInterval (39651847093 / 1000000000000) (39651847768 / 1000000000000), orderedInterval (-2790615546 / 1000000000000) (-2790614872 / 1000000000000))) = true
  rfl'

theorem compactCertificate405_stateChecks3 :
    compactCertificate405.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 197 12 (2473091183114447 / 4000000000000)) (orderedInterval (-5246528096 / 1000000000000) (-5246528095 / 1000000000000), orderedInterval (-31652491422 / 1000000000000) (-31652491421 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 114 12 (1427839860301463 / 4000000000000)) (orderedInterval (-16311163522 / 1000000000000) (-16311163199 / 1000000000000), orderedInterval (38976612533 / 1000000000000) (38976612856 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 202 12 (2533726888300867 / 4000000000000)) (orderedInterval (-11899991141 / 1000000000000) (-11899991103 / 1000000000000), orderedInterval (29393460661 / 1000000000000) (29393460700 / 1000000000000))) = true
  rfl'

theorem compactCertificate405_stateChecks4 :
    compactCertificate405.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 188 12 (2367336325458223 / 4000000000000)) (orderedInterval (29824649666 / 1000000000000) (29824720248 / 1000000000000), orderedInterval (-13669298780 / 1000000000000) (-13669228197 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 135 12 (1689442906206559 / 4000000000000)) (orderedInterval (32007141479 / 1000000000000) (32007228949 / 1000000000000), orderedInterval (-22011300437 / 1000000000000) (-22011212967 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 153 12 (1915648193170761 / 4000000000000)) (orderedInterval (30002462880 / 1000000000000) (30002529836 / 1000000000000), orderedInterval (-20747389875 / 1000000000000) (-20747322919 / 1000000000000))) = true
  rfl'

theorem compactCertificate405_stateChecks5 :
    compactCertificate405.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 127 12 (1597067747102009 / 4000000000000)) (orderedInterval (-35022633706 / 1000000000000) (-35022633705 / 1000000000000), orderedInterval (-19136496116 / 1000000000000) (-19136496115 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 112 12 (1411057788770189 / 4000000000000)) (orderedInterval (42174149408 / 1000000000000) (42174150330 / 1000000000000), orderedInterval (-5158697971 / 1000000000000) (-5158697048 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 163 12 (408979545804711 / 800000000000)) (orderedInterval (2468768900 / 1000000000000) (2468768901 / 1000000000000), orderedInterval (-35204546537 / 1000000000000) (-35204546536 / 1000000000000))) = true
  rfl'

theorem compactCertificate405_stateChecks6 :
    compactCertificate405.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (1131258947110117 / 4000000000000)) (orderedInterval (35842600159 / 1000000000000) (35842600160 / 1000000000000), orderedInterval (31022335907 / 1000000000000) (31022335908 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (958980737815037 / 4000000000000)) (orderedInterval (50521463461 / 1000000000000) (50521464640 / 1000000000000), orderedInterval (-10253175116 / 1000000000000) (-10253173936 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (600085618821311 / 4000000000000)) (orderedInterval (620294020 / 1000000000000) (620294024 / 1000000000000), orderedInterval (65137514114 / 1000000000000) (65137514118 / 1000000000000))) = true
  rfl'

theorem compactCertificate405_stateChecks7 :
    compactCertificate405.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (322728041596737 / 4000000000000)) (orderedInterval (-18998815688 / 1000000000000) (-18998815504 / 1000000000000), orderedInterval (86891361660 / 1000000000000) (86891361844 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (876269412481211 / 4000000000000)) (orderedInterval (-3195124799 / 1000000000000) (-3195124792 / 1000000000000), orderedInterval (53820344314 / 1000000000000) (53820344321 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 95 12 (1196470968166747 / 4000000000000)) (orderedInterval (-45805412991 / 1000000000000) (-45805412967 / 1000000000000), orderedInterval (-5417635661 / 1000000000000) (-5417635636 / 1000000000000))) = true
  rfl'

theorem compactCertificate405_stateChecks8 :
    compactCertificate405.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (505914381178689 / 4000000000000)) (orderedInterval (70917499224 / 1000000000000) (70917499285 / 1000000000000), orderedInterval (-2302253704 / 1000000000000) (-2302253643 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 164 12 (2056513871964769 / 4000000000000)) (orderedInterval (-10653247472 / 1000000000000) (-10653247442 / 1000000000000), orderedInterval (33547790001 / 1000000000000) (33547790031 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 109 12 (1373655959262671 / 4000000000000)) (orderedInterval (-42242810253 / 1000000000000) (-42242808184 / 1000000000000), orderedInterval (8388573208 / 1000000000000) (8388575276 / 1000000000000))) = true
  rfl'

theorem compactCertificate405_states : ∀ j,
    BesselStateValid (compactCertificate405.point j) (compactCertificate405.state j) :=
  compactCertificate405.statesValid_of_checks3 compactCertificate405_stateChecks0
    compactCertificate405_stateChecks1 compactCertificate405_stateChecks2
    compactCertificate405_stateChecks3 compactCertificate405_stateChecks4
    compactCertificate405_stateChecks5 compactCertificate405_stateChecks6
    compactCertificate405_stateChecks7 compactCertificate405_stateChecks8

theorem compactCertificate405_chunkChecks0_0 :
    compactCertificate405.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (553 / 2) 0 (IntervalRat.scale (553 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (35239436457 / 1000000000000) (35239436458 / 1000000000000), orderedInterval (32503194046 / 1000000000000) (32503194047 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (814674594189253 / 4000000000000) 0 (IntervalRat.scale (553 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-13827118885 / 1000000000000) (-13827118884 / 1000000000000), orderedInterval (-54137830899 / 1000000000000) (-54137830898 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (263449025214949 / 800000000000) 0 (IntervalRat.scale (553 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-9983956516 / 1000000000000) (-9983956515 / 1000000000000), orderedInterval (-42804323251 / 1000000000000) (-42804323250 / 1000000000000)))) (orderedInterval (13252967101 / 1000000000000) (13252967122 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (237720014757071 / 4000000000000) 0 (IntervalRat.scale (553 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-51698474609 / 1000000000000) (-51698474608 / 1000000000000), orderedInterval (-89228623329 / 1000000000000) (-89228623328 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (638549397723587 / 4000000000000) 0 (IntervalRat.scale (553 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-12591671277 / 1000000000000) (-12591671276 / 1000000000000), orderedInterval (-61842548605 / 1000000000000) (-61842548604 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1733785830367479 / 4000000000000) 0 (IntervalRat.scale (553 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (24447335194 / 1000000000000) (24447335195 / 1000000000000), orderedInterval (29485645046 / 1000000000000) (29485645047 / 1000000000000)))) (orderedInterval (-1636804407 / 1000000000000) (-1636804374 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1277098795447727 / 4000000000000) 0 (IntervalRat.scale (553 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-16676749336 / 1000000000000) (-16676748991 / 1000000000000), orderedInterval (41448864017 / 1000000000000) (41448864362 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2188330553451371 / 4000000000000) 0 (IntervalRat.scale (553 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (32158463579 / 1000000000000) (32158463585 / 1000000000000), orderedInterval (11350228986 / 1000000000000) (11350228992 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1611914381178689 / 4000000000000) 0 (IntervalRat.scale (553 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (39651847093 / 1000000000000) (39651847768 / 1000000000000), orderedInterval (-2790615546 / 1000000000000) (-2790614872 / 1000000000000)))) (orderedInterval (-33588780 / 1000000000000) (-33588747 / 1000000000000))) = true
  rfl'

theorem compactCertificate405_chunkChecks0_1 :
    compactCertificate405.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2473091183114447 / 4000000000000) 0 (IntervalRat.scale (553 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-5246528096 / 1000000000000) (-5246528095 / 1000000000000), orderedInterval (-31652491422 / 1000000000000) (-31652491421 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1427839860301463 / 4000000000000) 0 (IntervalRat.scale (553 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-16311163522 / 1000000000000) (-16311163199 / 1000000000000), orderedInterval (38976612533 / 1000000000000) (38976612856 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2533726888300867 / 4000000000000) 0 (IntervalRat.scale (553 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-11899991141 / 1000000000000) (-11899991103 / 1000000000000), orderedInterval (29393460661 / 1000000000000) (29393460700 / 1000000000000)))) (orderedInterval (-1967932207 / 1000000000000) (-1967932067 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2367336325458223 / 4000000000000) 0 (IntervalRat.scale (553 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (29824649666 / 1000000000000) (29824720248 / 1000000000000), orderedInterval (-13669298780 / 1000000000000) (-13669228197 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1689442906206559 / 4000000000000) 0 (IntervalRat.scale (553 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (32007141479 / 1000000000000) (32007228949 / 1000000000000), orderedInterval (-22011300437 / 1000000000000) (-22011212967 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1915648193170761 / 4000000000000) 0 (IntervalRat.scale (553 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (30002462880 / 1000000000000) (30002529836 / 1000000000000), orderedInterval (-20747389875 / 1000000000000) (-20747322919 / 1000000000000)))) (orderedInterval (2336428692 / 1000000000000) (2336438610 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1597067747102009 / 4000000000000) 0 (IntervalRat.scale (553 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-35022633706 / 1000000000000) (-35022633705 / 1000000000000), orderedInterval (-19136496116 / 1000000000000) (-19136496115 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1411057788770189 / 4000000000000) 0 (IntervalRat.scale (553 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (42174149408 / 1000000000000) (42174150330 / 1000000000000), orderedInterval (-5158697971 / 1000000000000) (-5158697048 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (408979545804711 / 800000000000) 0 (IntervalRat.scale (553 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (2468768900 / 1000000000000) (2468768901 / 1000000000000), orderedInterval (-35204546537 / 1000000000000) (-35204546536 / 1000000000000)))) (orderedInterval (-2754706073 / 1000000000000) (-2754705993 / 1000000000000))) = true
  rfl'

theorem compactCertificate405_chunkChecks0_2 :
    compactCertificate405.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1131258947110117 / 4000000000000) 0 (IntervalRat.scale (553 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (35842600159 / 1000000000000) (35842600160 / 1000000000000), orderedInterval (31022335907 / 1000000000000) (31022335908 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (958980737815037 / 4000000000000) 0 (IntervalRat.scale (553 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (50521463461 / 1000000000000) (50521464640 / 1000000000000), orderedInterval (-10253175116 / 1000000000000) (-10253173936 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (600085618821311 / 4000000000000) 0 (IntervalRat.scale (553 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (620294020 / 1000000000000) (620294024 / 1000000000000), orderedInterval (65137514114 / 1000000000000) (65137514118 / 1000000000000)))) (orderedInterval (-8570279738 / 1000000000000) (-8570279601 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (322728041596737 / 4000000000000) 0 (IntervalRat.scale (553 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-18998815688 / 1000000000000) (-18998815504 / 1000000000000), orderedInterval (86891361660 / 1000000000000) (86891361844 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (876269412481211 / 4000000000000) 0 (IntervalRat.scale (553 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-3195124799 / 1000000000000) (-3195124792 / 1000000000000), orderedInterval (53820344314 / 1000000000000) (53820344321 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1196470968166747 / 4000000000000) 0 (IntervalRat.scale (553 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-45805412991 / 1000000000000) (-45805412967 / 1000000000000), orderedInterval (-5417635661 / 1000000000000) (-5417635636 / 1000000000000)))) (orderedInterval (3933777779 / 1000000000000) (3933777818 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (505914381178689 / 4000000000000) 0 (IntervalRat.scale (553 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (70917499224 / 1000000000000) (70917499285 / 1000000000000), orderedInterval (-2302253704 / 1000000000000) (-2302253643 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2056513871964769 / 4000000000000) 0 (IntervalRat.scale (553 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-10653247472 / 1000000000000) (-10653247442 / 1000000000000), orderedInterval (33547790001 / 1000000000000) (33547790031 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1373655959262671 / 4000000000000) 0 (IntervalRat.scale (553 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-42242810253 / 1000000000000) (-42242808184 / 1000000000000), orderedInterval (8388573208 / 1000000000000) (8388575276 / 1000000000000)))) (orderedInterval (9220578571 / 1000000000000) (9220579039 / 1000000000000))) = true
  rfl'

theorem compactCertificate405_chunkChecks0 :
    compactCertificate405.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate405.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate405_chunkChecks0_0
    compactCertificate405_chunkChecks0_1 compactCertificate405_chunkChecks0_2

theorem compactCertificate405_chunkChecks1_0 :
    compactCertificate405.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (553 / 2) 1 (IntervalRat.scale (553 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (35239436457 / 1000000000000) (35239436458 / 1000000000000), orderedInterval (32503194046 / 1000000000000) (32503194047 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (814674594189253 / 4000000000000) 1 (IntervalRat.scale (553 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-13827118885 / 1000000000000) (-13827118884 / 1000000000000), orderedInterval (-54137830899 / 1000000000000) (-54137830898 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (263449025214949 / 800000000000) 1 (IntervalRat.scale (553 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-9983956516 / 1000000000000) (-9983956515 / 1000000000000), orderedInterval (-42804323251 / 1000000000000) (-42804323250 / 1000000000000)))) (orderedInterval (9519986104 / 1000000000000) (9519986127 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (237720014757071 / 4000000000000) 1 (IntervalRat.scale (553 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-51698474609 / 1000000000000) (-51698474608 / 1000000000000), orderedInterval (-89228623329 / 1000000000000) (-89228623328 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (638549397723587 / 4000000000000) 1 (IntervalRat.scale (553 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-12591671277 / 1000000000000) (-12591671276 / 1000000000000), orderedInterval (-61842548605 / 1000000000000) (-61842548604 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1733785830367479 / 4000000000000) 1 (IntervalRat.scale (553 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (24447335194 / 1000000000000) (24447335195 / 1000000000000), orderedInterval (29485645046 / 1000000000000) (29485645047 / 1000000000000)))) (orderedInterval (-4381494036 / 1000000000000) (-4381493998 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1277098795447727 / 4000000000000) 1 (IntervalRat.scale (553 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-16676749336 / 1000000000000) (-16676748991 / 1000000000000), orderedInterval (41448864017 / 1000000000000) (41448864362 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2188330553451371 / 4000000000000) 1 (IntervalRat.scale (553 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (32158463579 / 1000000000000) (32158463585 / 1000000000000), orderedInterval (11350228986 / 1000000000000) (11350228992 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1611914381178689 / 4000000000000) 1 (IntervalRat.scale (553 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (39651847093 / 1000000000000) (39651847768 / 1000000000000), orderedInterval (-2790615546 / 1000000000000) (-2790614872 / 1000000000000)))) (orderedInterval (-790975016 / 1000000000000) (-790974965 / 1000000000000))) = true
  rfl'

theorem compactCertificate405_chunkChecks1_1 :
    compactCertificate405.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2473091183114447 / 4000000000000) 1 (IntervalRat.scale (553 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-5246528096 / 1000000000000) (-5246528095 / 1000000000000), orderedInterval (-31652491422 / 1000000000000) (-31652491421 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1427839860301463 / 4000000000000) 1 (IntervalRat.scale (553 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-16311163522 / 1000000000000) (-16311163199 / 1000000000000), orderedInterval (38976612533 / 1000000000000) (38976612856 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2533726888300867 / 4000000000000) 1 (IntervalRat.scale (553 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-11899991141 / 1000000000000) (-11899991103 / 1000000000000), orderedInterval (29393460661 / 1000000000000) (29393460700 / 1000000000000)))) (orderedInterval (25876820704 / 1000000000000) (25876820975 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2367336325458223 / 4000000000000) 1 (IntervalRat.scale (553 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (29824649666 / 1000000000000) (29824720248 / 1000000000000), orderedInterval (-13669298780 / 1000000000000) (-13669228197 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1689442906206559 / 4000000000000) 1 (IntervalRat.scale (553 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (32007141479 / 1000000000000) (32007228949 / 1000000000000), orderedInterval (-22011300437 / 1000000000000) (-22011212967 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1915648193170761 / 4000000000000) 1 (IntervalRat.scale (553 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (30002462880 / 1000000000000) (30002529836 / 1000000000000), orderedInterval (-20747389875 / 1000000000000) (-20747322919 / 1000000000000)))) (orderedInterval (-2469413745 / 1000000000000) (-2469397742 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1597067747102009 / 4000000000000) 1 (IntervalRat.scale (553 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-35022633706 / 1000000000000) (-35022633705 / 1000000000000), orderedInterval (-19136496116 / 1000000000000) (-19136496115 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1411057788770189 / 4000000000000) 1 (IntervalRat.scale (553 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (42174149408 / 1000000000000) (42174150330 / 1000000000000), orderedInterval (-5158697971 / 1000000000000) (-5158697048 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (408979545804711 / 800000000000) 1 (IntervalRat.scale (553 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (2468768900 / 1000000000000) (2468768901 / 1000000000000), orderedInterval (-35204546537 / 1000000000000) (-35204546536 / 1000000000000)))) (orderedInterval (-1609021891 / 1000000000000) (-1609021785 / 1000000000000))) = true
  rfl'

theorem compactCertificate405_chunkChecks1_2 :
    compactCertificate405.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1131258947110117 / 4000000000000) 1 (IntervalRat.scale (553 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (35842600159 / 1000000000000) (35842600160 / 1000000000000), orderedInterval (31022335907 / 1000000000000) (31022335908 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (958980737815037 / 4000000000000) 1 (IntervalRat.scale (553 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (50521463461 / 1000000000000) (50521464640 / 1000000000000), orderedInterval (-10253175116 / 1000000000000) (-10253173936 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (600085618821311 / 4000000000000) 1 (IntervalRat.scale (553 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (620294020 / 1000000000000) (620294024 / 1000000000000), orderedInterval (65137514114 / 1000000000000) (65137514118 / 1000000000000)))) (orderedInterval (-3419769294 / 1000000000000) (-3419769171 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (322728041596737 / 4000000000000) 1 (IntervalRat.scale (553 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-18998815688 / 1000000000000) (-18998815504 / 1000000000000), orderedInterval (86891361660 / 1000000000000) (86891361844 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (876269412481211 / 4000000000000) 1 (IntervalRat.scale (553 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-3195124799 / 1000000000000) (-3195124792 / 1000000000000), orderedInterval (53820344314 / 1000000000000) (53820344321 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1196470968166747 / 4000000000000) 1 (IntervalRat.scale (553 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-45805412991 / 1000000000000) (-45805412967 / 1000000000000), orderedInterval (-5417635661 / 1000000000000) (-5417635636 / 1000000000000)))) (orderedInterval (-986406263 / 1000000000000) (-986406229 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (505914381178689 / 4000000000000) 1 (IntervalRat.scale (553 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (70917499224 / 1000000000000) (70917499285 / 1000000000000), orderedInterval (-2302253704 / 1000000000000) (-2302253643 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2056513871964769 / 4000000000000) 1 (IntervalRat.scale (553 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-10653247472 / 1000000000000) (-10653247442 / 1000000000000), orderedInterval (33547790001 / 1000000000000) (33547790031 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1373655959262671 / 4000000000000) 1 (IntervalRat.scale (553 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-42242810253 / 1000000000000) (-42242808184 / 1000000000000), orderedInterval (8388573208 / 1000000000000) (8388575276 / 1000000000000)))) (orderedInterval (-7038947019 / 1000000000000) (-7038946424 / 1000000000000))) = true
  rfl'

theorem compactCertificate405_chunkChecks1 :
    compactCertificate405.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate405.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate405_chunkChecks1_0
    compactCertificate405_chunkChecks1_1 compactCertificate405_chunkChecks1_2

theorem compactCertificate405_chunkChecks2_0 :
    compactCertificate405.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (553 / 2) 2 (IntervalRat.scale (553 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (35239436457 / 1000000000000) (35239436458 / 1000000000000), orderedInterval (32503194046 / 1000000000000) (32503194047 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (814674594189253 / 4000000000000) 2 (IntervalRat.scale (553 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-13827118885 / 1000000000000) (-13827118884 / 1000000000000), orderedInterval (-54137830899 / 1000000000000) (-54137830898 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (263449025214949 / 800000000000) 2 (IntervalRat.scale (553 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-9983956516 / 1000000000000) (-9983956515 / 1000000000000), orderedInterval (-42804323251 / 1000000000000) (-42804323250 / 1000000000000)))) (orderedInterval (-13101158902 / 1000000000000) (-13101158876 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (237720014757071 / 4000000000000) 2 (IntervalRat.scale (553 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-51698474609 / 1000000000000) (-51698474608 / 1000000000000), orderedInterval (-89228623329 / 1000000000000) (-89228623328 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (638549397723587 / 4000000000000) 2 (IntervalRat.scale (553 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-12591671277 / 1000000000000) (-12591671276 / 1000000000000), orderedInterval (-61842548605 / 1000000000000) (-61842548604 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1733785830367479 / 4000000000000) 2 (IntervalRat.scale (553 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (24447335194 / 1000000000000) (24447335195 / 1000000000000), orderedInterval (29485645046 / 1000000000000) (29485645047 / 1000000000000)))) (orderedInterval (4414073299 / 1000000000000) (4414073352 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1277098795447727 / 4000000000000) 2 (IntervalRat.scale (553 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-16676749336 / 1000000000000) (-16676748991 / 1000000000000), orderedInterval (41448864017 / 1000000000000) (41448864362 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2188330553451371 / 4000000000000) 2 (IntervalRat.scale (553 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (32158463579 / 1000000000000) (32158463585 / 1000000000000), orderedInterval (11350228986 / 1000000000000) (11350228992 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1611914381178689 / 4000000000000) 2 (IntervalRat.scale (553 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (39651847093 / 1000000000000) (39651847768 / 1000000000000), orderedInterval (-2790615546 / 1000000000000) (-2790614872 / 1000000000000)))) (orderedInterval (1850453861 / 1000000000000) (1850453945 / 1000000000000))) = true
  rfl'

theorem compactCertificate405_chunkChecks2_1 :
    compactCertificate405.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2473091183114447 / 4000000000000) 2 (IntervalRat.scale (553 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-5246528096 / 1000000000000) (-5246528095 / 1000000000000), orderedInterval (-31652491422 / 1000000000000) (-31652491421 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1427839860301463 / 4000000000000) 2 (IntervalRat.scale (553 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-16311163522 / 1000000000000) (-16311163199 / 1000000000000), orderedInterval (38976612533 / 1000000000000) (38976612856 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2533726888300867 / 4000000000000) 2 (IntervalRat.scale (553 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-11899991141 / 1000000000000) (-11899991103 / 1000000000000), orderedInterval (29393460661 / 1000000000000) (29393460700 / 1000000000000)))) (orderedInterval (6137510841 / 1000000000000) (6137511397 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2367336325458223 / 4000000000000) 2 (IntervalRat.scale (553 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (29824649666 / 1000000000000) (29824720248 / 1000000000000), orderedInterval (-13669298780 / 1000000000000) (-13669228197 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1689442906206559 / 4000000000000) 2 (IntervalRat.scale (553 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (32007141479 / 1000000000000) (32007228949 / 1000000000000), orderedInterval (-22011300437 / 1000000000000) (-22011212967 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1915648193170761 / 4000000000000) 2 (IntervalRat.scale (553 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (30002462880 / 1000000000000) (30002529836 / 1000000000000), orderedInterval (-20747389875 / 1000000000000) (-20747322919 / 1000000000000)))) (orderedInterval (-4131054553 / 1000000000000) (-4131028252 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1597067747102009 / 4000000000000) 2 (IntervalRat.scale (553 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-35022633706 / 1000000000000) (-35022633705 / 1000000000000), orderedInterval (-19136496116 / 1000000000000) (-19136496115 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1411057788770189 / 4000000000000) 2 (IntervalRat.scale (553 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (42174149408 / 1000000000000) (42174150330 / 1000000000000), orderedInterval (-5158697971 / 1000000000000) (-5158697048 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (408979545804711 / 800000000000) 2 (IntervalRat.scale (553 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (2468768900 / 1000000000000) (2468768901 / 1000000000000), orderedInterval (-35204546537 / 1000000000000) (-35204546536 / 1000000000000)))) (orderedInterval (4561508407 / 1000000000000) (4561508551 / 1000000000000))) = true
  rfl'

theorem compactCertificate405_chunkChecks2_2 :
    compactCertificate405.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1131258947110117 / 4000000000000) 2 (IntervalRat.scale (553 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (35842600159 / 1000000000000) (35842600160 / 1000000000000), orderedInterval (31022335907 / 1000000000000) (31022335908 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (958980737815037 / 4000000000000) 2 (IntervalRat.scale (553 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (50521463461 / 1000000000000) (50521464640 / 1000000000000), orderedInterval (-10253175116 / 1000000000000) (-10253173936 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (600085618821311 / 4000000000000) 2 (IntervalRat.scale (553 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (620294020 / 1000000000000) (620294024 / 1000000000000), orderedInterval (65137514114 / 1000000000000) (65137514118 / 1000000000000)))) (orderedInterval (8151959064 / 1000000000000) (8151959177 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (322728041596737 / 4000000000000) 2 (IntervalRat.scale (553 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-18998815688 / 1000000000000) (-18998815504 / 1000000000000), orderedInterval (86891361660 / 1000000000000) (86891361844 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (876269412481211 / 4000000000000) 2 (IntervalRat.scale (553 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-3195124799 / 1000000000000) (-3195124792 / 1000000000000), orderedInterval (53820344314 / 1000000000000) (53820344321 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1196470968166747 / 4000000000000) 2 (IntervalRat.scale (553 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-45805412991 / 1000000000000) (-45805412967 / 1000000000000), orderedInterval (-5417635661 / 1000000000000) (-5417635636 / 1000000000000)))) (orderedInterval (-4180084060 / 1000000000000) (-4180084028 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (505914381178689 / 4000000000000) 2 (IntervalRat.scale (553 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (70917499224 / 1000000000000) (70917499285 / 1000000000000), orderedInterval (-2302253704 / 1000000000000) (-2302253643 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2056513871964769 / 4000000000000) 2 (IntervalRat.scale (553 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-10653247472 / 1000000000000) (-10653247442 / 1000000000000), orderedInterval (33547790001 / 1000000000000) (33547790031 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1373655959262671 / 4000000000000) 2 (IntervalRat.scale (553 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-42242810253 / 1000000000000) (-42242808184 / 1000000000000), orderedInterval (8388573208 / 1000000000000) (8388575276 / 1000000000000)))) (orderedInterval (-15288488088 / 1000000000000) (-15288487320 / 1000000000000))) = true
  rfl'

theorem compactCertificate405_chunkChecks2 :
    compactCertificate405.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate405.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate405_chunkChecks2_0
    compactCertificate405_chunkChecks2_1 compactCertificate405_chunkChecks2_2

theorem compactCertificate405_chunkChecks3_0 :
    compactCertificate405.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (553 / 2) 3 (IntervalRat.scale (553 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (35239436457 / 1000000000000) (35239436458 / 1000000000000), orderedInterval (32503194046 / 1000000000000) (32503194047 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (814674594189253 / 4000000000000) 3 (IntervalRat.scale (553 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-13827118885 / 1000000000000) (-13827118884 / 1000000000000), orderedInterval (-54137830899 / 1000000000000) (-54137830898 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (263449025214949 / 800000000000) 3 (IntervalRat.scale (553 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-9983956516 / 1000000000000) (-9983956515 / 1000000000000), orderedInterval (-42804323251 / 1000000000000) (-42804323250 / 1000000000000)))) (orderedInterval (-8390546248 / 1000000000000) (-8390546218 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (237720014757071 / 4000000000000) 3 (IntervalRat.scale (553 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-51698474609 / 1000000000000) (-51698474608 / 1000000000000), orderedInterval (-89228623329 / 1000000000000) (-89228623328 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (638549397723587 / 4000000000000) 3 (IntervalRat.scale (553 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-12591671277 / 1000000000000) (-12591671276 / 1000000000000), orderedInterval (-61842548605 / 1000000000000) (-61842548604 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1733785830367479 / 4000000000000) 3 (IntervalRat.scale (553 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (24447335194 / 1000000000000) (24447335195 / 1000000000000), orderedInterval (29485645046 / 1000000000000) (29485645047 / 1000000000000)))) (orderedInterval (8483828659 / 1000000000000) (8483828738 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1277098795447727 / 4000000000000) 3 (IntervalRat.scale (553 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-16676749336 / 1000000000000) (-16676748991 / 1000000000000), orderedInterval (41448864017 / 1000000000000) (41448864362 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2188330553451371 / 4000000000000) 3 (IntervalRat.scale (553 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (32158463579 / 1000000000000) (32158463585 / 1000000000000), orderedInterval (11350228986 / 1000000000000) (11350228992 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1611914381178689 / 4000000000000) 3 (IntervalRat.scale (553 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (39651847093 / 1000000000000) (39651847768 / 1000000000000), orderedInterval (-2790615546 / 1000000000000) (-2790614872 / 1000000000000)))) (orderedInterval (2913827533 / 1000000000000) (2913827673 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate405_chunkChecks3_1 :
    compactCertificate405.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2473091183114447 / 4000000000000) 3 (IntervalRat.scale (553 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-5246528096 / 1000000000000) (-5246528095 / 1000000000000), orderedInterval (-31652491422 / 1000000000000) (-31652491421 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1427839860301463 / 4000000000000) 3 (IntervalRat.scale (553 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-16311163522 / 1000000000000) (-16311163199 / 1000000000000), orderedInterval (38976612533 / 1000000000000) (38976612856 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2533726888300867 / 4000000000000) 3 (IntervalRat.scale (553 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-11899991141 / 1000000000000) (-11899991103 / 1000000000000), orderedInterval (29393460661 / 1000000000000) (29393460700 / 1000000000000)))) (orderedInterval (-119354399152 / 1000000000000) (-119354397964 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2367336325458223 / 4000000000000) 3 (IntervalRat.scale (553 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (29824649666 / 1000000000000) (29824720248 / 1000000000000), orderedInterval (-13669298780 / 1000000000000) (-13669228197 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1689442906206559 / 4000000000000) 3 (IntervalRat.scale (553 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (32007141479 / 1000000000000) (32007228949 / 1000000000000), orderedInterval (-22011300437 / 1000000000000) (-22011212967 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1915648193170761 / 4000000000000) 3 (IntervalRat.scale (553 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (30002462880 / 1000000000000) (30002529836 / 1000000000000), orderedInterval (-20747389875 / 1000000000000) (-20747322919 / 1000000000000)))) (orderedInterval (4468095905 / 1000000000000) (4468139887 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1597067747102009 / 4000000000000) 3 (IntervalRat.scale (553 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-35022633706 / 1000000000000) (-35022633705 / 1000000000000), orderedInterval (-19136496116 / 1000000000000) (-19136496115 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1411057788770189 / 4000000000000) 3 (IntervalRat.scale (553 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (42174149408 / 1000000000000) (42174150330 / 1000000000000), orderedInterval (-5158697971 / 1000000000000) (-5158697048 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (408979545804711 / 800000000000) 3 (IntervalRat.scale (553 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (2468768900 / 1000000000000) (2468768901 / 1000000000000), orderedInterval (-35204546537 / 1000000000000) (-35204546536 / 1000000000000)))) (orderedInterval (5732899036 / 1000000000000) (5732899235 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate405_chunkChecks3_2 :
    compactCertificate405.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1131258947110117 / 4000000000000) 3 (IntervalRat.scale (553 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (35842600159 / 1000000000000) (35842600160 / 1000000000000), orderedInterval (31022335907 / 1000000000000) (31022335908 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (958980737815037 / 4000000000000) 3 (IntervalRat.scale (553 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (50521463461 / 1000000000000) (50521464640 / 1000000000000), orderedInterval (-10253175116 / 1000000000000) (-10253173936 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (600085618821311 / 4000000000000) 3 (IntervalRat.scale (553 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (620294020 / 1000000000000) (620294024 / 1000000000000), orderedInterval (65137514114 / 1000000000000) (65137514118 / 1000000000000)))) (orderedInterval (4561366333 / 1000000000000) (4561366437 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (322728041596737 / 4000000000000) 3 (IntervalRat.scale (553 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-18998815688 / 1000000000000) (-18998815504 / 1000000000000), orderedInterval (86891361660 / 1000000000000) (86891361844 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (876269412481211 / 4000000000000) 3 (IntervalRat.scale (553 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-3195124799 / 1000000000000) (-3195124792 / 1000000000000), orderedInterval (53820344314 / 1000000000000) (53820344321 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1196470968166747 / 4000000000000) 3 (IntervalRat.scale (553 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-45805412991 / 1000000000000) (-45805412967 / 1000000000000), orderedInterval (-5417635661 / 1000000000000) (-5417635636 / 1000000000000)))) (orderedInterval (136565539 / 1000000000000) (136565572 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (505914381178689 / 4000000000000) 3 (IntervalRat.scale (553 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (70917499224 / 1000000000000) (70917499285 / 1000000000000), orderedInterval (-2302253704 / 1000000000000) (-2302253643 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2056513871964769 / 4000000000000) 3 (IntervalRat.scale (553 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-10653247472 / 1000000000000) (-10653247442 / 1000000000000), orderedInterval (33547790001 / 1000000000000) (33547790031 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1373655959262671 / 4000000000000) 3 (IntervalRat.scale (553 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-42242810253 / 1000000000000) (-42242808184 / 1000000000000), orderedInterval (8388573208 / 1000000000000) (8388575276 / 1000000000000)))) (orderedInterval (20628042279 / 1000000000000) (20628043285 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate405_chunkChecks3 :
    compactCertificate405.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate405.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate405_chunkChecks3_0
    compactCertificate405_chunkChecks3_1 compactCertificate405_chunkChecks3_2

theorem compactCertificate405_chunkChecks4_0 :
    compactCertificate405.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (553 / 2) 4 (IntervalRat.scale (553 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (35239436457 / 1000000000000) (35239436458 / 1000000000000), orderedInterval (32503194046 / 1000000000000) (32503194047 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (814674594189253 / 4000000000000) 4 (IntervalRat.scale (553 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-13827118885 / 1000000000000) (-13827118884 / 1000000000000), orderedInterval (-54137830899 / 1000000000000) (-54137830898 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (263449025214949 / 800000000000) 4 (IntervalRat.scale (553 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-9983956516 / 1000000000000) (-9983956515 / 1000000000000), orderedInterval (-42804323251 / 1000000000000) (-42804323250 / 1000000000000)))) (orderedInterval (12811450120 / 1000000000000) (12811450155 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (237720014757071 / 4000000000000) 4 (IntervalRat.scale (553 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-51698474609 / 1000000000000) (-51698474608 / 1000000000000), orderedInterval (-89228623329 / 1000000000000) (-89228623328 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (638549397723587 / 4000000000000) 4 (IntervalRat.scale (553 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-12591671277 / 1000000000000) (-12591671276 / 1000000000000), orderedInterval (-61842548605 / 1000000000000) (-61842548604 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1733785830367479 / 4000000000000) 4 (IntervalRat.scale (553 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (24447335194 / 1000000000000) (24447335195 / 1000000000000), orderedInterval (29485645046 / 1000000000000) (29485645047 / 1000000000000)))) (orderedInterval (-10606596989 / 1000000000000) (-10606596868 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1277098795447727 / 4000000000000) 4 (IntervalRat.scale (553 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-16676749336 / 1000000000000) (-16676748991 / 1000000000000), orderedInterval (41448864017 / 1000000000000) (41448864362 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2188330553451371 / 4000000000000) 4 (IntervalRat.scale (553 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (32158463579 / 1000000000000) (32158463585 / 1000000000000), orderedInterval (11350228986 / 1000000000000) (11350228992 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1611914381178689 / 4000000000000) 4 (IntervalRat.scale (553 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (39651847093 / 1000000000000) (39651847768 / 1000000000000), orderedInterval (-2790615546 / 1000000000000) (-2790614872 / 1000000000000)))) (orderedInterval (-10899263886 / 1000000000000) (-10899263648 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate405_chunkChecks4_1 :
    compactCertificate405.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2473091183114447 / 4000000000000) 4 (IntervalRat.scale (553 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-5246528096 / 1000000000000) (-5246528095 / 1000000000000), orderedInterval (-31652491422 / 1000000000000) (-31652491421 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1427839860301463 / 4000000000000) 4 (IntervalRat.scale (553 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-16311163522 / 1000000000000) (-16311163199 / 1000000000000), orderedInterval (38976612533 / 1000000000000) (38976612856 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2533726888300867 / 4000000000000) 4 (IntervalRat.scale (553 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-11899991141 / 1000000000000) (-11899991103 / 1000000000000), orderedInterval (29393460661 / 1000000000000) (29393460700 / 1000000000000)))) (orderedInterval (-25781511617 / 1000000000000) (-25781509028 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2367336325458223 / 4000000000000) 4 (IntervalRat.scale (553 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (29824649666 / 1000000000000) (29824720248 / 1000000000000), orderedInterval (-13669298780 / 1000000000000) (-13669228197 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1689442906206559 / 4000000000000) 4 (IntervalRat.scale (553 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (32007141479 / 1000000000000) (32007228949 / 1000000000000), orderedInterval (-22011300437 / 1000000000000) (-22011212967 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1915648193170761 / 4000000000000) 4 (IntervalRat.scale (553 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (30002462880 / 1000000000000) (30002529836 / 1000000000000), orderedInterval (-20747389875 / 1000000000000) (-20747322919 / 1000000000000)))) (orderedInterval (3777996961 / 1000000000000) (3778072366 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1597067747102009 / 4000000000000) 4 (IntervalRat.scale (553 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-35022633706 / 1000000000000) (-35022633705 / 1000000000000), orderedInterval (-19136496116 / 1000000000000) (-19136496115 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1411057788770189 / 4000000000000) 4 (IntervalRat.scale (553 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (42174149408 / 1000000000000) (42174150330 / 1000000000000), orderedInterval (-5158697971 / 1000000000000) (-5158697048 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (408979545804711 / 800000000000) 4 (IntervalRat.scale (553 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (2468768900 / 1000000000000) (2468768901 / 1000000000000), orderedInterval (-35204546537 / 1000000000000) (-35204546536 / 1000000000000)))) (orderedInterval (-7455581867 / 1000000000000) (-7455581587 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate405_chunkChecks4_2 :
    compactCertificate405.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1131258947110117 / 4000000000000) 4 (IntervalRat.scale (553 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (35842600159 / 1000000000000) (35842600160 / 1000000000000), orderedInterval (31022335907 / 1000000000000) (31022335908 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (958980737815037 / 4000000000000) 4 (IntervalRat.scale (553 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (50521463461 / 1000000000000) (50521464640 / 1000000000000), orderedInterval (-10253175116 / 1000000000000) (-10253173936 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (600085618821311 / 4000000000000) 4 (IntervalRat.scale (553 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (620294020 / 1000000000000) (620294024 / 1000000000000), orderedInterval (65137514114 / 1000000000000) (65137514118 / 1000000000000)))) (orderedInterval (-7920103756 / 1000000000000) (-7920103659 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (322728041596737 / 4000000000000) 4 (IntervalRat.scale (553 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-18998815688 / 1000000000000) (-18998815504 / 1000000000000), orderedInterval (86891361660 / 1000000000000) (86891361844 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (876269412481211 / 4000000000000) 4 (IntervalRat.scale (553 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-3195124799 / 1000000000000) (-3195124792 / 1000000000000), orderedInterval (53820344314 / 1000000000000) (53820344321 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1196470968166747 / 4000000000000) 4 (IntervalRat.scale (553 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-45805412991 / 1000000000000) (-45805412967 / 1000000000000), orderedInterval (-5417635661 / 1000000000000) (-5417635636 / 1000000000000)))) (orderedInterval (4837947873 / 1000000000000) (4837947908 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (505914381178689 / 4000000000000) 4 (IntervalRat.scale (553 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (70917499224 / 1000000000000) (70917499285 / 1000000000000), orderedInterval (-2302253704 / 1000000000000) (-2302253643 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2056513871964769 / 4000000000000) 4 (IntervalRat.scale (553 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-10653247472 / 1000000000000) (-10653247442 / 1000000000000), orderedInterval (33547790001 / 1000000000000) (33547790031 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1373655959262671 / 4000000000000) 4 (IntervalRat.scale (553 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-42242810253 / 1000000000000) (-42242808184 / 1000000000000), orderedInterval (8388573208 / 1000000000000) (8388575276 / 1000000000000)))) (orderedInterval (29095423507 / 1000000000000) (29095424859 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate405_chunkChecks4 :
    compactCertificate405.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate405.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate405_chunkChecks4_0
    compactCertificate405_chunkChecks4_1 compactCertificate405_chunkChecks4_2

theorem compactCertificate405_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate405.chunkCheck r b = true :=
  compactCertificate405.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate405_chunkChecks0
    · exact compactCertificate405_chunkChecks1
    · exact compactCertificate405_chunkChecks2
    · exact compactCertificate405_chunkChecks3
    · exact compactCertificate405_chunkChecks4)

theorem compactCertificate405_coefficient0 :
    compactCertificate405.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate405_coefficient1 :
    compactCertificate405.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate405_coefficient2 :
    compactCertificate405.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate405_coefficient3 :
    compactCertificate405.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate405_coefficient4 :
    compactCertificate405.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate405_coefficients : ∀ r : Fin 5,
    compactCertificate405.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate405_coefficient0
  · exact compactCertificate405_coefficient1
  · exact compactCertificate405_coefficient2
  · exact compactCertificate405_coefficient3
  · exact compactCertificate405_coefficient4

theorem compactCertificate405_lower : (1 : ℚ) ≤ compactCertificate405.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate405, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate405_proves {t : ℝ} (ht : t ∈ compactCertificate405.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate405.proves compactCertificate405_states compactCertificate405_chunks
    compactCertificate405_coefficients compactCertificate405_lower ht

end Erdos232
