/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate621 : CompactCertificate where
  left := 492
  right := 493
  center := 985 / 2
  grid := fun i =>
    match i.val with
    | 0 => 157
    | 1 => 116
    | 2 => 187
    | 3 => 34
    | 4 => 91
    | 5 => 246
    | 6 => 181
    | 7 => 310
    | 8 => 229
    | 9 => 351
    | 10 => 202
    | 11 => 359
    | 12 => 336
    | 13 => 240
    | 14 => 272
    | 15 => 226
    | 16 => 200
    | 17 => 290
    | 18 => 160
    | 19 => 136
    | 20 => 85
    | 21 => 46
    | 22 => 124
    | 23 => 170
    | 24 => 72
    | 25 => 292
    | _ => 195
  point := fun i =>
    match i.val with
    | 0 => 985 / 2
    | 1 => 290218616736497 / 800000000000
    | 2 => 93850737734801 / 160000000000
    | 3 => 84685068548179 / 800000000000
    | 4 => 227476006060663 / 800000000000
    | 5 => 617641606839771 / 800000000000
    | 6 => 454952012121523 / 800000000000
    | 7 => 779568027178879 / 800000000000
    | 8 => 574226280456061 / 800000000000
    | 9 => 881010783134803 / 800000000000
    | 10 => 508651812801787 / 800000000000
    | 11 => 902611567803383 / 800000000000
    | 12 => 843336810335027 / 800000000000
    | 13 => 601844941270691 / 800000000000
    | 14 => 682428018181989 / 800000000000
    | 15 => 568937334862741 / 800000000000
    | 16 => 502673389489561 / 800000000000
    | 17 => 145694340910539 / 160000000000
    | 18 => 402998214431633 / 800000000000
    | 19 => 341626049456713 / 800000000000
    | 20 => 213773719543939 / 800000000000
    | 21 => 114968217350013 / 800000000000
    | 22 => 312161074609039 / 800000000000
    | 23 => 426229259907503 / 800000000000
    | 24 => 180226280456061 / 800000000000
    | 25 => 732609824189981 / 800000000000
    | _ => 489349410442579 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-1979934782 / 1000000000000) (-1979934781 / 1000000000000), orderedInterval (-35896590165 / 1000000000000) (-35896590164 / 1000000000000))
    | 1 => (orderedInterval (-31921815328 / 1000000000000) (-31921768629 / 1000000000000), orderedInterval (27170868114 / 1000000000000) (27170914813 / 1000000000000))
    | 2 => (orderedInterval (4124663947 / 1000000000000) (4124663948 / 1000000000000), orderedInterval (-32688666178 / 1000000000000) (-32688666176 / 1000000000000))
    | 3 => (orderedInterval (-13394864640 / 1000000000000) (-13394864553 / 1000000000000), orderedInterval (76448073048 / 1000000000000) (76448073135 / 1000000000000))
    | 4 => (orderedInterval (32424576070 / 1000000000000) (32424600403 / 1000000000000), orderedInterval (-34517807476 / 1000000000000) (-34517783143 / 1000000000000))
    | 5 => (orderedInterval (156556946 / 1000000000000) (156556947 / 1000000000000), orderedInterval (28715001304 / 1000000000000) (28715001305 / 1000000000000))
    | 6 => (orderedInterval (-25068407117 / 1000000000000) (-25068407116 / 1000000000000), orderedInterval (-22137030935 / 1000000000000) (-22137030934 / 1000000000000))
    | 7 => (orderedInterval (24948146304 / 1000000000000) (24948146991 / 1000000000000), orderedInterval (5545531554 / 1000000000000) (5545532240 / 1000000000000))
    | 8 => (orderedInterval (22504169987 / 1000000000000) (22504177713 / 1000000000000), orderedInterval (-19521766913 / 1000000000000) (-19521759187 / 1000000000000))
    | 9 => (orderedInterval (14555624434 / 1000000000000) (14555624493 / 1000000000000), orderedInterval (-19143355112 / 1000000000000) (-19143355053 / 1000000000000))
    | 10 => (orderedInterval (28795638824 / 1000000000000) (28795723022 / 1000000000000), orderedInterval (-13140406721 / 1000000000000) (-13140322523 / 1000000000000))
    | 11 => (orderedInterval (-22290757268 / 1000000000000) (-22290756927 / 1000000000000), orderedInterval (-8197986887 / 1000000000000) (-8197986545 / 1000000000000))
    | 12 => (orderedInterval (-14255414031 / 1000000000000) (-14255413978 / 1000000000000), orderedInterval (20023973707 / 1000000000000) (20023973760 / 1000000000000))
    | 13 => (orderedInterval (-22620125829 / 1000000000000) (-22620116684 / 1000000000000), orderedInterval (18305856874 / 1000000000000) (18305866018 / 1000000000000))
    | 14 => (orderedInterval (-17450835054 / 1000000000000) (-17450834484 / 1000000000000), orderedInterval (21028508009 / 1000000000000) (21028508579 / 1000000000000))
    | 15 => (orderedInterval (27716208914 / 1000000000000) (27716290930 / 1000000000000), orderedInterval (-11288049090 / 1000000000000) (-11287967074 / 1000000000000))
    | 16 => (orderedInterval (23019320791 / 1000000000000) (23019320792 / 1000000000000), orderedInterval (21965432667 / 1000000000000) (21965432668 / 1000000000000))
    | 17 => (orderedInterval (8142130427 / 1000000000000) (8142130428 / 1000000000000), orderedInterval (25151740503 / 1000000000000) (25151740504 / 1000000000000))
    | 18 => (orderedInterval (33884153403 / 1000000000000) (33884168955 / 1000000000000), orderedInterval (-10786780200 / 1000000000000) (-10786764648 / 1000000000000))
    | 19 => (orderedInterval (20544426224 / 1000000000000) (20544426225 / 1000000000000), orderedInterval (32667322099 / 1000000000000) (32667322100 / 1000000000000))
    | 20 => (orderedInterval (-40171396850 / 1000000000000) (-40171396849 / 1000000000000), orderedInterval (-27649615693 / 1000000000000) (-27649615692 / 1000000000000))
    | 21 => (orderedInterval (-1228708517 / 1000000000000) (-1228708511 / 1000000000000), orderedInterval (66550504268 / 1000000000000) (66550504274 / 1000000000000))
    | 22 => (orderedInterval (39986240443 / 1000000000000) (39986240478 / 1000000000000), orderedInterval (5659750144 / 1000000000000) (5659750179 / 1000000000000))
    | 23 => (orderedInterval (-16542406347 / 1000000000000) (-16542405964 / 1000000000000), orderedInterval (30367396010 / 1000000000000) (30367396393 / 1000000000000))
    | 24 => (orderedInterval (-6731835039 / 1000000000000) (-6731835021 / 1000000000000), orderedInterval (52745936454 / 1000000000000) (52745936471 / 1000000000000))
    | 25 => (orderedInterval (-18868258701 / 1000000000000) (-18868257335 / 1000000000000), orderedInterval (18426842740 / 1000000000000) (18426844106 / 1000000000000))
    | _ => (orderedInterval (4457386363 / 1000000000000) (4457386364 / 1000000000000), orderedInterval (-31955061563 / 1000000000000) (-31955061562 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-840186261 / 1000000000000) (-840185791 / 1000000000000)
      | 1 => orderedInterval (1318073062 / 1000000000000) (1318074011 / 1000000000000)
      | 2 => orderedInterval (-225619297 / 1000000000000) (-225619061 / 1000000000000)
      | 3 => orderedInterval (-3621601431 / 1000000000000) (-3621594938 / 1000000000000)
      | 4 => orderedInterval (-1793358468 / 1000000000000) (-1793357541 / 1000000000000)
      | 5 => orderedInterval (-788790925 / 1000000000000) (-788789930 / 1000000000000)
      | 6 => orderedInterval (-7888426912 / 1000000000000) (-7888424302 / 1000000000000)
      | 7 => orderedInterval (383317197 / 1000000000000) (383317287 / 1000000000000)
      | _ => orderedInterval (659003975 / 1000000000000) (659004223 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-16326245096 / 1000000000000) (-16326244736 / 1000000000000)
      | 1 => orderedInterval (-4105948379 / 1000000000000) (-4105947798 / 1000000000000)
      | 2 => orderedInterval (-1026050157 / 1000000000000) (-1026049795 / 1000000000000)
      | 3 => orderedInterval (3679386380 / 1000000000000) (3679394972 / 1000000000000)
      | 4 => orderedInterval (1686150009 / 1000000000000) (1686151433 / 1000000000000)
      | 5 => orderedInterval (-601274503 / 1000000000000) (-601273067 / 1000000000000)
      | 6 => orderedInterval (-327468235 / 1000000000000) (-327465577 / 1000000000000)
      | 7 => orderedInterval (-2978008667 / 1000000000000) (-2978008582 / 1000000000000)
      | _ => orderedInterval (4802943445 / 1000000000000) (4802943844 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (635985628 / 1000000000000) (635985910 / 1000000000000)
      | 1 => orderedInterval (-365652915 / 1000000000000) (-365652524 / 1000000000000)
      | 2 => orderedInterval (1859310702 / 1000000000000) (1859311268 / 1000000000000)
      | 3 => orderedInterval (25998704994 / 1000000000000) (25998716582 / 1000000000000)
      | 4 => orderedInterval (3543622533 / 1000000000000) (3543624725 / 1000000000000)
      | 5 => orderedInterval (765424394 / 1000000000000) (765426473 / 1000000000000)
      | 6 => orderedInterval (6927988395 / 1000000000000) (6927991111 / 1000000000000)
      | 7 => orderedInterval (-910127891 / 1000000000000) (-910127803 / 1000000000000)
      | _ => orderedInterval (-4021466533 / 1000000000000) (-4021465865 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (17366243184 / 1000000000000) (17366243410 / 1000000000000)
      | 1 => orderedInterval (8115373282 / 1000000000000) (8115373593 / 1000000000000)
      | 2 => orderedInterval (2781697482 / 1000000000000) (2781698381 / 1000000000000)
      | 3 => orderedInterval (-21976804104 / 1000000000000) (-21976788058 / 1000000000000)
      | 4 => orderedInterval (-2079103849 / 1000000000000) (-2079100471 / 1000000000000)
      | 5 => orderedInterval (-1068958920 / 1000000000000) (-1068955908 / 1000000000000)
      | 6 => orderedInterval (-510608698 / 1000000000000) (-510605926 / 1000000000000)
      | 7 => orderedInterval (3042666826 / 1000000000000) (3042666918 / 1000000000000)
      | _ => orderedInterval (-1866089132 / 1000000000000) (-1866087979 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-455857128 / 1000000000000) (-455856938 / 1000000000000)
      | 1 => orderedInterval (31683795 / 1000000000000) (31684109 / 1000000000000)
      | 2 => orderedInterval (-9350850160 / 1000000000000) (-9350848702 / 1000000000000)
      | 3 => orderedInterval (-145921895656 / 1000000000000) (-145921872454 / 1000000000000)
      | 4 => orderedInterval (-5440587246 / 1000000000000) (-5440582015 / 1000000000000)
      | 5 => orderedInterval (341894316 / 1000000000000) (341898693 / 1000000000000)
      | 6 => orderedInterval (-6698450805 / 1000000000000) (-6698447968 / 1000000000000)
      | 7 => orderedInterval (1366699481 / 1000000000000) (1366699578 / 1000000000000)
      | _ => orderedInterval (16375686002 / 1000000000000) (16375688035 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-12797589060 / 1000000000000) (-12797576042 / 1000000000000)
    | 1 => orderedInterval (-15196515203 / 1000000000000) (-15196499306 / 1000000000000)
    | 2 => orderedInterval (34433789307 / 1000000000000) (34433809877 / 1000000000000)
    | 3 => orderedInterval (3804416071 / 1000000000000) (3804443960 / 1000000000000)
    | _ => orderedInterval (-149751677401 / 1000000000000) (-149751637662 / 1000000000000)

theorem compactCertificate621_stateChecks0 :
    compactCertificate621.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 157 12 (985 / 2)) (orderedInterval (-1979934782 / 1000000000000) (-1979934781 / 1000000000000), orderedInterval (-35896590165 / 1000000000000) (-35896590164 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 116 12 (290218616736497 / 800000000000)) (orderedInterval (-31921815328 / 1000000000000) (-31921768629 / 1000000000000), orderedInterval (27170868114 / 1000000000000) (27170914813 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 187 12 (93850737734801 / 160000000000)) (orderedInterval (4124663947 / 1000000000000) (4124663948 / 1000000000000), orderedInterval (-32688666178 / 1000000000000) (-32688666176 / 1000000000000))) = true
  rfl'

theorem compactCertificate621_stateChecks1 :
    compactCertificate621.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (84685068548179 / 800000000000)) (orderedInterval (-13394864640 / 1000000000000) (-13394864553 / 1000000000000), orderedInterval (76448073048 / 1000000000000) (76448073135 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 91 12 (227476006060663 / 800000000000)) (orderedInterval (32424576070 / 1000000000000) (32424600403 / 1000000000000), orderedInterval (-34517807476 / 1000000000000) (-34517783143 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 246 12 (617641606839771 / 800000000000)) (orderedInterval (156556946 / 1000000000000) (156556947 / 1000000000000), orderedInterval (28715001304 / 1000000000000) (28715001305 / 1000000000000))) = true
  rfl'

theorem compactCertificate621_stateChecks2 :
    compactCertificate621.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 181 12 (454952012121523 / 800000000000)) (orderedInterval (-25068407117 / 1000000000000) (-25068407116 / 1000000000000), orderedInterval (-22137030935 / 1000000000000) (-22137030934 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 310 12 (779568027178879 / 800000000000)) (orderedInterval (24948146304 / 1000000000000) (24948146991 / 1000000000000), orderedInterval (5545531554 / 1000000000000) (5545532240 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 229 12 (574226280456061 / 800000000000)) (orderedInterval (22504169987 / 1000000000000) (22504177713 / 1000000000000), orderedInterval (-19521766913 / 1000000000000) (-19521759187 / 1000000000000))) = true
  rfl'

theorem compactCertificate621_stateChecks3 :
    compactCertificate621.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 351 12 (881010783134803 / 800000000000)) (orderedInterval (14555624434 / 1000000000000) (14555624493 / 1000000000000), orderedInterval (-19143355112 / 1000000000000) (-19143355053 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 202 12 (508651812801787 / 800000000000)) (orderedInterval (28795638824 / 1000000000000) (28795723022 / 1000000000000), orderedInterval (-13140406721 / 1000000000000) (-13140322523 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 359 12 (902611567803383 / 800000000000)) (orderedInterval (-22290757268 / 1000000000000) (-22290756927 / 1000000000000), orderedInterval (-8197986887 / 1000000000000) (-8197986545 / 1000000000000))) = true
  rfl'

theorem compactCertificate621_stateChecks4 :
    compactCertificate621.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 336 12 (843336810335027 / 800000000000)) (orderedInterval (-14255414031 / 1000000000000) (-14255413978 / 1000000000000), orderedInterval (20023973707 / 1000000000000) (20023973760 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 240 12 (601844941270691 / 800000000000)) (orderedInterval (-22620125829 / 1000000000000) (-22620116684 / 1000000000000), orderedInterval (18305856874 / 1000000000000) (18305866018 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 272 12 (682428018181989 / 800000000000)) (orderedInterval (-17450835054 / 1000000000000) (-17450834484 / 1000000000000), orderedInterval (21028508009 / 1000000000000) (21028508579 / 1000000000000))) = true
  rfl'

theorem compactCertificate621_stateChecks5 :
    compactCertificate621.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 226 12 (568937334862741 / 800000000000)) (orderedInterval (27716208914 / 1000000000000) (27716290930 / 1000000000000), orderedInterval (-11288049090 / 1000000000000) (-11287967074 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 200 12 (502673389489561 / 800000000000)) (orderedInterval (23019320791 / 1000000000000) (23019320792 / 1000000000000), orderedInterval (21965432667 / 1000000000000) (21965432668 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 290 12 (145694340910539 / 160000000000)) (orderedInterval (8142130427 / 1000000000000) (8142130428 / 1000000000000), orderedInterval (25151740503 / 1000000000000) (25151740504 / 1000000000000))) = true
  rfl'

theorem compactCertificate621_stateChecks6 :
    compactCertificate621.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 160 12 (402998214431633 / 800000000000)) (orderedInterval (33884153403 / 1000000000000) (33884168955 / 1000000000000), orderedInterval (-10786780200 / 1000000000000) (-10786764648 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 136 12 (341626049456713 / 800000000000)) (orderedInterval (20544426224 / 1000000000000) (20544426225 / 1000000000000), orderedInterval (32667322099 / 1000000000000) (32667322100 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (213773719543939 / 800000000000)) (orderedInterval (-40171396850 / 1000000000000) (-40171396849 / 1000000000000), orderedInterval (-27649615693 / 1000000000000) (-27649615692 / 1000000000000))) = true
  rfl'

theorem compactCertificate621_stateChecks7 :
    compactCertificate621.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (114968217350013 / 800000000000)) (orderedInterval (-1228708517 / 1000000000000) (-1228708511 / 1000000000000), orderedInterval (66550504268 / 1000000000000) (66550504274 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 124 12 (312161074609039 / 800000000000)) (orderedInterval (39986240443 / 1000000000000) (39986240478 / 1000000000000), orderedInterval (5659750144 / 1000000000000) (5659750179 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 170 12 (426229259907503 / 800000000000)) (orderedInterval (-16542406347 / 1000000000000) (-16542405964 / 1000000000000), orderedInterval (30367396010 / 1000000000000) (30367396393 / 1000000000000))) = true
  rfl'

theorem compactCertificate621_stateChecks8 :
    compactCertificate621.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (180226280456061 / 800000000000)) (orderedInterval (-6731835039 / 1000000000000) (-6731835021 / 1000000000000), orderedInterval (52745936454 / 1000000000000) (52745936471 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 292 12 (732609824189981 / 800000000000)) (orderedInterval (-18868258701 / 1000000000000) (-18868257335 / 1000000000000), orderedInterval (18426842740 / 1000000000000) (18426844106 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 195 12 (489349410442579 / 800000000000)) (orderedInterval (4457386363 / 1000000000000) (4457386364 / 1000000000000), orderedInterval (-31955061563 / 1000000000000) (-31955061562 / 1000000000000))) = true
  rfl'

theorem compactCertificate621_states : ∀ j,
    BesselStateValid (compactCertificate621.point j) (compactCertificate621.state j) :=
  compactCertificate621.statesValid_of_checks3 compactCertificate621_stateChecks0
    compactCertificate621_stateChecks1 compactCertificate621_stateChecks2
    compactCertificate621_stateChecks3 compactCertificate621_stateChecks4
    compactCertificate621_stateChecks5 compactCertificate621_stateChecks6
    compactCertificate621_stateChecks7 compactCertificate621_stateChecks8

theorem compactCertificate621_chunkChecks0_0 :
    compactCertificate621.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (985 / 2) 0 (IntervalRat.scale (985 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-1979934782 / 1000000000000) (-1979934781 / 1000000000000), orderedInterval (-35896590165 / 1000000000000) (-35896590164 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (290218616736497 / 800000000000) 0 (IntervalRat.scale (985 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-31921815328 / 1000000000000) (-31921768629 / 1000000000000), orderedInterval (27170868114 / 1000000000000) (27170914813 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (93850737734801 / 160000000000) 0 (IntervalRat.scale (985 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (4124663947 / 1000000000000) (4124663948 / 1000000000000), orderedInterval (-32688666178 / 1000000000000) (-32688666176 / 1000000000000)))) (orderedInterval (-840186261 / 1000000000000) (-840185791 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (84685068548179 / 800000000000) 0 (IntervalRat.scale (985 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-13394864640 / 1000000000000) (-13394864553 / 1000000000000), orderedInterval (76448073048 / 1000000000000) (76448073135 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (227476006060663 / 800000000000) 0 (IntervalRat.scale (985 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (32424576070 / 1000000000000) (32424600403 / 1000000000000), orderedInterval (-34517807476 / 1000000000000) (-34517783143 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (617641606839771 / 800000000000) 0 (IntervalRat.scale (985 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (156556946 / 1000000000000) (156556947 / 1000000000000), orderedInterval (28715001304 / 1000000000000) (28715001305 / 1000000000000)))) (orderedInterval (1318073062 / 1000000000000) (1318074011 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (454952012121523 / 800000000000) 0 (IntervalRat.scale (985 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-25068407117 / 1000000000000) (-25068407116 / 1000000000000), orderedInterval (-22137030935 / 1000000000000) (-22137030934 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (779568027178879 / 800000000000) 0 (IntervalRat.scale (985 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (24948146304 / 1000000000000) (24948146991 / 1000000000000), orderedInterval (5545531554 / 1000000000000) (5545532240 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (574226280456061 / 800000000000) 0 (IntervalRat.scale (985 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (22504169987 / 1000000000000) (22504177713 / 1000000000000), orderedInterval (-19521766913 / 1000000000000) (-19521759187 / 1000000000000)))) (orderedInterval (-225619297 / 1000000000000) (-225619061 / 1000000000000))) = true
  rfl'

theorem compactCertificate621_chunkChecks0_1 :
    compactCertificate621.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (881010783134803 / 800000000000) 0 (IntervalRat.scale (985 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (14555624434 / 1000000000000) (14555624493 / 1000000000000), orderedInterval (-19143355112 / 1000000000000) (-19143355053 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (508651812801787 / 800000000000) 0 (IntervalRat.scale (985 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (28795638824 / 1000000000000) (28795723022 / 1000000000000), orderedInterval (-13140406721 / 1000000000000) (-13140322523 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (902611567803383 / 800000000000) 0 (IntervalRat.scale (985 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-22290757268 / 1000000000000) (-22290756927 / 1000000000000), orderedInterval (-8197986887 / 1000000000000) (-8197986545 / 1000000000000)))) (orderedInterval (-3621601431 / 1000000000000) (-3621594938 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (843336810335027 / 800000000000) 0 (IntervalRat.scale (985 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-14255414031 / 1000000000000) (-14255413978 / 1000000000000), orderedInterval (20023973707 / 1000000000000) (20023973760 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (601844941270691 / 800000000000) 0 (IntervalRat.scale (985 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-22620125829 / 1000000000000) (-22620116684 / 1000000000000), orderedInterval (18305856874 / 1000000000000) (18305866018 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (682428018181989 / 800000000000) 0 (IntervalRat.scale (985 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-17450835054 / 1000000000000) (-17450834484 / 1000000000000), orderedInterval (21028508009 / 1000000000000) (21028508579 / 1000000000000)))) (orderedInterval (-1793358468 / 1000000000000) (-1793357541 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (568937334862741 / 800000000000) 0 (IntervalRat.scale (985 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (27716208914 / 1000000000000) (27716290930 / 1000000000000), orderedInterval (-11288049090 / 1000000000000) (-11287967074 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (502673389489561 / 800000000000) 0 (IntervalRat.scale (985 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (23019320791 / 1000000000000) (23019320792 / 1000000000000), orderedInterval (21965432667 / 1000000000000) (21965432668 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (145694340910539 / 160000000000) 0 (IntervalRat.scale (985 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (8142130427 / 1000000000000) (8142130428 / 1000000000000), orderedInterval (25151740503 / 1000000000000) (25151740504 / 1000000000000)))) (orderedInterval (-788790925 / 1000000000000) (-788789930 / 1000000000000))) = true
  rfl'

theorem compactCertificate621_chunkChecks0_2 :
    compactCertificate621.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (402998214431633 / 800000000000) 0 (IntervalRat.scale (985 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (33884153403 / 1000000000000) (33884168955 / 1000000000000), orderedInterval (-10786780200 / 1000000000000) (-10786764648 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (341626049456713 / 800000000000) 0 (IntervalRat.scale (985 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (20544426224 / 1000000000000) (20544426225 / 1000000000000), orderedInterval (32667322099 / 1000000000000) (32667322100 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (213773719543939 / 800000000000) 0 (IntervalRat.scale (985 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-40171396850 / 1000000000000) (-40171396849 / 1000000000000), orderedInterval (-27649615693 / 1000000000000) (-27649615692 / 1000000000000)))) (orderedInterval (-7888426912 / 1000000000000) (-7888424302 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (114968217350013 / 800000000000) 0 (IntervalRat.scale (985 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-1228708517 / 1000000000000) (-1228708511 / 1000000000000), orderedInterval (66550504268 / 1000000000000) (66550504274 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (312161074609039 / 800000000000) 0 (IntervalRat.scale (985 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (39986240443 / 1000000000000) (39986240478 / 1000000000000), orderedInterval (5659750144 / 1000000000000) (5659750179 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (426229259907503 / 800000000000) 0 (IntervalRat.scale (985 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-16542406347 / 1000000000000) (-16542405964 / 1000000000000), orderedInterval (30367396010 / 1000000000000) (30367396393 / 1000000000000)))) (orderedInterval (383317197 / 1000000000000) (383317287 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (180226280456061 / 800000000000) 0 (IntervalRat.scale (985 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-6731835039 / 1000000000000) (-6731835021 / 1000000000000), orderedInterval (52745936454 / 1000000000000) (52745936471 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (732609824189981 / 800000000000) 0 (IntervalRat.scale (985 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-18868258701 / 1000000000000) (-18868257335 / 1000000000000), orderedInterval (18426842740 / 1000000000000) (18426844106 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (489349410442579 / 800000000000) 0 (IntervalRat.scale (985 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (4457386363 / 1000000000000) (4457386364 / 1000000000000), orderedInterval (-31955061563 / 1000000000000) (-31955061562 / 1000000000000)))) (orderedInterval (659003975 / 1000000000000) (659004223 / 1000000000000))) = true
  rfl'

theorem compactCertificate621_chunkChecks0 :
    compactCertificate621.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate621.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate621_chunkChecks0_0
    compactCertificate621_chunkChecks0_1 compactCertificate621_chunkChecks0_2

theorem compactCertificate621_chunkChecks1_0 :
    compactCertificate621.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (985 / 2) 1 (IntervalRat.scale (985 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-1979934782 / 1000000000000) (-1979934781 / 1000000000000), orderedInterval (-35896590165 / 1000000000000) (-35896590164 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (290218616736497 / 800000000000) 1 (IntervalRat.scale (985 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-31921815328 / 1000000000000) (-31921768629 / 1000000000000), orderedInterval (27170868114 / 1000000000000) (27170914813 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (93850737734801 / 160000000000) 1 (IntervalRat.scale (985 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (4124663947 / 1000000000000) (4124663948 / 1000000000000), orderedInterval (-32688666178 / 1000000000000) (-32688666176 / 1000000000000)))) (orderedInterval (-16326245096 / 1000000000000) (-16326244736 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (84685068548179 / 800000000000) 1 (IntervalRat.scale (985 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-13394864640 / 1000000000000) (-13394864553 / 1000000000000), orderedInterval (76448073048 / 1000000000000) (76448073135 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (227476006060663 / 800000000000) 1 (IntervalRat.scale (985 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (32424576070 / 1000000000000) (32424600403 / 1000000000000), orderedInterval (-34517807476 / 1000000000000) (-34517783143 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (617641606839771 / 800000000000) 1 (IntervalRat.scale (985 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (156556946 / 1000000000000) (156556947 / 1000000000000), orderedInterval (28715001304 / 1000000000000) (28715001305 / 1000000000000)))) (orderedInterval (-4105948379 / 1000000000000) (-4105947798 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (454952012121523 / 800000000000) 1 (IntervalRat.scale (985 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-25068407117 / 1000000000000) (-25068407116 / 1000000000000), orderedInterval (-22137030935 / 1000000000000) (-22137030934 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (779568027178879 / 800000000000) 1 (IntervalRat.scale (985 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (24948146304 / 1000000000000) (24948146991 / 1000000000000), orderedInterval (5545531554 / 1000000000000) (5545532240 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (574226280456061 / 800000000000) 1 (IntervalRat.scale (985 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (22504169987 / 1000000000000) (22504177713 / 1000000000000), orderedInterval (-19521766913 / 1000000000000) (-19521759187 / 1000000000000)))) (orderedInterval (-1026050157 / 1000000000000) (-1026049795 / 1000000000000))) = true
  rfl'

theorem compactCertificate621_chunkChecks1_1 :
    compactCertificate621.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (881010783134803 / 800000000000) 1 (IntervalRat.scale (985 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (14555624434 / 1000000000000) (14555624493 / 1000000000000), orderedInterval (-19143355112 / 1000000000000) (-19143355053 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (508651812801787 / 800000000000) 1 (IntervalRat.scale (985 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (28795638824 / 1000000000000) (28795723022 / 1000000000000), orderedInterval (-13140406721 / 1000000000000) (-13140322523 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (902611567803383 / 800000000000) 1 (IntervalRat.scale (985 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-22290757268 / 1000000000000) (-22290756927 / 1000000000000), orderedInterval (-8197986887 / 1000000000000) (-8197986545 / 1000000000000)))) (orderedInterval (3679386380 / 1000000000000) (3679394972 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (843336810335027 / 800000000000) 1 (IntervalRat.scale (985 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-14255414031 / 1000000000000) (-14255413978 / 1000000000000), orderedInterval (20023973707 / 1000000000000) (20023973760 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (601844941270691 / 800000000000) 1 (IntervalRat.scale (985 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-22620125829 / 1000000000000) (-22620116684 / 1000000000000), orderedInterval (18305856874 / 1000000000000) (18305866018 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (682428018181989 / 800000000000) 1 (IntervalRat.scale (985 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-17450835054 / 1000000000000) (-17450834484 / 1000000000000), orderedInterval (21028508009 / 1000000000000) (21028508579 / 1000000000000)))) (orderedInterval (1686150009 / 1000000000000) (1686151433 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (568937334862741 / 800000000000) 1 (IntervalRat.scale (985 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (27716208914 / 1000000000000) (27716290930 / 1000000000000), orderedInterval (-11288049090 / 1000000000000) (-11287967074 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (502673389489561 / 800000000000) 1 (IntervalRat.scale (985 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (23019320791 / 1000000000000) (23019320792 / 1000000000000), orderedInterval (21965432667 / 1000000000000) (21965432668 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (145694340910539 / 160000000000) 1 (IntervalRat.scale (985 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (8142130427 / 1000000000000) (8142130428 / 1000000000000), orderedInterval (25151740503 / 1000000000000) (25151740504 / 1000000000000)))) (orderedInterval (-601274503 / 1000000000000) (-601273067 / 1000000000000))) = true
  rfl'

theorem compactCertificate621_chunkChecks1_2 :
    compactCertificate621.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (402998214431633 / 800000000000) 1 (IntervalRat.scale (985 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (33884153403 / 1000000000000) (33884168955 / 1000000000000), orderedInterval (-10786780200 / 1000000000000) (-10786764648 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (341626049456713 / 800000000000) 1 (IntervalRat.scale (985 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (20544426224 / 1000000000000) (20544426225 / 1000000000000), orderedInterval (32667322099 / 1000000000000) (32667322100 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (213773719543939 / 800000000000) 1 (IntervalRat.scale (985 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-40171396850 / 1000000000000) (-40171396849 / 1000000000000), orderedInterval (-27649615693 / 1000000000000) (-27649615692 / 1000000000000)))) (orderedInterval (-327468235 / 1000000000000) (-327465577 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (114968217350013 / 800000000000) 1 (IntervalRat.scale (985 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-1228708517 / 1000000000000) (-1228708511 / 1000000000000), orderedInterval (66550504268 / 1000000000000) (66550504274 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (312161074609039 / 800000000000) 1 (IntervalRat.scale (985 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (39986240443 / 1000000000000) (39986240478 / 1000000000000), orderedInterval (5659750144 / 1000000000000) (5659750179 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (426229259907503 / 800000000000) 1 (IntervalRat.scale (985 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-16542406347 / 1000000000000) (-16542405964 / 1000000000000), orderedInterval (30367396010 / 1000000000000) (30367396393 / 1000000000000)))) (orderedInterval (-2978008667 / 1000000000000) (-2978008582 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (180226280456061 / 800000000000) 1 (IntervalRat.scale (985 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-6731835039 / 1000000000000) (-6731835021 / 1000000000000), orderedInterval (52745936454 / 1000000000000) (52745936471 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (732609824189981 / 800000000000) 1 (IntervalRat.scale (985 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-18868258701 / 1000000000000) (-18868257335 / 1000000000000), orderedInterval (18426842740 / 1000000000000) (18426844106 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (489349410442579 / 800000000000) 1 (IntervalRat.scale (985 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (4457386363 / 1000000000000) (4457386364 / 1000000000000), orderedInterval (-31955061563 / 1000000000000) (-31955061562 / 1000000000000)))) (orderedInterval (4802943445 / 1000000000000) (4802943844 / 1000000000000))) = true
  rfl'

theorem compactCertificate621_chunkChecks1 :
    compactCertificate621.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate621.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate621_chunkChecks1_0
    compactCertificate621_chunkChecks1_1 compactCertificate621_chunkChecks1_2

theorem compactCertificate621_chunkChecks2_0 :
    compactCertificate621.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (985 / 2) 2 (IntervalRat.scale (985 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-1979934782 / 1000000000000) (-1979934781 / 1000000000000), orderedInterval (-35896590165 / 1000000000000) (-35896590164 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (290218616736497 / 800000000000) 2 (IntervalRat.scale (985 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-31921815328 / 1000000000000) (-31921768629 / 1000000000000), orderedInterval (27170868114 / 1000000000000) (27170914813 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (93850737734801 / 160000000000) 2 (IntervalRat.scale (985 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (4124663947 / 1000000000000) (4124663948 / 1000000000000), orderedInterval (-32688666178 / 1000000000000) (-32688666176 / 1000000000000)))) (orderedInterval (635985628 / 1000000000000) (635985910 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (84685068548179 / 800000000000) 2 (IntervalRat.scale (985 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-13394864640 / 1000000000000) (-13394864553 / 1000000000000), orderedInterval (76448073048 / 1000000000000) (76448073135 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (227476006060663 / 800000000000) 2 (IntervalRat.scale (985 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (32424576070 / 1000000000000) (32424600403 / 1000000000000), orderedInterval (-34517807476 / 1000000000000) (-34517783143 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (617641606839771 / 800000000000) 2 (IntervalRat.scale (985 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (156556946 / 1000000000000) (156556947 / 1000000000000), orderedInterval (28715001304 / 1000000000000) (28715001305 / 1000000000000)))) (orderedInterval (-365652915 / 1000000000000) (-365652524 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (454952012121523 / 800000000000) 2 (IntervalRat.scale (985 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-25068407117 / 1000000000000) (-25068407116 / 1000000000000), orderedInterval (-22137030935 / 1000000000000) (-22137030934 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (779568027178879 / 800000000000) 2 (IntervalRat.scale (985 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (24948146304 / 1000000000000) (24948146991 / 1000000000000), orderedInterval (5545531554 / 1000000000000) (5545532240 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (574226280456061 / 800000000000) 2 (IntervalRat.scale (985 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (22504169987 / 1000000000000) (22504177713 / 1000000000000), orderedInterval (-19521766913 / 1000000000000) (-19521759187 / 1000000000000)))) (orderedInterval (1859310702 / 1000000000000) (1859311268 / 1000000000000))) = true
  rfl'

theorem compactCertificate621_chunkChecks2_1 :
    compactCertificate621.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (881010783134803 / 800000000000) 2 (IntervalRat.scale (985 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (14555624434 / 1000000000000) (14555624493 / 1000000000000), orderedInterval (-19143355112 / 1000000000000) (-19143355053 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (508651812801787 / 800000000000) 2 (IntervalRat.scale (985 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (28795638824 / 1000000000000) (28795723022 / 1000000000000), orderedInterval (-13140406721 / 1000000000000) (-13140322523 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (902611567803383 / 800000000000) 2 (IntervalRat.scale (985 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-22290757268 / 1000000000000) (-22290756927 / 1000000000000), orderedInterval (-8197986887 / 1000000000000) (-8197986545 / 1000000000000)))) (orderedInterval (25998704994 / 1000000000000) (25998716582 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (843336810335027 / 800000000000) 2 (IntervalRat.scale (985 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-14255414031 / 1000000000000) (-14255413978 / 1000000000000), orderedInterval (20023973707 / 1000000000000) (20023973760 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (601844941270691 / 800000000000) 2 (IntervalRat.scale (985 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-22620125829 / 1000000000000) (-22620116684 / 1000000000000), orderedInterval (18305856874 / 1000000000000) (18305866018 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (682428018181989 / 800000000000) 2 (IntervalRat.scale (985 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-17450835054 / 1000000000000) (-17450834484 / 1000000000000), orderedInterval (21028508009 / 1000000000000) (21028508579 / 1000000000000)))) (orderedInterval (3543622533 / 1000000000000) (3543624725 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (568937334862741 / 800000000000) 2 (IntervalRat.scale (985 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (27716208914 / 1000000000000) (27716290930 / 1000000000000), orderedInterval (-11288049090 / 1000000000000) (-11287967074 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (502673389489561 / 800000000000) 2 (IntervalRat.scale (985 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (23019320791 / 1000000000000) (23019320792 / 1000000000000), orderedInterval (21965432667 / 1000000000000) (21965432668 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (145694340910539 / 160000000000) 2 (IntervalRat.scale (985 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (8142130427 / 1000000000000) (8142130428 / 1000000000000), orderedInterval (25151740503 / 1000000000000) (25151740504 / 1000000000000)))) (orderedInterval (765424394 / 1000000000000) (765426473 / 1000000000000))) = true
  rfl'

theorem compactCertificate621_chunkChecks2_2 :
    compactCertificate621.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (402998214431633 / 800000000000) 2 (IntervalRat.scale (985 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (33884153403 / 1000000000000) (33884168955 / 1000000000000), orderedInterval (-10786780200 / 1000000000000) (-10786764648 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (341626049456713 / 800000000000) 2 (IntervalRat.scale (985 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (20544426224 / 1000000000000) (20544426225 / 1000000000000), orderedInterval (32667322099 / 1000000000000) (32667322100 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (213773719543939 / 800000000000) 2 (IntervalRat.scale (985 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-40171396850 / 1000000000000) (-40171396849 / 1000000000000), orderedInterval (-27649615693 / 1000000000000) (-27649615692 / 1000000000000)))) (orderedInterval (6927988395 / 1000000000000) (6927991111 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (114968217350013 / 800000000000) 2 (IntervalRat.scale (985 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-1228708517 / 1000000000000) (-1228708511 / 1000000000000), orderedInterval (66550504268 / 1000000000000) (66550504274 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (312161074609039 / 800000000000) 2 (IntervalRat.scale (985 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (39986240443 / 1000000000000) (39986240478 / 1000000000000), orderedInterval (5659750144 / 1000000000000) (5659750179 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (426229259907503 / 800000000000) 2 (IntervalRat.scale (985 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-16542406347 / 1000000000000) (-16542405964 / 1000000000000), orderedInterval (30367396010 / 1000000000000) (30367396393 / 1000000000000)))) (orderedInterval (-910127891 / 1000000000000) (-910127803 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (180226280456061 / 800000000000) 2 (IntervalRat.scale (985 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-6731835039 / 1000000000000) (-6731835021 / 1000000000000), orderedInterval (52745936454 / 1000000000000) (52745936471 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (732609824189981 / 800000000000) 2 (IntervalRat.scale (985 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-18868258701 / 1000000000000) (-18868257335 / 1000000000000), orderedInterval (18426842740 / 1000000000000) (18426844106 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (489349410442579 / 800000000000) 2 (IntervalRat.scale (985 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (4457386363 / 1000000000000) (4457386364 / 1000000000000), orderedInterval (-31955061563 / 1000000000000) (-31955061562 / 1000000000000)))) (orderedInterval (-4021466533 / 1000000000000) (-4021465865 / 1000000000000))) = true
  rfl'

theorem compactCertificate621_chunkChecks2 :
    compactCertificate621.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate621.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate621_chunkChecks2_0
    compactCertificate621_chunkChecks2_1 compactCertificate621_chunkChecks2_2

theorem compactCertificate621_chunkChecks3_0 :
    compactCertificate621.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (985 / 2) 3 (IntervalRat.scale (985 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-1979934782 / 1000000000000) (-1979934781 / 1000000000000), orderedInterval (-35896590165 / 1000000000000) (-35896590164 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (290218616736497 / 800000000000) 3 (IntervalRat.scale (985 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-31921815328 / 1000000000000) (-31921768629 / 1000000000000), orderedInterval (27170868114 / 1000000000000) (27170914813 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (93850737734801 / 160000000000) 3 (IntervalRat.scale (985 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (4124663947 / 1000000000000) (4124663948 / 1000000000000), orderedInterval (-32688666178 / 1000000000000) (-32688666176 / 1000000000000)))) (orderedInterval (17366243184 / 1000000000000) (17366243410 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (84685068548179 / 800000000000) 3 (IntervalRat.scale (985 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-13394864640 / 1000000000000) (-13394864553 / 1000000000000), orderedInterval (76448073048 / 1000000000000) (76448073135 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (227476006060663 / 800000000000) 3 (IntervalRat.scale (985 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (32424576070 / 1000000000000) (32424600403 / 1000000000000), orderedInterval (-34517807476 / 1000000000000) (-34517783143 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (617641606839771 / 800000000000) 3 (IntervalRat.scale (985 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (156556946 / 1000000000000) (156556947 / 1000000000000), orderedInterval (28715001304 / 1000000000000) (28715001305 / 1000000000000)))) (orderedInterval (8115373282 / 1000000000000) (8115373593 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (454952012121523 / 800000000000) 3 (IntervalRat.scale (985 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-25068407117 / 1000000000000) (-25068407116 / 1000000000000), orderedInterval (-22137030935 / 1000000000000) (-22137030934 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (779568027178879 / 800000000000) 3 (IntervalRat.scale (985 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (24948146304 / 1000000000000) (24948146991 / 1000000000000), orderedInterval (5545531554 / 1000000000000) (5545532240 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (574226280456061 / 800000000000) 3 (IntervalRat.scale (985 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (22504169987 / 1000000000000) (22504177713 / 1000000000000), orderedInterval (-19521766913 / 1000000000000) (-19521759187 / 1000000000000)))) (orderedInterval (2781697482 / 1000000000000) (2781698381 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate621_chunkChecks3_1 :
    compactCertificate621.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (881010783134803 / 800000000000) 3 (IntervalRat.scale (985 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (14555624434 / 1000000000000) (14555624493 / 1000000000000), orderedInterval (-19143355112 / 1000000000000) (-19143355053 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (508651812801787 / 800000000000) 3 (IntervalRat.scale (985 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (28795638824 / 1000000000000) (28795723022 / 1000000000000), orderedInterval (-13140406721 / 1000000000000) (-13140322523 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (902611567803383 / 800000000000) 3 (IntervalRat.scale (985 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-22290757268 / 1000000000000) (-22290756927 / 1000000000000), orderedInterval (-8197986887 / 1000000000000) (-8197986545 / 1000000000000)))) (orderedInterval (-21976804104 / 1000000000000) (-21976788058 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (843336810335027 / 800000000000) 3 (IntervalRat.scale (985 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-14255414031 / 1000000000000) (-14255413978 / 1000000000000), orderedInterval (20023973707 / 1000000000000) (20023973760 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (601844941270691 / 800000000000) 3 (IntervalRat.scale (985 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-22620125829 / 1000000000000) (-22620116684 / 1000000000000), orderedInterval (18305856874 / 1000000000000) (18305866018 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (682428018181989 / 800000000000) 3 (IntervalRat.scale (985 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-17450835054 / 1000000000000) (-17450834484 / 1000000000000), orderedInterval (21028508009 / 1000000000000) (21028508579 / 1000000000000)))) (orderedInterval (-2079103849 / 1000000000000) (-2079100471 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (568937334862741 / 800000000000) 3 (IntervalRat.scale (985 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (27716208914 / 1000000000000) (27716290930 / 1000000000000), orderedInterval (-11288049090 / 1000000000000) (-11287967074 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (502673389489561 / 800000000000) 3 (IntervalRat.scale (985 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (23019320791 / 1000000000000) (23019320792 / 1000000000000), orderedInterval (21965432667 / 1000000000000) (21965432668 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (145694340910539 / 160000000000) 3 (IntervalRat.scale (985 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (8142130427 / 1000000000000) (8142130428 / 1000000000000), orderedInterval (25151740503 / 1000000000000) (25151740504 / 1000000000000)))) (orderedInterval (-1068958920 / 1000000000000) (-1068955908 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate621_chunkChecks3_2 :
    compactCertificate621.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (402998214431633 / 800000000000) 3 (IntervalRat.scale (985 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (33884153403 / 1000000000000) (33884168955 / 1000000000000), orderedInterval (-10786780200 / 1000000000000) (-10786764648 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (341626049456713 / 800000000000) 3 (IntervalRat.scale (985 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (20544426224 / 1000000000000) (20544426225 / 1000000000000), orderedInterval (32667322099 / 1000000000000) (32667322100 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (213773719543939 / 800000000000) 3 (IntervalRat.scale (985 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-40171396850 / 1000000000000) (-40171396849 / 1000000000000), orderedInterval (-27649615693 / 1000000000000) (-27649615692 / 1000000000000)))) (orderedInterval (-510608698 / 1000000000000) (-510605926 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (114968217350013 / 800000000000) 3 (IntervalRat.scale (985 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-1228708517 / 1000000000000) (-1228708511 / 1000000000000), orderedInterval (66550504268 / 1000000000000) (66550504274 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (312161074609039 / 800000000000) 3 (IntervalRat.scale (985 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (39986240443 / 1000000000000) (39986240478 / 1000000000000), orderedInterval (5659750144 / 1000000000000) (5659750179 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (426229259907503 / 800000000000) 3 (IntervalRat.scale (985 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-16542406347 / 1000000000000) (-16542405964 / 1000000000000), orderedInterval (30367396010 / 1000000000000) (30367396393 / 1000000000000)))) (orderedInterval (3042666826 / 1000000000000) (3042666918 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (180226280456061 / 800000000000) 3 (IntervalRat.scale (985 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-6731835039 / 1000000000000) (-6731835021 / 1000000000000), orderedInterval (52745936454 / 1000000000000) (52745936471 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (732609824189981 / 800000000000) 3 (IntervalRat.scale (985 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-18868258701 / 1000000000000) (-18868257335 / 1000000000000), orderedInterval (18426842740 / 1000000000000) (18426844106 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (489349410442579 / 800000000000) 3 (IntervalRat.scale (985 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (4457386363 / 1000000000000) (4457386364 / 1000000000000), orderedInterval (-31955061563 / 1000000000000) (-31955061562 / 1000000000000)))) (orderedInterval (-1866089132 / 1000000000000) (-1866087979 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate621_chunkChecks3 :
    compactCertificate621.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate621.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate621_chunkChecks3_0
    compactCertificate621_chunkChecks3_1 compactCertificate621_chunkChecks3_2

theorem compactCertificate621_chunkChecks4_0 :
    compactCertificate621.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (985 / 2) 4 (IntervalRat.scale (985 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-1979934782 / 1000000000000) (-1979934781 / 1000000000000), orderedInterval (-35896590165 / 1000000000000) (-35896590164 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (290218616736497 / 800000000000) 4 (IntervalRat.scale (985 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-31921815328 / 1000000000000) (-31921768629 / 1000000000000), orderedInterval (27170868114 / 1000000000000) (27170914813 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (93850737734801 / 160000000000) 4 (IntervalRat.scale (985 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (4124663947 / 1000000000000) (4124663948 / 1000000000000), orderedInterval (-32688666178 / 1000000000000) (-32688666176 / 1000000000000)))) (orderedInterval (-455857128 / 1000000000000) (-455856938 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (84685068548179 / 800000000000) 4 (IntervalRat.scale (985 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-13394864640 / 1000000000000) (-13394864553 / 1000000000000), orderedInterval (76448073048 / 1000000000000) (76448073135 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (227476006060663 / 800000000000) 4 (IntervalRat.scale (985 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (32424576070 / 1000000000000) (32424600403 / 1000000000000), orderedInterval (-34517807476 / 1000000000000) (-34517783143 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (617641606839771 / 800000000000) 4 (IntervalRat.scale (985 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (156556946 / 1000000000000) (156556947 / 1000000000000), orderedInterval (28715001304 / 1000000000000) (28715001305 / 1000000000000)))) (orderedInterval (31683795 / 1000000000000) (31684109 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (454952012121523 / 800000000000) 4 (IntervalRat.scale (985 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-25068407117 / 1000000000000) (-25068407116 / 1000000000000), orderedInterval (-22137030935 / 1000000000000) (-22137030934 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (779568027178879 / 800000000000) 4 (IntervalRat.scale (985 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (24948146304 / 1000000000000) (24948146991 / 1000000000000), orderedInterval (5545531554 / 1000000000000) (5545532240 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (574226280456061 / 800000000000) 4 (IntervalRat.scale (985 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (22504169987 / 1000000000000) (22504177713 / 1000000000000), orderedInterval (-19521766913 / 1000000000000) (-19521759187 / 1000000000000)))) (orderedInterval (-9350850160 / 1000000000000) (-9350848702 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate621_chunkChecks4_1 :
    compactCertificate621.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (881010783134803 / 800000000000) 4 (IntervalRat.scale (985 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (14555624434 / 1000000000000) (14555624493 / 1000000000000), orderedInterval (-19143355112 / 1000000000000) (-19143355053 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (508651812801787 / 800000000000) 4 (IntervalRat.scale (985 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (28795638824 / 1000000000000) (28795723022 / 1000000000000), orderedInterval (-13140406721 / 1000000000000) (-13140322523 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (902611567803383 / 800000000000) 4 (IntervalRat.scale (985 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-22290757268 / 1000000000000) (-22290756927 / 1000000000000), orderedInterval (-8197986887 / 1000000000000) (-8197986545 / 1000000000000)))) (orderedInterval (-145921895656 / 1000000000000) (-145921872454 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (843336810335027 / 800000000000) 4 (IntervalRat.scale (985 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-14255414031 / 1000000000000) (-14255413978 / 1000000000000), orderedInterval (20023973707 / 1000000000000) (20023973760 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (601844941270691 / 800000000000) 4 (IntervalRat.scale (985 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-22620125829 / 1000000000000) (-22620116684 / 1000000000000), orderedInterval (18305856874 / 1000000000000) (18305866018 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (682428018181989 / 800000000000) 4 (IntervalRat.scale (985 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-17450835054 / 1000000000000) (-17450834484 / 1000000000000), orderedInterval (21028508009 / 1000000000000) (21028508579 / 1000000000000)))) (orderedInterval (-5440587246 / 1000000000000) (-5440582015 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (568937334862741 / 800000000000) 4 (IntervalRat.scale (985 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (27716208914 / 1000000000000) (27716290930 / 1000000000000), orderedInterval (-11288049090 / 1000000000000) (-11287967074 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (502673389489561 / 800000000000) 4 (IntervalRat.scale (985 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (23019320791 / 1000000000000) (23019320792 / 1000000000000), orderedInterval (21965432667 / 1000000000000) (21965432668 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (145694340910539 / 160000000000) 4 (IntervalRat.scale (985 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (8142130427 / 1000000000000) (8142130428 / 1000000000000), orderedInterval (25151740503 / 1000000000000) (25151740504 / 1000000000000)))) (orderedInterval (341894316 / 1000000000000) (341898693 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate621_chunkChecks4_2 :
    compactCertificate621.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (402998214431633 / 800000000000) 4 (IntervalRat.scale (985 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (33884153403 / 1000000000000) (33884168955 / 1000000000000), orderedInterval (-10786780200 / 1000000000000) (-10786764648 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (341626049456713 / 800000000000) 4 (IntervalRat.scale (985 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (20544426224 / 1000000000000) (20544426225 / 1000000000000), orderedInterval (32667322099 / 1000000000000) (32667322100 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (213773719543939 / 800000000000) 4 (IntervalRat.scale (985 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-40171396850 / 1000000000000) (-40171396849 / 1000000000000), orderedInterval (-27649615693 / 1000000000000) (-27649615692 / 1000000000000)))) (orderedInterval (-6698450805 / 1000000000000) (-6698447968 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (114968217350013 / 800000000000) 4 (IntervalRat.scale (985 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-1228708517 / 1000000000000) (-1228708511 / 1000000000000), orderedInterval (66550504268 / 1000000000000) (66550504274 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (312161074609039 / 800000000000) 4 (IntervalRat.scale (985 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (39986240443 / 1000000000000) (39986240478 / 1000000000000), orderedInterval (5659750144 / 1000000000000) (5659750179 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (426229259907503 / 800000000000) 4 (IntervalRat.scale (985 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-16542406347 / 1000000000000) (-16542405964 / 1000000000000), orderedInterval (30367396010 / 1000000000000) (30367396393 / 1000000000000)))) (orderedInterval (1366699481 / 1000000000000) (1366699578 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (180226280456061 / 800000000000) 4 (IntervalRat.scale (985 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-6731835039 / 1000000000000) (-6731835021 / 1000000000000), orderedInterval (52745936454 / 1000000000000) (52745936471 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (732609824189981 / 800000000000) 4 (IntervalRat.scale (985 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-18868258701 / 1000000000000) (-18868257335 / 1000000000000), orderedInterval (18426842740 / 1000000000000) (18426844106 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (489349410442579 / 800000000000) 4 (IntervalRat.scale (985 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (4457386363 / 1000000000000) (4457386364 / 1000000000000), orderedInterval (-31955061563 / 1000000000000) (-31955061562 / 1000000000000)))) (orderedInterval (16375686002 / 1000000000000) (16375688035 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate621_chunkChecks4 :
    compactCertificate621.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate621.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate621_chunkChecks4_0
    compactCertificate621_chunkChecks4_1 compactCertificate621_chunkChecks4_2

theorem compactCertificate621_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate621.chunkCheck r b = true :=
  compactCertificate621.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate621_chunkChecks0
    · exact compactCertificate621_chunkChecks1
    · exact compactCertificate621_chunkChecks2
    · exact compactCertificate621_chunkChecks3
    · exact compactCertificate621_chunkChecks4)

theorem compactCertificate621_coefficient0 :
    compactCertificate621.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate621_coefficient1 :
    compactCertificate621.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate621_coefficient2 :
    compactCertificate621.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate621_coefficient3 :
    compactCertificate621.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate621_coefficient4 :
    compactCertificate621.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate621_coefficients : ∀ r : Fin 5,
    compactCertificate621.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate621_coefficient0
  · exact compactCertificate621_coefficient1
  · exact compactCertificate621_coefficient2
  · exact compactCertificate621_coefficient3
  · exact compactCertificate621_coefficient4

theorem compactCertificate621_lower : (1 : ℚ) ≤ compactCertificate621.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate621, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate621_proves {t : ℝ} (ht : t ∈ compactCertificate621.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate621.proves compactCertificate621_states compactCertificate621_chunks
    compactCertificate621_coefficients compactCertificate621_lower ht

end Erdos232
