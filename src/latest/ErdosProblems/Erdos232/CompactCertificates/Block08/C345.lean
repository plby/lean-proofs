/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate345 : CompactCertificate where
  left := 433 / 2
  right := 217
  center := 867 / 4
  grid := fun i =>
    match i.val with
    | 0 => 69
    | 1 => 51
    | 2 => 82
    | 3 => 15
    | 4 => 40
    | 5 => 108
    | 6 => 80
    | 7 => 137
    | 8 => 101
    | 9 => 154
    | 10 => 89
    | 11 => 158
    | 12 => 148
    | 13 => 105
    | 14 => 120
    | 15 => 100
    | 16 => 88
    | 17 => 128
    | 18 => 71
    | 19 => 60
    | 20 => 37
    | 21 => 20
    | 22 => 55
    | 23 => 75
    | 24 => 32
    | 25 => 128
    | _ => 86
  point := fun i =>
    match i.val with
    | 0 => 867 / 4
    | 1 => 1277256551830167 / 8000000000000
    | 2 => 413038525969911 / 1600000000000
    | 3 => 372700276300869 / 8000000000000
    | 4 => 1001125366774593 / 8000000000000
    | 5 => 2718250117411581 / 8000000000000
    | 6 => 2002250733550053 / 8000000000000
    | 7 => 3430890759208569 / 8000000000000
    | 8 => 2527178604849771 / 8000000000000
    | 9 => 3877341872984133 / 8000000000000
    | 10 => 2238584374107357 / 8000000000000
    | 11 => 3972407255256513 / 8000000000000
    | 12 => 3711538144976997 / 8000000000000
    | 13 => 2648728751683701 / 8000000000000
    | 14 => 3003376100323779 / 8000000000000
    | 15 => 2503901874751251 / 8000000000000
    | 16 => 2212273242068271 / 8000000000000
    | 17 => 641203013042829 / 1600000000000
    | 18 => 1773601278742263 / 8000000000000
    | 19 => 1503501446086143 / 8000000000000
    | 20 => 940821395150229 / 8000000000000
    | 21 => 505976875342443 / 8000000000000
    | 22 => 1373825643076329 / 8000000000000
    | 23 => 1875841463653833 / 8000000000000
    | 24 => 793178604849771 / 8000000000000
    | 25 => 3224226992754891 / 8000000000000
    | _ => 2153634207379269 / 8000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-37529303535 / 1000000000000) (-37529303534 / 1000000000000), orderedInterval (-39011600771 / 1000000000000) (-39011600770 / 1000000000000))
    | 1 => (orderedInterval (-13808576008 / 1000000000000) (-13808576007 / 1000000000000), orderedInterval (-61574616990 / 1000000000000) (-61574616989 / 1000000000000))
    | 2 => (orderedInterval (48147696315 / 1000000000000) (48147696318 / 1000000000000), orderedInterval (12067698524 / 1000000000000) (12067698527 / 1000000000000))
    | 3 => (orderedInterval (-28507660205 / 1000000000000) (-28507660204 / 1000000000000), orderedInterval (-113065282056 / 1000000000000) (-113065282055 / 1000000000000))
    | 4 => (orderedInterval (18430158186 / 1000000000000) (18430158187 / 1000000000000), orderedInterval (68829176310 / 1000000000000) (68829176311 / 1000000000000))
    | 5 => (orderedInterval (41396412939 / 1000000000000) (41396412941 / 1000000000000), orderedInterval (12586288281 / 1000000000000) (12586288284 / 1000000000000))
    | 6 => (orderedInterval (-13022766336 / 1000000000000) (-13022766228 / 1000000000000), orderedInterval (48750019882 / 1000000000000) (48750019990 / 1000000000000))
    | 7 => (orderedInterval (26311541312 / 1000000000000) (26311553020 / 1000000000000), orderedInterval (-28175743425 / 1000000000000) (-28175731717 / 1000000000000))
    | 8 => (orderedInterval (26029960153 / 1000000000000) (26029965567 / 1000000000000), orderedInterval (-36616005225 / 1000000000000) (-36615999811 / 1000000000000))
    | 9 => (orderedInterval (36135620997 / 1000000000000) (36135622213 / 1000000000000), orderedInterval (-2818307373 / 1000000000000) (-2818306157 / 1000000000000))
    | 10 => (orderedInterval (-40296617588 / 1000000000000) (-40296617587 / 1000000000000), orderedInterval (-25447810314 / 1000000000000) (-25447810313 / 1000000000000))
    | 11 => (orderedInterval (29422484863 / 1000000000000) (29422484864 / 1000000000000), orderedInterval (20376273124 / 1000000000000) (20376273125 / 1000000000000))
    | 12 => (orderedInterval (-8384252253 / 1000000000000) (-8384252240 / 1000000000000), orderedInterval (36090902950 / 1000000000000) (36090902963 / 1000000000000))
    | 13 => (orderedInterval (-39708657104 / 1000000000000) (-39708633640 / 1000000000000), orderedInterval (18661444811 / 1000000000000) (18661468275 / 1000000000000))
    | 14 => (orderedInterval (-29078687954 / 1000000000000) (-29078667206 / 1000000000000), orderedInterval (29196475904 / 1000000000000) (29196496651 / 1000000000000))
    | 15 => (orderedInterval (-17001725956 / 1000000000000) (-17001725579 / 1000000000000), orderedInterval (41799781179 / 1000000000000) (41799781556 / 1000000000000))
    | 16 => (orderedInterval (36328755073 / 1000000000000) (36328755074 / 1000000000000), orderedInterval (31276920362 / 1000000000000) (31276920363 / 1000000000000))
    | 17 => (orderedInterval (-22071657382 / 1000000000000) (-22071654959 / 1000000000000), orderedInterval (33214971892 / 1000000000000) (33214974314 / 1000000000000))
    | 18 => (orderedInterval (28830581354 / 1000000000000) (28830586609 / 1000000000000), orderedInterval (-45235096987 / 1000000000000) (-45235091731 / 1000000000000))
    | 19 => (orderedInterval (13090267820 / 1000000000000) (13090267821 / 1000000000000), orderedInterval (56675437083 / 1000000000000) (56675437084 / 1000000000000))
    | 20 => (orderedInterval (-61651881723 / 1000000000000) (-61651850308 / 1000000000000), orderedInterval (40416025310 / 1000000000000) (40416056725 / 1000000000000))
    | 21 => (orderedInterval (93459505681 / 1000000000000) (93459505682 / 1000000000000), orderedInterval (35739747403 / 1000000000000) (35739747404 / 1000000000000))
    | 22 => (orderedInterval (16517048555 / 1000000000000) (16517048777 / 1000000000000), orderedInterval (-58651300775 / 1000000000000) (-58651300552 / 1000000000000))
    | 23 => (orderedInterval (18082222573 / 1000000000000) (18082222989 / 1000000000000), orderedInterval (-48906377970 / 1000000000000) (-48906377555 / 1000000000000))
    | 24 => (orderedInterval (-45212028342 / 1000000000000) (-45212014908 / 1000000000000), orderedInterval (66385759033 / 1000000000000) (66385772467 / 1000000000000))
    | 25 => (orderedInterval (39463884208 / 1000000000000) (39463885433 / 1000000000000), orderedInterval (-4759699128 / 1000000000000) (-4759697903 / 1000000000000))
    | _ => (orderedInterval (-9077024024 / 1000000000000) (-9077023992 / 1000000000000), orderedInterval (47791662554 / 1000000000000) (47791662586 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-12178609572 / 1000000000000) (-12178609556 / 1000000000000)
      | 1 => orderedInterval (-1960650992 / 1000000000000) (-1960650965 / 1000000000000)
      | 2 => orderedInterval (-182460794 / 1000000000000) (-182460289 / 1000000000000)
      | 3 => orderedInterval (-5223931991 / 1000000000000) (-5223931688 / 1000000000000)
      | 4 => orderedInterval (-3456448002 / 1000000000000) (-3456445651 / 1000000000000)
      | 5 => orderedInterval (-2840425876 / 1000000000000) (-2840425788 / 1000000000000)
      | 6 => orderedInterval (-7357795225 / 1000000000000) (-7357793307 / 1000000000000)
      | 7 => orderedInterval (-3486261864 / 1000000000000) (-3486261800 / 1000000000000)
      | _ => orderedInterval (-1781892881 / 1000000000000) (-1781892634 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-15042057239 / 1000000000000) (-15042057220 / 1000000000000)
      | 1 => orderedInterval (311947912 / 1000000000000) (311947943 / 1000000000000)
      | 2 => orderedInterval (429775448 / 1000000000000) (429776375 / 1000000000000)
      | 3 => orderedInterval (5321455464 / 1000000000000) (5321456126 / 1000000000000)
      | 4 => orderedInterval (1045066316 / 1000000000000) (1045069930 / 1000000000000)
      | 5 => orderedInterval (-14173311 / 1000000000000) (-14173159 / 1000000000000)
      | 6 => orderedInterval (5330409780 / 1000000000000) (5330411246 / 1000000000000)
      | 7 => orderedInterval (4916386753 / 1000000000000) (4916386816 / 1000000000000)
      | _ => orderedInterval (-10233539075 / 1000000000000) (-10233538761 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (11006796114 / 1000000000000) (11006796135 / 1000000000000)
      | 1 => orderedInterval (6991821042 / 1000000000000) (6991821084 / 1000000000000)
      | 2 => orderedInterval (1838877317 / 1000000000000) (1838879051 / 1000000000000)
      | 3 => orderedInterval (15104883960 / 1000000000000) (15104885426 / 1000000000000)
      | 4 => orderedInterval (7621825705 / 1000000000000) (7621831285 / 1000000000000)
      | 5 => orderedInterval (5725283614 / 1000000000000) (5725283881 / 1000000000000)
      | 6 => orderedInterval (5946044789 / 1000000000000) (5946046025 / 1000000000000)
      | 7 => orderedInterval (1981267335 / 1000000000000) (1981267400 / 1000000000000)
      | _ => orderedInterval (8583844715 / 1000000000000) (8583845212 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (14444689365 / 1000000000000) (14444689389 / 1000000000000)
      | 1 => orderedInterval (2918797910 / 1000000000000) (2918797972 / 1000000000000)
      | 2 => orderedInterval (-4000584755 / 1000000000000) (-4000581476 / 1000000000000)
      | 3 => orderedInterval (-36437567485 / 1000000000000) (-36437564226 / 1000000000000)
      | 4 => orderedInterval (832323643 / 1000000000000) (832332243 / 1000000000000)
      | 5 => orderedInterval (-3137929018 / 1000000000000) (-3137928543 / 1000000000000)
      | 6 => orderedInterval (-5886077534 / 1000000000000) (-5886076419 / 1000000000000)
      | 7 => orderedInterval (-5399611411 / 1000000000000) (-5399611344 / 1000000000000)
      | _ => orderedInterval (14610726867 / 1000000000000) (14610727721 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-9361366742 / 1000000000000) (-9361366714 / 1000000000000)
      | 1 => orderedInterval (-17723110108 / 1000000000000) (-17723110012 / 1000000000000)
      | 2 => orderedInterval (-9562659808 / 1000000000000) (-9562653527 / 1000000000000)
      | 3 => orderedInterval (-53275756796 / 1000000000000) (-53275749510 / 1000000000000)
      | 4 => orderedInterval (-15949688976 / 1000000000000) (-15949675664 / 1000000000000)
      | 5 => orderedInterval (-12936721225 / 1000000000000) (-12936720368 / 1000000000000)
      | 6 => orderedInterval (-5583835698 / 1000000000000) (-5583834633 / 1000000000000)
      | 7 => orderedInterval (-2008266190 / 1000000000000) (-2008266118 / 1000000000000)
      | _ => orderedInterval (-34494766326 / 1000000000000) (-34494764801 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-38468477197 / 1000000000000) (-38468471678 / 1000000000000)
    | 1 => orderedInterval (-7934727952 / 1000000000000) (-7934720704 / 1000000000000)
    | 2 => orderedInterval (64800644591 / 1000000000000) (64800655499 / 1000000000000)
    | 3 => orderedInterval (-22055232418 / 1000000000000) (-22055214683 / 1000000000000)
    | _ => orderedInterval (-160896171869 / 1000000000000) (-160896141347 / 1000000000000)

theorem compactCertificate345_stateChecks0 :
    compactCertificate345.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (867 / 4)) (orderedInterval (-37529303535 / 1000000000000) (-37529303534 / 1000000000000), orderedInterval (-39011600771 / 1000000000000) (-39011600770 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (1277256551830167 / 8000000000000)) (orderedInterval (-13808576008 / 1000000000000) (-13808576007 / 1000000000000), orderedInterval (-61574616990 / 1000000000000) (-61574616989 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (413038525969911 / 1600000000000)) (orderedInterval (48147696315 / 1000000000000) (48147696318 / 1000000000000), orderedInterval (12067698524 / 1000000000000) (12067698527 / 1000000000000))) = true
  rfl'

theorem compactCertificate345_stateChecks1 :
    compactCertificate345.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 15 12 (372700276300869 / 8000000000000)) (orderedInterval (-28507660205 / 1000000000000) (-28507660204 / 1000000000000), orderedInterval (-113065282056 / 1000000000000) (-113065282055 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (1001125366774593 / 8000000000000)) (orderedInterval (18430158186 / 1000000000000) (18430158187 / 1000000000000), orderedInterval (68829176310 / 1000000000000) (68829176311 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 108 12 (2718250117411581 / 8000000000000)) (orderedInterval (41396412939 / 1000000000000) (41396412941 / 1000000000000), orderedInterval (12586288281 / 1000000000000) (12586288284 / 1000000000000))) = true
  rfl'

theorem compactCertificate345_stateChecks2 :
    compactCertificate345.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (2002250733550053 / 8000000000000)) (orderedInterval (-13022766336 / 1000000000000) (-13022766228 / 1000000000000), orderedInterval (48750019882 / 1000000000000) (48750019990 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 137 12 (3430890759208569 / 8000000000000)) (orderedInterval (26311541312 / 1000000000000) (26311553020 / 1000000000000), orderedInterval (-28175743425 / 1000000000000) (-28175731717 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 101 12 (2527178604849771 / 8000000000000)) (orderedInterval (26029960153 / 1000000000000) (26029965567 / 1000000000000), orderedInterval (-36616005225 / 1000000000000) (-36615999811 / 1000000000000))) = true
  rfl'

theorem compactCertificate345_stateChecks3 :
    compactCertificate345.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 154 12 (3877341872984133 / 8000000000000)) (orderedInterval (36135620997 / 1000000000000) (36135622213 / 1000000000000), orderedInterval (-2818307373 / 1000000000000) (-2818306157 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (2238584374107357 / 8000000000000)) (orderedInterval (-40296617588 / 1000000000000) (-40296617587 / 1000000000000), orderedInterval (-25447810314 / 1000000000000) (-25447810313 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 158 12 (3972407255256513 / 8000000000000)) (orderedInterval (29422484863 / 1000000000000) (29422484864 / 1000000000000), orderedInterval (20376273124 / 1000000000000) (20376273125 / 1000000000000))) = true
  rfl'

theorem compactCertificate345_stateChecks4 :
    compactCertificate345.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 148 12 (3711538144976997 / 8000000000000)) (orderedInterval (-8384252253 / 1000000000000) (-8384252240 / 1000000000000), orderedInterval (36090902950 / 1000000000000) (36090902963 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 105 12 (2648728751683701 / 8000000000000)) (orderedInterval (-39708657104 / 1000000000000) (-39708633640 / 1000000000000), orderedInterval (18661444811 / 1000000000000) (18661468275 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 120 12 (3003376100323779 / 8000000000000)) (orderedInterval (-29078687954 / 1000000000000) (-29078667206 / 1000000000000), orderedInterval (29196475904 / 1000000000000) (29196496651 / 1000000000000))) = true
  rfl'

theorem compactCertificate345_stateChecks5 :
    compactCertificate345.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 100 12 (2503901874751251 / 8000000000000)) (orderedInterval (-17001725956 / 1000000000000) (-17001725579 / 1000000000000), orderedInterval (41799781179 / 1000000000000) (41799781556 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 88 12 (2212273242068271 / 8000000000000)) (orderedInterval (36328755073 / 1000000000000) (36328755074 / 1000000000000), orderedInterval (31276920362 / 1000000000000) (31276920363 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 128 12 (641203013042829 / 1600000000000)) (orderedInterval (-22071657382 / 1000000000000) (-22071654959 / 1000000000000), orderedInterval (33214971892 / 1000000000000) (33214974314 / 1000000000000))) = true
  rfl'

theorem compactCertificate345_stateChecks6 :
    compactCertificate345.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (1773601278742263 / 8000000000000)) (orderedInterval (28830581354 / 1000000000000) (28830586609 / 1000000000000), orderedInterval (-45235096987 / 1000000000000) (-45235091731 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (1503501446086143 / 8000000000000)) (orderedInterval (13090267820 / 1000000000000) (13090267821 / 1000000000000), orderedInterval (56675437083 / 1000000000000) (56675437084 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (940821395150229 / 8000000000000)) (orderedInterval (-61651881723 / 1000000000000) (-61651850308 / 1000000000000), orderedInterval (40416025310 / 1000000000000) (40416056725 / 1000000000000))) = true
  rfl'

theorem compactCertificate345_stateChecks7 :
    compactCertificate345.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 20 12 (505976875342443 / 8000000000000)) (orderedInterval (93459505681 / 1000000000000) (93459505682 / 1000000000000), orderedInterval (35739747403 / 1000000000000) (35739747404 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (1373825643076329 / 8000000000000)) (orderedInterval (16517048555 / 1000000000000) (16517048777 / 1000000000000), orderedInterval (-58651300775 / 1000000000000) (-58651300552 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (1875841463653833 / 8000000000000)) (orderedInterval (18082222573 / 1000000000000) (18082222989 / 1000000000000), orderedInterval (-48906377970 / 1000000000000) (-48906377555 / 1000000000000))) = true
  rfl'

theorem compactCertificate345_stateChecks8 :
    compactCertificate345.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (793178604849771 / 8000000000000)) (orderedInterval (-45212028342 / 1000000000000) (-45212014908 / 1000000000000), orderedInterval (66385759033 / 1000000000000) (66385772467 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 128 12 (3224226992754891 / 8000000000000)) (orderedInterval (39463884208 / 1000000000000) (39463885433 / 1000000000000), orderedInterval (-4759699128 / 1000000000000) (-4759697903 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (2153634207379269 / 8000000000000)) (orderedInterval (-9077024024 / 1000000000000) (-9077023992 / 1000000000000), orderedInterval (47791662554 / 1000000000000) (47791662586 / 1000000000000))) = true
  rfl'

theorem compactCertificate345_states : ∀ j,
    BesselStateValid (compactCertificate345.point j) (compactCertificate345.state j) :=
  compactCertificate345.statesValid_of_checks3 compactCertificate345_stateChecks0
    compactCertificate345_stateChecks1 compactCertificate345_stateChecks2
    compactCertificate345_stateChecks3 compactCertificate345_stateChecks4
    compactCertificate345_stateChecks5 compactCertificate345_stateChecks6
    compactCertificate345_stateChecks7 compactCertificate345_stateChecks8

theorem compactCertificate345_chunkChecks0_0 :
    compactCertificate345.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (867 / 4) 0 (IntervalRat.scale (867 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-37529303535 / 1000000000000) (-37529303534 / 1000000000000), orderedInterval (-39011600771 / 1000000000000) (-39011600770 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1277256551830167 / 8000000000000) 0 (IntervalRat.scale (867 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-13808576008 / 1000000000000) (-13808576007 / 1000000000000), orderedInterval (-61574616990 / 1000000000000) (-61574616989 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (413038525969911 / 1600000000000) 0 (IntervalRat.scale (867 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (48147696315 / 1000000000000) (48147696318 / 1000000000000), orderedInterval (12067698524 / 1000000000000) (12067698527 / 1000000000000)))) (orderedInterval (-12178609572 / 1000000000000) (-12178609556 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (372700276300869 / 8000000000000) 0 (IntervalRat.scale (867 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-28507660205 / 1000000000000) (-28507660204 / 1000000000000), orderedInterval (-113065282056 / 1000000000000) (-113065282055 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (1001125366774593 / 8000000000000) 0 (IntervalRat.scale (867 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (18430158186 / 1000000000000) (18430158187 / 1000000000000), orderedInterval (68829176310 / 1000000000000) (68829176311 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2718250117411581 / 8000000000000) 0 (IntervalRat.scale (867 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (41396412939 / 1000000000000) (41396412941 / 1000000000000), orderedInterval (12586288281 / 1000000000000) (12586288284 / 1000000000000)))) (orderedInterval (-1960650992 / 1000000000000) (-1960650965 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (2002250733550053 / 8000000000000) 0 (IntervalRat.scale (867 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-13022766336 / 1000000000000) (-13022766228 / 1000000000000), orderedInterval (48750019882 / 1000000000000) (48750019990 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3430890759208569 / 8000000000000) 0 (IntervalRat.scale (867 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (26311541312 / 1000000000000) (26311553020 / 1000000000000), orderedInterval (-28175743425 / 1000000000000) (-28175731717 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2527178604849771 / 8000000000000) 0 (IntervalRat.scale (867 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (26029960153 / 1000000000000) (26029965567 / 1000000000000), orderedInterval (-36616005225 / 1000000000000) (-36615999811 / 1000000000000)))) (orderedInterval (-182460794 / 1000000000000) (-182460289 / 1000000000000))) = true
  rfl'

theorem compactCertificate345_chunkChecks0_1 :
    compactCertificate345.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3877341872984133 / 8000000000000) 0 (IntervalRat.scale (867 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (36135620997 / 1000000000000) (36135622213 / 1000000000000), orderedInterval (-2818307373 / 1000000000000) (-2818306157 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2238584374107357 / 8000000000000) 0 (IntervalRat.scale (867 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-40296617588 / 1000000000000) (-40296617587 / 1000000000000), orderedInterval (-25447810314 / 1000000000000) (-25447810313 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3972407255256513 / 8000000000000) 0 (IntervalRat.scale (867 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (29422484863 / 1000000000000) (29422484864 / 1000000000000), orderedInterval (20376273124 / 1000000000000) (20376273125 / 1000000000000)))) (orderedInterval (-5223931991 / 1000000000000) (-5223931688 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3711538144976997 / 8000000000000) 0 (IntervalRat.scale (867 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-8384252253 / 1000000000000) (-8384252240 / 1000000000000), orderedInterval (36090902950 / 1000000000000) (36090902963 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2648728751683701 / 8000000000000) 0 (IntervalRat.scale (867 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-39708657104 / 1000000000000) (-39708633640 / 1000000000000), orderedInterval (18661444811 / 1000000000000) (18661468275 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (3003376100323779 / 8000000000000) 0 (IntervalRat.scale (867 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-29078687954 / 1000000000000) (-29078667206 / 1000000000000), orderedInterval (29196475904 / 1000000000000) (29196496651 / 1000000000000)))) (orderedInterval (-3456448002 / 1000000000000) (-3456445651 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2503901874751251 / 8000000000000) 0 (IntervalRat.scale (867 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-17001725956 / 1000000000000) (-17001725579 / 1000000000000), orderedInterval (41799781179 / 1000000000000) (41799781556 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2212273242068271 / 8000000000000) 0 (IntervalRat.scale (867 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (36328755073 / 1000000000000) (36328755074 / 1000000000000), orderedInterval (31276920362 / 1000000000000) (31276920363 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (641203013042829 / 1600000000000) 0 (IntervalRat.scale (867 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-22071657382 / 1000000000000) (-22071654959 / 1000000000000), orderedInterval (33214971892 / 1000000000000) (33214974314 / 1000000000000)))) (orderedInterval (-2840425876 / 1000000000000) (-2840425788 / 1000000000000))) = true
  rfl'

theorem compactCertificate345_chunkChecks0_2 :
    compactCertificate345.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1773601278742263 / 8000000000000) 0 (IntervalRat.scale (867 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (28830581354 / 1000000000000) (28830586609 / 1000000000000), orderedInterval (-45235096987 / 1000000000000) (-45235091731 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1503501446086143 / 8000000000000) 0 (IntervalRat.scale (867 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (13090267820 / 1000000000000) (13090267821 / 1000000000000), orderedInterval (56675437083 / 1000000000000) (56675437084 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (940821395150229 / 8000000000000) 0 (IntervalRat.scale (867 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-61651881723 / 1000000000000) (-61651850308 / 1000000000000), orderedInterval (40416025310 / 1000000000000) (40416056725 / 1000000000000)))) (orderedInterval (-7357795225 / 1000000000000) (-7357793307 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (505976875342443 / 8000000000000) 0 (IntervalRat.scale (867 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (93459505681 / 1000000000000) (93459505682 / 1000000000000), orderedInterval (35739747403 / 1000000000000) (35739747404 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1373825643076329 / 8000000000000) 0 (IntervalRat.scale (867 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (16517048555 / 1000000000000) (16517048777 / 1000000000000), orderedInterval (-58651300775 / 1000000000000) (-58651300552 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1875841463653833 / 8000000000000) 0 (IntervalRat.scale (867 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (18082222573 / 1000000000000) (18082222989 / 1000000000000), orderedInterval (-48906377970 / 1000000000000) (-48906377555 / 1000000000000)))) (orderedInterval (-3486261864 / 1000000000000) (-3486261800 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (793178604849771 / 8000000000000) 0 (IntervalRat.scale (867 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-45212028342 / 1000000000000) (-45212014908 / 1000000000000), orderedInterval (66385759033 / 1000000000000) (66385772467 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3224226992754891 / 8000000000000) 0 (IntervalRat.scale (867 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (39463884208 / 1000000000000) (39463885433 / 1000000000000), orderedInterval (-4759699128 / 1000000000000) (-4759697903 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2153634207379269 / 8000000000000) 0 (IntervalRat.scale (867 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-9077024024 / 1000000000000) (-9077023992 / 1000000000000), orderedInterval (47791662554 / 1000000000000) (47791662586 / 1000000000000)))) (orderedInterval (-1781892881 / 1000000000000) (-1781892634 / 1000000000000))) = true
  rfl'

theorem compactCertificate345_chunkChecks0 :
    compactCertificate345.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate345.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate345_chunkChecks0_0
    compactCertificate345_chunkChecks0_1 compactCertificate345_chunkChecks0_2

theorem compactCertificate345_chunkChecks1_0 :
    compactCertificate345.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (867 / 4) 1 (IntervalRat.scale (867 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-37529303535 / 1000000000000) (-37529303534 / 1000000000000), orderedInterval (-39011600771 / 1000000000000) (-39011600770 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1277256551830167 / 8000000000000) 1 (IntervalRat.scale (867 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-13808576008 / 1000000000000) (-13808576007 / 1000000000000), orderedInterval (-61574616990 / 1000000000000) (-61574616989 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (413038525969911 / 1600000000000) 1 (IntervalRat.scale (867 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (48147696315 / 1000000000000) (48147696318 / 1000000000000), orderedInterval (12067698524 / 1000000000000) (12067698527 / 1000000000000)))) (orderedInterval (-15042057239 / 1000000000000) (-15042057220 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (372700276300869 / 8000000000000) 1 (IntervalRat.scale (867 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-28507660205 / 1000000000000) (-28507660204 / 1000000000000), orderedInterval (-113065282056 / 1000000000000) (-113065282055 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (1001125366774593 / 8000000000000) 1 (IntervalRat.scale (867 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (18430158186 / 1000000000000) (18430158187 / 1000000000000), orderedInterval (68829176310 / 1000000000000) (68829176311 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2718250117411581 / 8000000000000) 1 (IntervalRat.scale (867 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (41396412939 / 1000000000000) (41396412941 / 1000000000000), orderedInterval (12586288281 / 1000000000000) (12586288284 / 1000000000000)))) (orderedInterval (311947912 / 1000000000000) (311947943 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (2002250733550053 / 8000000000000) 1 (IntervalRat.scale (867 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-13022766336 / 1000000000000) (-13022766228 / 1000000000000), orderedInterval (48750019882 / 1000000000000) (48750019990 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3430890759208569 / 8000000000000) 1 (IntervalRat.scale (867 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (26311541312 / 1000000000000) (26311553020 / 1000000000000), orderedInterval (-28175743425 / 1000000000000) (-28175731717 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2527178604849771 / 8000000000000) 1 (IntervalRat.scale (867 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (26029960153 / 1000000000000) (26029965567 / 1000000000000), orderedInterval (-36616005225 / 1000000000000) (-36615999811 / 1000000000000)))) (orderedInterval (429775448 / 1000000000000) (429776375 / 1000000000000))) = true
  rfl'

theorem compactCertificate345_chunkChecks1_1 :
    compactCertificate345.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3877341872984133 / 8000000000000) 1 (IntervalRat.scale (867 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (36135620997 / 1000000000000) (36135622213 / 1000000000000), orderedInterval (-2818307373 / 1000000000000) (-2818306157 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2238584374107357 / 8000000000000) 1 (IntervalRat.scale (867 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-40296617588 / 1000000000000) (-40296617587 / 1000000000000), orderedInterval (-25447810314 / 1000000000000) (-25447810313 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3972407255256513 / 8000000000000) 1 (IntervalRat.scale (867 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (29422484863 / 1000000000000) (29422484864 / 1000000000000), orderedInterval (20376273124 / 1000000000000) (20376273125 / 1000000000000)))) (orderedInterval (5321455464 / 1000000000000) (5321456126 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3711538144976997 / 8000000000000) 1 (IntervalRat.scale (867 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-8384252253 / 1000000000000) (-8384252240 / 1000000000000), orderedInterval (36090902950 / 1000000000000) (36090902963 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2648728751683701 / 8000000000000) 1 (IntervalRat.scale (867 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-39708657104 / 1000000000000) (-39708633640 / 1000000000000), orderedInterval (18661444811 / 1000000000000) (18661468275 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (3003376100323779 / 8000000000000) 1 (IntervalRat.scale (867 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-29078687954 / 1000000000000) (-29078667206 / 1000000000000), orderedInterval (29196475904 / 1000000000000) (29196496651 / 1000000000000)))) (orderedInterval (1045066316 / 1000000000000) (1045069930 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2503901874751251 / 8000000000000) 1 (IntervalRat.scale (867 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-17001725956 / 1000000000000) (-17001725579 / 1000000000000), orderedInterval (41799781179 / 1000000000000) (41799781556 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2212273242068271 / 8000000000000) 1 (IntervalRat.scale (867 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (36328755073 / 1000000000000) (36328755074 / 1000000000000), orderedInterval (31276920362 / 1000000000000) (31276920363 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (641203013042829 / 1600000000000) 1 (IntervalRat.scale (867 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-22071657382 / 1000000000000) (-22071654959 / 1000000000000), orderedInterval (33214971892 / 1000000000000) (33214974314 / 1000000000000)))) (orderedInterval (-14173311 / 1000000000000) (-14173159 / 1000000000000))) = true
  rfl'

theorem compactCertificate345_chunkChecks1_2 :
    compactCertificate345.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1773601278742263 / 8000000000000) 1 (IntervalRat.scale (867 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (28830581354 / 1000000000000) (28830586609 / 1000000000000), orderedInterval (-45235096987 / 1000000000000) (-45235091731 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1503501446086143 / 8000000000000) 1 (IntervalRat.scale (867 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (13090267820 / 1000000000000) (13090267821 / 1000000000000), orderedInterval (56675437083 / 1000000000000) (56675437084 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (940821395150229 / 8000000000000) 1 (IntervalRat.scale (867 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-61651881723 / 1000000000000) (-61651850308 / 1000000000000), orderedInterval (40416025310 / 1000000000000) (40416056725 / 1000000000000)))) (orderedInterval (5330409780 / 1000000000000) (5330411246 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (505976875342443 / 8000000000000) 1 (IntervalRat.scale (867 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (93459505681 / 1000000000000) (93459505682 / 1000000000000), orderedInterval (35739747403 / 1000000000000) (35739747404 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1373825643076329 / 8000000000000) 1 (IntervalRat.scale (867 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (16517048555 / 1000000000000) (16517048777 / 1000000000000), orderedInterval (-58651300775 / 1000000000000) (-58651300552 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1875841463653833 / 8000000000000) 1 (IntervalRat.scale (867 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (18082222573 / 1000000000000) (18082222989 / 1000000000000), orderedInterval (-48906377970 / 1000000000000) (-48906377555 / 1000000000000)))) (orderedInterval (4916386753 / 1000000000000) (4916386816 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (793178604849771 / 8000000000000) 1 (IntervalRat.scale (867 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-45212028342 / 1000000000000) (-45212014908 / 1000000000000), orderedInterval (66385759033 / 1000000000000) (66385772467 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3224226992754891 / 8000000000000) 1 (IntervalRat.scale (867 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (39463884208 / 1000000000000) (39463885433 / 1000000000000), orderedInterval (-4759699128 / 1000000000000) (-4759697903 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2153634207379269 / 8000000000000) 1 (IntervalRat.scale (867 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-9077024024 / 1000000000000) (-9077023992 / 1000000000000), orderedInterval (47791662554 / 1000000000000) (47791662586 / 1000000000000)))) (orderedInterval (-10233539075 / 1000000000000) (-10233538761 / 1000000000000))) = true
  rfl'

theorem compactCertificate345_chunkChecks1 :
    compactCertificate345.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate345.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate345_chunkChecks1_0
    compactCertificate345_chunkChecks1_1 compactCertificate345_chunkChecks1_2

theorem compactCertificate345_chunkChecks2_0 :
    compactCertificate345.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (867 / 4) 2 (IntervalRat.scale (867 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-37529303535 / 1000000000000) (-37529303534 / 1000000000000), orderedInterval (-39011600771 / 1000000000000) (-39011600770 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1277256551830167 / 8000000000000) 2 (IntervalRat.scale (867 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-13808576008 / 1000000000000) (-13808576007 / 1000000000000), orderedInterval (-61574616990 / 1000000000000) (-61574616989 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (413038525969911 / 1600000000000) 2 (IntervalRat.scale (867 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (48147696315 / 1000000000000) (48147696318 / 1000000000000), orderedInterval (12067698524 / 1000000000000) (12067698527 / 1000000000000)))) (orderedInterval (11006796114 / 1000000000000) (11006796135 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (372700276300869 / 8000000000000) 2 (IntervalRat.scale (867 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-28507660205 / 1000000000000) (-28507660204 / 1000000000000), orderedInterval (-113065282056 / 1000000000000) (-113065282055 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (1001125366774593 / 8000000000000) 2 (IntervalRat.scale (867 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (18430158186 / 1000000000000) (18430158187 / 1000000000000), orderedInterval (68829176310 / 1000000000000) (68829176311 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2718250117411581 / 8000000000000) 2 (IntervalRat.scale (867 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (41396412939 / 1000000000000) (41396412941 / 1000000000000), orderedInterval (12586288281 / 1000000000000) (12586288284 / 1000000000000)))) (orderedInterval (6991821042 / 1000000000000) (6991821084 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (2002250733550053 / 8000000000000) 2 (IntervalRat.scale (867 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-13022766336 / 1000000000000) (-13022766228 / 1000000000000), orderedInterval (48750019882 / 1000000000000) (48750019990 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3430890759208569 / 8000000000000) 2 (IntervalRat.scale (867 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (26311541312 / 1000000000000) (26311553020 / 1000000000000), orderedInterval (-28175743425 / 1000000000000) (-28175731717 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2527178604849771 / 8000000000000) 2 (IntervalRat.scale (867 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (26029960153 / 1000000000000) (26029965567 / 1000000000000), orderedInterval (-36616005225 / 1000000000000) (-36615999811 / 1000000000000)))) (orderedInterval (1838877317 / 1000000000000) (1838879051 / 1000000000000))) = true
  rfl'

theorem compactCertificate345_chunkChecks2_1 :
    compactCertificate345.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3877341872984133 / 8000000000000) 2 (IntervalRat.scale (867 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (36135620997 / 1000000000000) (36135622213 / 1000000000000), orderedInterval (-2818307373 / 1000000000000) (-2818306157 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2238584374107357 / 8000000000000) 2 (IntervalRat.scale (867 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-40296617588 / 1000000000000) (-40296617587 / 1000000000000), orderedInterval (-25447810314 / 1000000000000) (-25447810313 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3972407255256513 / 8000000000000) 2 (IntervalRat.scale (867 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (29422484863 / 1000000000000) (29422484864 / 1000000000000), orderedInterval (20376273124 / 1000000000000) (20376273125 / 1000000000000)))) (orderedInterval (15104883960 / 1000000000000) (15104885426 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3711538144976997 / 8000000000000) 2 (IntervalRat.scale (867 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-8384252253 / 1000000000000) (-8384252240 / 1000000000000), orderedInterval (36090902950 / 1000000000000) (36090902963 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2648728751683701 / 8000000000000) 2 (IntervalRat.scale (867 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-39708657104 / 1000000000000) (-39708633640 / 1000000000000), orderedInterval (18661444811 / 1000000000000) (18661468275 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (3003376100323779 / 8000000000000) 2 (IntervalRat.scale (867 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-29078687954 / 1000000000000) (-29078667206 / 1000000000000), orderedInterval (29196475904 / 1000000000000) (29196496651 / 1000000000000)))) (orderedInterval (7621825705 / 1000000000000) (7621831285 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2503901874751251 / 8000000000000) 2 (IntervalRat.scale (867 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-17001725956 / 1000000000000) (-17001725579 / 1000000000000), orderedInterval (41799781179 / 1000000000000) (41799781556 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2212273242068271 / 8000000000000) 2 (IntervalRat.scale (867 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (36328755073 / 1000000000000) (36328755074 / 1000000000000), orderedInterval (31276920362 / 1000000000000) (31276920363 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (641203013042829 / 1600000000000) 2 (IntervalRat.scale (867 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-22071657382 / 1000000000000) (-22071654959 / 1000000000000), orderedInterval (33214971892 / 1000000000000) (33214974314 / 1000000000000)))) (orderedInterval (5725283614 / 1000000000000) (5725283881 / 1000000000000))) = true
  rfl'

theorem compactCertificate345_chunkChecks2_2 :
    compactCertificate345.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1773601278742263 / 8000000000000) 2 (IntervalRat.scale (867 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (28830581354 / 1000000000000) (28830586609 / 1000000000000), orderedInterval (-45235096987 / 1000000000000) (-45235091731 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1503501446086143 / 8000000000000) 2 (IntervalRat.scale (867 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (13090267820 / 1000000000000) (13090267821 / 1000000000000), orderedInterval (56675437083 / 1000000000000) (56675437084 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (940821395150229 / 8000000000000) 2 (IntervalRat.scale (867 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-61651881723 / 1000000000000) (-61651850308 / 1000000000000), orderedInterval (40416025310 / 1000000000000) (40416056725 / 1000000000000)))) (orderedInterval (5946044789 / 1000000000000) (5946046025 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (505976875342443 / 8000000000000) 2 (IntervalRat.scale (867 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (93459505681 / 1000000000000) (93459505682 / 1000000000000), orderedInterval (35739747403 / 1000000000000) (35739747404 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1373825643076329 / 8000000000000) 2 (IntervalRat.scale (867 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (16517048555 / 1000000000000) (16517048777 / 1000000000000), orderedInterval (-58651300775 / 1000000000000) (-58651300552 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1875841463653833 / 8000000000000) 2 (IntervalRat.scale (867 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (18082222573 / 1000000000000) (18082222989 / 1000000000000), orderedInterval (-48906377970 / 1000000000000) (-48906377555 / 1000000000000)))) (orderedInterval (1981267335 / 1000000000000) (1981267400 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (793178604849771 / 8000000000000) 2 (IntervalRat.scale (867 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-45212028342 / 1000000000000) (-45212014908 / 1000000000000), orderedInterval (66385759033 / 1000000000000) (66385772467 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3224226992754891 / 8000000000000) 2 (IntervalRat.scale (867 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (39463884208 / 1000000000000) (39463885433 / 1000000000000), orderedInterval (-4759699128 / 1000000000000) (-4759697903 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2153634207379269 / 8000000000000) 2 (IntervalRat.scale (867 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-9077024024 / 1000000000000) (-9077023992 / 1000000000000), orderedInterval (47791662554 / 1000000000000) (47791662586 / 1000000000000)))) (orderedInterval (8583844715 / 1000000000000) (8583845212 / 1000000000000))) = true
  rfl'

theorem compactCertificate345_chunkChecks2 :
    compactCertificate345.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate345.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate345_chunkChecks2_0
    compactCertificate345_chunkChecks2_1 compactCertificate345_chunkChecks2_2

theorem compactCertificate345_chunkChecks3_0 :
    compactCertificate345.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (867 / 4) 3 (IntervalRat.scale (867 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-37529303535 / 1000000000000) (-37529303534 / 1000000000000), orderedInterval (-39011600771 / 1000000000000) (-39011600770 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1277256551830167 / 8000000000000) 3 (IntervalRat.scale (867 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-13808576008 / 1000000000000) (-13808576007 / 1000000000000), orderedInterval (-61574616990 / 1000000000000) (-61574616989 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (413038525969911 / 1600000000000) 3 (IntervalRat.scale (867 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (48147696315 / 1000000000000) (48147696318 / 1000000000000), orderedInterval (12067698524 / 1000000000000) (12067698527 / 1000000000000)))) (orderedInterval (14444689365 / 1000000000000) (14444689389 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (372700276300869 / 8000000000000) 3 (IntervalRat.scale (867 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-28507660205 / 1000000000000) (-28507660204 / 1000000000000), orderedInterval (-113065282056 / 1000000000000) (-113065282055 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (1001125366774593 / 8000000000000) 3 (IntervalRat.scale (867 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (18430158186 / 1000000000000) (18430158187 / 1000000000000), orderedInterval (68829176310 / 1000000000000) (68829176311 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2718250117411581 / 8000000000000) 3 (IntervalRat.scale (867 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (41396412939 / 1000000000000) (41396412941 / 1000000000000), orderedInterval (12586288281 / 1000000000000) (12586288284 / 1000000000000)))) (orderedInterval (2918797910 / 1000000000000) (2918797972 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (2002250733550053 / 8000000000000) 3 (IntervalRat.scale (867 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-13022766336 / 1000000000000) (-13022766228 / 1000000000000), orderedInterval (48750019882 / 1000000000000) (48750019990 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3430890759208569 / 8000000000000) 3 (IntervalRat.scale (867 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (26311541312 / 1000000000000) (26311553020 / 1000000000000), orderedInterval (-28175743425 / 1000000000000) (-28175731717 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2527178604849771 / 8000000000000) 3 (IntervalRat.scale (867 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (26029960153 / 1000000000000) (26029965567 / 1000000000000), orderedInterval (-36616005225 / 1000000000000) (-36615999811 / 1000000000000)))) (orderedInterval (-4000584755 / 1000000000000) (-4000581476 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate345_chunkChecks3_1 :
    compactCertificate345.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3877341872984133 / 8000000000000) 3 (IntervalRat.scale (867 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (36135620997 / 1000000000000) (36135622213 / 1000000000000), orderedInterval (-2818307373 / 1000000000000) (-2818306157 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2238584374107357 / 8000000000000) 3 (IntervalRat.scale (867 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-40296617588 / 1000000000000) (-40296617587 / 1000000000000), orderedInterval (-25447810314 / 1000000000000) (-25447810313 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3972407255256513 / 8000000000000) 3 (IntervalRat.scale (867 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (29422484863 / 1000000000000) (29422484864 / 1000000000000), orderedInterval (20376273124 / 1000000000000) (20376273125 / 1000000000000)))) (orderedInterval (-36437567485 / 1000000000000) (-36437564226 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3711538144976997 / 8000000000000) 3 (IntervalRat.scale (867 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-8384252253 / 1000000000000) (-8384252240 / 1000000000000), orderedInterval (36090902950 / 1000000000000) (36090902963 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2648728751683701 / 8000000000000) 3 (IntervalRat.scale (867 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-39708657104 / 1000000000000) (-39708633640 / 1000000000000), orderedInterval (18661444811 / 1000000000000) (18661468275 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (3003376100323779 / 8000000000000) 3 (IntervalRat.scale (867 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-29078687954 / 1000000000000) (-29078667206 / 1000000000000), orderedInterval (29196475904 / 1000000000000) (29196496651 / 1000000000000)))) (orderedInterval (832323643 / 1000000000000) (832332243 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2503901874751251 / 8000000000000) 3 (IntervalRat.scale (867 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-17001725956 / 1000000000000) (-17001725579 / 1000000000000), orderedInterval (41799781179 / 1000000000000) (41799781556 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2212273242068271 / 8000000000000) 3 (IntervalRat.scale (867 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (36328755073 / 1000000000000) (36328755074 / 1000000000000), orderedInterval (31276920362 / 1000000000000) (31276920363 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (641203013042829 / 1600000000000) 3 (IntervalRat.scale (867 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-22071657382 / 1000000000000) (-22071654959 / 1000000000000), orderedInterval (33214971892 / 1000000000000) (33214974314 / 1000000000000)))) (orderedInterval (-3137929018 / 1000000000000) (-3137928543 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate345_chunkChecks3_2 :
    compactCertificate345.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1773601278742263 / 8000000000000) 3 (IntervalRat.scale (867 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (28830581354 / 1000000000000) (28830586609 / 1000000000000), orderedInterval (-45235096987 / 1000000000000) (-45235091731 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1503501446086143 / 8000000000000) 3 (IntervalRat.scale (867 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (13090267820 / 1000000000000) (13090267821 / 1000000000000), orderedInterval (56675437083 / 1000000000000) (56675437084 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (940821395150229 / 8000000000000) 3 (IntervalRat.scale (867 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-61651881723 / 1000000000000) (-61651850308 / 1000000000000), orderedInterval (40416025310 / 1000000000000) (40416056725 / 1000000000000)))) (orderedInterval (-5886077534 / 1000000000000) (-5886076419 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (505976875342443 / 8000000000000) 3 (IntervalRat.scale (867 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (93459505681 / 1000000000000) (93459505682 / 1000000000000), orderedInterval (35739747403 / 1000000000000) (35739747404 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1373825643076329 / 8000000000000) 3 (IntervalRat.scale (867 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (16517048555 / 1000000000000) (16517048777 / 1000000000000), orderedInterval (-58651300775 / 1000000000000) (-58651300552 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1875841463653833 / 8000000000000) 3 (IntervalRat.scale (867 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (18082222573 / 1000000000000) (18082222989 / 1000000000000), orderedInterval (-48906377970 / 1000000000000) (-48906377555 / 1000000000000)))) (orderedInterval (-5399611411 / 1000000000000) (-5399611344 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (793178604849771 / 8000000000000) 3 (IntervalRat.scale (867 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-45212028342 / 1000000000000) (-45212014908 / 1000000000000), orderedInterval (66385759033 / 1000000000000) (66385772467 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3224226992754891 / 8000000000000) 3 (IntervalRat.scale (867 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (39463884208 / 1000000000000) (39463885433 / 1000000000000), orderedInterval (-4759699128 / 1000000000000) (-4759697903 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2153634207379269 / 8000000000000) 3 (IntervalRat.scale (867 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-9077024024 / 1000000000000) (-9077023992 / 1000000000000), orderedInterval (47791662554 / 1000000000000) (47791662586 / 1000000000000)))) (orderedInterval (14610726867 / 1000000000000) (14610727721 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate345_chunkChecks3 :
    compactCertificate345.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate345.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate345_chunkChecks3_0
    compactCertificate345_chunkChecks3_1 compactCertificate345_chunkChecks3_2

theorem compactCertificate345_chunkChecks4_0 :
    compactCertificate345.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (867 / 4) 4 (IntervalRat.scale (867 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-37529303535 / 1000000000000) (-37529303534 / 1000000000000), orderedInterval (-39011600771 / 1000000000000) (-39011600770 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1277256551830167 / 8000000000000) 4 (IntervalRat.scale (867 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-13808576008 / 1000000000000) (-13808576007 / 1000000000000), orderedInterval (-61574616990 / 1000000000000) (-61574616989 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (413038525969911 / 1600000000000) 4 (IntervalRat.scale (867 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (48147696315 / 1000000000000) (48147696318 / 1000000000000), orderedInterval (12067698524 / 1000000000000) (12067698527 / 1000000000000)))) (orderedInterval (-9361366742 / 1000000000000) (-9361366714 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (372700276300869 / 8000000000000) 4 (IntervalRat.scale (867 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-28507660205 / 1000000000000) (-28507660204 / 1000000000000), orderedInterval (-113065282056 / 1000000000000) (-113065282055 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (1001125366774593 / 8000000000000) 4 (IntervalRat.scale (867 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (18430158186 / 1000000000000) (18430158187 / 1000000000000), orderedInterval (68829176310 / 1000000000000) (68829176311 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2718250117411581 / 8000000000000) 4 (IntervalRat.scale (867 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (41396412939 / 1000000000000) (41396412941 / 1000000000000), orderedInterval (12586288281 / 1000000000000) (12586288284 / 1000000000000)))) (orderedInterval (-17723110108 / 1000000000000) (-17723110012 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (2002250733550053 / 8000000000000) 4 (IntervalRat.scale (867 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-13022766336 / 1000000000000) (-13022766228 / 1000000000000), orderedInterval (48750019882 / 1000000000000) (48750019990 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3430890759208569 / 8000000000000) 4 (IntervalRat.scale (867 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (26311541312 / 1000000000000) (26311553020 / 1000000000000), orderedInterval (-28175743425 / 1000000000000) (-28175731717 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2527178604849771 / 8000000000000) 4 (IntervalRat.scale (867 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (26029960153 / 1000000000000) (26029965567 / 1000000000000), orderedInterval (-36616005225 / 1000000000000) (-36615999811 / 1000000000000)))) (orderedInterval (-9562659808 / 1000000000000) (-9562653527 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate345_chunkChecks4_1 :
    compactCertificate345.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3877341872984133 / 8000000000000) 4 (IntervalRat.scale (867 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (36135620997 / 1000000000000) (36135622213 / 1000000000000), orderedInterval (-2818307373 / 1000000000000) (-2818306157 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2238584374107357 / 8000000000000) 4 (IntervalRat.scale (867 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-40296617588 / 1000000000000) (-40296617587 / 1000000000000), orderedInterval (-25447810314 / 1000000000000) (-25447810313 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3972407255256513 / 8000000000000) 4 (IntervalRat.scale (867 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (29422484863 / 1000000000000) (29422484864 / 1000000000000), orderedInterval (20376273124 / 1000000000000) (20376273125 / 1000000000000)))) (orderedInterval (-53275756796 / 1000000000000) (-53275749510 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3711538144976997 / 8000000000000) 4 (IntervalRat.scale (867 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-8384252253 / 1000000000000) (-8384252240 / 1000000000000), orderedInterval (36090902950 / 1000000000000) (36090902963 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2648728751683701 / 8000000000000) 4 (IntervalRat.scale (867 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-39708657104 / 1000000000000) (-39708633640 / 1000000000000), orderedInterval (18661444811 / 1000000000000) (18661468275 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (3003376100323779 / 8000000000000) 4 (IntervalRat.scale (867 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-29078687954 / 1000000000000) (-29078667206 / 1000000000000), orderedInterval (29196475904 / 1000000000000) (29196496651 / 1000000000000)))) (orderedInterval (-15949688976 / 1000000000000) (-15949675664 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2503901874751251 / 8000000000000) 4 (IntervalRat.scale (867 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-17001725956 / 1000000000000) (-17001725579 / 1000000000000), orderedInterval (41799781179 / 1000000000000) (41799781556 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2212273242068271 / 8000000000000) 4 (IntervalRat.scale (867 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (36328755073 / 1000000000000) (36328755074 / 1000000000000), orderedInterval (31276920362 / 1000000000000) (31276920363 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (641203013042829 / 1600000000000) 4 (IntervalRat.scale (867 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-22071657382 / 1000000000000) (-22071654959 / 1000000000000), orderedInterval (33214971892 / 1000000000000) (33214974314 / 1000000000000)))) (orderedInterval (-12936721225 / 1000000000000) (-12936720368 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate345_chunkChecks4_2 :
    compactCertificate345.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1773601278742263 / 8000000000000) 4 (IntervalRat.scale (867 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (28830581354 / 1000000000000) (28830586609 / 1000000000000), orderedInterval (-45235096987 / 1000000000000) (-45235091731 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1503501446086143 / 8000000000000) 4 (IntervalRat.scale (867 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (13090267820 / 1000000000000) (13090267821 / 1000000000000), orderedInterval (56675437083 / 1000000000000) (56675437084 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (940821395150229 / 8000000000000) 4 (IntervalRat.scale (867 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-61651881723 / 1000000000000) (-61651850308 / 1000000000000), orderedInterval (40416025310 / 1000000000000) (40416056725 / 1000000000000)))) (orderedInterval (-5583835698 / 1000000000000) (-5583834633 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (505976875342443 / 8000000000000) 4 (IntervalRat.scale (867 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (93459505681 / 1000000000000) (93459505682 / 1000000000000), orderedInterval (35739747403 / 1000000000000) (35739747404 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1373825643076329 / 8000000000000) 4 (IntervalRat.scale (867 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (16517048555 / 1000000000000) (16517048777 / 1000000000000), orderedInterval (-58651300775 / 1000000000000) (-58651300552 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1875841463653833 / 8000000000000) 4 (IntervalRat.scale (867 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (18082222573 / 1000000000000) (18082222989 / 1000000000000), orderedInterval (-48906377970 / 1000000000000) (-48906377555 / 1000000000000)))) (orderedInterval (-2008266190 / 1000000000000) (-2008266118 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (793178604849771 / 8000000000000) 4 (IntervalRat.scale (867 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-45212028342 / 1000000000000) (-45212014908 / 1000000000000), orderedInterval (66385759033 / 1000000000000) (66385772467 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3224226992754891 / 8000000000000) 4 (IntervalRat.scale (867 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (39463884208 / 1000000000000) (39463885433 / 1000000000000), orderedInterval (-4759699128 / 1000000000000) (-4759697903 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2153634207379269 / 8000000000000) 4 (IntervalRat.scale (867 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-9077024024 / 1000000000000) (-9077023992 / 1000000000000), orderedInterval (47791662554 / 1000000000000) (47791662586 / 1000000000000)))) (orderedInterval (-34494766326 / 1000000000000) (-34494764801 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate345_chunkChecks4 :
    compactCertificate345.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate345.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate345_chunkChecks4_0
    compactCertificate345_chunkChecks4_1 compactCertificate345_chunkChecks4_2

theorem compactCertificate345_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate345.chunkCheck r b = true :=
  compactCertificate345.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate345_chunkChecks0
    · exact compactCertificate345_chunkChecks1
    · exact compactCertificate345_chunkChecks2
    · exact compactCertificate345_chunkChecks3
    · exact compactCertificate345_chunkChecks4)

theorem compactCertificate345_coefficient0 :
    compactCertificate345.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate345_coefficient1 :
    compactCertificate345.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate345_coefficient2 :
    compactCertificate345.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate345_coefficient3 :
    compactCertificate345.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate345_coefficient4 :
    compactCertificate345.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate345_coefficients : ∀ r : Fin 5,
    compactCertificate345.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate345_coefficient0
  · exact compactCertificate345_coefficient1
  · exact compactCertificate345_coefficient2
  · exact compactCertificate345_coefficient3
  · exact compactCertificate345_coefficient4

theorem compactCertificate345_lower : (1 : ℚ) ≤ compactCertificate345.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate345, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate345_proves {t : ℝ} (ht : t ∈ compactCertificate345.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate345.proves compactCertificate345_states compactCertificate345_chunks
    compactCertificate345_coefficients compactCertificate345_lower ht

end Erdos232
