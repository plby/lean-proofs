/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate561 : CompactCertificate where
  left := 432
  right := 433
  center := 865 / 2
  grid := fun i =>
    match i.val with
    | 0 => 138
    | 1 => 101
    | 2 => 164
    | 3 => 30
    | 4 => 80
    | 5 => 216
    | 6 => 159
    | 7 => 273
    | 8 => 201
    | 9 => 308
    | 10 => 178
    | 11 => 316
    | 12 => 295
    | 13 => 210
    | 14 => 239
    | 15 => 199
    | 16 => 176
    | 17 => 255
    | 18 => 141
    | 19 => 119
    | 20 => 75
    | 21 => 40
    | 22 => 109
    | 23 => 149
    | 24 => 63
    | 25 => 256
    | _ => 171
  point := fun i =>
    match i.val with
    | 0 => 865 / 2
    | 1 => 254862033986873 / 800000000000
    | 2 => 82417145320409 / 160000000000
    | 3 => 74368105882411 / 800000000000
    | 4 => 199763193139567 / 800000000000
    | 5 => 542395928849139 / 800000000000
    | 6 => 399526386279307 / 800000000000
    | 7 => 684595272598711 / 800000000000
    | 8 => 504269779283749 / 800000000000
    | 9 => 773679520214827 / 800000000000
    | 10 => 446684079262483 / 800000000000
    | 11 => 792648737208047 / 800000000000
    | 12 => 740595269989643 / 800000000000
    | 13 => 528523730151419 / 800000000000
    | 14 => 599289579418701 / 800000000000
    | 15 => 499625172239869 / 800000000000
    | 16 => 441433991785249 / 800000000000
    | 17 => 127944776535651 / 160000000000
    | 18 => 353901985262297 / 800000000000
    | 19 => 300006632264017 / 800000000000
    | 20 => 187730220716251 / 800000000000
    | 21 => 100961937063717 / 800000000000
    | 22 => 274131299022151 / 800000000000
    | 23 => 374302852609127 / 800000000000
    | 24 => 158269779283749 / 800000000000
    | 25 => 643357865913029 / 800000000000
    | _ => 429733238612011 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-9665664686 / 1000000000000) (-9665664660 / 1000000000000), orderedInterval (37139721336 / 1000000000000) (37139721362 / 1000000000000))
    | 1 => (orderedInterval (-39423716000 / 1000000000000) (-39423680039 / 1000000000000), orderedInterval (21135306007 / 1000000000000) (21135341968 / 1000000000000))
    | 2 => (orderedInterval (21861775497 / 1000000000000) (21861775498 / 1000000000000), orderedInterval (27509864447 / 1000000000000) (27509864448 / 1000000000000))
    | 3 => (orderedInterval (-39935071193 / 1000000000000) (-39935065936 / 1000000000000), orderedInterval (72696184406 / 1000000000000) (72696189662 / 1000000000000))
    | 4 => (orderedInterval (-37549113573 / 1000000000000) (-37549053192 / 1000000000000), orderedInterval (33832577018 / 1000000000000) (33832637399 / 1000000000000))
    | 5 => (orderedInterval (5970942112 / 1000000000000) (5970942113 / 1000000000000), orderedInterval (30050918109 / 1000000000000) (30050918110 / 1000000000000))
    | 6 => (orderedInterval (-22447375415 / 1000000000000) (-22447375414 / 1000000000000), orderedInterval (-27741970242 / 1000000000000) (-27741970241 / 1000000000000))
    | 7 => (orderedInterval (24614818626 / 1000000000000) (24614869271 / 1000000000000), orderedInterval (-11763723813 / 1000000000000) (-11763673169 / 1000000000000))
    | 8 => (orderedInterval (10529255256 / 1000000000000) (10529255275 / 1000000000000), orderedInterval (-29993381605 / 1000000000000) (-29993381585 / 1000000000000))
    | 9 => (orderedInterval (6945618179 / 1000000000000) (6945618180 / 1000000000000), orderedInterval (24695315095 / 1000000000000) (24695315096 / 1000000000000))
    | 10 => (orderedInterval (-2133255211 / 1000000000000) (-2133255210 / 1000000000000), orderedInterval (33700867936 / 1000000000000) (33700867937 / 1000000000000))
    | 11 => (orderedInterval (-23106525814 / 1000000000000) (-23106492510 / 1000000000000), orderedInterval (10433406320 / 1000000000000) (10433439623 / 1000000000000))
    | 12 => (orderedInterval (6245732353 / 1000000000000) (6245732354 / 1000000000000), orderedInterval (-25472478597 / 1000000000000) (-25472478596 / 1000000000000))
    | 13 => (orderedInterval (30761365644 / 1000000000000) (30761371777 / 1000000000000), orderedInterval (-4189518462 / 1000000000000) (-4189512329 / 1000000000000))
    | 14 => (orderedInterval (23600815589 / 1000000000000) (23600831180 / 1000000000000), orderedInterval (-17128143507 / 1000000000000) (-17128127917 / 1000000000000))
    | 15 => (orderedInterval (-4446555008 / 1000000000000) (-4446555007 / 1000000000000), orderedInterval (-31612642646 / 1000000000000) (-31612642645 / 1000000000000))
    | 16 => (orderedInterval (-11412103140 / 1000000000000) (-11412103102 / 1000000000000), orderedInterval (32002444209 / 1000000000000) (32002444247 / 1000000000000))
    | 17 => (orderedInterval (17433563744 / 1000000000000) (17433564315 / 1000000000000), orderedInterval (-22196235510 / 1000000000000) (-22196234939 / 1000000000000))
    | 18 => (orderedInterval (-7463433790 / 1000000000000) (-7463433789 / 1000000000000), orderedInterval (-37185451099 / 1000000000000) (-37185451098 / 1000000000000))
    | 19 => (orderedInterval (-38368492151 / 1000000000000) (-38368476521 / 1000000000000), orderedInterval (15066923077 / 1000000000000) (15066938707 / 1000000000000))
    | 20 => (orderedInterval (8904740022 / 1000000000000) (8904740055 / 1000000000000), orderedInterval (-51337826977 / 1000000000000) (-51337826944 / 1000000000000))
    | 21 => (orderedInterval (68856634036 / 1000000000000) (68856634037 / 1000000000000), orderedInterval (17138779140 / 1000000000000) (17138779141 / 1000000000000))
    | 22 => (orderedInterval (-36627675026 / 1000000000000) (-36627675025 / 1000000000000), orderedInterval (-22668045225 / 1000000000000) (-22668045224 / 1000000000000))
    | 23 => (orderedInterval (-19793212734 / 1000000000000) (-19793212733 / 1000000000000), orderedInterval (-31105697654 / 1000000000000) (-31105697653 / 1000000000000))
    | 24 => (orderedInterval (-36615841958 / 1000000000000) (-36615841957 / 1000000000000), orderedInterval (-43233879932 / 1000000000000) (-43233879931 / 1000000000000))
    | 25 => (orderedInterval (18864471738 / 1000000000000) (18864471739 / 1000000000000), orderedInterval (20862970395 / 1000000000000) (20862970396 / 1000000000000))
    | _ => (orderedInterval (-23196956389 / 1000000000000) (-23196956388 / 1000000000000), orderedInterval (-25415494655 / 1000000000000) (-25415494654 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-2915609773 / 1000000000000) (-2915609397 / 1000000000000)
      | 1 => orderedInterval (-1362188703 / 1000000000000) (-1362186389 / 1000000000000)
      | 2 => orderedInterval (-504749739 / 1000000000000) (-504748152 / 1000000000000)
      | 3 => orderedInterval (-4676938020 / 1000000000000) (-4676933114 / 1000000000000)
      | 4 => orderedInterval (2676694328 / 1000000000000) (2676695039 / 1000000000000)
      | 5 => orderedInterval (1048097462 / 1000000000000) (1048097520 / 1000000000000)
      | 6 => orderedInterval (3654896907 / 1000000000000) (3654897902 / 1000000000000)
      | 7 => orderedInterval (1076450637 / 1000000000000) (1076450689 / 1000000000000)
      | _ => orderedInterval (2596030477 / 1000000000000) (2596030597 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (16788592700 / 1000000000000) (16788592992 / 1000000000000)
      | 1 => orderedInterval (-2805245141 / 1000000000000) (-2805243797 / 1000000000000)
      | 2 => orderedInterval (-338548630 / 1000000000000) (-338545496 / 1000000000000)
      | 3 => orderedInterval (-3190658341 / 1000000000000) (-3190647140 / 1000000000000)
      | 4 => orderedInterval (529266949 / 1000000000000) (529268055 / 1000000000000)
      | 5 => orderedInterval (-3914424960 / 1000000000000) (-3914424870 / 1000000000000)
      | 6 => orderedInterval (4435221249 / 1000000000000) (4435222118 / 1000000000000)
      | 7 => orderedInterval (2894011207 / 1000000000000) (2894011254 / 1000000000000)
      | _ => orderedInterval (2645611959 / 1000000000000) (2645612128 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (2171899034 / 1000000000000) (2171899266 / 1000000000000)
      | 1 => orderedInterval (1486573235 / 1000000000000) (1486574058 / 1000000000000)
      | 2 => orderedInterval (2432495390 / 1000000000000) (2432501589 / 1000000000000)
      | 3 => orderedInterval (23680414925 / 1000000000000) (23680440559 / 1000000000000)
      | 4 => orderedInterval (-5913729217 / 1000000000000) (-5913727486 / 1000000000000)
      | 5 => orderedInterval (-2472807908 / 1000000000000) (-2472807765 / 1000000000000)
      | 6 => orderedInterval (-2976749979 / 1000000000000) (-2976749216 / 1000000000000)
      | 7 => orderedInterval (-2195296394 / 1000000000000) (-2195296348 / 1000000000000)
      | _ => orderedInterval (-1364540174 / 1000000000000) (-1364539925 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-17531753737 / 1000000000000) (-17531753547 / 1000000000000)
      | 1 => orderedInterval (7996367360 / 1000000000000) (7996367909 / 1000000000000)
      | 2 => orderedInterval (-572138397 / 1000000000000) (-572126145 / 1000000000000)
      | 3 => orderedInterval (25800368111 / 1000000000000) (25800426759 / 1000000000000)
      | 4 => orderedInterval (-3534261115 / 1000000000000) (-3534258400 / 1000000000000)
      | 5 => orderedInterval (8500061734 / 1000000000000) (8500061968 / 1000000000000)
      | 6 => orderedInterval (-5532641726 / 1000000000000) (-5532641054 / 1000000000000)
      | 7 => orderedInterval (-3260883839 / 1000000000000) (-3260883791 / 1000000000000)
      | _ => orderedInterval (1809915202 / 1000000000000) (1809915586 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-1276942460 / 1000000000000) (-1276942297 / 1000000000000)
      | 1 => orderedInterval (-2751741487 / 1000000000000) (-2751741051 / 1000000000000)
      | 2 => orderedInterval (-10485109512 / 1000000000000) (-10485085261 / 1000000000000)
      | 3 => orderedInterval (-121884879246 / 1000000000000) (-121884744873 / 1000000000000)
      | 4 => orderedInterval (12411899022 / 1000000000000) (12411903309 / 1000000000000)
      | 5 => orderedInterval (6683993673 / 1000000000000) (6683994068 / 1000000000000)
      | 6 => orderedInterval (2584311737 / 1000000000000) (2584312332 / 1000000000000)
      | 7 => orderedInterval (2410836065 / 1000000000000) (2410836115 / 1000000000000)
      | _ => orderedInterval (-8017731483 / 1000000000000) (-8017730866 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (1592683576 / 1000000000000) (1592694695 / 1000000000000)
    | 1 => orderedInterval (17043826992 / 1000000000000) (17043845244 / 1000000000000)
    | 2 => orderedInterval (14848258912 / 1000000000000) (14848294732 / 1000000000000)
    | 3 => orderedInterval (13675033593 / 1000000000000) (13675109285 / 1000000000000)
    | _ => orderedInterval (-120325363691 / 1000000000000) (-120325198524 / 1000000000000)

theorem compactCertificate561_stateChecks0 :
    compactCertificate561.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 138 12 (865 / 2)) (orderedInterval (-9665664686 / 1000000000000) (-9665664660 / 1000000000000), orderedInterval (37139721336 / 1000000000000) (37139721362 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 101 12 (254862033986873 / 800000000000)) (orderedInterval (-39423716000 / 1000000000000) (-39423680039 / 1000000000000), orderedInterval (21135306007 / 1000000000000) (21135341968 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 164 12 (82417145320409 / 160000000000)) (orderedInterval (21861775497 / 1000000000000) (21861775498 / 1000000000000), orderedInterval (27509864447 / 1000000000000) (27509864448 / 1000000000000))) = true
  rfl'

theorem compactCertificate561_stateChecks1 :
    compactCertificate561.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (74368105882411 / 800000000000)) (orderedInterval (-39935071193 / 1000000000000) (-39935065936 / 1000000000000), orderedInterval (72696184406 / 1000000000000) (72696189662 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (199763193139567 / 800000000000)) (orderedInterval (-37549113573 / 1000000000000) (-37549053192 / 1000000000000), orderedInterval (33832577018 / 1000000000000) (33832637399 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 216 12 (542395928849139 / 800000000000)) (orderedInterval (5970942112 / 1000000000000) (5970942113 / 1000000000000), orderedInterval (30050918109 / 1000000000000) (30050918110 / 1000000000000))) = true
  rfl'

theorem compactCertificate561_stateChecks2 :
    compactCertificate561.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 159 12 (399526386279307 / 800000000000)) (orderedInterval (-22447375415 / 1000000000000) (-22447375414 / 1000000000000), orderedInterval (-27741970242 / 1000000000000) (-27741970241 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 273 12 (684595272598711 / 800000000000)) (orderedInterval (24614818626 / 1000000000000) (24614869271 / 1000000000000), orderedInterval (-11763723813 / 1000000000000) (-11763673169 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 201 12 (504269779283749 / 800000000000)) (orderedInterval (10529255256 / 1000000000000) (10529255275 / 1000000000000), orderedInterval (-29993381605 / 1000000000000) (-29993381585 / 1000000000000))) = true
  rfl'

theorem compactCertificate561_stateChecks3 :
    compactCertificate561.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 308 12 (773679520214827 / 800000000000)) (orderedInterval (6945618179 / 1000000000000) (6945618180 / 1000000000000), orderedInterval (24695315095 / 1000000000000) (24695315096 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 178 12 (446684079262483 / 800000000000)) (orderedInterval (-2133255211 / 1000000000000) (-2133255210 / 1000000000000), orderedInterval (33700867936 / 1000000000000) (33700867937 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 316 12 (792648737208047 / 800000000000)) (orderedInterval (-23106525814 / 1000000000000) (-23106492510 / 1000000000000), orderedInterval (10433406320 / 1000000000000) (10433439623 / 1000000000000))) = true
  rfl'

theorem compactCertificate561_stateChecks4 :
    compactCertificate561.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 295 12 (740595269989643 / 800000000000)) (orderedInterval (6245732353 / 1000000000000) (6245732354 / 1000000000000), orderedInterval (-25472478597 / 1000000000000) (-25472478596 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 210 12 (528523730151419 / 800000000000)) (orderedInterval (30761365644 / 1000000000000) (30761371777 / 1000000000000), orderedInterval (-4189518462 / 1000000000000) (-4189512329 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 239 12 (599289579418701 / 800000000000)) (orderedInterval (23600815589 / 1000000000000) (23600831180 / 1000000000000), orderedInterval (-17128143507 / 1000000000000) (-17128127917 / 1000000000000))) = true
  rfl'

theorem compactCertificate561_stateChecks5 :
    compactCertificate561.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 199 12 (499625172239869 / 800000000000)) (orderedInterval (-4446555008 / 1000000000000) (-4446555007 / 1000000000000), orderedInterval (-31612642646 / 1000000000000) (-31612642645 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 176 12 (441433991785249 / 800000000000)) (orderedInterval (-11412103140 / 1000000000000) (-11412103102 / 1000000000000), orderedInterval (32002444209 / 1000000000000) (32002444247 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 255 12 (127944776535651 / 160000000000)) (orderedInterval (17433563744 / 1000000000000) (17433564315 / 1000000000000), orderedInterval (-22196235510 / 1000000000000) (-22196234939 / 1000000000000))) = true
  rfl'

theorem compactCertificate561_stateChecks6 :
    compactCertificate561.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 141 12 (353901985262297 / 800000000000)) (orderedInterval (-7463433790 / 1000000000000) (-7463433789 / 1000000000000), orderedInterval (-37185451099 / 1000000000000) (-37185451098 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 119 12 (300006632264017 / 800000000000)) (orderedInterval (-38368492151 / 1000000000000) (-38368476521 / 1000000000000), orderedInterval (15066923077 / 1000000000000) (15066938707 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (187730220716251 / 800000000000)) (orderedInterval (8904740022 / 1000000000000) (8904740055 / 1000000000000), orderedInterval (-51337826977 / 1000000000000) (-51337826944 / 1000000000000))) = true
  rfl'

theorem compactCertificate561_stateChecks7 :
    compactCertificate561.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (100961937063717 / 800000000000)) (orderedInterval (68856634036 / 1000000000000) (68856634037 / 1000000000000), orderedInterval (17138779140 / 1000000000000) (17138779141 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 109 12 (274131299022151 / 800000000000)) (orderedInterval (-36627675026 / 1000000000000) (-36627675025 / 1000000000000), orderedInterval (-22668045225 / 1000000000000) (-22668045224 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 149 12 (374302852609127 / 800000000000)) (orderedInterval (-19793212734 / 1000000000000) (-19793212733 / 1000000000000), orderedInterval (-31105697654 / 1000000000000) (-31105697653 / 1000000000000))) = true
  rfl'

theorem compactCertificate561_stateChecks8 :
    compactCertificate561.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (158269779283749 / 800000000000)) (orderedInterval (-36615841958 / 1000000000000) (-36615841957 / 1000000000000), orderedInterval (-43233879932 / 1000000000000) (-43233879931 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 256 12 (643357865913029 / 800000000000)) (orderedInterval (18864471738 / 1000000000000) (18864471739 / 1000000000000), orderedInterval (20862970395 / 1000000000000) (20862970396 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 171 12 (429733238612011 / 800000000000)) (orderedInterval (-23196956389 / 1000000000000) (-23196956388 / 1000000000000), orderedInterval (-25415494655 / 1000000000000) (-25415494654 / 1000000000000))) = true
  rfl'

theorem compactCertificate561_states : ∀ j,
    BesselStateValid (compactCertificate561.point j) (compactCertificate561.state j) :=
  compactCertificate561.statesValid_of_checks3 compactCertificate561_stateChecks0
    compactCertificate561_stateChecks1 compactCertificate561_stateChecks2
    compactCertificate561_stateChecks3 compactCertificate561_stateChecks4
    compactCertificate561_stateChecks5 compactCertificate561_stateChecks6
    compactCertificate561_stateChecks7 compactCertificate561_stateChecks8

theorem compactCertificate561_chunkChecks0_0 :
    compactCertificate561.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (865 / 2) 0 (IntervalRat.scale (865 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-9665664686 / 1000000000000) (-9665664660 / 1000000000000), orderedInterval (37139721336 / 1000000000000) (37139721362 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (254862033986873 / 800000000000) 0 (IntervalRat.scale (865 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-39423716000 / 1000000000000) (-39423680039 / 1000000000000), orderedInterval (21135306007 / 1000000000000) (21135341968 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (82417145320409 / 160000000000) 0 (IntervalRat.scale (865 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (21861775497 / 1000000000000) (21861775498 / 1000000000000), orderedInterval (27509864447 / 1000000000000) (27509864448 / 1000000000000)))) (orderedInterval (-2915609773 / 1000000000000) (-2915609397 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (74368105882411 / 800000000000) 0 (IntervalRat.scale (865 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-39935071193 / 1000000000000) (-39935065936 / 1000000000000), orderedInterval (72696184406 / 1000000000000) (72696189662 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (199763193139567 / 800000000000) 0 (IntervalRat.scale (865 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-37549113573 / 1000000000000) (-37549053192 / 1000000000000), orderedInterval (33832577018 / 1000000000000) (33832637399 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (542395928849139 / 800000000000) 0 (IntervalRat.scale (865 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (5970942112 / 1000000000000) (5970942113 / 1000000000000), orderedInterval (30050918109 / 1000000000000) (30050918110 / 1000000000000)))) (orderedInterval (-1362188703 / 1000000000000) (-1362186389 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (399526386279307 / 800000000000) 0 (IntervalRat.scale (865 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-22447375415 / 1000000000000) (-22447375414 / 1000000000000), orderedInterval (-27741970242 / 1000000000000) (-27741970241 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (684595272598711 / 800000000000) 0 (IntervalRat.scale (865 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (24614818626 / 1000000000000) (24614869271 / 1000000000000), orderedInterval (-11763723813 / 1000000000000) (-11763673169 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (504269779283749 / 800000000000) 0 (IntervalRat.scale (865 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (10529255256 / 1000000000000) (10529255275 / 1000000000000), orderedInterval (-29993381605 / 1000000000000) (-29993381585 / 1000000000000)))) (orderedInterval (-504749739 / 1000000000000) (-504748152 / 1000000000000))) = true
  rfl'

theorem compactCertificate561_chunkChecks0_1 :
    compactCertificate561.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (773679520214827 / 800000000000) 0 (IntervalRat.scale (865 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (6945618179 / 1000000000000) (6945618180 / 1000000000000), orderedInterval (24695315095 / 1000000000000) (24695315096 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (446684079262483 / 800000000000) 0 (IntervalRat.scale (865 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-2133255211 / 1000000000000) (-2133255210 / 1000000000000), orderedInterval (33700867936 / 1000000000000) (33700867937 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (792648737208047 / 800000000000) 0 (IntervalRat.scale (865 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-23106525814 / 1000000000000) (-23106492510 / 1000000000000), orderedInterval (10433406320 / 1000000000000) (10433439623 / 1000000000000)))) (orderedInterval (-4676938020 / 1000000000000) (-4676933114 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (740595269989643 / 800000000000) 0 (IntervalRat.scale (865 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (6245732353 / 1000000000000) (6245732354 / 1000000000000), orderedInterval (-25472478597 / 1000000000000) (-25472478596 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (528523730151419 / 800000000000) 0 (IntervalRat.scale (865 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (30761365644 / 1000000000000) (30761371777 / 1000000000000), orderedInterval (-4189518462 / 1000000000000) (-4189512329 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (599289579418701 / 800000000000) 0 (IntervalRat.scale (865 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (23600815589 / 1000000000000) (23600831180 / 1000000000000), orderedInterval (-17128143507 / 1000000000000) (-17128127917 / 1000000000000)))) (orderedInterval (2676694328 / 1000000000000) (2676695039 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (499625172239869 / 800000000000) 0 (IntervalRat.scale (865 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-4446555008 / 1000000000000) (-4446555007 / 1000000000000), orderedInterval (-31612642646 / 1000000000000) (-31612642645 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (441433991785249 / 800000000000) 0 (IntervalRat.scale (865 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-11412103140 / 1000000000000) (-11412103102 / 1000000000000), orderedInterval (32002444209 / 1000000000000) (32002444247 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (127944776535651 / 160000000000) 0 (IntervalRat.scale (865 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (17433563744 / 1000000000000) (17433564315 / 1000000000000), orderedInterval (-22196235510 / 1000000000000) (-22196234939 / 1000000000000)))) (orderedInterval (1048097462 / 1000000000000) (1048097520 / 1000000000000))) = true
  rfl'

theorem compactCertificate561_chunkChecks0_2 :
    compactCertificate561.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (353901985262297 / 800000000000) 0 (IntervalRat.scale (865 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-7463433790 / 1000000000000) (-7463433789 / 1000000000000), orderedInterval (-37185451099 / 1000000000000) (-37185451098 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (300006632264017 / 800000000000) 0 (IntervalRat.scale (865 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-38368492151 / 1000000000000) (-38368476521 / 1000000000000), orderedInterval (15066923077 / 1000000000000) (15066938707 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (187730220716251 / 800000000000) 0 (IntervalRat.scale (865 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (8904740022 / 1000000000000) (8904740055 / 1000000000000), orderedInterval (-51337826977 / 1000000000000) (-51337826944 / 1000000000000)))) (orderedInterval (3654896907 / 1000000000000) (3654897902 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (100961937063717 / 800000000000) 0 (IntervalRat.scale (865 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (68856634036 / 1000000000000) (68856634037 / 1000000000000), orderedInterval (17138779140 / 1000000000000) (17138779141 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (274131299022151 / 800000000000) 0 (IntervalRat.scale (865 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-36627675026 / 1000000000000) (-36627675025 / 1000000000000), orderedInterval (-22668045225 / 1000000000000) (-22668045224 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (374302852609127 / 800000000000) 0 (IntervalRat.scale (865 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-19793212734 / 1000000000000) (-19793212733 / 1000000000000), orderedInterval (-31105697654 / 1000000000000) (-31105697653 / 1000000000000)))) (orderedInterval (1076450637 / 1000000000000) (1076450689 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (158269779283749 / 800000000000) 0 (IntervalRat.scale (865 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-36615841958 / 1000000000000) (-36615841957 / 1000000000000), orderedInterval (-43233879932 / 1000000000000) (-43233879931 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (643357865913029 / 800000000000) 0 (IntervalRat.scale (865 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (18864471738 / 1000000000000) (18864471739 / 1000000000000), orderedInterval (20862970395 / 1000000000000) (20862970396 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (429733238612011 / 800000000000) 0 (IntervalRat.scale (865 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-23196956389 / 1000000000000) (-23196956388 / 1000000000000), orderedInterval (-25415494655 / 1000000000000) (-25415494654 / 1000000000000)))) (orderedInterval (2596030477 / 1000000000000) (2596030597 / 1000000000000))) = true
  rfl'

theorem compactCertificate561_chunkChecks0 :
    compactCertificate561.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate561.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate561_chunkChecks0_0
    compactCertificate561_chunkChecks0_1 compactCertificate561_chunkChecks0_2

theorem compactCertificate561_chunkChecks1_0 :
    compactCertificate561.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (865 / 2) 1 (IntervalRat.scale (865 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-9665664686 / 1000000000000) (-9665664660 / 1000000000000), orderedInterval (37139721336 / 1000000000000) (37139721362 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (254862033986873 / 800000000000) 1 (IntervalRat.scale (865 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-39423716000 / 1000000000000) (-39423680039 / 1000000000000), orderedInterval (21135306007 / 1000000000000) (21135341968 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (82417145320409 / 160000000000) 1 (IntervalRat.scale (865 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (21861775497 / 1000000000000) (21861775498 / 1000000000000), orderedInterval (27509864447 / 1000000000000) (27509864448 / 1000000000000)))) (orderedInterval (16788592700 / 1000000000000) (16788592992 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (74368105882411 / 800000000000) 1 (IntervalRat.scale (865 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-39935071193 / 1000000000000) (-39935065936 / 1000000000000), orderedInterval (72696184406 / 1000000000000) (72696189662 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (199763193139567 / 800000000000) 1 (IntervalRat.scale (865 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-37549113573 / 1000000000000) (-37549053192 / 1000000000000), orderedInterval (33832577018 / 1000000000000) (33832637399 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (542395928849139 / 800000000000) 1 (IntervalRat.scale (865 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (5970942112 / 1000000000000) (5970942113 / 1000000000000), orderedInterval (30050918109 / 1000000000000) (30050918110 / 1000000000000)))) (orderedInterval (-2805245141 / 1000000000000) (-2805243797 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (399526386279307 / 800000000000) 1 (IntervalRat.scale (865 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-22447375415 / 1000000000000) (-22447375414 / 1000000000000), orderedInterval (-27741970242 / 1000000000000) (-27741970241 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (684595272598711 / 800000000000) 1 (IntervalRat.scale (865 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (24614818626 / 1000000000000) (24614869271 / 1000000000000), orderedInterval (-11763723813 / 1000000000000) (-11763673169 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (504269779283749 / 800000000000) 1 (IntervalRat.scale (865 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (10529255256 / 1000000000000) (10529255275 / 1000000000000), orderedInterval (-29993381605 / 1000000000000) (-29993381585 / 1000000000000)))) (orderedInterval (-338548630 / 1000000000000) (-338545496 / 1000000000000))) = true
  rfl'

theorem compactCertificate561_chunkChecks1_1 :
    compactCertificate561.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (773679520214827 / 800000000000) 1 (IntervalRat.scale (865 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (6945618179 / 1000000000000) (6945618180 / 1000000000000), orderedInterval (24695315095 / 1000000000000) (24695315096 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (446684079262483 / 800000000000) 1 (IntervalRat.scale (865 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-2133255211 / 1000000000000) (-2133255210 / 1000000000000), orderedInterval (33700867936 / 1000000000000) (33700867937 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (792648737208047 / 800000000000) 1 (IntervalRat.scale (865 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-23106525814 / 1000000000000) (-23106492510 / 1000000000000), orderedInterval (10433406320 / 1000000000000) (10433439623 / 1000000000000)))) (orderedInterval (-3190658341 / 1000000000000) (-3190647140 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (740595269989643 / 800000000000) 1 (IntervalRat.scale (865 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (6245732353 / 1000000000000) (6245732354 / 1000000000000), orderedInterval (-25472478597 / 1000000000000) (-25472478596 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (528523730151419 / 800000000000) 1 (IntervalRat.scale (865 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (30761365644 / 1000000000000) (30761371777 / 1000000000000), orderedInterval (-4189518462 / 1000000000000) (-4189512329 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (599289579418701 / 800000000000) 1 (IntervalRat.scale (865 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (23600815589 / 1000000000000) (23600831180 / 1000000000000), orderedInterval (-17128143507 / 1000000000000) (-17128127917 / 1000000000000)))) (orderedInterval (529266949 / 1000000000000) (529268055 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (499625172239869 / 800000000000) 1 (IntervalRat.scale (865 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-4446555008 / 1000000000000) (-4446555007 / 1000000000000), orderedInterval (-31612642646 / 1000000000000) (-31612642645 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (441433991785249 / 800000000000) 1 (IntervalRat.scale (865 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-11412103140 / 1000000000000) (-11412103102 / 1000000000000), orderedInterval (32002444209 / 1000000000000) (32002444247 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (127944776535651 / 160000000000) 1 (IntervalRat.scale (865 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (17433563744 / 1000000000000) (17433564315 / 1000000000000), orderedInterval (-22196235510 / 1000000000000) (-22196234939 / 1000000000000)))) (orderedInterval (-3914424960 / 1000000000000) (-3914424870 / 1000000000000))) = true
  rfl'

theorem compactCertificate561_chunkChecks1_2 :
    compactCertificate561.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (353901985262297 / 800000000000) 1 (IntervalRat.scale (865 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-7463433790 / 1000000000000) (-7463433789 / 1000000000000), orderedInterval (-37185451099 / 1000000000000) (-37185451098 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (300006632264017 / 800000000000) 1 (IntervalRat.scale (865 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-38368492151 / 1000000000000) (-38368476521 / 1000000000000), orderedInterval (15066923077 / 1000000000000) (15066938707 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (187730220716251 / 800000000000) 1 (IntervalRat.scale (865 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (8904740022 / 1000000000000) (8904740055 / 1000000000000), orderedInterval (-51337826977 / 1000000000000) (-51337826944 / 1000000000000)))) (orderedInterval (4435221249 / 1000000000000) (4435222118 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (100961937063717 / 800000000000) 1 (IntervalRat.scale (865 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (68856634036 / 1000000000000) (68856634037 / 1000000000000), orderedInterval (17138779140 / 1000000000000) (17138779141 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (274131299022151 / 800000000000) 1 (IntervalRat.scale (865 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-36627675026 / 1000000000000) (-36627675025 / 1000000000000), orderedInterval (-22668045225 / 1000000000000) (-22668045224 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (374302852609127 / 800000000000) 1 (IntervalRat.scale (865 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-19793212734 / 1000000000000) (-19793212733 / 1000000000000), orderedInterval (-31105697654 / 1000000000000) (-31105697653 / 1000000000000)))) (orderedInterval (2894011207 / 1000000000000) (2894011254 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (158269779283749 / 800000000000) 1 (IntervalRat.scale (865 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-36615841958 / 1000000000000) (-36615841957 / 1000000000000), orderedInterval (-43233879932 / 1000000000000) (-43233879931 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (643357865913029 / 800000000000) 1 (IntervalRat.scale (865 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (18864471738 / 1000000000000) (18864471739 / 1000000000000), orderedInterval (20862970395 / 1000000000000) (20862970396 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (429733238612011 / 800000000000) 1 (IntervalRat.scale (865 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-23196956389 / 1000000000000) (-23196956388 / 1000000000000), orderedInterval (-25415494655 / 1000000000000) (-25415494654 / 1000000000000)))) (orderedInterval (2645611959 / 1000000000000) (2645612128 / 1000000000000))) = true
  rfl'

theorem compactCertificate561_chunkChecks1 :
    compactCertificate561.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate561.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate561_chunkChecks1_0
    compactCertificate561_chunkChecks1_1 compactCertificate561_chunkChecks1_2

theorem compactCertificate561_chunkChecks2_0 :
    compactCertificate561.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (865 / 2) 2 (IntervalRat.scale (865 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-9665664686 / 1000000000000) (-9665664660 / 1000000000000), orderedInterval (37139721336 / 1000000000000) (37139721362 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (254862033986873 / 800000000000) 2 (IntervalRat.scale (865 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-39423716000 / 1000000000000) (-39423680039 / 1000000000000), orderedInterval (21135306007 / 1000000000000) (21135341968 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (82417145320409 / 160000000000) 2 (IntervalRat.scale (865 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (21861775497 / 1000000000000) (21861775498 / 1000000000000), orderedInterval (27509864447 / 1000000000000) (27509864448 / 1000000000000)))) (orderedInterval (2171899034 / 1000000000000) (2171899266 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (74368105882411 / 800000000000) 2 (IntervalRat.scale (865 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-39935071193 / 1000000000000) (-39935065936 / 1000000000000), orderedInterval (72696184406 / 1000000000000) (72696189662 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (199763193139567 / 800000000000) 2 (IntervalRat.scale (865 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-37549113573 / 1000000000000) (-37549053192 / 1000000000000), orderedInterval (33832577018 / 1000000000000) (33832637399 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (542395928849139 / 800000000000) 2 (IntervalRat.scale (865 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (5970942112 / 1000000000000) (5970942113 / 1000000000000), orderedInterval (30050918109 / 1000000000000) (30050918110 / 1000000000000)))) (orderedInterval (1486573235 / 1000000000000) (1486574058 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (399526386279307 / 800000000000) 2 (IntervalRat.scale (865 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-22447375415 / 1000000000000) (-22447375414 / 1000000000000), orderedInterval (-27741970242 / 1000000000000) (-27741970241 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (684595272598711 / 800000000000) 2 (IntervalRat.scale (865 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (24614818626 / 1000000000000) (24614869271 / 1000000000000), orderedInterval (-11763723813 / 1000000000000) (-11763673169 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (504269779283749 / 800000000000) 2 (IntervalRat.scale (865 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (10529255256 / 1000000000000) (10529255275 / 1000000000000), orderedInterval (-29993381605 / 1000000000000) (-29993381585 / 1000000000000)))) (orderedInterval (2432495390 / 1000000000000) (2432501589 / 1000000000000))) = true
  rfl'

theorem compactCertificate561_chunkChecks2_1 :
    compactCertificate561.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (773679520214827 / 800000000000) 2 (IntervalRat.scale (865 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (6945618179 / 1000000000000) (6945618180 / 1000000000000), orderedInterval (24695315095 / 1000000000000) (24695315096 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (446684079262483 / 800000000000) 2 (IntervalRat.scale (865 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-2133255211 / 1000000000000) (-2133255210 / 1000000000000), orderedInterval (33700867936 / 1000000000000) (33700867937 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (792648737208047 / 800000000000) 2 (IntervalRat.scale (865 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-23106525814 / 1000000000000) (-23106492510 / 1000000000000), orderedInterval (10433406320 / 1000000000000) (10433439623 / 1000000000000)))) (orderedInterval (23680414925 / 1000000000000) (23680440559 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (740595269989643 / 800000000000) 2 (IntervalRat.scale (865 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (6245732353 / 1000000000000) (6245732354 / 1000000000000), orderedInterval (-25472478597 / 1000000000000) (-25472478596 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (528523730151419 / 800000000000) 2 (IntervalRat.scale (865 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (30761365644 / 1000000000000) (30761371777 / 1000000000000), orderedInterval (-4189518462 / 1000000000000) (-4189512329 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (599289579418701 / 800000000000) 2 (IntervalRat.scale (865 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (23600815589 / 1000000000000) (23600831180 / 1000000000000), orderedInterval (-17128143507 / 1000000000000) (-17128127917 / 1000000000000)))) (orderedInterval (-5913729217 / 1000000000000) (-5913727486 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (499625172239869 / 800000000000) 2 (IntervalRat.scale (865 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-4446555008 / 1000000000000) (-4446555007 / 1000000000000), orderedInterval (-31612642646 / 1000000000000) (-31612642645 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (441433991785249 / 800000000000) 2 (IntervalRat.scale (865 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-11412103140 / 1000000000000) (-11412103102 / 1000000000000), orderedInterval (32002444209 / 1000000000000) (32002444247 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (127944776535651 / 160000000000) 2 (IntervalRat.scale (865 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (17433563744 / 1000000000000) (17433564315 / 1000000000000), orderedInterval (-22196235510 / 1000000000000) (-22196234939 / 1000000000000)))) (orderedInterval (-2472807908 / 1000000000000) (-2472807765 / 1000000000000))) = true
  rfl'

theorem compactCertificate561_chunkChecks2_2 :
    compactCertificate561.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (353901985262297 / 800000000000) 2 (IntervalRat.scale (865 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-7463433790 / 1000000000000) (-7463433789 / 1000000000000), orderedInterval (-37185451099 / 1000000000000) (-37185451098 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (300006632264017 / 800000000000) 2 (IntervalRat.scale (865 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-38368492151 / 1000000000000) (-38368476521 / 1000000000000), orderedInterval (15066923077 / 1000000000000) (15066938707 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (187730220716251 / 800000000000) 2 (IntervalRat.scale (865 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (8904740022 / 1000000000000) (8904740055 / 1000000000000), orderedInterval (-51337826977 / 1000000000000) (-51337826944 / 1000000000000)))) (orderedInterval (-2976749979 / 1000000000000) (-2976749216 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (100961937063717 / 800000000000) 2 (IntervalRat.scale (865 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (68856634036 / 1000000000000) (68856634037 / 1000000000000), orderedInterval (17138779140 / 1000000000000) (17138779141 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (274131299022151 / 800000000000) 2 (IntervalRat.scale (865 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-36627675026 / 1000000000000) (-36627675025 / 1000000000000), orderedInterval (-22668045225 / 1000000000000) (-22668045224 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (374302852609127 / 800000000000) 2 (IntervalRat.scale (865 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-19793212734 / 1000000000000) (-19793212733 / 1000000000000), orderedInterval (-31105697654 / 1000000000000) (-31105697653 / 1000000000000)))) (orderedInterval (-2195296394 / 1000000000000) (-2195296348 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (158269779283749 / 800000000000) 2 (IntervalRat.scale (865 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-36615841958 / 1000000000000) (-36615841957 / 1000000000000), orderedInterval (-43233879932 / 1000000000000) (-43233879931 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (643357865913029 / 800000000000) 2 (IntervalRat.scale (865 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (18864471738 / 1000000000000) (18864471739 / 1000000000000), orderedInterval (20862970395 / 1000000000000) (20862970396 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (429733238612011 / 800000000000) 2 (IntervalRat.scale (865 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-23196956389 / 1000000000000) (-23196956388 / 1000000000000), orderedInterval (-25415494655 / 1000000000000) (-25415494654 / 1000000000000)))) (orderedInterval (-1364540174 / 1000000000000) (-1364539925 / 1000000000000))) = true
  rfl'

theorem compactCertificate561_chunkChecks2 :
    compactCertificate561.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate561.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate561_chunkChecks2_0
    compactCertificate561_chunkChecks2_1 compactCertificate561_chunkChecks2_2

theorem compactCertificate561_chunkChecks3_0 :
    compactCertificate561.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (865 / 2) 3 (IntervalRat.scale (865 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-9665664686 / 1000000000000) (-9665664660 / 1000000000000), orderedInterval (37139721336 / 1000000000000) (37139721362 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (254862033986873 / 800000000000) 3 (IntervalRat.scale (865 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-39423716000 / 1000000000000) (-39423680039 / 1000000000000), orderedInterval (21135306007 / 1000000000000) (21135341968 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (82417145320409 / 160000000000) 3 (IntervalRat.scale (865 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (21861775497 / 1000000000000) (21861775498 / 1000000000000), orderedInterval (27509864447 / 1000000000000) (27509864448 / 1000000000000)))) (orderedInterval (-17531753737 / 1000000000000) (-17531753547 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (74368105882411 / 800000000000) 3 (IntervalRat.scale (865 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-39935071193 / 1000000000000) (-39935065936 / 1000000000000), orderedInterval (72696184406 / 1000000000000) (72696189662 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (199763193139567 / 800000000000) 3 (IntervalRat.scale (865 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-37549113573 / 1000000000000) (-37549053192 / 1000000000000), orderedInterval (33832577018 / 1000000000000) (33832637399 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (542395928849139 / 800000000000) 3 (IntervalRat.scale (865 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (5970942112 / 1000000000000) (5970942113 / 1000000000000), orderedInterval (30050918109 / 1000000000000) (30050918110 / 1000000000000)))) (orderedInterval (7996367360 / 1000000000000) (7996367909 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (399526386279307 / 800000000000) 3 (IntervalRat.scale (865 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-22447375415 / 1000000000000) (-22447375414 / 1000000000000), orderedInterval (-27741970242 / 1000000000000) (-27741970241 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (684595272598711 / 800000000000) 3 (IntervalRat.scale (865 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (24614818626 / 1000000000000) (24614869271 / 1000000000000), orderedInterval (-11763723813 / 1000000000000) (-11763673169 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (504269779283749 / 800000000000) 3 (IntervalRat.scale (865 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (10529255256 / 1000000000000) (10529255275 / 1000000000000), orderedInterval (-29993381605 / 1000000000000) (-29993381585 / 1000000000000)))) (orderedInterval (-572138397 / 1000000000000) (-572126145 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate561_chunkChecks3_1 :
    compactCertificate561.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (773679520214827 / 800000000000) 3 (IntervalRat.scale (865 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (6945618179 / 1000000000000) (6945618180 / 1000000000000), orderedInterval (24695315095 / 1000000000000) (24695315096 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (446684079262483 / 800000000000) 3 (IntervalRat.scale (865 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-2133255211 / 1000000000000) (-2133255210 / 1000000000000), orderedInterval (33700867936 / 1000000000000) (33700867937 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (792648737208047 / 800000000000) 3 (IntervalRat.scale (865 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-23106525814 / 1000000000000) (-23106492510 / 1000000000000), orderedInterval (10433406320 / 1000000000000) (10433439623 / 1000000000000)))) (orderedInterval (25800368111 / 1000000000000) (25800426759 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (740595269989643 / 800000000000) 3 (IntervalRat.scale (865 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (6245732353 / 1000000000000) (6245732354 / 1000000000000), orderedInterval (-25472478597 / 1000000000000) (-25472478596 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (528523730151419 / 800000000000) 3 (IntervalRat.scale (865 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (30761365644 / 1000000000000) (30761371777 / 1000000000000), orderedInterval (-4189518462 / 1000000000000) (-4189512329 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (599289579418701 / 800000000000) 3 (IntervalRat.scale (865 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (23600815589 / 1000000000000) (23600831180 / 1000000000000), orderedInterval (-17128143507 / 1000000000000) (-17128127917 / 1000000000000)))) (orderedInterval (-3534261115 / 1000000000000) (-3534258400 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (499625172239869 / 800000000000) 3 (IntervalRat.scale (865 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-4446555008 / 1000000000000) (-4446555007 / 1000000000000), orderedInterval (-31612642646 / 1000000000000) (-31612642645 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (441433991785249 / 800000000000) 3 (IntervalRat.scale (865 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-11412103140 / 1000000000000) (-11412103102 / 1000000000000), orderedInterval (32002444209 / 1000000000000) (32002444247 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (127944776535651 / 160000000000) 3 (IntervalRat.scale (865 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (17433563744 / 1000000000000) (17433564315 / 1000000000000), orderedInterval (-22196235510 / 1000000000000) (-22196234939 / 1000000000000)))) (orderedInterval (8500061734 / 1000000000000) (8500061968 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate561_chunkChecks3_2 :
    compactCertificate561.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (353901985262297 / 800000000000) 3 (IntervalRat.scale (865 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-7463433790 / 1000000000000) (-7463433789 / 1000000000000), orderedInterval (-37185451099 / 1000000000000) (-37185451098 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (300006632264017 / 800000000000) 3 (IntervalRat.scale (865 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-38368492151 / 1000000000000) (-38368476521 / 1000000000000), orderedInterval (15066923077 / 1000000000000) (15066938707 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (187730220716251 / 800000000000) 3 (IntervalRat.scale (865 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (8904740022 / 1000000000000) (8904740055 / 1000000000000), orderedInterval (-51337826977 / 1000000000000) (-51337826944 / 1000000000000)))) (orderedInterval (-5532641726 / 1000000000000) (-5532641054 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (100961937063717 / 800000000000) 3 (IntervalRat.scale (865 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (68856634036 / 1000000000000) (68856634037 / 1000000000000), orderedInterval (17138779140 / 1000000000000) (17138779141 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (274131299022151 / 800000000000) 3 (IntervalRat.scale (865 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-36627675026 / 1000000000000) (-36627675025 / 1000000000000), orderedInterval (-22668045225 / 1000000000000) (-22668045224 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (374302852609127 / 800000000000) 3 (IntervalRat.scale (865 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-19793212734 / 1000000000000) (-19793212733 / 1000000000000), orderedInterval (-31105697654 / 1000000000000) (-31105697653 / 1000000000000)))) (orderedInterval (-3260883839 / 1000000000000) (-3260883791 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (158269779283749 / 800000000000) 3 (IntervalRat.scale (865 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-36615841958 / 1000000000000) (-36615841957 / 1000000000000), orderedInterval (-43233879932 / 1000000000000) (-43233879931 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (643357865913029 / 800000000000) 3 (IntervalRat.scale (865 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (18864471738 / 1000000000000) (18864471739 / 1000000000000), orderedInterval (20862970395 / 1000000000000) (20862970396 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (429733238612011 / 800000000000) 3 (IntervalRat.scale (865 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-23196956389 / 1000000000000) (-23196956388 / 1000000000000), orderedInterval (-25415494655 / 1000000000000) (-25415494654 / 1000000000000)))) (orderedInterval (1809915202 / 1000000000000) (1809915586 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate561_chunkChecks3 :
    compactCertificate561.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate561.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate561_chunkChecks3_0
    compactCertificate561_chunkChecks3_1 compactCertificate561_chunkChecks3_2

theorem compactCertificate561_chunkChecks4_0 :
    compactCertificate561.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (865 / 2) 4 (IntervalRat.scale (865 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-9665664686 / 1000000000000) (-9665664660 / 1000000000000), orderedInterval (37139721336 / 1000000000000) (37139721362 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (254862033986873 / 800000000000) 4 (IntervalRat.scale (865 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-39423716000 / 1000000000000) (-39423680039 / 1000000000000), orderedInterval (21135306007 / 1000000000000) (21135341968 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (82417145320409 / 160000000000) 4 (IntervalRat.scale (865 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (21861775497 / 1000000000000) (21861775498 / 1000000000000), orderedInterval (27509864447 / 1000000000000) (27509864448 / 1000000000000)))) (orderedInterval (-1276942460 / 1000000000000) (-1276942297 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (74368105882411 / 800000000000) 4 (IntervalRat.scale (865 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-39935071193 / 1000000000000) (-39935065936 / 1000000000000), orderedInterval (72696184406 / 1000000000000) (72696189662 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (199763193139567 / 800000000000) 4 (IntervalRat.scale (865 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-37549113573 / 1000000000000) (-37549053192 / 1000000000000), orderedInterval (33832577018 / 1000000000000) (33832637399 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (542395928849139 / 800000000000) 4 (IntervalRat.scale (865 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (5970942112 / 1000000000000) (5970942113 / 1000000000000), orderedInterval (30050918109 / 1000000000000) (30050918110 / 1000000000000)))) (orderedInterval (-2751741487 / 1000000000000) (-2751741051 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (399526386279307 / 800000000000) 4 (IntervalRat.scale (865 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-22447375415 / 1000000000000) (-22447375414 / 1000000000000), orderedInterval (-27741970242 / 1000000000000) (-27741970241 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (684595272598711 / 800000000000) 4 (IntervalRat.scale (865 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (24614818626 / 1000000000000) (24614869271 / 1000000000000), orderedInterval (-11763723813 / 1000000000000) (-11763673169 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (504269779283749 / 800000000000) 4 (IntervalRat.scale (865 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (10529255256 / 1000000000000) (10529255275 / 1000000000000), orderedInterval (-29993381605 / 1000000000000) (-29993381585 / 1000000000000)))) (orderedInterval (-10485109512 / 1000000000000) (-10485085261 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate561_chunkChecks4_1 :
    compactCertificate561.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (773679520214827 / 800000000000) 4 (IntervalRat.scale (865 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (6945618179 / 1000000000000) (6945618180 / 1000000000000), orderedInterval (24695315095 / 1000000000000) (24695315096 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (446684079262483 / 800000000000) 4 (IntervalRat.scale (865 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-2133255211 / 1000000000000) (-2133255210 / 1000000000000), orderedInterval (33700867936 / 1000000000000) (33700867937 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (792648737208047 / 800000000000) 4 (IntervalRat.scale (865 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-23106525814 / 1000000000000) (-23106492510 / 1000000000000), orderedInterval (10433406320 / 1000000000000) (10433439623 / 1000000000000)))) (orderedInterval (-121884879246 / 1000000000000) (-121884744873 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (740595269989643 / 800000000000) 4 (IntervalRat.scale (865 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (6245732353 / 1000000000000) (6245732354 / 1000000000000), orderedInterval (-25472478597 / 1000000000000) (-25472478596 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (528523730151419 / 800000000000) 4 (IntervalRat.scale (865 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (30761365644 / 1000000000000) (30761371777 / 1000000000000), orderedInterval (-4189518462 / 1000000000000) (-4189512329 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (599289579418701 / 800000000000) 4 (IntervalRat.scale (865 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (23600815589 / 1000000000000) (23600831180 / 1000000000000), orderedInterval (-17128143507 / 1000000000000) (-17128127917 / 1000000000000)))) (orderedInterval (12411899022 / 1000000000000) (12411903309 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (499625172239869 / 800000000000) 4 (IntervalRat.scale (865 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-4446555008 / 1000000000000) (-4446555007 / 1000000000000), orderedInterval (-31612642646 / 1000000000000) (-31612642645 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (441433991785249 / 800000000000) 4 (IntervalRat.scale (865 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-11412103140 / 1000000000000) (-11412103102 / 1000000000000), orderedInterval (32002444209 / 1000000000000) (32002444247 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (127944776535651 / 160000000000) 4 (IntervalRat.scale (865 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (17433563744 / 1000000000000) (17433564315 / 1000000000000), orderedInterval (-22196235510 / 1000000000000) (-22196234939 / 1000000000000)))) (orderedInterval (6683993673 / 1000000000000) (6683994068 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate561_chunkChecks4_2 :
    compactCertificate561.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (353901985262297 / 800000000000) 4 (IntervalRat.scale (865 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-7463433790 / 1000000000000) (-7463433789 / 1000000000000), orderedInterval (-37185451099 / 1000000000000) (-37185451098 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (300006632264017 / 800000000000) 4 (IntervalRat.scale (865 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-38368492151 / 1000000000000) (-38368476521 / 1000000000000), orderedInterval (15066923077 / 1000000000000) (15066938707 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (187730220716251 / 800000000000) 4 (IntervalRat.scale (865 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (8904740022 / 1000000000000) (8904740055 / 1000000000000), orderedInterval (-51337826977 / 1000000000000) (-51337826944 / 1000000000000)))) (orderedInterval (2584311737 / 1000000000000) (2584312332 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (100961937063717 / 800000000000) 4 (IntervalRat.scale (865 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (68856634036 / 1000000000000) (68856634037 / 1000000000000), orderedInterval (17138779140 / 1000000000000) (17138779141 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (274131299022151 / 800000000000) 4 (IntervalRat.scale (865 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-36627675026 / 1000000000000) (-36627675025 / 1000000000000), orderedInterval (-22668045225 / 1000000000000) (-22668045224 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (374302852609127 / 800000000000) 4 (IntervalRat.scale (865 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-19793212734 / 1000000000000) (-19793212733 / 1000000000000), orderedInterval (-31105697654 / 1000000000000) (-31105697653 / 1000000000000)))) (orderedInterval (2410836065 / 1000000000000) (2410836115 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (158269779283749 / 800000000000) 4 (IntervalRat.scale (865 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-36615841958 / 1000000000000) (-36615841957 / 1000000000000), orderedInterval (-43233879932 / 1000000000000) (-43233879931 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (643357865913029 / 800000000000) 4 (IntervalRat.scale (865 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (18864471738 / 1000000000000) (18864471739 / 1000000000000), orderedInterval (20862970395 / 1000000000000) (20862970396 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (429733238612011 / 800000000000) 4 (IntervalRat.scale (865 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-23196956389 / 1000000000000) (-23196956388 / 1000000000000), orderedInterval (-25415494655 / 1000000000000) (-25415494654 / 1000000000000)))) (orderedInterval (-8017731483 / 1000000000000) (-8017730866 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate561_chunkChecks4 :
    compactCertificate561.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate561.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate561_chunkChecks4_0
    compactCertificate561_chunkChecks4_1 compactCertificate561_chunkChecks4_2

theorem compactCertificate561_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate561.chunkCheck r b = true :=
  compactCertificate561.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate561_chunkChecks0
    · exact compactCertificate561_chunkChecks1
    · exact compactCertificate561_chunkChecks2
    · exact compactCertificate561_chunkChecks3
    · exact compactCertificate561_chunkChecks4)

theorem compactCertificate561_coefficient0 :
    compactCertificate561.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate561_coefficient1 :
    compactCertificate561.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate561_coefficient2 :
    compactCertificate561.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate561_coefficient3 :
    compactCertificate561.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate561_coefficient4 :
    compactCertificate561.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate561_coefficients : ∀ r : Fin 5,
    compactCertificate561.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate561_coefficient0
  · exact compactCertificate561_coefficient1
  · exact compactCertificate561_coefficient2
  · exact compactCertificate561_coefficient3
  · exact compactCertificate561_coefficient4

theorem compactCertificate561_lower : (1 : ℚ) ≤ compactCertificate561.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate561, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate561_proves {t : ℝ} (ht : t ∈ compactCertificate561.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate561.proves compactCertificate561_states compactCertificate561_chunks
    compactCertificate561_coefficients compactCertificate561_lower ht

end Erdos232
