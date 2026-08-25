/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate414 : CompactCertificate where
  left := 285
  right := 286
  center := 571 / 2
  grid := fun i =>
    match i.val with
    | 0 => 91
    | 1 => 67
    | 2 => 108
    | 3 => 20
    | 4 => 52
    | 5 => 143
    | 6 => 105
    | 7 => 180
    | 8 => 133
    | 9 => 203
    | 10 => 117
    | 11 => 208
    | 12 => 195
    | 13 => 139
    | 14 => 157
    | 15 => 131
    | 16 => 116
    | 17 => 168
    | 18 => 93
    | 19 => 79
    | 20 => 49
    | 21 => 27
    | 22 => 72
    | 23 => 98
    | 24 => 42
    | 25 => 169
    | _ => 113
  point := fun i =>
    match i.val with
    | 0 => 571 / 2
    | 1 => 841192031251471 / 4000000000000
    | 2 => 272024219525743 / 800000000000
    | 3 => 245457736756397 / 4000000000000
    | 4 => 659334007414409 / 4000000000000
    | 5 => 1790220088860453 / 4000000000000
    | 6 => 1318668014829389 / 4000000000000
    | 7 => 2259560119386497 / 4000000000000
    | 8 => 1664381757057923 / 4000000000000
    | 9 => 2553589630304429 / 4000000000000
    | 10 => 1474315660455941 / 4000000000000
    | 11 => 2616199011247369 / 4000000000000
    | 12 => 2444392480717261 / 4000000000000
    | 13 => 1744433814546013 / 4000000000000
    | 14 => 1978002022243227 / 4000000000000
    | 15 => 1649051869069163 / 4000000000000
    | 16 => 1456987337048423 / 4000000000000
    | 17 => 422291719085877 / 800000000000
    | 18 => 1168081118987119 / 4000000000000
    | 19 => 990195300709559 / 4000000000000
    | 20 => 619618242942077 / 4000000000000
    | 21 => 333232751811459 / 4000000000000
    | 22 => 904791744171377 / 4000000000000
    | 23 => 1235415773640529 / 4000000000000
    | 24 => 522381757057923 / 4000000000000
    | 25 => 2123452840672483 / 4000000000000
    | _ => 1418368088135597 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-18390041996 / 1000000000000) (-18390041995 / 1000000000000), orderedInterval (-43460899976 / 1000000000000) (-43460899975 / 1000000000000))
    | 1 => (orderedInterval (-30889558354 / 1000000000000) (-30889558353 / 1000000000000), orderedInterval (-45457483614 / 1000000000000) (-45457483613 / 1000000000000))
    | 2 => (orderedInterval (43220616028 / 1000000000000) (43220616124 / 1000000000000), orderedInterval (1990884394 / 1000000000000) (1990884490 / 1000000000000))
    | 3 => (orderedInterval (-64365384850 / 1000000000000) (-64365349526 / 1000000000000), orderedInterval (79464743882 / 1000000000000) (79464779205 / 1000000000000))
    | 4 => (orderedInterval (48145920066 / 1000000000000) (48146018651 / 1000000000000), orderedInterval (-39441901349 / 1000000000000) (-39441802765 / 1000000000000))
    | 5 => (orderedInterval (29720842518 / 1000000000000) (29720888497 / 1000000000000), orderedInterval (-23251947342 / 1000000000000) (-23251901363 / 1000000000000))
    | 6 => (orderedInterval (-24258443568 / 1000000000000) (-24258443567 / 1000000000000), orderedInterval (-36605099636 / 1000000000000) (-36605099635 / 1000000000000))
    | 7 => (orderedInterval (6291592937 / 1000000000000) (6291592938 / 1000000000000), orderedInterval (32970123403 / 1000000000000) (32970123404 / 1000000000000))
    | 8 => (orderedInterval (31845945717 / 1000000000000) (31846022921 / 1000000000000), orderedInterval (-22749928478 / 1000000000000) (-22749851274 / 1000000000000))
    | 9 => (orderedInterval (-31306094069 / 1000000000000) (-31306093829 / 1000000000000), orderedInterval (-4115970981 / 1000000000000) (-4115970742 / 1000000000000))
    | 10 => (orderedInterval (-40495254113 / 1000000000000) (-40495250715 / 1000000000000), orderedInterval (9401641150 / 1000000000000) (9401644547 / 1000000000000))
    | 11 => (orderedInterval (30654031407 / 1000000000000) (30654031533 / 1000000000000), orderedInterval (5780079599 / 1000000000000) (5780079724 / 1000000000000))
    | 12 => (orderedInterval (21457986024 / 1000000000000) (21457989532 / 1000000000000), orderedInterval (-24128103835 / 1000000000000) (-24128100327 / 1000000000000))
    | 13 => (orderedInterval (-8046301055 / 1000000000000) (-8046301054 / 1000000000000), orderedInterval (-37340900627 / 1000000000000) (-37340900626 / 1000000000000))
    | 14 => (orderedInterval (-31745687514 / 1000000000000) (-31745612938 / 1000000000000), orderedInterval (16753690021 / 1000000000000) (16753764597 / 1000000000000))
    | 15 => (orderedInterval (-39196353740 / 1000000000000) (-39196353626 / 1000000000000), orderedInterval (-2754735121 / 1000000000000) (-2754735006 / 1000000000000))
    | 16 => (orderedInterval (23851431055 / 1000000000000) (23851431056 / 1000000000000), orderedInterval (34302081847 / 1000000000000) (34302081848 / 1000000000000))
    | 17 => (orderedInterval (26369077147 / 1000000000000) (26369077148 / 1000000000000), orderedInterval (22573697974 / 1000000000000) (22573697975 / 1000000000000))
    | 18 => (orderedInterval (-27776173676 / 1000000000000) (-27776173675 / 1000000000000), orderedInterval (-37482941130 / 1000000000000) (-37482941129 / 1000000000000))
    | 19 => (orderedInterval (-7472901645 / 1000000000000) (-7472901643 / 1000000000000), orderedInterval (-50143201020 / 1000000000000) (-50143201019 / 1000000000000))
    | 20 => (orderedInterval (-63067841988 / 1000000000000) (-63067841421 / 1000000000000), orderedInterval (11700618394 / 1000000000000) (11700618961 / 1000000000000))
    | 21 => (orderedInterval (58354870579 / 1000000000000) (58354919426 / 1000000000000), orderedInterval (-65438371388 / 1000000000000) (-65438322541 / 1000000000000))
    | 22 => (orderedInterval (37614474180 / 1000000000000) (37614474181 / 1000000000000), orderedInterval (37327923158 / 1000000000000) (37327923159 / 1000000000000))
    | 23 => (orderedInterval (44565983980 / 1000000000000) (44565985627 / 1000000000000), orderedInterval (-8738343663 / 1000000000000) (-8738342016 / 1000000000000))
    | 24 => (orderedInterval (-37500791753 / 1000000000000) (-37500783424 / 1000000000000), orderedInterval (59037146478 / 1000000000000) (59037154807 / 1000000000000))
    | 25 => (orderedInterval (-22813829515 / 1000000000000) (-22813829514 / 1000000000000), orderedInterval (-26031256601 / 1000000000000) (-26031256600 / 1000000000000))
    | _ => (orderedInterval (-15602248071 / 1000000000000) (-15602248070 / 1000000000000), orderedInterval (-39372537149 / 1000000000000) (-39372537148 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-5040764615 / 1000000000000) (-5040764589 / 1000000000000)
      | 1 => orderedInterval (343362701 / 1000000000000) (343369987 / 1000000000000)
      | 2 => orderedInterval (575595769 / 1000000000000) (575597651 / 1000000000000)
      | 3 => orderedInterval (6920000911 / 1000000000000) (6920001336 / 1000000000000)
      | 4 => orderedInterval (-987613149 / 1000000000000) (-987612674 / 1000000000000)
      | 5 => orderedInterval (-1142412180 / 1000000000000) (-1142412151 / 1000000000000)
      | 6 => orderedInterval (2810975419 / 1000000000000) (2810975510 / 1000000000000)
      | 7 => orderedInterval (-5346371596 / 1000000000000) (-5346370533 / 1000000000000)
      | _ => orderedInterval (4558414769 / 1000000000000) (4558414899 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-17399241866 / 1000000000000) (-17399241836 / 1000000000000)
      | 1 => orderedInterval (1574482227 / 1000000000000) (1574489551 / 1000000000000)
      | 2 => orderedInterval (-2813421641 / 1000000000000) (-2813418893 / 1000000000000)
      | 3 => orderedInterval (4417016070 / 1000000000000) (4417016766 / 1000000000000)
      | 4 => orderedInterval (-4608285944 / 1000000000000) (-4608285099 / 1000000000000)
      | 5 => orderedInterval (-1481736624 / 1000000000000) (-1481736582 / 1000000000000)
      | 6 => orderedInterval (8797625651 / 1000000000000) (8797625728 / 1000000000000)
      | 7 => orderedInterval (406113561 / 1000000000000) (406113992 / 1000000000000)
      | _ => orderedInterval (13277973879 / 1000000000000) (13277974014 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (3908684652 / 1000000000000) (3908684687 / 1000000000000)
      | 1 => orderedInterval (4568419448 / 1000000000000) (4568428778 / 1000000000000)
      | 2 => orderedInterval (-865257830 / 1000000000000) (-865253807 / 1000000000000)
      | 3 => orderedInterval (-45698208722 / 1000000000000) (-45698207491 / 1000000000000)
      | 4 => orderedInterval (3084379033 / 1000000000000) (3084380550 / 1000000000000)
      | 5 => orderedInterval (862722768 / 1000000000000) (862722830 / 1000000000000)
      | 6 => orderedInterval (-4390750521 / 1000000000000) (-4390750451 / 1000000000000)
      | 7 => orderedInterval (4623106333 / 1000000000000) (4623106590 / 1000000000000)
      | _ => orderedInterval (-10935667221 / 1000000000000) (-10935667045 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (17184390961 / 1000000000000) (17184391002 / 1000000000000)
      | 1 => orderedInterval (-6098035290 / 1000000000000) (-6098021888 / 1000000000000)
      | 2 => orderedInterval (9582146763 / 1000000000000) (9582152644 / 1000000000000)
      | 3 => orderedInterval (-19394522489 / 1000000000000) (-19394520154 / 1000000000000)
      | 4 => orderedInterval (8743604501 / 1000000000000) (8743607243 / 1000000000000)
      | 5 => orderedInterval (516167199 / 1000000000000) (516167294 / 1000000000000)
      | 6 => orderedInterval (-8308754150 / 1000000000000) (-8308754085 / 1000000000000)
      | 7 => orderedInterval (-472891476 / 1000000000000) (-472891261 / 1000000000000)
      | _ => orderedInterval (-27771402195 / 1000000000000) (-27771401936 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-2391118976 / 1000000000000) (-2391118928 / 1000000000000)
      | 1 => orderedInterval (-12519789140 / 1000000000000) (-12519768783 / 1000000000000)
      | 2 => orderedInterval (431220166 / 1000000000000) (431228792 / 1000000000000)
      | 3 => orderedInterval (250893671688 / 1000000000000) (250893676402 / 1000000000000)
      | 4 => orderedInterval (-10889226344 / 1000000000000) (-10889221330 / 1000000000000)
      | 5 => orderedInterval (2301922129 / 1000000000000) (2301922280 / 1000000000000)
      | 6 => orderedInterval (4980311285 / 1000000000000) (4980311347 / 1000000000000)
      | 7 => orderedInterval (-5018480766 / 1000000000000) (-5018480552 / 1000000000000)
      | _ => orderedInterval (29349584161 / 1000000000000) (29349584571 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (2691188029 / 1000000000000) (2691199436 / 1000000000000)
    | 1 => orderedInterval (2170525313 / 1000000000000) (2170537641 / 1000000000000)
    | 2 => orderedInterval (-44842572060 / 1000000000000) (-44842555359 / 1000000000000)
    | 3 => orderedInterval (-26019296176 / 1000000000000) (-26019271141 / 1000000000000)
    | _ => orderedInterval (257138094203 / 1000000000000) (257138133799 / 1000000000000)

theorem compactCertificate414_stateChecks0 :
    compactCertificate414.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 91 12 (571 / 2)) (orderedInterval (-18390041996 / 1000000000000) (-18390041995 / 1000000000000), orderedInterval (-43460899976 / 1000000000000) (-43460899975 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (841192031251471 / 4000000000000)) (orderedInterval (-30889558354 / 1000000000000) (-30889558353 / 1000000000000), orderedInterval (-45457483614 / 1000000000000) (-45457483613 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 108 12 (272024219525743 / 800000000000)) (orderedInterval (43220616028 / 1000000000000) (43220616124 / 1000000000000), orderedInterval (1990884394 / 1000000000000) (1990884490 / 1000000000000))) = true
  rfl'

theorem compactCertificate414_stateChecks1 :
    compactCertificate414.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 20 12 (245457736756397 / 4000000000000)) (orderedInterval (-64365384850 / 1000000000000) (-64365349526 / 1000000000000), orderedInterval (79464743882 / 1000000000000) (79464779205 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (659334007414409 / 4000000000000)) (orderedInterval (48145920066 / 1000000000000) (48146018651 / 1000000000000), orderedInterval (-39441901349 / 1000000000000) (-39441802765 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 143 12 (1790220088860453 / 4000000000000)) (orderedInterval (29720842518 / 1000000000000) (29720888497 / 1000000000000), orderedInterval (-23251947342 / 1000000000000) (-23251901363 / 1000000000000))) = true
  rfl'

theorem compactCertificate414_stateChecks2 :
    compactCertificate414.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 105 12 (1318668014829389 / 4000000000000)) (orderedInterval (-24258443568 / 1000000000000) (-24258443567 / 1000000000000), orderedInterval (-36605099636 / 1000000000000) (-36605099635 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 180 12 (2259560119386497 / 4000000000000)) (orderedInterval (6291592937 / 1000000000000) (6291592938 / 1000000000000), orderedInterval (32970123403 / 1000000000000) (32970123404 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 133 12 (1664381757057923 / 4000000000000)) (orderedInterval (31845945717 / 1000000000000) (31846022921 / 1000000000000), orderedInterval (-22749928478 / 1000000000000) (-22749851274 / 1000000000000))) = true
  rfl'

theorem compactCertificate414_stateChecks3 :
    compactCertificate414.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 203 12 (2553589630304429 / 4000000000000)) (orderedInterval (-31306094069 / 1000000000000) (-31306093829 / 1000000000000), orderedInterval (-4115970981 / 1000000000000) (-4115970742 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 117 12 (1474315660455941 / 4000000000000)) (orderedInterval (-40495254113 / 1000000000000) (-40495250715 / 1000000000000), orderedInterval (9401641150 / 1000000000000) (9401644547 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 208 12 (2616199011247369 / 4000000000000)) (orderedInterval (30654031407 / 1000000000000) (30654031533 / 1000000000000), orderedInterval (5780079599 / 1000000000000) (5780079724 / 1000000000000))) = true
  rfl'

theorem compactCertificate414_stateChecks4 :
    compactCertificate414.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 195 12 (2444392480717261 / 4000000000000)) (orderedInterval (21457986024 / 1000000000000) (21457989532 / 1000000000000), orderedInterval (-24128103835 / 1000000000000) (-24128100327 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 139 12 (1744433814546013 / 4000000000000)) (orderedInterval (-8046301055 / 1000000000000) (-8046301054 / 1000000000000), orderedInterval (-37340900627 / 1000000000000) (-37340900626 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 157 12 (1978002022243227 / 4000000000000)) (orderedInterval (-31745687514 / 1000000000000) (-31745612938 / 1000000000000), orderedInterval (16753690021 / 1000000000000) (16753764597 / 1000000000000))) = true
  rfl'

theorem compactCertificate414_stateChecks5 :
    compactCertificate414.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 131 12 (1649051869069163 / 4000000000000)) (orderedInterval (-39196353740 / 1000000000000) (-39196353626 / 1000000000000), orderedInterval (-2754735121 / 1000000000000) (-2754735006 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 116 12 (1456987337048423 / 4000000000000)) (orderedInterval (23851431055 / 1000000000000) (23851431056 / 1000000000000), orderedInterval (34302081847 / 1000000000000) (34302081848 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 168 12 (422291719085877 / 800000000000)) (orderedInterval (26369077147 / 1000000000000) (26369077148 / 1000000000000), orderedInterval (22573697974 / 1000000000000) (22573697975 / 1000000000000))) = true
  rfl'

theorem compactCertificate414_stateChecks6 :
    compactCertificate414.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 93 12 (1168081118987119 / 4000000000000)) (orderedInterval (-27776173676 / 1000000000000) (-27776173675 / 1000000000000), orderedInterval (-37482941130 / 1000000000000) (-37482941129 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (990195300709559 / 4000000000000)) (orderedInterval (-7472901645 / 1000000000000) (-7472901643 / 1000000000000), orderedInterval (-50143201020 / 1000000000000) (-50143201019 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (619618242942077 / 4000000000000)) (orderedInterval (-63067841988 / 1000000000000) (-63067841421 / 1000000000000), orderedInterval (11700618394 / 1000000000000) (11700618961 / 1000000000000))) = true
  rfl'

theorem compactCertificate414_stateChecks7 :
    compactCertificate414.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (333232751811459 / 4000000000000)) (orderedInterval (58354870579 / 1000000000000) (58354919426 / 1000000000000), orderedInterval (-65438371388 / 1000000000000) (-65438322541 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (904791744171377 / 4000000000000)) (orderedInterval (37614474180 / 1000000000000) (37614474181 / 1000000000000), orderedInterval (37327923158 / 1000000000000) (37327923159 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 98 12 (1235415773640529 / 4000000000000)) (orderedInterval (44565983980 / 1000000000000) (44565985627 / 1000000000000), orderedInterval (-8738343663 / 1000000000000) (-8738342016 / 1000000000000))) = true
  rfl'

theorem compactCertificate414_stateChecks8 :
    compactCertificate414.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (522381757057923 / 4000000000000)) (orderedInterval (-37500791753 / 1000000000000) (-37500783424 / 1000000000000), orderedInterval (59037146478 / 1000000000000) (59037154807 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 169 12 (2123452840672483 / 4000000000000)) (orderedInterval (-22813829515 / 1000000000000) (-22813829514 / 1000000000000), orderedInterval (-26031256601 / 1000000000000) (-26031256600 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 113 12 (1418368088135597 / 4000000000000)) (orderedInterval (-15602248071 / 1000000000000) (-15602248070 / 1000000000000), orderedInterval (-39372537149 / 1000000000000) (-39372537148 / 1000000000000))) = true
  rfl'

theorem compactCertificate414_states : ∀ j,
    BesselStateValid (compactCertificate414.point j) (compactCertificate414.state j) :=
  compactCertificate414.statesValid_of_checks3 compactCertificate414_stateChecks0
    compactCertificate414_stateChecks1 compactCertificate414_stateChecks2
    compactCertificate414_stateChecks3 compactCertificate414_stateChecks4
    compactCertificate414_stateChecks5 compactCertificate414_stateChecks6
    compactCertificate414_stateChecks7 compactCertificate414_stateChecks8

theorem compactCertificate414_chunkChecks0_0 :
    compactCertificate414.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (571 / 2) 0 (IntervalRat.scale (571 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-18390041996 / 1000000000000) (-18390041995 / 1000000000000), orderedInterval (-43460899976 / 1000000000000) (-43460899975 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (841192031251471 / 4000000000000) 0 (IntervalRat.scale (571 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-30889558354 / 1000000000000) (-30889558353 / 1000000000000), orderedInterval (-45457483614 / 1000000000000) (-45457483613 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (272024219525743 / 800000000000) 0 (IntervalRat.scale (571 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (43220616028 / 1000000000000) (43220616124 / 1000000000000), orderedInterval (1990884394 / 1000000000000) (1990884490 / 1000000000000)))) (orderedInterval (-5040764615 / 1000000000000) (-5040764589 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (245457736756397 / 4000000000000) 0 (IntervalRat.scale (571 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-64365384850 / 1000000000000) (-64365349526 / 1000000000000), orderedInterval (79464743882 / 1000000000000) (79464779205 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (659334007414409 / 4000000000000) 0 (IntervalRat.scale (571 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (48145920066 / 1000000000000) (48146018651 / 1000000000000), orderedInterval (-39441901349 / 1000000000000) (-39441802765 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1790220088860453 / 4000000000000) 0 (IntervalRat.scale (571 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29720842518 / 1000000000000) (29720888497 / 1000000000000), orderedInterval (-23251947342 / 1000000000000) (-23251901363 / 1000000000000)))) (orderedInterval (343362701 / 1000000000000) (343369987 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1318668014829389 / 4000000000000) 0 (IntervalRat.scale (571 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-24258443568 / 1000000000000) (-24258443567 / 1000000000000), orderedInterval (-36605099636 / 1000000000000) (-36605099635 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2259560119386497 / 4000000000000) 0 (IntervalRat.scale (571 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (6291592937 / 1000000000000) (6291592938 / 1000000000000), orderedInterval (32970123403 / 1000000000000) (32970123404 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1664381757057923 / 4000000000000) 0 (IntervalRat.scale (571 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (31845945717 / 1000000000000) (31846022921 / 1000000000000), orderedInterval (-22749928478 / 1000000000000) (-22749851274 / 1000000000000)))) (orderedInterval (575595769 / 1000000000000) (575597651 / 1000000000000))) = true
  rfl'

theorem compactCertificate414_chunkChecks0_1 :
    compactCertificate414.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2553589630304429 / 4000000000000) 0 (IntervalRat.scale (571 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-31306094069 / 1000000000000) (-31306093829 / 1000000000000), orderedInterval (-4115970981 / 1000000000000) (-4115970742 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1474315660455941 / 4000000000000) 0 (IntervalRat.scale (571 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-40495254113 / 1000000000000) (-40495250715 / 1000000000000), orderedInterval (9401641150 / 1000000000000) (9401644547 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2616199011247369 / 4000000000000) 0 (IntervalRat.scale (571 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (30654031407 / 1000000000000) (30654031533 / 1000000000000), orderedInterval (5780079599 / 1000000000000) (5780079724 / 1000000000000)))) (orderedInterval (6920000911 / 1000000000000) (6920001336 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2444392480717261 / 4000000000000) 0 (IntervalRat.scale (571 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (21457986024 / 1000000000000) (21457989532 / 1000000000000), orderedInterval (-24128103835 / 1000000000000) (-24128100327 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1744433814546013 / 4000000000000) 0 (IntervalRat.scale (571 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-8046301055 / 1000000000000) (-8046301054 / 1000000000000), orderedInterval (-37340900627 / 1000000000000) (-37340900626 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1978002022243227 / 4000000000000) 0 (IntervalRat.scale (571 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-31745687514 / 1000000000000) (-31745612938 / 1000000000000), orderedInterval (16753690021 / 1000000000000) (16753764597 / 1000000000000)))) (orderedInterval (-987613149 / 1000000000000) (-987612674 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1649051869069163 / 4000000000000) 0 (IntervalRat.scale (571 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-39196353740 / 1000000000000) (-39196353626 / 1000000000000), orderedInterval (-2754735121 / 1000000000000) (-2754735006 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1456987337048423 / 4000000000000) 0 (IntervalRat.scale (571 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (23851431055 / 1000000000000) (23851431056 / 1000000000000), orderedInterval (34302081847 / 1000000000000) (34302081848 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (422291719085877 / 800000000000) 0 (IntervalRat.scale (571 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (26369077147 / 1000000000000) (26369077148 / 1000000000000), orderedInterval (22573697974 / 1000000000000) (22573697975 / 1000000000000)))) (orderedInterval (-1142412180 / 1000000000000) (-1142412151 / 1000000000000))) = true
  rfl'

theorem compactCertificate414_chunkChecks0_2 :
    compactCertificate414.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1168081118987119 / 4000000000000) 0 (IntervalRat.scale (571 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-27776173676 / 1000000000000) (-27776173675 / 1000000000000), orderedInterval (-37482941130 / 1000000000000) (-37482941129 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (990195300709559 / 4000000000000) 0 (IntervalRat.scale (571 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-7472901645 / 1000000000000) (-7472901643 / 1000000000000), orderedInterval (-50143201020 / 1000000000000) (-50143201019 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (619618242942077 / 4000000000000) 0 (IntervalRat.scale (571 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-63067841988 / 1000000000000) (-63067841421 / 1000000000000), orderedInterval (11700618394 / 1000000000000) (11700618961 / 1000000000000)))) (orderedInterval (2810975419 / 1000000000000) (2810975510 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (333232751811459 / 4000000000000) 0 (IntervalRat.scale (571 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (58354870579 / 1000000000000) (58354919426 / 1000000000000), orderedInterval (-65438371388 / 1000000000000) (-65438322541 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (904791744171377 / 4000000000000) 0 (IntervalRat.scale (571 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (37614474180 / 1000000000000) (37614474181 / 1000000000000), orderedInterval (37327923158 / 1000000000000) (37327923159 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1235415773640529 / 4000000000000) 0 (IntervalRat.scale (571 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (44565983980 / 1000000000000) (44565985627 / 1000000000000), orderedInterval (-8738343663 / 1000000000000) (-8738342016 / 1000000000000)))) (orderedInterval (-5346371596 / 1000000000000) (-5346370533 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (522381757057923 / 4000000000000) 0 (IntervalRat.scale (571 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-37500791753 / 1000000000000) (-37500783424 / 1000000000000), orderedInterval (59037146478 / 1000000000000) (59037154807 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2123452840672483 / 4000000000000) 0 (IntervalRat.scale (571 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-22813829515 / 1000000000000) (-22813829514 / 1000000000000), orderedInterval (-26031256601 / 1000000000000) (-26031256600 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1418368088135597 / 4000000000000) 0 (IntervalRat.scale (571 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-15602248071 / 1000000000000) (-15602248070 / 1000000000000), orderedInterval (-39372537149 / 1000000000000) (-39372537148 / 1000000000000)))) (orderedInterval (4558414769 / 1000000000000) (4558414899 / 1000000000000))) = true
  rfl'

theorem compactCertificate414_chunkChecks0 :
    compactCertificate414.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate414.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate414_chunkChecks0_0
    compactCertificate414_chunkChecks0_1 compactCertificate414_chunkChecks0_2

theorem compactCertificate414_chunkChecks1_0 :
    compactCertificate414.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (571 / 2) 1 (IntervalRat.scale (571 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-18390041996 / 1000000000000) (-18390041995 / 1000000000000), orderedInterval (-43460899976 / 1000000000000) (-43460899975 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (841192031251471 / 4000000000000) 1 (IntervalRat.scale (571 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-30889558354 / 1000000000000) (-30889558353 / 1000000000000), orderedInterval (-45457483614 / 1000000000000) (-45457483613 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (272024219525743 / 800000000000) 1 (IntervalRat.scale (571 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (43220616028 / 1000000000000) (43220616124 / 1000000000000), orderedInterval (1990884394 / 1000000000000) (1990884490 / 1000000000000)))) (orderedInterval (-17399241866 / 1000000000000) (-17399241836 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (245457736756397 / 4000000000000) 1 (IntervalRat.scale (571 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-64365384850 / 1000000000000) (-64365349526 / 1000000000000), orderedInterval (79464743882 / 1000000000000) (79464779205 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (659334007414409 / 4000000000000) 1 (IntervalRat.scale (571 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (48145920066 / 1000000000000) (48146018651 / 1000000000000), orderedInterval (-39441901349 / 1000000000000) (-39441802765 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1790220088860453 / 4000000000000) 1 (IntervalRat.scale (571 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29720842518 / 1000000000000) (29720888497 / 1000000000000), orderedInterval (-23251947342 / 1000000000000) (-23251901363 / 1000000000000)))) (orderedInterval (1574482227 / 1000000000000) (1574489551 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1318668014829389 / 4000000000000) 1 (IntervalRat.scale (571 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-24258443568 / 1000000000000) (-24258443567 / 1000000000000), orderedInterval (-36605099636 / 1000000000000) (-36605099635 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2259560119386497 / 4000000000000) 1 (IntervalRat.scale (571 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (6291592937 / 1000000000000) (6291592938 / 1000000000000), orderedInterval (32970123403 / 1000000000000) (32970123404 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1664381757057923 / 4000000000000) 1 (IntervalRat.scale (571 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (31845945717 / 1000000000000) (31846022921 / 1000000000000), orderedInterval (-22749928478 / 1000000000000) (-22749851274 / 1000000000000)))) (orderedInterval (-2813421641 / 1000000000000) (-2813418893 / 1000000000000))) = true
  rfl'

theorem compactCertificate414_chunkChecks1_1 :
    compactCertificate414.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2553589630304429 / 4000000000000) 1 (IntervalRat.scale (571 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-31306094069 / 1000000000000) (-31306093829 / 1000000000000), orderedInterval (-4115970981 / 1000000000000) (-4115970742 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1474315660455941 / 4000000000000) 1 (IntervalRat.scale (571 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-40495254113 / 1000000000000) (-40495250715 / 1000000000000), orderedInterval (9401641150 / 1000000000000) (9401644547 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2616199011247369 / 4000000000000) 1 (IntervalRat.scale (571 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (30654031407 / 1000000000000) (30654031533 / 1000000000000), orderedInterval (5780079599 / 1000000000000) (5780079724 / 1000000000000)))) (orderedInterval (4417016070 / 1000000000000) (4417016766 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2444392480717261 / 4000000000000) 1 (IntervalRat.scale (571 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (21457986024 / 1000000000000) (21457989532 / 1000000000000), orderedInterval (-24128103835 / 1000000000000) (-24128100327 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1744433814546013 / 4000000000000) 1 (IntervalRat.scale (571 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-8046301055 / 1000000000000) (-8046301054 / 1000000000000), orderedInterval (-37340900627 / 1000000000000) (-37340900626 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1978002022243227 / 4000000000000) 1 (IntervalRat.scale (571 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-31745687514 / 1000000000000) (-31745612938 / 1000000000000), orderedInterval (16753690021 / 1000000000000) (16753764597 / 1000000000000)))) (orderedInterval (-4608285944 / 1000000000000) (-4608285099 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1649051869069163 / 4000000000000) 1 (IntervalRat.scale (571 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-39196353740 / 1000000000000) (-39196353626 / 1000000000000), orderedInterval (-2754735121 / 1000000000000) (-2754735006 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1456987337048423 / 4000000000000) 1 (IntervalRat.scale (571 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (23851431055 / 1000000000000) (23851431056 / 1000000000000), orderedInterval (34302081847 / 1000000000000) (34302081848 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (422291719085877 / 800000000000) 1 (IntervalRat.scale (571 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (26369077147 / 1000000000000) (26369077148 / 1000000000000), orderedInterval (22573697974 / 1000000000000) (22573697975 / 1000000000000)))) (orderedInterval (-1481736624 / 1000000000000) (-1481736582 / 1000000000000))) = true
  rfl'

theorem compactCertificate414_chunkChecks1_2 :
    compactCertificate414.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1168081118987119 / 4000000000000) 1 (IntervalRat.scale (571 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-27776173676 / 1000000000000) (-27776173675 / 1000000000000), orderedInterval (-37482941130 / 1000000000000) (-37482941129 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (990195300709559 / 4000000000000) 1 (IntervalRat.scale (571 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-7472901645 / 1000000000000) (-7472901643 / 1000000000000), orderedInterval (-50143201020 / 1000000000000) (-50143201019 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (619618242942077 / 4000000000000) 1 (IntervalRat.scale (571 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-63067841988 / 1000000000000) (-63067841421 / 1000000000000), orderedInterval (11700618394 / 1000000000000) (11700618961 / 1000000000000)))) (orderedInterval (8797625651 / 1000000000000) (8797625728 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (333232751811459 / 4000000000000) 1 (IntervalRat.scale (571 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (58354870579 / 1000000000000) (58354919426 / 1000000000000), orderedInterval (-65438371388 / 1000000000000) (-65438322541 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (904791744171377 / 4000000000000) 1 (IntervalRat.scale (571 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (37614474180 / 1000000000000) (37614474181 / 1000000000000), orderedInterval (37327923158 / 1000000000000) (37327923159 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1235415773640529 / 4000000000000) 1 (IntervalRat.scale (571 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (44565983980 / 1000000000000) (44565985627 / 1000000000000), orderedInterval (-8738343663 / 1000000000000) (-8738342016 / 1000000000000)))) (orderedInterval (406113561 / 1000000000000) (406113992 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (522381757057923 / 4000000000000) 1 (IntervalRat.scale (571 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-37500791753 / 1000000000000) (-37500783424 / 1000000000000), orderedInterval (59037146478 / 1000000000000) (59037154807 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2123452840672483 / 4000000000000) 1 (IntervalRat.scale (571 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-22813829515 / 1000000000000) (-22813829514 / 1000000000000), orderedInterval (-26031256601 / 1000000000000) (-26031256600 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1418368088135597 / 4000000000000) 1 (IntervalRat.scale (571 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-15602248071 / 1000000000000) (-15602248070 / 1000000000000), orderedInterval (-39372537149 / 1000000000000) (-39372537148 / 1000000000000)))) (orderedInterval (13277973879 / 1000000000000) (13277974014 / 1000000000000))) = true
  rfl'

theorem compactCertificate414_chunkChecks1 :
    compactCertificate414.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate414.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate414_chunkChecks1_0
    compactCertificate414_chunkChecks1_1 compactCertificate414_chunkChecks1_2

theorem compactCertificate414_chunkChecks2_0 :
    compactCertificate414.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (571 / 2) 2 (IntervalRat.scale (571 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-18390041996 / 1000000000000) (-18390041995 / 1000000000000), orderedInterval (-43460899976 / 1000000000000) (-43460899975 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (841192031251471 / 4000000000000) 2 (IntervalRat.scale (571 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-30889558354 / 1000000000000) (-30889558353 / 1000000000000), orderedInterval (-45457483614 / 1000000000000) (-45457483613 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (272024219525743 / 800000000000) 2 (IntervalRat.scale (571 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (43220616028 / 1000000000000) (43220616124 / 1000000000000), orderedInterval (1990884394 / 1000000000000) (1990884490 / 1000000000000)))) (orderedInterval (3908684652 / 1000000000000) (3908684687 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (245457736756397 / 4000000000000) 2 (IntervalRat.scale (571 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-64365384850 / 1000000000000) (-64365349526 / 1000000000000), orderedInterval (79464743882 / 1000000000000) (79464779205 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (659334007414409 / 4000000000000) 2 (IntervalRat.scale (571 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (48145920066 / 1000000000000) (48146018651 / 1000000000000), orderedInterval (-39441901349 / 1000000000000) (-39441802765 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1790220088860453 / 4000000000000) 2 (IntervalRat.scale (571 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29720842518 / 1000000000000) (29720888497 / 1000000000000), orderedInterval (-23251947342 / 1000000000000) (-23251901363 / 1000000000000)))) (orderedInterval (4568419448 / 1000000000000) (4568428778 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1318668014829389 / 4000000000000) 2 (IntervalRat.scale (571 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-24258443568 / 1000000000000) (-24258443567 / 1000000000000), orderedInterval (-36605099636 / 1000000000000) (-36605099635 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2259560119386497 / 4000000000000) 2 (IntervalRat.scale (571 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (6291592937 / 1000000000000) (6291592938 / 1000000000000), orderedInterval (32970123403 / 1000000000000) (32970123404 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1664381757057923 / 4000000000000) 2 (IntervalRat.scale (571 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (31845945717 / 1000000000000) (31846022921 / 1000000000000), orderedInterval (-22749928478 / 1000000000000) (-22749851274 / 1000000000000)))) (orderedInterval (-865257830 / 1000000000000) (-865253807 / 1000000000000))) = true
  rfl'

theorem compactCertificate414_chunkChecks2_1 :
    compactCertificate414.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2553589630304429 / 4000000000000) 2 (IntervalRat.scale (571 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-31306094069 / 1000000000000) (-31306093829 / 1000000000000), orderedInterval (-4115970981 / 1000000000000) (-4115970742 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1474315660455941 / 4000000000000) 2 (IntervalRat.scale (571 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-40495254113 / 1000000000000) (-40495250715 / 1000000000000), orderedInterval (9401641150 / 1000000000000) (9401644547 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2616199011247369 / 4000000000000) 2 (IntervalRat.scale (571 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (30654031407 / 1000000000000) (30654031533 / 1000000000000), orderedInterval (5780079599 / 1000000000000) (5780079724 / 1000000000000)))) (orderedInterval (-45698208722 / 1000000000000) (-45698207491 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2444392480717261 / 4000000000000) 2 (IntervalRat.scale (571 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (21457986024 / 1000000000000) (21457989532 / 1000000000000), orderedInterval (-24128103835 / 1000000000000) (-24128100327 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1744433814546013 / 4000000000000) 2 (IntervalRat.scale (571 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-8046301055 / 1000000000000) (-8046301054 / 1000000000000), orderedInterval (-37340900627 / 1000000000000) (-37340900626 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1978002022243227 / 4000000000000) 2 (IntervalRat.scale (571 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-31745687514 / 1000000000000) (-31745612938 / 1000000000000), orderedInterval (16753690021 / 1000000000000) (16753764597 / 1000000000000)))) (orderedInterval (3084379033 / 1000000000000) (3084380550 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1649051869069163 / 4000000000000) 2 (IntervalRat.scale (571 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-39196353740 / 1000000000000) (-39196353626 / 1000000000000), orderedInterval (-2754735121 / 1000000000000) (-2754735006 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1456987337048423 / 4000000000000) 2 (IntervalRat.scale (571 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (23851431055 / 1000000000000) (23851431056 / 1000000000000), orderedInterval (34302081847 / 1000000000000) (34302081848 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (422291719085877 / 800000000000) 2 (IntervalRat.scale (571 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (26369077147 / 1000000000000) (26369077148 / 1000000000000), orderedInterval (22573697974 / 1000000000000) (22573697975 / 1000000000000)))) (orderedInterval (862722768 / 1000000000000) (862722830 / 1000000000000))) = true
  rfl'

theorem compactCertificate414_chunkChecks2_2 :
    compactCertificate414.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1168081118987119 / 4000000000000) 2 (IntervalRat.scale (571 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-27776173676 / 1000000000000) (-27776173675 / 1000000000000), orderedInterval (-37482941130 / 1000000000000) (-37482941129 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (990195300709559 / 4000000000000) 2 (IntervalRat.scale (571 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-7472901645 / 1000000000000) (-7472901643 / 1000000000000), orderedInterval (-50143201020 / 1000000000000) (-50143201019 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (619618242942077 / 4000000000000) 2 (IntervalRat.scale (571 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-63067841988 / 1000000000000) (-63067841421 / 1000000000000), orderedInterval (11700618394 / 1000000000000) (11700618961 / 1000000000000)))) (orderedInterval (-4390750521 / 1000000000000) (-4390750451 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (333232751811459 / 4000000000000) 2 (IntervalRat.scale (571 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (58354870579 / 1000000000000) (58354919426 / 1000000000000), orderedInterval (-65438371388 / 1000000000000) (-65438322541 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (904791744171377 / 4000000000000) 2 (IntervalRat.scale (571 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (37614474180 / 1000000000000) (37614474181 / 1000000000000), orderedInterval (37327923158 / 1000000000000) (37327923159 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1235415773640529 / 4000000000000) 2 (IntervalRat.scale (571 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (44565983980 / 1000000000000) (44565985627 / 1000000000000), orderedInterval (-8738343663 / 1000000000000) (-8738342016 / 1000000000000)))) (orderedInterval (4623106333 / 1000000000000) (4623106590 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (522381757057923 / 4000000000000) 2 (IntervalRat.scale (571 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-37500791753 / 1000000000000) (-37500783424 / 1000000000000), orderedInterval (59037146478 / 1000000000000) (59037154807 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2123452840672483 / 4000000000000) 2 (IntervalRat.scale (571 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-22813829515 / 1000000000000) (-22813829514 / 1000000000000), orderedInterval (-26031256601 / 1000000000000) (-26031256600 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1418368088135597 / 4000000000000) 2 (IntervalRat.scale (571 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-15602248071 / 1000000000000) (-15602248070 / 1000000000000), orderedInterval (-39372537149 / 1000000000000) (-39372537148 / 1000000000000)))) (orderedInterval (-10935667221 / 1000000000000) (-10935667045 / 1000000000000))) = true
  rfl'

theorem compactCertificate414_chunkChecks2 :
    compactCertificate414.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate414.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate414_chunkChecks2_0
    compactCertificate414_chunkChecks2_1 compactCertificate414_chunkChecks2_2

theorem compactCertificate414_chunkChecks3_0 :
    compactCertificate414.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (571 / 2) 3 (IntervalRat.scale (571 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-18390041996 / 1000000000000) (-18390041995 / 1000000000000), orderedInterval (-43460899976 / 1000000000000) (-43460899975 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (841192031251471 / 4000000000000) 3 (IntervalRat.scale (571 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-30889558354 / 1000000000000) (-30889558353 / 1000000000000), orderedInterval (-45457483614 / 1000000000000) (-45457483613 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (272024219525743 / 800000000000) 3 (IntervalRat.scale (571 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (43220616028 / 1000000000000) (43220616124 / 1000000000000), orderedInterval (1990884394 / 1000000000000) (1990884490 / 1000000000000)))) (orderedInterval (17184390961 / 1000000000000) (17184391002 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (245457736756397 / 4000000000000) 3 (IntervalRat.scale (571 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-64365384850 / 1000000000000) (-64365349526 / 1000000000000), orderedInterval (79464743882 / 1000000000000) (79464779205 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (659334007414409 / 4000000000000) 3 (IntervalRat.scale (571 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (48145920066 / 1000000000000) (48146018651 / 1000000000000), orderedInterval (-39441901349 / 1000000000000) (-39441802765 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1790220088860453 / 4000000000000) 3 (IntervalRat.scale (571 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29720842518 / 1000000000000) (29720888497 / 1000000000000), orderedInterval (-23251947342 / 1000000000000) (-23251901363 / 1000000000000)))) (orderedInterval (-6098035290 / 1000000000000) (-6098021888 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1318668014829389 / 4000000000000) 3 (IntervalRat.scale (571 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-24258443568 / 1000000000000) (-24258443567 / 1000000000000), orderedInterval (-36605099636 / 1000000000000) (-36605099635 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2259560119386497 / 4000000000000) 3 (IntervalRat.scale (571 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (6291592937 / 1000000000000) (6291592938 / 1000000000000), orderedInterval (32970123403 / 1000000000000) (32970123404 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1664381757057923 / 4000000000000) 3 (IntervalRat.scale (571 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (31845945717 / 1000000000000) (31846022921 / 1000000000000), orderedInterval (-22749928478 / 1000000000000) (-22749851274 / 1000000000000)))) (orderedInterval (9582146763 / 1000000000000) (9582152644 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate414_chunkChecks3_1 :
    compactCertificate414.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2553589630304429 / 4000000000000) 3 (IntervalRat.scale (571 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-31306094069 / 1000000000000) (-31306093829 / 1000000000000), orderedInterval (-4115970981 / 1000000000000) (-4115970742 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1474315660455941 / 4000000000000) 3 (IntervalRat.scale (571 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-40495254113 / 1000000000000) (-40495250715 / 1000000000000), orderedInterval (9401641150 / 1000000000000) (9401644547 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2616199011247369 / 4000000000000) 3 (IntervalRat.scale (571 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (30654031407 / 1000000000000) (30654031533 / 1000000000000), orderedInterval (5780079599 / 1000000000000) (5780079724 / 1000000000000)))) (orderedInterval (-19394522489 / 1000000000000) (-19394520154 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2444392480717261 / 4000000000000) 3 (IntervalRat.scale (571 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (21457986024 / 1000000000000) (21457989532 / 1000000000000), orderedInterval (-24128103835 / 1000000000000) (-24128100327 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1744433814546013 / 4000000000000) 3 (IntervalRat.scale (571 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-8046301055 / 1000000000000) (-8046301054 / 1000000000000), orderedInterval (-37340900627 / 1000000000000) (-37340900626 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1978002022243227 / 4000000000000) 3 (IntervalRat.scale (571 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-31745687514 / 1000000000000) (-31745612938 / 1000000000000), orderedInterval (16753690021 / 1000000000000) (16753764597 / 1000000000000)))) (orderedInterval (8743604501 / 1000000000000) (8743607243 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1649051869069163 / 4000000000000) 3 (IntervalRat.scale (571 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-39196353740 / 1000000000000) (-39196353626 / 1000000000000), orderedInterval (-2754735121 / 1000000000000) (-2754735006 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1456987337048423 / 4000000000000) 3 (IntervalRat.scale (571 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (23851431055 / 1000000000000) (23851431056 / 1000000000000), orderedInterval (34302081847 / 1000000000000) (34302081848 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (422291719085877 / 800000000000) 3 (IntervalRat.scale (571 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (26369077147 / 1000000000000) (26369077148 / 1000000000000), orderedInterval (22573697974 / 1000000000000) (22573697975 / 1000000000000)))) (orderedInterval (516167199 / 1000000000000) (516167294 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate414_chunkChecks3_2 :
    compactCertificate414.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1168081118987119 / 4000000000000) 3 (IntervalRat.scale (571 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-27776173676 / 1000000000000) (-27776173675 / 1000000000000), orderedInterval (-37482941130 / 1000000000000) (-37482941129 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (990195300709559 / 4000000000000) 3 (IntervalRat.scale (571 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-7472901645 / 1000000000000) (-7472901643 / 1000000000000), orderedInterval (-50143201020 / 1000000000000) (-50143201019 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (619618242942077 / 4000000000000) 3 (IntervalRat.scale (571 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-63067841988 / 1000000000000) (-63067841421 / 1000000000000), orderedInterval (11700618394 / 1000000000000) (11700618961 / 1000000000000)))) (orderedInterval (-8308754150 / 1000000000000) (-8308754085 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (333232751811459 / 4000000000000) 3 (IntervalRat.scale (571 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (58354870579 / 1000000000000) (58354919426 / 1000000000000), orderedInterval (-65438371388 / 1000000000000) (-65438322541 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (904791744171377 / 4000000000000) 3 (IntervalRat.scale (571 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (37614474180 / 1000000000000) (37614474181 / 1000000000000), orderedInterval (37327923158 / 1000000000000) (37327923159 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1235415773640529 / 4000000000000) 3 (IntervalRat.scale (571 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (44565983980 / 1000000000000) (44565985627 / 1000000000000), orderedInterval (-8738343663 / 1000000000000) (-8738342016 / 1000000000000)))) (orderedInterval (-472891476 / 1000000000000) (-472891261 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (522381757057923 / 4000000000000) 3 (IntervalRat.scale (571 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-37500791753 / 1000000000000) (-37500783424 / 1000000000000), orderedInterval (59037146478 / 1000000000000) (59037154807 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2123452840672483 / 4000000000000) 3 (IntervalRat.scale (571 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-22813829515 / 1000000000000) (-22813829514 / 1000000000000), orderedInterval (-26031256601 / 1000000000000) (-26031256600 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1418368088135597 / 4000000000000) 3 (IntervalRat.scale (571 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-15602248071 / 1000000000000) (-15602248070 / 1000000000000), orderedInterval (-39372537149 / 1000000000000) (-39372537148 / 1000000000000)))) (orderedInterval (-27771402195 / 1000000000000) (-27771401936 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate414_chunkChecks3 :
    compactCertificate414.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate414.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate414_chunkChecks3_0
    compactCertificate414_chunkChecks3_1 compactCertificate414_chunkChecks3_2

theorem compactCertificate414_chunkChecks4_0 :
    compactCertificate414.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (571 / 2) 4 (IntervalRat.scale (571 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-18390041996 / 1000000000000) (-18390041995 / 1000000000000), orderedInterval (-43460899976 / 1000000000000) (-43460899975 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (841192031251471 / 4000000000000) 4 (IntervalRat.scale (571 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-30889558354 / 1000000000000) (-30889558353 / 1000000000000), orderedInterval (-45457483614 / 1000000000000) (-45457483613 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (272024219525743 / 800000000000) 4 (IntervalRat.scale (571 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (43220616028 / 1000000000000) (43220616124 / 1000000000000), orderedInterval (1990884394 / 1000000000000) (1990884490 / 1000000000000)))) (orderedInterval (-2391118976 / 1000000000000) (-2391118928 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (245457736756397 / 4000000000000) 4 (IntervalRat.scale (571 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-64365384850 / 1000000000000) (-64365349526 / 1000000000000), orderedInterval (79464743882 / 1000000000000) (79464779205 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (659334007414409 / 4000000000000) 4 (IntervalRat.scale (571 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (48145920066 / 1000000000000) (48146018651 / 1000000000000), orderedInterval (-39441901349 / 1000000000000) (-39441802765 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1790220088860453 / 4000000000000) 4 (IntervalRat.scale (571 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29720842518 / 1000000000000) (29720888497 / 1000000000000), orderedInterval (-23251947342 / 1000000000000) (-23251901363 / 1000000000000)))) (orderedInterval (-12519789140 / 1000000000000) (-12519768783 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1318668014829389 / 4000000000000) 4 (IntervalRat.scale (571 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-24258443568 / 1000000000000) (-24258443567 / 1000000000000), orderedInterval (-36605099636 / 1000000000000) (-36605099635 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2259560119386497 / 4000000000000) 4 (IntervalRat.scale (571 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (6291592937 / 1000000000000) (6291592938 / 1000000000000), orderedInterval (32970123403 / 1000000000000) (32970123404 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1664381757057923 / 4000000000000) 4 (IntervalRat.scale (571 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (31845945717 / 1000000000000) (31846022921 / 1000000000000), orderedInterval (-22749928478 / 1000000000000) (-22749851274 / 1000000000000)))) (orderedInterval (431220166 / 1000000000000) (431228792 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate414_chunkChecks4_1 :
    compactCertificate414.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2553589630304429 / 4000000000000) 4 (IntervalRat.scale (571 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-31306094069 / 1000000000000) (-31306093829 / 1000000000000), orderedInterval (-4115970981 / 1000000000000) (-4115970742 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1474315660455941 / 4000000000000) 4 (IntervalRat.scale (571 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-40495254113 / 1000000000000) (-40495250715 / 1000000000000), orderedInterval (9401641150 / 1000000000000) (9401644547 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2616199011247369 / 4000000000000) 4 (IntervalRat.scale (571 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (30654031407 / 1000000000000) (30654031533 / 1000000000000), orderedInterval (5780079599 / 1000000000000) (5780079724 / 1000000000000)))) (orderedInterval (250893671688 / 1000000000000) (250893676402 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2444392480717261 / 4000000000000) 4 (IntervalRat.scale (571 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (21457986024 / 1000000000000) (21457989532 / 1000000000000), orderedInterval (-24128103835 / 1000000000000) (-24128100327 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1744433814546013 / 4000000000000) 4 (IntervalRat.scale (571 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-8046301055 / 1000000000000) (-8046301054 / 1000000000000), orderedInterval (-37340900627 / 1000000000000) (-37340900626 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1978002022243227 / 4000000000000) 4 (IntervalRat.scale (571 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-31745687514 / 1000000000000) (-31745612938 / 1000000000000), orderedInterval (16753690021 / 1000000000000) (16753764597 / 1000000000000)))) (orderedInterval (-10889226344 / 1000000000000) (-10889221330 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1649051869069163 / 4000000000000) 4 (IntervalRat.scale (571 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-39196353740 / 1000000000000) (-39196353626 / 1000000000000), orderedInterval (-2754735121 / 1000000000000) (-2754735006 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1456987337048423 / 4000000000000) 4 (IntervalRat.scale (571 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (23851431055 / 1000000000000) (23851431056 / 1000000000000), orderedInterval (34302081847 / 1000000000000) (34302081848 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (422291719085877 / 800000000000) 4 (IntervalRat.scale (571 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (26369077147 / 1000000000000) (26369077148 / 1000000000000), orderedInterval (22573697974 / 1000000000000) (22573697975 / 1000000000000)))) (orderedInterval (2301922129 / 1000000000000) (2301922280 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate414_chunkChecks4_2 :
    compactCertificate414.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1168081118987119 / 4000000000000) 4 (IntervalRat.scale (571 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-27776173676 / 1000000000000) (-27776173675 / 1000000000000), orderedInterval (-37482941130 / 1000000000000) (-37482941129 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (990195300709559 / 4000000000000) 4 (IntervalRat.scale (571 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-7472901645 / 1000000000000) (-7472901643 / 1000000000000), orderedInterval (-50143201020 / 1000000000000) (-50143201019 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (619618242942077 / 4000000000000) 4 (IntervalRat.scale (571 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-63067841988 / 1000000000000) (-63067841421 / 1000000000000), orderedInterval (11700618394 / 1000000000000) (11700618961 / 1000000000000)))) (orderedInterval (4980311285 / 1000000000000) (4980311347 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (333232751811459 / 4000000000000) 4 (IntervalRat.scale (571 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (58354870579 / 1000000000000) (58354919426 / 1000000000000), orderedInterval (-65438371388 / 1000000000000) (-65438322541 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (904791744171377 / 4000000000000) 4 (IntervalRat.scale (571 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (37614474180 / 1000000000000) (37614474181 / 1000000000000), orderedInterval (37327923158 / 1000000000000) (37327923159 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1235415773640529 / 4000000000000) 4 (IntervalRat.scale (571 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (44565983980 / 1000000000000) (44565985627 / 1000000000000), orderedInterval (-8738343663 / 1000000000000) (-8738342016 / 1000000000000)))) (orderedInterval (-5018480766 / 1000000000000) (-5018480552 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (522381757057923 / 4000000000000) 4 (IntervalRat.scale (571 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-37500791753 / 1000000000000) (-37500783424 / 1000000000000), orderedInterval (59037146478 / 1000000000000) (59037154807 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2123452840672483 / 4000000000000) 4 (IntervalRat.scale (571 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-22813829515 / 1000000000000) (-22813829514 / 1000000000000), orderedInterval (-26031256601 / 1000000000000) (-26031256600 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1418368088135597 / 4000000000000) 4 (IntervalRat.scale (571 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-15602248071 / 1000000000000) (-15602248070 / 1000000000000), orderedInterval (-39372537149 / 1000000000000) (-39372537148 / 1000000000000)))) (orderedInterval (29349584161 / 1000000000000) (29349584571 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate414_chunkChecks4 :
    compactCertificate414.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate414.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate414_chunkChecks4_0
    compactCertificate414_chunkChecks4_1 compactCertificate414_chunkChecks4_2

theorem compactCertificate414_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate414.chunkCheck r b = true :=
  compactCertificate414.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate414_chunkChecks0
    · exact compactCertificate414_chunkChecks1
    · exact compactCertificate414_chunkChecks2
    · exact compactCertificate414_chunkChecks3
    · exact compactCertificate414_chunkChecks4)

theorem compactCertificate414_coefficient0 :
    compactCertificate414.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate414_coefficient1 :
    compactCertificate414.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate414_coefficient2 :
    compactCertificate414.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate414_coefficient3 :
    compactCertificate414.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate414_coefficient4 :
    compactCertificate414.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate414_coefficients : ∀ r : Fin 5,
    compactCertificate414.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate414_coefficient0
  · exact compactCertificate414_coefficient1
  · exact compactCertificate414_coefficient2
  · exact compactCertificate414_coefficient3
  · exact compactCertificate414_coefficient4

theorem compactCertificate414_lower : (1 : ℚ) ≤ compactCertificate414.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate414, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate414_proves {t : ℝ} (ht : t ∈ compactCertificate414.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate414.proves compactCertificate414_states compactCertificate414_chunks
    compactCertificate414_coefficients compactCertificate414_lower ht

end Erdos232
