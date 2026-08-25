/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate466 : CompactCertificate where
  left := 337
  right := 338
  center := 675 / 2
  grid := fun i =>
    match i.val with
    | 0 => 107
    | 1 => 79
    | 2 => 128
    | 3 => 23
    | 4 => 62
    | 5 => 168
    | 6 => 124
    | 7 => 213
    | 8 => 157
    | 9 => 240
    | 10 => 139
    | 11 => 246
    | 12 => 230
    | 13 => 164
    | 14 => 186
    | 15 => 155
    | 16 => 137
    | 17 => 199
    | 18 => 110
    | 19 => 93
    | 20 => 58
    | 21 => 31
    | 22 => 85
    | 23 => 116
    | 24 => 49
    | 25 => 200
    | _ => 133
  point := fun i =>
    match i.val with
    | 0 => 675 / 2
    | 1 => 39776155593327 / 160000000000
    | 2 => 12862791466191 / 32000000000
    | 3 => 11606582998989 / 160000000000
    | 4 => 31176914536233 / 160000000000
    | 5 => 84651387739461 / 160000000000
    | 6 => 62353829072493 / 160000000000
    | 7 => 106844348902689 / 160000000000
    | 8 => 78701063818851 / 160000000000
    | 9 => 120747670784973 / 160000000000
    | 10 => 69713700231717 / 160000000000
    | 11 => 123708184419753 / 160000000000
    | 12 => 115584232888557 / 160000000000
    | 13 => 82486362509181 / 160000000000
    | 14 => 93530743608699 / 160000000000
    | 15 => 77976182950731 / 160000000000
    | 16 => 68894322417351 / 160000000000
    | 17 => 19968259921749 / 32000000000
    | 18 => 55233257815503 / 160000000000
    | 19 => 46821844341783 / 160000000000
    | 20 => 29298936181149 / 160000000000
    | 21 => 15757065322083 / 160000000000
    | 22 => 42783497535249 / 160000000000
    | 23 => 58417208210673 / 160000000000
    | 24 => 24701063818851 / 160000000000
    | 25 => 100408453061571 / 160000000000
    | _ => 67068193309389 / 160000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-36709096938 / 1000000000000) (-36709022683 / 1000000000000), orderedInterval (23264790528 / 1000000000000) (23264864783 / 1000000000000))
    | 1 => (orderedInterval (-47166154596 / 1000000000000) (-47166154595 / 1000000000000), orderedInterval (-18239795746 / 1000000000000) (-18239795745 / 1000000000000))
    | 2 => (orderedInterval (23235250121 / 1000000000000) (23235250122 / 1000000000000), orderedInterval (32280594937 / 1000000000000) (32280594938 / 1000000000000))
    | 3 => (orderedInterval (-82093713498 / 1000000000000) (-82093713497 / 1000000000000), orderedInterval (-44561698566 / 1000000000000) (-44561698565 / 1000000000000))
    | 4 => (orderedInterval (43381715273 / 1000000000000) (43381715274 / 1000000000000), orderedInterval (37106412031 / 1000000000000) (37106412032 / 1000000000000))
    | 5 => (orderedInterval (30475435377 / 1000000000000) (30475532057 / 1000000000000), orderedInterval (-16597573270 / 1000000000000) (-16597476590 / 1000000000000))
    | 6 => (orderedInterval (32616019189 / 1000000000000) (32616019190 / 1000000000000), orderedInterval (23827841234 / 1000000000000) (23827841235 / 1000000000000))
    | 7 => (orderedInterval (17353506322 / 1000000000000) (17353506877 / 1000000000000), orderedInterval (-25551151803 / 1000000000000) (-25551151248 / 1000000000000))
    | 8 => (orderedInterval (19208885450 / 1000000000000) (19208886538 / 1000000000000), orderedInterval (-30437825972 / 1000000000000) (-30437824884 / 1000000000000))
    | 9 => (orderedInterval (28913706661 / 1000000000000) (28913707464 / 1000000000000), orderedInterval (2731803599 / 1000000000000) (2731804402 / 1000000000000))
    | 10 => (orderedInterval (7055335527 / 1000000000000) (7055335535 / 1000000000000), orderedInterval (-37575768187 / 1000000000000) (-37575768179 / 1000000000000))
    | 11 => (orderedInterval (25946838654 / 1000000000000) (25946838661 / 1000000000000), orderedInterval (12236547942 / 1000000000000) (12236547949 / 1000000000000))
    | 12 => (orderedInterval (17257517787 / 1000000000000) (17257517788 / 1000000000000), orderedInterval (24142412805 / 1000000000000) (24142412806 / 1000000000000))
    | 13 => (orderedInterval (31376716450 / 1000000000000) (31376716452 / 1000000000000), orderedInterval (15792399867 / 1000000000000) (15792399869 / 1000000000000))
    | 14 => (orderedInterval (28052535589 / 1000000000000) (28052535590 / 1000000000000), orderedInterval (17357024158 / 1000000000000) (17357024159 / 1000000000000))
    | 15 => (orderedInterval (-33545888970 / 1000000000000) (-33545888968 / 1000000000000), orderedInterval (-13417662098 / 1000000000000) (-13417662096 / 1000000000000))
    | 16 => (orderedInterval (-31856816692 / 1000000000000) (-31856816691 / 1000000000000), orderedInterval (-21495007551 / 1000000000000) (-21495007550 / 1000000000000))
    | 17 => (orderedInterval (11954701651 / 1000000000000) (11954701692 / 1000000000000), orderedInterval (-29628762927 / 1000000000000) (-29628762886 / 1000000000000))
    | 18 => (orderedInterval (17420727993 / 1000000000000) (17420727994 / 1000000000000), orderedInterval (39226304532 / 1000000000000) (39226304533 / 1000000000000))
    | 19 => (orderedInterval (-44311846002 / 1000000000000) (-44311846000 / 1000000000000), orderedInterval (-14481767439 / 1000000000000) (-14481767437 / 1000000000000))
    | 20 => (orderedInterval (58538862956 / 1000000000000) (58538863271 / 1000000000000), orderedInterval (-7212291836 / 1000000000000) (-7212291520 / 1000000000000))
    | 21 => (orderedInterval (-76674969776 / 1000000000000) (-76674967978 / 1000000000000), orderedInterval (24580792675 / 1000000000000) (24580794474 / 1000000000000))
    | 22 => (orderedInterval (-44465156306 / 1000000000000) (-44465156305 / 1000000000000), orderedInterval (-20007950690 / 1000000000000) (-20007950689 / 1000000000000))
    | 23 => (orderedInterval (41535981372 / 1000000000000) (41535981424 / 1000000000000), orderedInterval (4233878397 / 1000000000000) (4233878449 / 1000000000000))
    | 24 => (orderedInterval (-60483769894 / 1000000000000) (-60483769893 / 1000000000000), orderedInterval (-21376594259 / 1000000000000) (-21376594258 / 1000000000000))
    | 25 => (orderedInterval (621040002 / 1000000000000) (621040003 / 1000000000000), orderedInterval (31843856690 / 1000000000000) (31843856691 / 1000000000000))
    | _ => (orderedInterval (-33045543969 / 1000000000000) (-33045443129 / 1000000000000), orderedInterval (20696931074 / 1000000000000) (20697031914 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-13626227056 / 1000000000000) (-13626197600 / 1000000000000)
      | 1 => orderedInterval (308106102 / 1000000000000) (308113016 / 1000000000000)
      | 2 => orderedInterval (-71010731 / 1000000000000) (-71010668 / 1000000000000)
      | 3 => orderedInterval (-926378482 / 1000000000000) (-926378203 / 1000000000000)
      | 4 => orderedInterval (2513558772 / 1000000000000) (2513558813 / 1000000000000)
      | 5 => orderedInterval (1741770470 / 1000000000000) (1741770504 / 1000000000000)
      | 6 => orderedInterval (1628354299 / 1000000000000) (1628354394 / 1000000000000)
      | 7 => orderedInterval (-758683581 / 1000000000000) (-758683504 / 1000000000000)
      | _ => orderedInterval (5785031917 / 1000000000000) (5785050931 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (11352221792 / 1000000000000) (11352251251 / 1000000000000)
      | 1 => orderedInterval (2735765908 / 1000000000000) (2735776729 / 1000000000000)
      | 2 => orderedInterval (487217637 / 1000000000000) (487217743 / 1000000000000)
      | 3 => orderedInterval (-694605541 / 1000000000000) (-694604941 / 1000000000000)
      | 4 => orderedInterval (1196125982 / 1000000000000) (1196126048 / 1000000000000)
      | 5 => orderedInterval (-56976282 / 1000000000000) (-56976233 / 1000000000000)
      | 6 => orderedInterval (-5831915140 / 1000000000000) (-5831915055 / 1000000000000)
      | 7 => orderedInterval (-123832308 / 1000000000000) (-123832257 / 1000000000000)
      | _ => orderedInterval (-9701912332 / 1000000000000) (-9701888701 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (12820939301 / 1000000000000) (12820968852 / 1000000000000)
      | 1 => orderedInterval (4746752528 / 1000000000000) (4746769514 / 1000000000000)
      | 2 => orderedInterval (1107897032 / 1000000000000) (1107897214 / 1000000000000)
      | 3 => orderedInterval (5460984713 / 1000000000000) (5460986028 / 1000000000000)
      | 4 => orderedInterval (-5073447224 / 1000000000000) (-5073447115 / 1000000000000)
      | 5 => orderedInterval (-3205876433 / 1000000000000) (-3205876359 / 1000000000000)
      | 6 => orderedInterval (484797203 / 1000000000000) (484797281 / 1000000000000)
      | 7 => orderedInterval (2971944456 / 1000000000000) (2971944500 / 1000000000000)
      | _ => orderedInterval (-9284468026 / 1000000000000) (-9284438576 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-12391521547 / 1000000000000) (-12391491992 / 1000000000000)
      | 1 => orderedInterval (-4824973980 / 1000000000000) (-4824947358 / 1000000000000)
      | 2 => orderedInterval (-3830567182 / 1000000000000) (-3830566861 / 1000000000000)
      | 3 => orderedInterval (-9512855799 / 1000000000000) (-9512852886 / 1000000000000)
      | 4 => orderedInterval (-577149788 / 1000000000000) (-577149603 / 1000000000000)
      | 5 => orderedInterval (2716322045 / 1000000000000) (2716322159 / 1000000000000)
      | 6 => orderedInterval (6213294430 / 1000000000000) (6213294504 / 1000000000000)
      | 7 => orderedInterval (187519997 / 1000000000000) (187520040 / 1000000000000)
      | _ => orderedInterval (24144063611 / 1000000000000) (24144100246 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-11862622377 / 1000000000000) (-11862592730 / 1000000000000)
      | 1 => orderedInterval (-12876820151 / 1000000000000) (-12876778342 / 1000000000000)
      | 2 => orderedInterval (-6086051186 / 1000000000000) (-6086050607 / 1000000000000)
      | 3 => orderedInterval (-25337948731 / 1000000000000) (-25337942234 / 1000000000000)
      | 4 => orderedInterval (8340208531 / 1000000000000) (8340208851 / 1000000000000)
      | 5 => orderedInterval (6706703192 / 1000000000000) (6706703374 / 1000000000000)
      | 6 => orderedInterval (-1502803822 / 1000000000000) (-1502803749 / 1000000000000)
      | 7 => orderedInterval (-3953083849 / 1000000000000) (-3953083804 / 1000000000000)
      | _ => orderedInterval (13990142395 / 1000000000000) (13990188111 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-3405478290 / 1000000000000) (-3405422317 / 1000000000000)
    | 1 => orderedInterval (-637910284 / 1000000000000) (-637845416 / 1000000000000)
    | 2 => orderedInterval (10029523550 / 1000000000000) (10029601339 / 1000000000000)
    | 3 => orderedInterval (2124131787 / 1000000000000) (2124228249 / 1000000000000)
    | _ => orderedInterval (-32582275998 / 1000000000000) (-32582151130 / 1000000000000)

theorem compactCertificate466_stateChecks0 :
    compactCertificate466.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 107 12 (675 / 2)) (orderedInterval (-36709096938 / 1000000000000) (-36709022683 / 1000000000000), orderedInterval (23264790528 / 1000000000000) (23264864783 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (39776155593327 / 160000000000)) (orderedInterval (-47166154596 / 1000000000000) (-47166154595 / 1000000000000), orderedInterval (-18239795746 / 1000000000000) (-18239795745 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 128 12 (12862791466191 / 32000000000)) (orderedInterval (23235250121 / 1000000000000) (23235250122 / 1000000000000), orderedInterval (32280594937 / 1000000000000) (32280594938 / 1000000000000))) = true
  rfl'

theorem compactCertificate466_stateChecks1 :
    compactCertificate466.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (11606582998989 / 160000000000)) (orderedInterval (-82093713498 / 1000000000000) (-82093713497 / 1000000000000), orderedInterval (-44561698566 / 1000000000000) (-44561698565 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (31176914536233 / 160000000000)) (orderedInterval (43381715273 / 1000000000000) (43381715274 / 1000000000000), orderedInterval (37106412031 / 1000000000000) (37106412032 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 168 12 (84651387739461 / 160000000000)) (orderedInterval (30475435377 / 1000000000000) (30475532057 / 1000000000000), orderedInterval (-16597573270 / 1000000000000) (-16597476590 / 1000000000000))) = true
  rfl'

theorem compactCertificate466_stateChecks2 :
    compactCertificate466.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 124 12 (62353829072493 / 160000000000)) (orderedInterval (32616019189 / 1000000000000) (32616019190 / 1000000000000), orderedInterval (23827841234 / 1000000000000) (23827841235 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 213 12 (106844348902689 / 160000000000)) (orderedInterval (17353506322 / 1000000000000) (17353506877 / 1000000000000), orderedInterval (-25551151803 / 1000000000000) (-25551151248 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 157 12 (78701063818851 / 160000000000)) (orderedInterval (19208885450 / 1000000000000) (19208886538 / 1000000000000), orderedInterval (-30437825972 / 1000000000000) (-30437824884 / 1000000000000))) = true
  rfl'

theorem compactCertificate466_stateChecks3 :
    compactCertificate466.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 240 12 (120747670784973 / 160000000000)) (orderedInterval (28913706661 / 1000000000000) (28913707464 / 1000000000000), orderedInterval (2731803599 / 1000000000000) (2731804402 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 139 12 (69713700231717 / 160000000000)) (orderedInterval (7055335527 / 1000000000000) (7055335535 / 1000000000000), orderedInterval (-37575768187 / 1000000000000) (-37575768179 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 246 12 (123708184419753 / 160000000000)) (orderedInterval (25946838654 / 1000000000000) (25946838661 / 1000000000000), orderedInterval (12236547942 / 1000000000000) (12236547949 / 1000000000000))) = true
  rfl'

theorem compactCertificate466_stateChecks4 :
    compactCertificate466.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 230 12 (115584232888557 / 160000000000)) (orderedInterval (17257517787 / 1000000000000) (17257517788 / 1000000000000), orderedInterval (24142412805 / 1000000000000) (24142412806 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 164 12 (82486362509181 / 160000000000)) (orderedInterval (31376716450 / 1000000000000) (31376716452 / 1000000000000), orderedInterval (15792399867 / 1000000000000) (15792399869 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 186 12 (93530743608699 / 160000000000)) (orderedInterval (28052535589 / 1000000000000) (28052535590 / 1000000000000), orderedInterval (17357024158 / 1000000000000) (17357024159 / 1000000000000))) = true
  rfl'

theorem compactCertificate466_stateChecks5 :
    compactCertificate466.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 155 12 (77976182950731 / 160000000000)) (orderedInterval (-33545888970 / 1000000000000) (-33545888968 / 1000000000000), orderedInterval (-13417662098 / 1000000000000) (-13417662096 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 137 12 (68894322417351 / 160000000000)) (orderedInterval (-31856816692 / 1000000000000) (-31856816691 / 1000000000000), orderedInterval (-21495007551 / 1000000000000) (-21495007550 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 199 12 (19968259921749 / 32000000000)) (orderedInterval (11954701651 / 1000000000000) (11954701692 / 1000000000000), orderedInterval (-29628762927 / 1000000000000) (-29628762886 / 1000000000000))) = true
  rfl'

theorem compactCertificate466_stateChecks6 :
    compactCertificate466.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 110 12 (55233257815503 / 160000000000)) (orderedInterval (17420727993 / 1000000000000) (17420727994 / 1000000000000), orderedInterval (39226304532 / 1000000000000) (39226304533 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 93 12 (46821844341783 / 160000000000)) (orderedInterval (-44311846002 / 1000000000000) (-44311846000 / 1000000000000), orderedInterval (-14481767439 / 1000000000000) (-14481767437 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (29298936181149 / 160000000000)) (orderedInterval (58538862956 / 1000000000000) (58538863271 / 1000000000000), orderedInterval (-7212291836 / 1000000000000) (-7212291520 / 1000000000000))) = true
  rfl'

theorem compactCertificate466_stateChecks7 :
    compactCertificate466.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (15757065322083 / 160000000000)) (orderedInterval (-76674969776 / 1000000000000) (-76674967978 / 1000000000000), orderedInterval (24580792675 / 1000000000000) (24580794474 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (42783497535249 / 160000000000)) (orderedInterval (-44465156306 / 1000000000000) (-44465156305 / 1000000000000), orderedInterval (-20007950690 / 1000000000000) (-20007950689 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 116 12 (58417208210673 / 160000000000)) (orderedInterval (41535981372 / 1000000000000) (41535981424 / 1000000000000), orderedInterval (4233878397 / 1000000000000) (4233878449 / 1000000000000))) = true
  rfl'

theorem compactCertificate466_stateChecks8 :
    compactCertificate466.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (24701063818851 / 160000000000)) (orderedInterval (-60483769894 / 1000000000000) (-60483769893 / 1000000000000), orderedInterval (-21376594259 / 1000000000000) (-21376594258 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 200 12 (100408453061571 / 160000000000)) (orderedInterval (621040002 / 1000000000000) (621040003 / 1000000000000), orderedInterval (31843856690 / 1000000000000) (31843856691 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 133 12 (67068193309389 / 160000000000)) (orderedInterval (-33045543969 / 1000000000000) (-33045443129 / 1000000000000), orderedInterval (20696931074 / 1000000000000) (20697031914 / 1000000000000))) = true
  rfl'

theorem compactCertificate466_states : ∀ j,
    BesselStateValid (compactCertificate466.point j) (compactCertificate466.state j) :=
  compactCertificate466.statesValid_of_checks3 compactCertificate466_stateChecks0
    compactCertificate466_stateChecks1 compactCertificate466_stateChecks2
    compactCertificate466_stateChecks3 compactCertificate466_stateChecks4
    compactCertificate466_stateChecks5 compactCertificate466_stateChecks6
    compactCertificate466_stateChecks7 compactCertificate466_stateChecks8

theorem compactCertificate466_chunkChecks0_0 :
    compactCertificate466.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (675 / 2) 0 (IntervalRat.scale (675 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-36709096938 / 1000000000000) (-36709022683 / 1000000000000), orderedInterval (23264790528 / 1000000000000) (23264864783 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (39776155593327 / 160000000000) 0 (IntervalRat.scale (675 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-47166154596 / 1000000000000) (-47166154595 / 1000000000000), orderedInterval (-18239795746 / 1000000000000) (-18239795745 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (12862791466191 / 32000000000) 0 (IntervalRat.scale (675 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (23235250121 / 1000000000000) (23235250122 / 1000000000000), orderedInterval (32280594937 / 1000000000000) (32280594938 / 1000000000000)))) (orderedInterval (-13626227056 / 1000000000000) (-13626197600 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (11606582998989 / 160000000000) 0 (IntervalRat.scale (675 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-82093713498 / 1000000000000) (-82093713497 / 1000000000000), orderedInterval (-44561698566 / 1000000000000) (-44561698565 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (31176914536233 / 160000000000) 0 (IntervalRat.scale (675 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (43381715273 / 1000000000000) (43381715274 / 1000000000000), orderedInterval (37106412031 / 1000000000000) (37106412032 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (84651387739461 / 160000000000) 0 (IntervalRat.scale (675 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30475435377 / 1000000000000) (30475532057 / 1000000000000), orderedInterval (-16597573270 / 1000000000000) (-16597476590 / 1000000000000)))) (orderedInterval (308106102 / 1000000000000) (308113016 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (62353829072493 / 160000000000) 0 (IntervalRat.scale (675 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (32616019189 / 1000000000000) (32616019190 / 1000000000000), orderedInterval (23827841234 / 1000000000000) (23827841235 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (106844348902689 / 160000000000) 0 (IntervalRat.scale (675 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (17353506322 / 1000000000000) (17353506877 / 1000000000000), orderedInterval (-25551151803 / 1000000000000) (-25551151248 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (78701063818851 / 160000000000) 0 (IntervalRat.scale (675 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (19208885450 / 1000000000000) (19208886538 / 1000000000000), orderedInterval (-30437825972 / 1000000000000) (-30437824884 / 1000000000000)))) (orderedInterval (-71010731 / 1000000000000) (-71010668 / 1000000000000))) = true
  rfl'

theorem compactCertificate466_chunkChecks0_1 :
    compactCertificate466.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (120747670784973 / 160000000000) 0 (IntervalRat.scale (675 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (28913706661 / 1000000000000) (28913707464 / 1000000000000), orderedInterval (2731803599 / 1000000000000) (2731804402 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (69713700231717 / 160000000000) 0 (IntervalRat.scale (675 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (7055335527 / 1000000000000) (7055335535 / 1000000000000), orderedInterval (-37575768187 / 1000000000000) (-37575768179 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (123708184419753 / 160000000000) 0 (IntervalRat.scale (675 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (25946838654 / 1000000000000) (25946838661 / 1000000000000), orderedInterval (12236547942 / 1000000000000) (12236547949 / 1000000000000)))) (orderedInterval (-926378482 / 1000000000000) (-926378203 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (115584232888557 / 160000000000) 0 (IntervalRat.scale (675 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (17257517787 / 1000000000000) (17257517788 / 1000000000000), orderedInterval (24142412805 / 1000000000000) (24142412806 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (82486362509181 / 160000000000) 0 (IntervalRat.scale (675 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (31376716450 / 1000000000000) (31376716452 / 1000000000000), orderedInterval (15792399867 / 1000000000000) (15792399869 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (93530743608699 / 160000000000) 0 (IntervalRat.scale (675 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (28052535589 / 1000000000000) (28052535590 / 1000000000000), orderedInterval (17357024158 / 1000000000000) (17357024159 / 1000000000000)))) (orderedInterval (2513558772 / 1000000000000) (2513558813 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (77976182950731 / 160000000000) 0 (IntervalRat.scale (675 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-33545888970 / 1000000000000) (-33545888968 / 1000000000000), orderedInterval (-13417662098 / 1000000000000) (-13417662096 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (68894322417351 / 160000000000) 0 (IntervalRat.scale (675 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-31856816692 / 1000000000000) (-31856816691 / 1000000000000), orderedInterval (-21495007551 / 1000000000000) (-21495007550 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (19968259921749 / 32000000000) 0 (IntervalRat.scale (675 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (11954701651 / 1000000000000) (11954701692 / 1000000000000), orderedInterval (-29628762927 / 1000000000000) (-29628762886 / 1000000000000)))) (orderedInterval (1741770470 / 1000000000000) (1741770504 / 1000000000000))) = true
  rfl'

theorem compactCertificate466_chunkChecks0_2 :
    compactCertificate466.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (55233257815503 / 160000000000) 0 (IntervalRat.scale (675 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (17420727993 / 1000000000000) (17420727994 / 1000000000000), orderedInterval (39226304532 / 1000000000000) (39226304533 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (46821844341783 / 160000000000) 0 (IntervalRat.scale (675 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-44311846002 / 1000000000000) (-44311846000 / 1000000000000), orderedInterval (-14481767439 / 1000000000000) (-14481767437 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (29298936181149 / 160000000000) 0 (IntervalRat.scale (675 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (58538862956 / 1000000000000) (58538863271 / 1000000000000), orderedInterval (-7212291836 / 1000000000000) (-7212291520 / 1000000000000)))) (orderedInterval (1628354299 / 1000000000000) (1628354394 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (15757065322083 / 160000000000) 0 (IntervalRat.scale (675 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-76674969776 / 1000000000000) (-76674967978 / 1000000000000), orderedInterval (24580792675 / 1000000000000) (24580794474 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (42783497535249 / 160000000000) 0 (IntervalRat.scale (675 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-44465156306 / 1000000000000) (-44465156305 / 1000000000000), orderedInterval (-20007950690 / 1000000000000) (-20007950689 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (58417208210673 / 160000000000) 0 (IntervalRat.scale (675 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (41535981372 / 1000000000000) (41535981424 / 1000000000000), orderedInterval (4233878397 / 1000000000000) (4233878449 / 1000000000000)))) (orderedInterval (-758683581 / 1000000000000) (-758683504 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (24701063818851 / 160000000000) 0 (IntervalRat.scale (675 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-60483769894 / 1000000000000) (-60483769893 / 1000000000000), orderedInterval (-21376594259 / 1000000000000) (-21376594258 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (100408453061571 / 160000000000) 0 (IntervalRat.scale (675 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (621040002 / 1000000000000) (621040003 / 1000000000000), orderedInterval (31843856690 / 1000000000000) (31843856691 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (67068193309389 / 160000000000) 0 (IntervalRat.scale (675 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-33045543969 / 1000000000000) (-33045443129 / 1000000000000), orderedInterval (20696931074 / 1000000000000) (20697031914 / 1000000000000)))) (orderedInterval (5785031917 / 1000000000000) (5785050931 / 1000000000000))) = true
  rfl'

theorem compactCertificate466_chunkChecks0 :
    compactCertificate466.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate466.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate466_chunkChecks0_0
    compactCertificate466_chunkChecks0_1 compactCertificate466_chunkChecks0_2

theorem compactCertificate466_chunkChecks1_0 :
    compactCertificate466.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (675 / 2) 1 (IntervalRat.scale (675 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-36709096938 / 1000000000000) (-36709022683 / 1000000000000), orderedInterval (23264790528 / 1000000000000) (23264864783 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (39776155593327 / 160000000000) 1 (IntervalRat.scale (675 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-47166154596 / 1000000000000) (-47166154595 / 1000000000000), orderedInterval (-18239795746 / 1000000000000) (-18239795745 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (12862791466191 / 32000000000) 1 (IntervalRat.scale (675 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (23235250121 / 1000000000000) (23235250122 / 1000000000000), orderedInterval (32280594937 / 1000000000000) (32280594938 / 1000000000000)))) (orderedInterval (11352221792 / 1000000000000) (11352251251 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (11606582998989 / 160000000000) 1 (IntervalRat.scale (675 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-82093713498 / 1000000000000) (-82093713497 / 1000000000000), orderedInterval (-44561698566 / 1000000000000) (-44561698565 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (31176914536233 / 160000000000) 1 (IntervalRat.scale (675 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (43381715273 / 1000000000000) (43381715274 / 1000000000000), orderedInterval (37106412031 / 1000000000000) (37106412032 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (84651387739461 / 160000000000) 1 (IntervalRat.scale (675 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30475435377 / 1000000000000) (30475532057 / 1000000000000), orderedInterval (-16597573270 / 1000000000000) (-16597476590 / 1000000000000)))) (orderedInterval (2735765908 / 1000000000000) (2735776729 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (62353829072493 / 160000000000) 1 (IntervalRat.scale (675 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (32616019189 / 1000000000000) (32616019190 / 1000000000000), orderedInterval (23827841234 / 1000000000000) (23827841235 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (106844348902689 / 160000000000) 1 (IntervalRat.scale (675 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (17353506322 / 1000000000000) (17353506877 / 1000000000000), orderedInterval (-25551151803 / 1000000000000) (-25551151248 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (78701063818851 / 160000000000) 1 (IntervalRat.scale (675 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (19208885450 / 1000000000000) (19208886538 / 1000000000000), orderedInterval (-30437825972 / 1000000000000) (-30437824884 / 1000000000000)))) (orderedInterval (487217637 / 1000000000000) (487217743 / 1000000000000))) = true
  rfl'

theorem compactCertificate466_chunkChecks1_1 :
    compactCertificate466.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (120747670784973 / 160000000000) 1 (IntervalRat.scale (675 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (28913706661 / 1000000000000) (28913707464 / 1000000000000), orderedInterval (2731803599 / 1000000000000) (2731804402 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (69713700231717 / 160000000000) 1 (IntervalRat.scale (675 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (7055335527 / 1000000000000) (7055335535 / 1000000000000), orderedInterval (-37575768187 / 1000000000000) (-37575768179 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (123708184419753 / 160000000000) 1 (IntervalRat.scale (675 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (25946838654 / 1000000000000) (25946838661 / 1000000000000), orderedInterval (12236547942 / 1000000000000) (12236547949 / 1000000000000)))) (orderedInterval (-694605541 / 1000000000000) (-694604941 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (115584232888557 / 160000000000) 1 (IntervalRat.scale (675 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (17257517787 / 1000000000000) (17257517788 / 1000000000000), orderedInterval (24142412805 / 1000000000000) (24142412806 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (82486362509181 / 160000000000) 1 (IntervalRat.scale (675 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (31376716450 / 1000000000000) (31376716452 / 1000000000000), orderedInterval (15792399867 / 1000000000000) (15792399869 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (93530743608699 / 160000000000) 1 (IntervalRat.scale (675 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (28052535589 / 1000000000000) (28052535590 / 1000000000000), orderedInterval (17357024158 / 1000000000000) (17357024159 / 1000000000000)))) (orderedInterval (1196125982 / 1000000000000) (1196126048 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (77976182950731 / 160000000000) 1 (IntervalRat.scale (675 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-33545888970 / 1000000000000) (-33545888968 / 1000000000000), orderedInterval (-13417662098 / 1000000000000) (-13417662096 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (68894322417351 / 160000000000) 1 (IntervalRat.scale (675 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-31856816692 / 1000000000000) (-31856816691 / 1000000000000), orderedInterval (-21495007551 / 1000000000000) (-21495007550 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (19968259921749 / 32000000000) 1 (IntervalRat.scale (675 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (11954701651 / 1000000000000) (11954701692 / 1000000000000), orderedInterval (-29628762927 / 1000000000000) (-29628762886 / 1000000000000)))) (orderedInterval (-56976282 / 1000000000000) (-56976233 / 1000000000000))) = true
  rfl'

theorem compactCertificate466_chunkChecks1_2 :
    compactCertificate466.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (55233257815503 / 160000000000) 1 (IntervalRat.scale (675 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (17420727993 / 1000000000000) (17420727994 / 1000000000000), orderedInterval (39226304532 / 1000000000000) (39226304533 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (46821844341783 / 160000000000) 1 (IntervalRat.scale (675 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-44311846002 / 1000000000000) (-44311846000 / 1000000000000), orderedInterval (-14481767439 / 1000000000000) (-14481767437 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (29298936181149 / 160000000000) 1 (IntervalRat.scale (675 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (58538862956 / 1000000000000) (58538863271 / 1000000000000), orderedInterval (-7212291836 / 1000000000000) (-7212291520 / 1000000000000)))) (orderedInterval (-5831915140 / 1000000000000) (-5831915055 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (15757065322083 / 160000000000) 1 (IntervalRat.scale (675 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-76674969776 / 1000000000000) (-76674967978 / 1000000000000), orderedInterval (24580792675 / 1000000000000) (24580794474 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (42783497535249 / 160000000000) 1 (IntervalRat.scale (675 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-44465156306 / 1000000000000) (-44465156305 / 1000000000000), orderedInterval (-20007950690 / 1000000000000) (-20007950689 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (58417208210673 / 160000000000) 1 (IntervalRat.scale (675 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (41535981372 / 1000000000000) (41535981424 / 1000000000000), orderedInterval (4233878397 / 1000000000000) (4233878449 / 1000000000000)))) (orderedInterval (-123832308 / 1000000000000) (-123832257 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (24701063818851 / 160000000000) 1 (IntervalRat.scale (675 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-60483769894 / 1000000000000) (-60483769893 / 1000000000000), orderedInterval (-21376594259 / 1000000000000) (-21376594258 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (100408453061571 / 160000000000) 1 (IntervalRat.scale (675 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (621040002 / 1000000000000) (621040003 / 1000000000000), orderedInterval (31843856690 / 1000000000000) (31843856691 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (67068193309389 / 160000000000) 1 (IntervalRat.scale (675 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-33045543969 / 1000000000000) (-33045443129 / 1000000000000), orderedInterval (20696931074 / 1000000000000) (20697031914 / 1000000000000)))) (orderedInterval (-9701912332 / 1000000000000) (-9701888701 / 1000000000000))) = true
  rfl'

theorem compactCertificate466_chunkChecks1 :
    compactCertificate466.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate466.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate466_chunkChecks1_0
    compactCertificate466_chunkChecks1_1 compactCertificate466_chunkChecks1_2

theorem compactCertificate466_chunkChecks2_0 :
    compactCertificate466.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (675 / 2) 2 (IntervalRat.scale (675 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-36709096938 / 1000000000000) (-36709022683 / 1000000000000), orderedInterval (23264790528 / 1000000000000) (23264864783 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (39776155593327 / 160000000000) 2 (IntervalRat.scale (675 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-47166154596 / 1000000000000) (-47166154595 / 1000000000000), orderedInterval (-18239795746 / 1000000000000) (-18239795745 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (12862791466191 / 32000000000) 2 (IntervalRat.scale (675 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (23235250121 / 1000000000000) (23235250122 / 1000000000000), orderedInterval (32280594937 / 1000000000000) (32280594938 / 1000000000000)))) (orderedInterval (12820939301 / 1000000000000) (12820968852 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (11606582998989 / 160000000000) 2 (IntervalRat.scale (675 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-82093713498 / 1000000000000) (-82093713497 / 1000000000000), orderedInterval (-44561698566 / 1000000000000) (-44561698565 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (31176914536233 / 160000000000) 2 (IntervalRat.scale (675 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (43381715273 / 1000000000000) (43381715274 / 1000000000000), orderedInterval (37106412031 / 1000000000000) (37106412032 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (84651387739461 / 160000000000) 2 (IntervalRat.scale (675 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30475435377 / 1000000000000) (30475532057 / 1000000000000), orderedInterval (-16597573270 / 1000000000000) (-16597476590 / 1000000000000)))) (orderedInterval (4746752528 / 1000000000000) (4746769514 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (62353829072493 / 160000000000) 2 (IntervalRat.scale (675 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (32616019189 / 1000000000000) (32616019190 / 1000000000000), orderedInterval (23827841234 / 1000000000000) (23827841235 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (106844348902689 / 160000000000) 2 (IntervalRat.scale (675 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (17353506322 / 1000000000000) (17353506877 / 1000000000000), orderedInterval (-25551151803 / 1000000000000) (-25551151248 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (78701063818851 / 160000000000) 2 (IntervalRat.scale (675 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (19208885450 / 1000000000000) (19208886538 / 1000000000000), orderedInterval (-30437825972 / 1000000000000) (-30437824884 / 1000000000000)))) (orderedInterval (1107897032 / 1000000000000) (1107897214 / 1000000000000))) = true
  rfl'

theorem compactCertificate466_chunkChecks2_1 :
    compactCertificate466.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (120747670784973 / 160000000000) 2 (IntervalRat.scale (675 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (28913706661 / 1000000000000) (28913707464 / 1000000000000), orderedInterval (2731803599 / 1000000000000) (2731804402 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (69713700231717 / 160000000000) 2 (IntervalRat.scale (675 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (7055335527 / 1000000000000) (7055335535 / 1000000000000), orderedInterval (-37575768187 / 1000000000000) (-37575768179 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (123708184419753 / 160000000000) 2 (IntervalRat.scale (675 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (25946838654 / 1000000000000) (25946838661 / 1000000000000), orderedInterval (12236547942 / 1000000000000) (12236547949 / 1000000000000)))) (orderedInterval (5460984713 / 1000000000000) (5460986028 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (115584232888557 / 160000000000) 2 (IntervalRat.scale (675 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (17257517787 / 1000000000000) (17257517788 / 1000000000000), orderedInterval (24142412805 / 1000000000000) (24142412806 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (82486362509181 / 160000000000) 2 (IntervalRat.scale (675 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (31376716450 / 1000000000000) (31376716452 / 1000000000000), orderedInterval (15792399867 / 1000000000000) (15792399869 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (93530743608699 / 160000000000) 2 (IntervalRat.scale (675 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (28052535589 / 1000000000000) (28052535590 / 1000000000000), orderedInterval (17357024158 / 1000000000000) (17357024159 / 1000000000000)))) (orderedInterval (-5073447224 / 1000000000000) (-5073447115 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (77976182950731 / 160000000000) 2 (IntervalRat.scale (675 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-33545888970 / 1000000000000) (-33545888968 / 1000000000000), orderedInterval (-13417662098 / 1000000000000) (-13417662096 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (68894322417351 / 160000000000) 2 (IntervalRat.scale (675 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-31856816692 / 1000000000000) (-31856816691 / 1000000000000), orderedInterval (-21495007551 / 1000000000000) (-21495007550 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (19968259921749 / 32000000000) 2 (IntervalRat.scale (675 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (11954701651 / 1000000000000) (11954701692 / 1000000000000), orderedInterval (-29628762927 / 1000000000000) (-29628762886 / 1000000000000)))) (orderedInterval (-3205876433 / 1000000000000) (-3205876359 / 1000000000000))) = true
  rfl'

theorem compactCertificate466_chunkChecks2_2 :
    compactCertificate466.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (55233257815503 / 160000000000) 2 (IntervalRat.scale (675 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (17420727993 / 1000000000000) (17420727994 / 1000000000000), orderedInterval (39226304532 / 1000000000000) (39226304533 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (46821844341783 / 160000000000) 2 (IntervalRat.scale (675 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-44311846002 / 1000000000000) (-44311846000 / 1000000000000), orderedInterval (-14481767439 / 1000000000000) (-14481767437 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (29298936181149 / 160000000000) 2 (IntervalRat.scale (675 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (58538862956 / 1000000000000) (58538863271 / 1000000000000), orderedInterval (-7212291836 / 1000000000000) (-7212291520 / 1000000000000)))) (orderedInterval (484797203 / 1000000000000) (484797281 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (15757065322083 / 160000000000) 2 (IntervalRat.scale (675 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-76674969776 / 1000000000000) (-76674967978 / 1000000000000), orderedInterval (24580792675 / 1000000000000) (24580794474 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (42783497535249 / 160000000000) 2 (IntervalRat.scale (675 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-44465156306 / 1000000000000) (-44465156305 / 1000000000000), orderedInterval (-20007950690 / 1000000000000) (-20007950689 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (58417208210673 / 160000000000) 2 (IntervalRat.scale (675 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (41535981372 / 1000000000000) (41535981424 / 1000000000000), orderedInterval (4233878397 / 1000000000000) (4233878449 / 1000000000000)))) (orderedInterval (2971944456 / 1000000000000) (2971944500 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (24701063818851 / 160000000000) 2 (IntervalRat.scale (675 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-60483769894 / 1000000000000) (-60483769893 / 1000000000000), orderedInterval (-21376594259 / 1000000000000) (-21376594258 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (100408453061571 / 160000000000) 2 (IntervalRat.scale (675 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (621040002 / 1000000000000) (621040003 / 1000000000000), orderedInterval (31843856690 / 1000000000000) (31843856691 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (67068193309389 / 160000000000) 2 (IntervalRat.scale (675 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-33045543969 / 1000000000000) (-33045443129 / 1000000000000), orderedInterval (20696931074 / 1000000000000) (20697031914 / 1000000000000)))) (orderedInterval (-9284468026 / 1000000000000) (-9284438576 / 1000000000000))) = true
  rfl'

theorem compactCertificate466_chunkChecks2 :
    compactCertificate466.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate466.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate466_chunkChecks2_0
    compactCertificate466_chunkChecks2_1 compactCertificate466_chunkChecks2_2

theorem compactCertificate466_chunkChecks3_0 :
    compactCertificate466.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (675 / 2) 3 (IntervalRat.scale (675 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-36709096938 / 1000000000000) (-36709022683 / 1000000000000), orderedInterval (23264790528 / 1000000000000) (23264864783 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (39776155593327 / 160000000000) 3 (IntervalRat.scale (675 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-47166154596 / 1000000000000) (-47166154595 / 1000000000000), orderedInterval (-18239795746 / 1000000000000) (-18239795745 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (12862791466191 / 32000000000) 3 (IntervalRat.scale (675 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (23235250121 / 1000000000000) (23235250122 / 1000000000000), orderedInterval (32280594937 / 1000000000000) (32280594938 / 1000000000000)))) (orderedInterval (-12391521547 / 1000000000000) (-12391491992 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (11606582998989 / 160000000000) 3 (IntervalRat.scale (675 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-82093713498 / 1000000000000) (-82093713497 / 1000000000000), orderedInterval (-44561698566 / 1000000000000) (-44561698565 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (31176914536233 / 160000000000) 3 (IntervalRat.scale (675 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (43381715273 / 1000000000000) (43381715274 / 1000000000000), orderedInterval (37106412031 / 1000000000000) (37106412032 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (84651387739461 / 160000000000) 3 (IntervalRat.scale (675 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30475435377 / 1000000000000) (30475532057 / 1000000000000), orderedInterval (-16597573270 / 1000000000000) (-16597476590 / 1000000000000)))) (orderedInterval (-4824973980 / 1000000000000) (-4824947358 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (62353829072493 / 160000000000) 3 (IntervalRat.scale (675 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (32616019189 / 1000000000000) (32616019190 / 1000000000000), orderedInterval (23827841234 / 1000000000000) (23827841235 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (106844348902689 / 160000000000) 3 (IntervalRat.scale (675 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (17353506322 / 1000000000000) (17353506877 / 1000000000000), orderedInterval (-25551151803 / 1000000000000) (-25551151248 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (78701063818851 / 160000000000) 3 (IntervalRat.scale (675 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (19208885450 / 1000000000000) (19208886538 / 1000000000000), orderedInterval (-30437825972 / 1000000000000) (-30437824884 / 1000000000000)))) (orderedInterval (-3830567182 / 1000000000000) (-3830566861 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate466_chunkChecks3_1 :
    compactCertificate466.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (120747670784973 / 160000000000) 3 (IntervalRat.scale (675 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (28913706661 / 1000000000000) (28913707464 / 1000000000000), orderedInterval (2731803599 / 1000000000000) (2731804402 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (69713700231717 / 160000000000) 3 (IntervalRat.scale (675 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (7055335527 / 1000000000000) (7055335535 / 1000000000000), orderedInterval (-37575768187 / 1000000000000) (-37575768179 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (123708184419753 / 160000000000) 3 (IntervalRat.scale (675 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (25946838654 / 1000000000000) (25946838661 / 1000000000000), orderedInterval (12236547942 / 1000000000000) (12236547949 / 1000000000000)))) (orderedInterval (-9512855799 / 1000000000000) (-9512852886 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (115584232888557 / 160000000000) 3 (IntervalRat.scale (675 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (17257517787 / 1000000000000) (17257517788 / 1000000000000), orderedInterval (24142412805 / 1000000000000) (24142412806 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (82486362509181 / 160000000000) 3 (IntervalRat.scale (675 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (31376716450 / 1000000000000) (31376716452 / 1000000000000), orderedInterval (15792399867 / 1000000000000) (15792399869 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (93530743608699 / 160000000000) 3 (IntervalRat.scale (675 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (28052535589 / 1000000000000) (28052535590 / 1000000000000), orderedInterval (17357024158 / 1000000000000) (17357024159 / 1000000000000)))) (orderedInterval (-577149788 / 1000000000000) (-577149603 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (77976182950731 / 160000000000) 3 (IntervalRat.scale (675 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-33545888970 / 1000000000000) (-33545888968 / 1000000000000), orderedInterval (-13417662098 / 1000000000000) (-13417662096 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (68894322417351 / 160000000000) 3 (IntervalRat.scale (675 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-31856816692 / 1000000000000) (-31856816691 / 1000000000000), orderedInterval (-21495007551 / 1000000000000) (-21495007550 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (19968259921749 / 32000000000) 3 (IntervalRat.scale (675 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (11954701651 / 1000000000000) (11954701692 / 1000000000000), orderedInterval (-29628762927 / 1000000000000) (-29628762886 / 1000000000000)))) (orderedInterval (2716322045 / 1000000000000) (2716322159 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate466_chunkChecks3_2 :
    compactCertificate466.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (55233257815503 / 160000000000) 3 (IntervalRat.scale (675 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (17420727993 / 1000000000000) (17420727994 / 1000000000000), orderedInterval (39226304532 / 1000000000000) (39226304533 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (46821844341783 / 160000000000) 3 (IntervalRat.scale (675 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-44311846002 / 1000000000000) (-44311846000 / 1000000000000), orderedInterval (-14481767439 / 1000000000000) (-14481767437 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (29298936181149 / 160000000000) 3 (IntervalRat.scale (675 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (58538862956 / 1000000000000) (58538863271 / 1000000000000), orderedInterval (-7212291836 / 1000000000000) (-7212291520 / 1000000000000)))) (orderedInterval (6213294430 / 1000000000000) (6213294504 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (15757065322083 / 160000000000) 3 (IntervalRat.scale (675 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-76674969776 / 1000000000000) (-76674967978 / 1000000000000), orderedInterval (24580792675 / 1000000000000) (24580794474 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (42783497535249 / 160000000000) 3 (IntervalRat.scale (675 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-44465156306 / 1000000000000) (-44465156305 / 1000000000000), orderedInterval (-20007950690 / 1000000000000) (-20007950689 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (58417208210673 / 160000000000) 3 (IntervalRat.scale (675 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (41535981372 / 1000000000000) (41535981424 / 1000000000000), orderedInterval (4233878397 / 1000000000000) (4233878449 / 1000000000000)))) (orderedInterval (187519997 / 1000000000000) (187520040 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (24701063818851 / 160000000000) 3 (IntervalRat.scale (675 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-60483769894 / 1000000000000) (-60483769893 / 1000000000000), orderedInterval (-21376594259 / 1000000000000) (-21376594258 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (100408453061571 / 160000000000) 3 (IntervalRat.scale (675 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (621040002 / 1000000000000) (621040003 / 1000000000000), orderedInterval (31843856690 / 1000000000000) (31843856691 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (67068193309389 / 160000000000) 3 (IntervalRat.scale (675 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-33045543969 / 1000000000000) (-33045443129 / 1000000000000), orderedInterval (20696931074 / 1000000000000) (20697031914 / 1000000000000)))) (orderedInterval (24144063611 / 1000000000000) (24144100246 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate466_chunkChecks3 :
    compactCertificate466.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate466.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate466_chunkChecks3_0
    compactCertificate466_chunkChecks3_1 compactCertificate466_chunkChecks3_2

theorem compactCertificate466_chunkChecks4_0 :
    compactCertificate466.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (675 / 2) 4 (IntervalRat.scale (675 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-36709096938 / 1000000000000) (-36709022683 / 1000000000000), orderedInterval (23264790528 / 1000000000000) (23264864783 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (39776155593327 / 160000000000) 4 (IntervalRat.scale (675 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-47166154596 / 1000000000000) (-47166154595 / 1000000000000), orderedInterval (-18239795746 / 1000000000000) (-18239795745 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (12862791466191 / 32000000000) 4 (IntervalRat.scale (675 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (23235250121 / 1000000000000) (23235250122 / 1000000000000), orderedInterval (32280594937 / 1000000000000) (32280594938 / 1000000000000)))) (orderedInterval (-11862622377 / 1000000000000) (-11862592730 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (11606582998989 / 160000000000) 4 (IntervalRat.scale (675 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-82093713498 / 1000000000000) (-82093713497 / 1000000000000), orderedInterval (-44561698566 / 1000000000000) (-44561698565 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (31176914536233 / 160000000000) 4 (IntervalRat.scale (675 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (43381715273 / 1000000000000) (43381715274 / 1000000000000), orderedInterval (37106412031 / 1000000000000) (37106412032 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (84651387739461 / 160000000000) 4 (IntervalRat.scale (675 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30475435377 / 1000000000000) (30475532057 / 1000000000000), orderedInterval (-16597573270 / 1000000000000) (-16597476590 / 1000000000000)))) (orderedInterval (-12876820151 / 1000000000000) (-12876778342 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (62353829072493 / 160000000000) 4 (IntervalRat.scale (675 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (32616019189 / 1000000000000) (32616019190 / 1000000000000), orderedInterval (23827841234 / 1000000000000) (23827841235 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (106844348902689 / 160000000000) 4 (IntervalRat.scale (675 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (17353506322 / 1000000000000) (17353506877 / 1000000000000), orderedInterval (-25551151803 / 1000000000000) (-25551151248 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (78701063818851 / 160000000000) 4 (IntervalRat.scale (675 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (19208885450 / 1000000000000) (19208886538 / 1000000000000), orderedInterval (-30437825972 / 1000000000000) (-30437824884 / 1000000000000)))) (orderedInterval (-6086051186 / 1000000000000) (-6086050607 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate466_chunkChecks4_1 :
    compactCertificate466.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (120747670784973 / 160000000000) 4 (IntervalRat.scale (675 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (28913706661 / 1000000000000) (28913707464 / 1000000000000), orderedInterval (2731803599 / 1000000000000) (2731804402 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (69713700231717 / 160000000000) 4 (IntervalRat.scale (675 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (7055335527 / 1000000000000) (7055335535 / 1000000000000), orderedInterval (-37575768187 / 1000000000000) (-37575768179 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (123708184419753 / 160000000000) 4 (IntervalRat.scale (675 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (25946838654 / 1000000000000) (25946838661 / 1000000000000), orderedInterval (12236547942 / 1000000000000) (12236547949 / 1000000000000)))) (orderedInterval (-25337948731 / 1000000000000) (-25337942234 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (115584232888557 / 160000000000) 4 (IntervalRat.scale (675 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (17257517787 / 1000000000000) (17257517788 / 1000000000000), orderedInterval (24142412805 / 1000000000000) (24142412806 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (82486362509181 / 160000000000) 4 (IntervalRat.scale (675 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (31376716450 / 1000000000000) (31376716452 / 1000000000000), orderedInterval (15792399867 / 1000000000000) (15792399869 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (93530743608699 / 160000000000) 4 (IntervalRat.scale (675 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (28052535589 / 1000000000000) (28052535590 / 1000000000000), orderedInterval (17357024158 / 1000000000000) (17357024159 / 1000000000000)))) (orderedInterval (8340208531 / 1000000000000) (8340208851 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (77976182950731 / 160000000000) 4 (IntervalRat.scale (675 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-33545888970 / 1000000000000) (-33545888968 / 1000000000000), orderedInterval (-13417662098 / 1000000000000) (-13417662096 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (68894322417351 / 160000000000) 4 (IntervalRat.scale (675 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-31856816692 / 1000000000000) (-31856816691 / 1000000000000), orderedInterval (-21495007551 / 1000000000000) (-21495007550 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (19968259921749 / 32000000000) 4 (IntervalRat.scale (675 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (11954701651 / 1000000000000) (11954701692 / 1000000000000), orderedInterval (-29628762927 / 1000000000000) (-29628762886 / 1000000000000)))) (orderedInterval (6706703192 / 1000000000000) (6706703374 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate466_chunkChecks4_2 :
    compactCertificate466.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (55233257815503 / 160000000000) 4 (IntervalRat.scale (675 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (17420727993 / 1000000000000) (17420727994 / 1000000000000), orderedInterval (39226304532 / 1000000000000) (39226304533 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (46821844341783 / 160000000000) 4 (IntervalRat.scale (675 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-44311846002 / 1000000000000) (-44311846000 / 1000000000000), orderedInterval (-14481767439 / 1000000000000) (-14481767437 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (29298936181149 / 160000000000) 4 (IntervalRat.scale (675 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (58538862956 / 1000000000000) (58538863271 / 1000000000000), orderedInterval (-7212291836 / 1000000000000) (-7212291520 / 1000000000000)))) (orderedInterval (-1502803822 / 1000000000000) (-1502803749 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (15757065322083 / 160000000000) 4 (IntervalRat.scale (675 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-76674969776 / 1000000000000) (-76674967978 / 1000000000000), orderedInterval (24580792675 / 1000000000000) (24580794474 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (42783497535249 / 160000000000) 4 (IntervalRat.scale (675 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-44465156306 / 1000000000000) (-44465156305 / 1000000000000), orderedInterval (-20007950690 / 1000000000000) (-20007950689 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (58417208210673 / 160000000000) 4 (IntervalRat.scale (675 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (41535981372 / 1000000000000) (41535981424 / 1000000000000), orderedInterval (4233878397 / 1000000000000) (4233878449 / 1000000000000)))) (orderedInterval (-3953083849 / 1000000000000) (-3953083804 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (24701063818851 / 160000000000) 4 (IntervalRat.scale (675 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-60483769894 / 1000000000000) (-60483769893 / 1000000000000), orderedInterval (-21376594259 / 1000000000000) (-21376594258 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (100408453061571 / 160000000000) 4 (IntervalRat.scale (675 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (621040002 / 1000000000000) (621040003 / 1000000000000), orderedInterval (31843856690 / 1000000000000) (31843856691 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (67068193309389 / 160000000000) 4 (IntervalRat.scale (675 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-33045543969 / 1000000000000) (-33045443129 / 1000000000000), orderedInterval (20696931074 / 1000000000000) (20697031914 / 1000000000000)))) (orderedInterval (13990142395 / 1000000000000) (13990188111 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate466_chunkChecks4 :
    compactCertificate466.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate466.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate466_chunkChecks4_0
    compactCertificate466_chunkChecks4_1 compactCertificate466_chunkChecks4_2

theorem compactCertificate466_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate466.chunkCheck r b = true :=
  compactCertificate466.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate466_chunkChecks0
    · exact compactCertificate466_chunkChecks1
    · exact compactCertificate466_chunkChecks2
    · exact compactCertificate466_chunkChecks3
    · exact compactCertificate466_chunkChecks4)

theorem compactCertificate466_coefficient0 :
    compactCertificate466.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate466_coefficient1 :
    compactCertificate466.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate466_coefficient2 :
    compactCertificate466.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate466_coefficient3 :
    compactCertificate466.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate466_coefficient4 :
    compactCertificate466.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate466_coefficients : ∀ r : Fin 5,
    compactCertificate466.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate466_coefficient0
  · exact compactCertificate466_coefficient1
  · exact compactCertificate466_coefficient2
  · exact compactCertificate466_coefficient3
  · exact compactCertificate466_coefficient4

theorem compactCertificate466_lower : (1 : ℚ) ≤ compactCertificate466.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate466, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate466_proves {t : ℝ} (ht : t ∈ compactCertificate466.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate466.proves compactCertificate466_states compactCertificate466_chunks
    compactCertificate466_coefficients compactCertificate466_lower ht

end Erdos232
