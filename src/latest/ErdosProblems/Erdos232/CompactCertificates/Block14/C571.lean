/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate571 : CompactCertificate where
  left := 442
  right := 443
  center := 885 / 2
  grid := fun i =>
    match i.val with
    | 0 => 141
    | 1 => 104
    | 2 => 168
    | 3 => 30
    | 4 => 81
    | 5 => 221
    | 6 => 163
    | 7 => 279
    | 8 => 205
    | 9 => 315
    | 10 => 182
    | 11 => 323
    | 12 => 302
    | 13 => 215
    | 14 => 244
    | 15 => 203
    | 16 => 180
    | 17 => 261
    | 18 => 144
    | 19 => 122
    | 20 => 76
    | 21 => 41
    | 22 => 112
    | 23 => 152
    | 24 => 64
    | 25 => 262
    | _ => 175
  point := fun i =>
    match i.val with
    | 0 => 885 / 2
    | 1 => 260754797778477 / 800000000000
    | 2 => 84322744056141 / 160000000000
    | 3 => 76087599660039 / 800000000000
    | 4 => 204381995293083 / 800000000000
    | 5 => 554936875180911 / 800000000000
    | 6 => 408763990586343 / 800000000000
    | 7 => 700424065028739 / 800000000000
    | 8 => 515929196145801 / 800000000000
    | 9 => 791568064034823 / 800000000000
    | 10 => 457012034852367 / 800000000000
    | 11 => 810975875640603 / 800000000000
    | 12 => 757718860047207 / 800000000000
    | 13 => 540743932004631 / 800000000000
    | 14 => 613145985879249 / 800000000000
    | 15 => 511177199343681 / 800000000000
    | 16 => 451640558069301 / 800000000000
    | 17 => 130903037264799 / 160000000000
    | 18 => 362084690123853 / 800000000000
    | 19 => 306943201796133 / 800000000000
    | 20 => 192070803854199 / 800000000000
    | 21 => 103296317111433 / 800000000000
    | 22 => 280469594953299 / 800000000000
    | 23 => 382957253825523 / 800000000000
    | 24 => 161929196145801 / 800000000000
    | 25 => 658233192292521 / 800000000000
    | _ => 439669267250439 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-11951377288 / 1000000000000) (-11951377287 / 1000000000000), orderedInterval (-35984468748 / 1000000000000) (-35984468747 / 1000000000000))
    | 1 => (orderedInterval (127099483 / 1000000000000) (127099485 / 1000000000000), orderedInterval (44194217070 / 1000000000000) (44194217072 / 1000000000000))
    | 2 => (orderedInterval (512474394 / 1000000000000) (512474395 / 1000000000000), orderedInterval (34751575035 / 1000000000000) (34751575036 / 1000000000000))
    | 3 => (orderedInterval (81583487145 / 1000000000000) (81583487239 / 1000000000000), orderedInterval (-6559849358 / 1000000000000) (-6559849263 / 1000000000000))
    | 4 => (orderedInterval (-48687031516 / 1000000000000) (-48687029801 / 1000000000000), orderedInterval (11115754625 / 1000000000000) (11115756340 / 1000000000000))
    | 5 => (orderedInterval (-4956077080 / 1000000000000) (-4956077079 / 1000000000000), orderedInterval (-29882746122 / 1000000000000) (-29882746121 / 1000000000000))
    | 6 => (orderedInterval (11753442178 / 1000000000000) (11753442228 / 1000000000000), orderedInterval (-33295102034 / 1000000000000) (-33295101984 / 1000000000000))
    | 7 => (orderedInterval (5066507364 / 1000000000000) (5066507365 / 1000000000000), orderedInterval (-26487899906 / 1000000000000) (-26487899905 / 1000000000000))
    | 8 => (orderedInterval (-31263711137 / 1000000000000) (-31263707246 / 1000000000000), orderedInterval (3142416537 / 1000000000000) (3142420427 / 1000000000000))
    | 9 => (orderedInterval (-15222556963 / 1000000000000) (-15222556962 / 1000000000000), orderedInterval (-20282082207 / 1000000000000) (-20282082206 / 1000000000000))
    | 10 => (orderedInterval (9237039164 / 1000000000000) (9237039165 / 1000000000000), orderedInterval (32071207414 / 1000000000000) (32071207415 / 1000000000000))
    | 11 => (orderedInterval (5696223207 / 1000000000000) (5696223208 / 1000000000000), orderedInterval (-24406841392 / 1000000000000) (-24406841391 / 1000000000000))
    | 12 => (orderedInterval (-19081293302 / 1000000000000) (-19081291702 / 1000000000000), orderedInterval (17561362272 / 1000000000000) (17561363872 / 1000000000000))
    | 13 => (orderedInterval (-29336037187 / 1000000000000) (-29336037158 / 1000000000000), orderedInterval (-8991599791 / 1000000000000) (-8991599761 / 1000000000000))
    | 14 => (orderedInterval (17877076986 / 1000000000000) (17877076987 / 1000000000000), orderedInterval (22594475957 / 1000000000000) (22594475958 / 1000000000000))
    | 15 => (orderedInterval (-28523095323 / 1000000000000) (-28522998378 / 1000000000000), orderedInterval (13540962598 / 1000000000000) (13541059543 / 1000000000000))
    | 16 => (orderedInterval (-5044893868 / 1000000000000) (-5044893866 / 1000000000000), orderedInterval (33203969094 / 1000000000000) (33203969096 / 1000000000000))
    | 17 => (orderedInterval (23863206409 / 1000000000000) (23863230975 / 1000000000000), orderedInterval (-14460132498 / 1000000000000) (-14460107931 / 1000000000000))
    | 18 => (orderedInterval (31591932274 / 1000000000000) (31591932275 / 1000000000000), orderedInterval (20176851851 / 1000000000000) (20176851852 / 1000000000000))
    | 19 => (orderedInterval (37812607501 / 1000000000000) (37812607503 / 1000000000000), orderedInterval (15098552139 / 1000000000000) (15098552141 / 1000000000000))
    | 20 => (orderedInterval (44125614698 / 1000000000000) (44125654391 / 1000000000000), orderedInterval (-26634900467 / 1000000000000) (-26634860773 / 1000000000000))
    | 21 => (orderedInterval (-62562675474 / 1000000000000) (-62562675473 / 1000000000000), orderedInterval (-31637596133 / 1000000000000) (-31637596132 / 1000000000000))
    | 22 => (orderedInterval (-19917099097 / 1000000000000) (-19917098075 / 1000000000000), orderedInterval (37700389339 / 1000000000000) (37700390361 / 1000000000000))
    | 23 => (orderedInterval (33745673120 / 1000000000000) (33745702826 / 1000000000000), orderedInterval (-13860258160 / 1000000000000) (-13860228454 / 1000000000000))
    | 24 => (orderedInterval (47409513575 / 1000000000000) (47409554347 / 1000000000000), orderedInterval (-30075566388 / 1000000000000) (-30075525616 / 1000000000000))
    | 25 => (orderedInterval (12831571412 / 1000000000000) (12831571413 / 1000000000000), orderedInterval (24671798290 / 1000000000000) (24671798291 / 1000000000000))
    | _ => (orderedInterval (-19021477264 / 1000000000000) (-19021477263 / 1000000000000), orderedInterval (-28205819632 / 1000000000000) (-28205819631 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-4705850688 / 1000000000000) (-4705850657 / 1000000000000)
      | 1 => orderedInterval (-2310445808 / 1000000000000) (-2310445691 / 1000000000000)
      | 2 => orderedInterval (-911853586 / 1000000000000) (-911853466 / 1000000000000)
      | 3 => orderedInterval (4199004769 / 1000000000000) (4199004945 / 1000000000000)
      | 4 => orderedInterval (-2520091887 / 1000000000000) (-2520091802 / 1000000000000)
      | 5 => orderedInterval (570319542 / 1000000000000) (570321333 / 1000000000000)
      | 6 => orderedInterval (-5754981831 / 1000000000000) (-5754980427 / 1000000000000)
      | 7 => orderedInterval (-979148981 / 1000000000000) (-979146628 / 1000000000000)
      | _ => orderedInterval (2810221039 / 1000000000000) (2810221408 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-11530891010 / 1000000000000) (-11530890975 / 1000000000000)
      | 1 => orderedInterval (3579793508 / 1000000000000) (3579793605 / 1000000000000)
      | 2 => orderedInterval (1727186952 / 1000000000000) (1727187132 / 1000000000000)
      | 3 => orderedInterval (3177774544 / 1000000000000) (3177774908 / 1000000000000)
      | 4 => orderedInterval (-2175456712 / 1000000000000) (-2175456560 / 1000000000000)
      | 5 => orderedInterval (-2882995713 / 1000000000000) (-2882992872 / 1000000000000)
      | 6 => orderedInterval (-4511252643 / 1000000000000) (-4511251839 / 1000000000000)
      | 7 => orderedInterval (641942846 / 1000000000000) (641945376 / 1000000000000)
      | _ => orderedInterval (2755630333 / 1000000000000) (2755630618 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (4719866156 / 1000000000000) (4719866196 / 1000000000000)
      | 1 => orderedInterval (-240464577 / 1000000000000) (-240464472 / 1000000000000)
      | 2 => orderedInterval (2212803578 / 1000000000000) (2212803855 / 1000000000000)
      | 3 => orderedInterval (-18921881071 / 1000000000000) (-18921880291 / 1000000000000)
      | 4 => orderedInterval (5170995517 / 1000000000000) (5170995798 / 1000000000000)
      | 5 => orderedInterval (-1865284829 / 1000000000000) (-1865280246 / 1000000000000)
      | 6 => orderedInterval (6480997230 / 1000000000000) (6480997711 / 1000000000000)
      | 7 => orderedInterval (2643191245 / 1000000000000) (2643193977 / 1000000000000)
      | _ => orderedInterval (-1960042111 / 1000000000000) (-1960041805 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (10642533435 / 1000000000000) (10642533482 / 1000000000000)
      | 1 => orderedInterval (-8261916064 / 1000000000000) (-8261915926 / 1000000000000)
      | 2 => orderedInterval (-6568465732 / 1000000000000) (-6568465300 / 1000000000000)
      | 3 => orderedInterval (-3647805933 / 1000000000000) (-3647804222 / 1000000000000)
      | 4 => orderedInterval (6722020290 / 1000000000000) (6722020824 / 1000000000000)
      | 5 => orderedInterval (5819453210 / 1000000000000) (5819460707 / 1000000000000)
      | 6 => orderedInterval (4133155389 / 1000000000000) (4133155692 / 1000000000000)
      | 7 => orderedInterval (-939925390 / 1000000000000) (-939922441 / 1000000000000)
      | _ => orderedInterval (2793776958 / 1000000000000) (2793777374 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-4724328033 / 1000000000000) (-4724327978 / 1000000000000)
      | 1 => orderedInterval (1965611884 / 1000000000000) (1965612084 / 1000000000000)
      | 2 => orderedInterval (-5774345224 / 1000000000000) (-5774344540 / 1000000000000)
      | 3 => orderedInterval (91842455952 / 1000000000000) (91842459751 / 1000000000000)
      | 4 => orderedInterval (-8717332186 / 1000000000000) (-8717331147 / 1000000000000)
      | 5 => orderedInterval (6446583306 / 1000000000000) (6446595780 / 1000000000000)
      | 6 => orderedInterval (-6632649204 / 1000000000000) (-6632648996 / 1000000000000)
      | 7 => orderedInterval (-3351376239 / 1000000000000) (-3351373047 / 1000000000000)
      | _ => orderedInterval (-3993634448 / 1000000000000) (-3993633806 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-9602827431 / 1000000000000) (-9602820985 / 1000000000000)
    | 1 => orderedInterval (-9218267895 / 1000000000000) (-9218260607 / 1000000000000)
    | 2 => orderedInterval (-1759818862 / 1000000000000) (-1759809277 / 1000000000000)
    | 3 => orderedInterval (10692826163 / 1000000000000) (10692840190 / 1000000000000)
    | _ => orderedInterval (67060985808 / 1000000000000) (67061008101 / 1000000000000)

theorem compactCertificate571_stateChecks0 :
    compactCertificate571.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 141 12 (885 / 2)) (orderedInterval (-11951377288 / 1000000000000) (-11951377287 / 1000000000000), orderedInterval (-35984468748 / 1000000000000) (-35984468747 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 104 12 (260754797778477 / 800000000000)) (orderedInterval (127099483 / 1000000000000) (127099485 / 1000000000000), orderedInterval (44194217070 / 1000000000000) (44194217072 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 168 12 (84322744056141 / 160000000000)) (orderedInterval (512474394 / 1000000000000) (512474395 / 1000000000000), orderedInterval (34751575035 / 1000000000000) (34751575036 / 1000000000000))) = true
  rfl'

theorem compactCertificate571_stateChecks1 :
    compactCertificate571.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (76087599660039 / 800000000000)) (orderedInterval (81583487145 / 1000000000000) (81583487239 / 1000000000000), orderedInterval (-6559849358 / 1000000000000) (-6559849263 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (204381995293083 / 800000000000)) (orderedInterval (-48687031516 / 1000000000000) (-48687029801 / 1000000000000), orderedInterval (11115754625 / 1000000000000) (11115756340 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 221 12 (554936875180911 / 800000000000)) (orderedInterval (-4956077080 / 1000000000000) (-4956077079 / 1000000000000), orderedInterval (-29882746122 / 1000000000000) (-29882746121 / 1000000000000))) = true
  rfl'

theorem compactCertificate571_stateChecks2 :
    compactCertificate571.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 163 12 (408763990586343 / 800000000000)) (orderedInterval (11753442178 / 1000000000000) (11753442228 / 1000000000000), orderedInterval (-33295102034 / 1000000000000) (-33295101984 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 279 12 (700424065028739 / 800000000000)) (orderedInterval (5066507364 / 1000000000000) (5066507365 / 1000000000000), orderedInterval (-26487899906 / 1000000000000) (-26487899905 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 205 12 (515929196145801 / 800000000000)) (orderedInterval (-31263711137 / 1000000000000) (-31263707246 / 1000000000000), orderedInterval (3142416537 / 1000000000000) (3142420427 / 1000000000000))) = true
  rfl'

theorem compactCertificate571_stateChecks3 :
    compactCertificate571.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 315 12 (791568064034823 / 800000000000)) (orderedInterval (-15222556963 / 1000000000000) (-15222556962 / 1000000000000), orderedInterval (-20282082207 / 1000000000000) (-20282082206 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 182 12 (457012034852367 / 800000000000)) (orderedInterval (9237039164 / 1000000000000) (9237039165 / 1000000000000), orderedInterval (32071207414 / 1000000000000) (32071207415 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 323 12 (810975875640603 / 800000000000)) (orderedInterval (5696223207 / 1000000000000) (5696223208 / 1000000000000), orderedInterval (-24406841392 / 1000000000000) (-24406841391 / 1000000000000))) = true
  rfl'

theorem compactCertificate571_stateChecks4 :
    compactCertificate571.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 302 12 (757718860047207 / 800000000000)) (orderedInterval (-19081293302 / 1000000000000) (-19081291702 / 1000000000000), orderedInterval (17561362272 / 1000000000000) (17561363872 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 215 12 (540743932004631 / 800000000000)) (orderedInterval (-29336037187 / 1000000000000) (-29336037158 / 1000000000000), orderedInterval (-8991599791 / 1000000000000) (-8991599761 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 244 12 (613145985879249 / 800000000000)) (orderedInterval (17877076986 / 1000000000000) (17877076987 / 1000000000000), orderedInterval (22594475957 / 1000000000000) (22594475958 / 1000000000000))) = true
  rfl'

theorem compactCertificate571_stateChecks5 :
    compactCertificate571.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 203 12 (511177199343681 / 800000000000)) (orderedInterval (-28523095323 / 1000000000000) (-28522998378 / 1000000000000), orderedInterval (13540962598 / 1000000000000) (13541059543 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 180 12 (451640558069301 / 800000000000)) (orderedInterval (-5044893868 / 1000000000000) (-5044893866 / 1000000000000), orderedInterval (33203969094 / 1000000000000) (33203969096 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 261 12 (130903037264799 / 160000000000)) (orderedInterval (23863206409 / 1000000000000) (23863230975 / 1000000000000), orderedInterval (-14460132498 / 1000000000000) (-14460107931 / 1000000000000))) = true
  rfl'

theorem compactCertificate571_stateChecks6 :
    compactCertificate571.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 144 12 (362084690123853 / 800000000000)) (orderedInterval (31591932274 / 1000000000000) (31591932275 / 1000000000000), orderedInterval (20176851851 / 1000000000000) (20176851852 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 122 12 (306943201796133 / 800000000000)) (orderedInterval (37812607501 / 1000000000000) (37812607503 / 1000000000000), orderedInterval (15098552139 / 1000000000000) (15098552141 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (192070803854199 / 800000000000)) (orderedInterval (44125614698 / 1000000000000) (44125654391 / 1000000000000), orderedInterval (-26634900467 / 1000000000000) (-26634860773 / 1000000000000))) = true
  rfl'

theorem compactCertificate571_stateChecks7 :
    compactCertificate571.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (103296317111433 / 800000000000)) (orderedInterval (-62562675474 / 1000000000000) (-62562675473 / 1000000000000), orderedInterval (-31637596133 / 1000000000000) (-31637596132 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 112 12 (280469594953299 / 800000000000)) (orderedInterval (-19917099097 / 1000000000000) (-19917098075 / 1000000000000), orderedInterval (37700389339 / 1000000000000) (37700390361 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 152 12 (382957253825523 / 800000000000)) (orderedInterval (33745673120 / 1000000000000) (33745702826 / 1000000000000), orderedInterval (-13860258160 / 1000000000000) (-13860228454 / 1000000000000))) = true
  rfl'

theorem compactCertificate571_stateChecks8 :
    compactCertificate571.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (161929196145801 / 800000000000)) (orderedInterval (47409513575 / 1000000000000) (47409554347 / 1000000000000), orderedInterval (-30075566388 / 1000000000000) (-30075525616 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 262 12 (658233192292521 / 800000000000)) (orderedInterval (12831571412 / 1000000000000) (12831571413 / 1000000000000), orderedInterval (24671798290 / 1000000000000) (24671798291 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 175 12 (439669267250439 / 800000000000)) (orderedInterval (-19021477264 / 1000000000000) (-19021477263 / 1000000000000), orderedInterval (-28205819632 / 1000000000000) (-28205819631 / 1000000000000))) = true
  rfl'

theorem compactCertificate571_states : ∀ j,
    BesselStateValid (compactCertificate571.point j) (compactCertificate571.state j) :=
  compactCertificate571.statesValid_of_checks3 compactCertificate571_stateChecks0
    compactCertificate571_stateChecks1 compactCertificate571_stateChecks2
    compactCertificate571_stateChecks3 compactCertificate571_stateChecks4
    compactCertificate571_stateChecks5 compactCertificate571_stateChecks6
    compactCertificate571_stateChecks7 compactCertificate571_stateChecks8

theorem compactCertificate571_chunkChecks0_0 :
    compactCertificate571.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (885 / 2) 0 (IntervalRat.scale (885 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-11951377288 / 1000000000000) (-11951377287 / 1000000000000), orderedInterval (-35984468748 / 1000000000000) (-35984468747 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (260754797778477 / 800000000000) 0 (IntervalRat.scale (885 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (127099483 / 1000000000000) (127099485 / 1000000000000), orderedInterval (44194217070 / 1000000000000) (44194217072 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (84322744056141 / 160000000000) 0 (IntervalRat.scale (885 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (512474394 / 1000000000000) (512474395 / 1000000000000), orderedInterval (34751575035 / 1000000000000) (34751575036 / 1000000000000)))) (orderedInterval (-4705850688 / 1000000000000) (-4705850657 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (76087599660039 / 800000000000) 0 (IntervalRat.scale (885 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (81583487145 / 1000000000000) (81583487239 / 1000000000000), orderedInterval (-6559849358 / 1000000000000) (-6559849263 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (204381995293083 / 800000000000) 0 (IntervalRat.scale (885 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-48687031516 / 1000000000000) (-48687029801 / 1000000000000), orderedInterval (11115754625 / 1000000000000) (11115756340 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (554936875180911 / 800000000000) 0 (IntervalRat.scale (885 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-4956077080 / 1000000000000) (-4956077079 / 1000000000000), orderedInterval (-29882746122 / 1000000000000) (-29882746121 / 1000000000000)))) (orderedInterval (-2310445808 / 1000000000000) (-2310445691 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (408763990586343 / 800000000000) 0 (IntervalRat.scale (885 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (11753442178 / 1000000000000) (11753442228 / 1000000000000), orderedInterval (-33295102034 / 1000000000000) (-33295101984 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (700424065028739 / 800000000000) 0 (IntervalRat.scale (885 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (5066507364 / 1000000000000) (5066507365 / 1000000000000), orderedInterval (-26487899906 / 1000000000000) (-26487899905 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (515929196145801 / 800000000000) 0 (IntervalRat.scale (885 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-31263711137 / 1000000000000) (-31263707246 / 1000000000000), orderedInterval (3142416537 / 1000000000000) (3142420427 / 1000000000000)))) (orderedInterval (-911853586 / 1000000000000) (-911853466 / 1000000000000))) = true
  rfl'

theorem compactCertificate571_chunkChecks0_1 :
    compactCertificate571.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (791568064034823 / 800000000000) 0 (IntervalRat.scale (885 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-15222556963 / 1000000000000) (-15222556962 / 1000000000000), orderedInterval (-20282082207 / 1000000000000) (-20282082206 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (457012034852367 / 800000000000) 0 (IntervalRat.scale (885 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (9237039164 / 1000000000000) (9237039165 / 1000000000000), orderedInterval (32071207414 / 1000000000000) (32071207415 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (810975875640603 / 800000000000) 0 (IntervalRat.scale (885 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (5696223207 / 1000000000000) (5696223208 / 1000000000000), orderedInterval (-24406841392 / 1000000000000) (-24406841391 / 1000000000000)))) (orderedInterval (4199004769 / 1000000000000) (4199004945 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (757718860047207 / 800000000000) 0 (IntervalRat.scale (885 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-19081293302 / 1000000000000) (-19081291702 / 1000000000000), orderedInterval (17561362272 / 1000000000000) (17561363872 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (540743932004631 / 800000000000) 0 (IntervalRat.scale (885 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-29336037187 / 1000000000000) (-29336037158 / 1000000000000), orderedInterval (-8991599791 / 1000000000000) (-8991599761 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (613145985879249 / 800000000000) 0 (IntervalRat.scale (885 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (17877076986 / 1000000000000) (17877076987 / 1000000000000), orderedInterval (22594475957 / 1000000000000) (22594475958 / 1000000000000)))) (orderedInterval (-2520091887 / 1000000000000) (-2520091802 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (511177199343681 / 800000000000) 0 (IntervalRat.scale (885 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-28523095323 / 1000000000000) (-28522998378 / 1000000000000), orderedInterval (13540962598 / 1000000000000) (13541059543 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (451640558069301 / 800000000000) 0 (IntervalRat.scale (885 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-5044893868 / 1000000000000) (-5044893866 / 1000000000000), orderedInterval (33203969094 / 1000000000000) (33203969096 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (130903037264799 / 160000000000) 0 (IntervalRat.scale (885 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (23863206409 / 1000000000000) (23863230975 / 1000000000000), orderedInterval (-14460132498 / 1000000000000) (-14460107931 / 1000000000000)))) (orderedInterval (570319542 / 1000000000000) (570321333 / 1000000000000))) = true
  rfl'

theorem compactCertificate571_chunkChecks0_2 :
    compactCertificate571.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (362084690123853 / 800000000000) 0 (IntervalRat.scale (885 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (31591932274 / 1000000000000) (31591932275 / 1000000000000), orderedInterval (20176851851 / 1000000000000) (20176851852 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (306943201796133 / 800000000000) 0 (IntervalRat.scale (885 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (37812607501 / 1000000000000) (37812607503 / 1000000000000), orderedInterval (15098552139 / 1000000000000) (15098552141 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (192070803854199 / 800000000000) 0 (IntervalRat.scale (885 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (44125614698 / 1000000000000) (44125654391 / 1000000000000), orderedInterval (-26634900467 / 1000000000000) (-26634860773 / 1000000000000)))) (orderedInterval (-5754981831 / 1000000000000) (-5754980427 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (103296317111433 / 800000000000) 0 (IntervalRat.scale (885 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-62562675474 / 1000000000000) (-62562675473 / 1000000000000), orderedInterval (-31637596133 / 1000000000000) (-31637596132 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (280469594953299 / 800000000000) 0 (IntervalRat.scale (885 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-19917099097 / 1000000000000) (-19917098075 / 1000000000000), orderedInterval (37700389339 / 1000000000000) (37700390361 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (382957253825523 / 800000000000) 0 (IntervalRat.scale (885 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (33745673120 / 1000000000000) (33745702826 / 1000000000000), orderedInterval (-13860258160 / 1000000000000) (-13860228454 / 1000000000000)))) (orderedInterval (-979148981 / 1000000000000) (-979146628 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (161929196145801 / 800000000000) 0 (IntervalRat.scale (885 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (47409513575 / 1000000000000) (47409554347 / 1000000000000), orderedInterval (-30075566388 / 1000000000000) (-30075525616 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (658233192292521 / 800000000000) 0 (IntervalRat.scale (885 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (12831571412 / 1000000000000) (12831571413 / 1000000000000), orderedInterval (24671798290 / 1000000000000) (24671798291 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (439669267250439 / 800000000000) 0 (IntervalRat.scale (885 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-19021477264 / 1000000000000) (-19021477263 / 1000000000000), orderedInterval (-28205819632 / 1000000000000) (-28205819631 / 1000000000000)))) (orderedInterval (2810221039 / 1000000000000) (2810221408 / 1000000000000))) = true
  rfl'

theorem compactCertificate571_chunkChecks0 :
    compactCertificate571.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate571.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate571_chunkChecks0_0
    compactCertificate571_chunkChecks0_1 compactCertificate571_chunkChecks0_2

theorem compactCertificate571_chunkChecks1_0 :
    compactCertificate571.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (885 / 2) 1 (IntervalRat.scale (885 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-11951377288 / 1000000000000) (-11951377287 / 1000000000000), orderedInterval (-35984468748 / 1000000000000) (-35984468747 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (260754797778477 / 800000000000) 1 (IntervalRat.scale (885 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (127099483 / 1000000000000) (127099485 / 1000000000000), orderedInterval (44194217070 / 1000000000000) (44194217072 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (84322744056141 / 160000000000) 1 (IntervalRat.scale (885 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (512474394 / 1000000000000) (512474395 / 1000000000000), orderedInterval (34751575035 / 1000000000000) (34751575036 / 1000000000000)))) (orderedInterval (-11530891010 / 1000000000000) (-11530890975 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (76087599660039 / 800000000000) 1 (IntervalRat.scale (885 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (81583487145 / 1000000000000) (81583487239 / 1000000000000), orderedInterval (-6559849358 / 1000000000000) (-6559849263 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (204381995293083 / 800000000000) 1 (IntervalRat.scale (885 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-48687031516 / 1000000000000) (-48687029801 / 1000000000000), orderedInterval (11115754625 / 1000000000000) (11115756340 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (554936875180911 / 800000000000) 1 (IntervalRat.scale (885 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-4956077080 / 1000000000000) (-4956077079 / 1000000000000), orderedInterval (-29882746122 / 1000000000000) (-29882746121 / 1000000000000)))) (orderedInterval (3579793508 / 1000000000000) (3579793605 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (408763990586343 / 800000000000) 1 (IntervalRat.scale (885 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (11753442178 / 1000000000000) (11753442228 / 1000000000000), orderedInterval (-33295102034 / 1000000000000) (-33295101984 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (700424065028739 / 800000000000) 1 (IntervalRat.scale (885 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (5066507364 / 1000000000000) (5066507365 / 1000000000000), orderedInterval (-26487899906 / 1000000000000) (-26487899905 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (515929196145801 / 800000000000) 1 (IntervalRat.scale (885 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-31263711137 / 1000000000000) (-31263707246 / 1000000000000), orderedInterval (3142416537 / 1000000000000) (3142420427 / 1000000000000)))) (orderedInterval (1727186952 / 1000000000000) (1727187132 / 1000000000000))) = true
  rfl'

theorem compactCertificate571_chunkChecks1_1 :
    compactCertificate571.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (791568064034823 / 800000000000) 1 (IntervalRat.scale (885 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-15222556963 / 1000000000000) (-15222556962 / 1000000000000), orderedInterval (-20282082207 / 1000000000000) (-20282082206 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (457012034852367 / 800000000000) 1 (IntervalRat.scale (885 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (9237039164 / 1000000000000) (9237039165 / 1000000000000), orderedInterval (32071207414 / 1000000000000) (32071207415 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (810975875640603 / 800000000000) 1 (IntervalRat.scale (885 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (5696223207 / 1000000000000) (5696223208 / 1000000000000), orderedInterval (-24406841392 / 1000000000000) (-24406841391 / 1000000000000)))) (orderedInterval (3177774544 / 1000000000000) (3177774908 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (757718860047207 / 800000000000) 1 (IntervalRat.scale (885 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-19081293302 / 1000000000000) (-19081291702 / 1000000000000), orderedInterval (17561362272 / 1000000000000) (17561363872 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (540743932004631 / 800000000000) 1 (IntervalRat.scale (885 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-29336037187 / 1000000000000) (-29336037158 / 1000000000000), orderedInterval (-8991599791 / 1000000000000) (-8991599761 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (613145985879249 / 800000000000) 1 (IntervalRat.scale (885 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (17877076986 / 1000000000000) (17877076987 / 1000000000000), orderedInterval (22594475957 / 1000000000000) (22594475958 / 1000000000000)))) (orderedInterval (-2175456712 / 1000000000000) (-2175456560 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (511177199343681 / 800000000000) 1 (IntervalRat.scale (885 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-28523095323 / 1000000000000) (-28522998378 / 1000000000000), orderedInterval (13540962598 / 1000000000000) (13541059543 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (451640558069301 / 800000000000) 1 (IntervalRat.scale (885 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-5044893868 / 1000000000000) (-5044893866 / 1000000000000), orderedInterval (33203969094 / 1000000000000) (33203969096 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (130903037264799 / 160000000000) 1 (IntervalRat.scale (885 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (23863206409 / 1000000000000) (23863230975 / 1000000000000), orderedInterval (-14460132498 / 1000000000000) (-14460107931 / 1000000000000)))) (orderedInterval (-2882995713 / 1000000000000) (-2882992872 / 1000000000000))) = true
  rfl'

theorem compactCertificate571_chunkChecks1_2 :
    compactCertificate571.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (362084690123853 / 800000000000) 1 (IntervalRat.scale (885 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (31591932274 / 1000000000000) (31591932275 / 1000000000000), orderedInterval (20176851851 / 1000000000000) (20176851852 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (306943201796133 / 800000000000) 1 (IntervalRat.scale (885 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (37812607501 / 1000000000000) (37812607503 / 1000000000000), orderedInterval (15098552139 / 1000000000000) (15098552141 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (192070803854199 / 800000000000) 1 (IntervalRat.scale (885 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (44125614698 / 1000000000000) (44125654391 / 1000000000000), orderedInterval (-26634900467 / 1000000000000) (-26634860773 / 1000000000000)))) (orderedInterval (-4511252643 / 1000000000000) (-4511251839 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (103296317111433 / 800000000000) 1 (IntervalRat.scale (885 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-62562675474 / 1000000000000) (-62562675473 / 1000000000000), orderedInterval (-31637596133 / 1000000000000) (-31637596132 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (280469594953299 / 800000000000) 1 (IntervalRat.scale (885 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-19917099097 / 1000000000000) (-19917098075 / 1000000000000), orderedInterval (37700389339 / 1000000000000) (37700390361 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (382957253825523 / 800000000000) 1 (IntervalRat.scale (885 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (33745673120 / 1000000000000) (33745702826 / 1000000000000), orderedInterval (-13860258160 / 1000000000000) (-13860228454 / 1000000000000)))) (orderedInterval (641942846 / 1000000000000) (641945376 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (161929196145801 / 800000000000) 1 (IntervalRat.scale (885 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (47409513575 / 1000000000000) (47409554347 / 1000000000000), orderedInterval (-30075566388 / 1000000000000) (-30075525616 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (658233192292521 / 800000000000) 1 (IntervalRat.scale (885 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (12831571412 / 1000000000000) (12831571413 / 1000000000000), orderedInterval (24671798290 / 1000000000000) (24671798291 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (439669267250439 / 800000000000) 1 (IntervalRat.scale (885 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-19021477264 / 1000000000000) (-19021477263 / 1000000000000), orderedInterval (-28205819632 / 1000000000000) (-28205819631 / 1000000000000)))) (orderedInterval (2755630333 / 1000000000000) (2755630618 / 1000000000000))) = true
  rfl'

theorem compactCertificate571_chunkChecks1 :
    compactCertificate571.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate571.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate571_chunkChecks1_0
    compactCertificate571_chunkChecks1_1 compactCertificate571_chunkChecks1_2

theorem compactCertificate571_chunkChecks2_0 :
    compactCertificate571.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (885 / 2) 2 (IntervalRat.scale (885 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-11951377288 / 1000000000000) (-11951377287 / 1000000000000), orderedInterval (-35984468748 / 1000000000000) (-35984468747 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (260754797778477 / 800000000000) 2 (IntervalRat.scale (885 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (127099483 / 1000000000000) (127099485 / 1000000000000), orderedInterval (44194217070 / 1000000000000) (44194217072 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (84322744056141 / 160000000000) 2 (IntervalRat.scale (885 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (512474394 / 1000000000000) (512474395 / 1000000000000), orderedInterval (34751575035 / 1000000000000) (34751575036 / 1000000000000)))) (orderedInterval (4719866156 / 1000000000000) (4719866196 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (76087599660039 / 800000000000) 2 (IntervalRat.scale (885 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (81583487145 / 1000000000000) (81583487239 / 1000000000000), orderedInterval (-6559849358 / 1000000000000) (-6559849263 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (204381995293083 / 800000000000) 2 (IntervalRat.scale (885 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-48687031516 / 1000000000000) (-48687029801 / 1000000000000), orderedInterval (11115754625 / 1000000000000) (11115756340 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (554936875180911 / 800000000000) 2 (IntervalRat.scale (885 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-4956077080 / 1000000000000) (-4956077079 / 1000000000000), orderedInterval (-29882746122 / 1000000000000) (-29882746121 / 1000000000000)))) (orderedInterval (-240464577 / 1000000000000) (-240464472 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (408763990586343 / 800000000000) 2 (IntervalRat.scale (885 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (11753442178 / 1000000000000) (11753442228 / 1000000000000), orderedInterval (-33295102034 / 1000000000000) (-33295101984 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (700424065028739 / 800000000000) 2 (IntervalRat.scale (885 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (5066507364 / 1000000000000) (5066507365 / 1000000000000), orderedInterval (-26487899906 / 1000000000000) (-26487899905 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (515929196145801 / 800000000000) 2 (IntervalRat.scale (885 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-31263711137 / 1000000000000) (-31263707246 / 1000000000000), orderedInterval (3142416537 / 1000000000000) (3142420427 / 1000000000000)))) (orderedInterval (2212803578 / 1000000000000) (2212803855 / 1000000000000))) = true
  rfl'

theorem compactCertificate571_chunkChecks2_1 :
    compactCertificate571.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (791568064034823 / 800000000000) 2 (IntervalRat.scale (885 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-15222556963 / 1000000000000) (-15222556962 / 1000000000000), orderedInterval (-20282082207 / 1000000000000) (-20282082206 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (457012034852367 / 800000000000) 2 (IntervalRat.scale (885 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (9237039164 / 1000000000000) (9237039165 / 1000000000000), orderedInterval (32071207414 / 1000000000000) (32071207415 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (810975875640603 / 800000000000) 2 (IntervalRat.scale (885 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (5696223207 / 1000000000000) (5696223208 / 1000000000000), orderedInterval (-24406841392 / 1000000000000) (-24406841391 / 1000000000000)))) (orderedInterval (-18921881071 / 1000000000000) (-18921880291 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (757718860047207 / 800000000000) 2 (IntervalRat.scale (885 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-19081293302 / 1000000000000) (-19081291702 / 1000000000000), orderedInterval (17561362272 / 1000000000000) (17561363872 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (540743932004631 / 800000000000) 2 (IntervalRat.scale (885 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-29336037187 / 1000000000000) (-29336037158 / 1000000000000), orderedInterval (-8991599791 / 1000000000000) (-8991599761 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (613145985879249 / 800000000000) 2 (IntervalRat.scale (885 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (17877076986 / 1000000000000) (17877076987 / 1000000000000), orderedInterval (22594475957 / 1000000000000) (22594475958 / 1000000000000)))) (orderedInterval (5170995517 / 1000000000000) (5170995798 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (511177199343681 / 800000000000) 2 (IntervalRat.scale (885 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-28523095323 / 1000000000000) (-28522998378 / 1000000000000), orderedInterval (13540962598 / 1000000000000) (13541059543 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (451640558069301 / 800000000000) 2 (IntervalRat.scale (885 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-5044893868 / 1000000000000) (-5044893866 / 1000000000000), orderedInterval (33203969094 / 1000000000000) (33203969096 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (130903037264799 / 160000000000) 2 (IntervalRat.scale (885 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (23863206409 / 1000000000000) (23863230975 / 1000000000000), orderedInterval (-14460132498 / 1000000000000) (-14460107931 / 1000000000000)))) (orderedInterval (-1865284829 / 1000000000000) (-1865280246 / 1000000000000))) = true
  rfl'

theorem compactCertificate571_chunkChecks2_2 :
    compactCertificate571.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (362084690123853 / 800000000000) 2 (IntervalRat.scale (885 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (31591932274 / 1000000000000) (31591932275 / 1000000000000), orderedInterval (20176851851 / 1000000000000) (20176851852 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (306943201796133 / 800000000000) 2 (IntervalRat.scale (885 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (37812607501 / 1000000000000) (37812607503 / 1000000000000), orderedInterval (15098552139 / 1000000000000) (15098552141 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (192070803854199 / 800000000000) 2 (IntervalRat.scale (885 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (44125614698 / 1000000000000) (44125654391 / 1000000000000), orderedInterval (-26634900467 / 1000000000000) (-26634860773 / 1000000000000)))) (orderedInterval (6480997230 / 1000000000000) (6480997711 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (103296317111433 / 800000000000) 2 (IntervalRat.scale (885 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-62562675474 / 1000000000000) (-62562675473 / 1000000000000), orderedInterval (-31637596133 / 1000000000000) (-31637596132 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (280469594953299 / 800000000000) 2 (IntervalRat.scale (885 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-19917099097 / 1000000000000) (-19917098075 / 1000000000000), orderedInterval (37700389339 / 1000000000000) (37700390361 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (382957253825523 / 800000000000) 2 (IntervalRat.scale (885 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (33745673120 / 1000000000000) (33745702826 / 1000000000000), orderedInterval (-13860258160 / 1000000000000) (-13860228454 / 1000000000000)))) (orderedInterval (2643191245 / 1000000000000) (2643193977 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (161929196145801 / 800000000000) 2 (IntervalRat.scale (885 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (47409513575 / 1000000000000) (47409554347 / 1000000000000), orderedInterval (-30075566388 / 1000000000000) (-30075525616 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (658233192292521 / 800000000000) 2 (IntervalRat.scale (885 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (12831571412 / 1000000000000) (12831571413 / 1000000000000), orderedInterval (24671798290 / 1000000000000) (24671798291 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (439669267250439 / 800000000000) 2 (IntervalRat.scale (885 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-19021477264 / 1000000000000) (-19021477263 / 1000000000000), orderedInterval (-28205819632 / 1000000000000) (-28205819631 / 1000000000000)))) (orderedInterval (-1960042111 / 1000000000000) (-1960041805 / 1000000000000))) = true
  rfl'

theorem compactCertificate571_chunkChecks2 :
    compactCertificate571.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate571.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate571_chunkChecks2_0
    compactCertificate571_chunkChecks2_1 compactCertificate571_chunkChecks2_2

theorem compactCertificate571_chunkChecks3_0 :
    compactCertificate571.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (885 / 2) 3 (IntervalRat.scale (885 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-11951377288 / 1000000000000) (-11951377287 / 1000000000000), orderedInterval (-35984468748 / 1000000000000) (-35984468747 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (260754797778477 / 800000000000) 3 (IntervalRat.scale (885 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (127099483 / 1000000000000) (127099485 / 1000000000000), orderedInterval (44194217070 / 1000000000000) (44194217072 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (84322744056141 / 160000000000) 3 (IntervalRat.scale (885 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (512474394 / 1000000000000) (512474395 / 1000000000000), orderedInterval (34751575035 / 1000000000000) (34751575036 / 1000000000000)))) (orderedInterval (10642533435 / 1000000000000) (10642533482 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (76087599660039 / 800000000000) 3 (IntervalRat.scale (885 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (81583487145 / 1000000000000) (81583487239 / 1000000000000), orderedInterval (-6559849358 / 1000000000000) (-6559849263 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (204381995293083 / 800000000000) 3 (IntervalRat.scale (885 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-48687031516 / 1000000000000) (-48687029801 / 1000000000000), orderedInterval (11115754625 / 1000000000000) (11115756340 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (554936875180911 / 800000000000) 3 (IntervalRat.scale (885 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-4956077080 / 1000000000000) (-4956077079 / 1000000000000), orderedInterval (-29882746122 / 1000000000000) (-29882746121 / 1000000000000)))) (orderedInterval (-8261916064 / 1000000000000) (-8261915926 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (408763990586343 / 800000000000) 3 (IntervalRat.scale (885 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (11753442178 / 1000000000000) (11753442228 / 1000000000000), orderedInterval (-33295102034 / 1000000000000) (-33295101984 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (700424065028739 / 800000000000) 3 (IntervalRat.scale (885 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (5066507364 / 1000000000000) (5066507365 / 1000000000000), orderedInterval (-26487899906 / 1000000000000) (-26487899905 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (515929196145801 / 800000000000) 3 (IntervalRat.scale (885 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-31263711137 / 1000000000000) (-31263707246 / 1000000000000), orderedInterval (3142416537 / 1000000000000) (3142420427 / 1000000000000)))) (orderedInterval (-6568465732 / 1000000000000) (-6568465300 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate571_chunkChecks3_1 :
    compactCertificate571.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (791568064034823 / 800000000000) 3 (IntervalRat.scale (885 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-15222556963 / 1000000000000) (-15222556962 / 1000000000000), orderedInterval (-20282082207 / 1000000000000) (-20282082206 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (457012034852367 / 800000000000) 3 (IntervalRat.scale (885 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (9237039164 / 1000000000000) (9237039165 / 1000000000000), orderedInterval (32071207414 / 1000000000000) (32071207415 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (810975875640603 / 800000000000) 3 (IntervalRat.scale (885 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (5696223207 / 1000000000000) (5696223208 / 1000000000000), orderedInterval (-24406841392 / 1000000000000) (-24406841391 / 1000000000000)))) (orderedInterval (-3647805933 / 1000000000000) (-3647804222 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (757718860047207 / 800000000000) 3 (IntervalRat.scale (885 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-19081293302 / 1000000000000) (-19081291702 / 1000000000000), orderedInterval (17561362272 / 1000000000000) (17561363872 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (540743932004631 / 800000000000) 3 (IntervalRat.scale (885 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-29336037187 / 1000000000000) (-29336037158 / 1000000000000), orderedInterval (-8991599791 / 1000000000000) (-8991599761 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (613145985879249 / 800000000000) 3 (IntervalRat.scale (885 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (17877076986 / 1000000000000) (17877076987 / 1000000000000), orderedInterval (22594475957 / 1000000000000) (22594475958 / 1000000000000)))) (orderedInterval (6722020290 / 1000000000000) (6722020824 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (511177199343681 / 800000000000) 3 (IntervalRat.scale (885 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-28523095323 / 1000000000000) (-28522998378 / 1000000000000), orderedInterval (13540962598 / 1000000000000) (13541059543 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (451640558069301 / 800000000000) 3 (IntervalRat.scale (885 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-5044893868 / 1000000000000) (-5044893866 / 1000000000000), orderedInterval (33203969094 / 1000000000000) (33203969096 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (130903037264799 / 160000000000) 3 (IntervalRat.scale (885 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (23863206409 / 1000000000000) (23863230975 / 1000000000000), orderedInterval (-14460132498 / 1000000000000) (-14460107931 / 1000000000000)))) (orderedInterval (5819453210 / 1000000000000) (5819460707 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate571_chunkChecks3_2 :
    compactCertificate571.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (362084690123853 / 800000000000) 3 (IntervalRat.scale (885 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (31591932274 / 1000000000000) (31591932275 / 1000000000000), orderedInterval (20176851851 / 1000000000000) (20176851852 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (306943201796133 / 800000000000) 3 (IntervalRat.scale (885 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (37812607501 / 1000000000000) (37812607503 / 1000000000000), orderedInterval (15098552139 / 1000000000000) (15098552141 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (192070803854199 / 800000000000) 3 (IntervalRat.scale (885 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (44125614698 / 1000000000000) (44125654391 / 1000000000000), orderedInterval (-26634900467 / 1000000000000) (-26634860773 / 1000000000000)))) (orderedInterval (4133155389 / 1000000000000) (4133155692 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (103296317111433 / 800000000000) 3 (IntervalRat.scale (885 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-62562675474 / 1000000000000) (-62562675473 / 1000000000000), orderedInterval (-31637596133 / 1000000000000) (-31637596132 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (280469594953299 / 800000000000) 3 (IntervalRat.scale (885 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-19917099097 / 1000000000000) (-19917098075 / 1000000000000), orderedInterval (37700389339 / 1000000000000) (37700390361 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (382957253825523 / 800000000000) 3 (IntervalRat.scale (885 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (33745673120 / 1000000000000) (33745702826 / 1000000000000), orderedInterval (-13860258160 / 1000000000000) (-13860228454 / 1000000000000)))) (orderedInterval (-939925390 / 1000000000000) (-939922441 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (161929196145801 / 800000000000) 3 (IntervalRat.scale (885 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (47409513575 / 1000000000000) (47409554347 / 1000000000000), orderedInterval (-30075566388 / 1000000000000) (-30075525616 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (658233192292521 / 800000000000) 3 (IntervalRat.scale (885 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (12831571412 / 1000000000000) (12831571413 / 1000000000000), orderedInterval (24671798290 / 1000000000000) (24671798291 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (439669267250439 / 800000000000) 3 (IntervalRat.scale (885 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-19021477264 / 1000000000000) (-19021477263 / 1000000000000), orderedInterval (-28205819632 / 1000000000000) (-28205819631 / 1000000000000)))) (orderedInterval (2793776958 / 1000000000000) (2793777374 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate571_chunkChecks3 :
    compactCertificate571.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate571.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate571_chunkChecks3_0
    compactCertificate571_chunkChecks3_1 compactCertificate571_chunkChecks3_2

theorem compactCertificate571_chunkChecks4_0 :
    compactCertificate571.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (885 / 2) 4 (IntervalRat.scale (885 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-11951377288 / 1000000000000) (-11951377287 / 1000000000000), orderedInterval (-35984468748 / 1000000000000) (-35984468747 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (260754797778477 / 800000000000) 4 (IntervalRat.scale (885 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (127099483 / 1000000000000) (127099485 / 1000000000000), orderedInterval (44194217070 / 1000000000000) (44194217072 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (84322744056141 / 160000000000) 4 (IntervalRat.scale (885 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (512474394 / 1000000000000) (512474395 / 1000000000000), orderedInterval (34751575035 / 1000000000000) (34751575036 / 1000000000000)))) (orderedInterval (-4724328033 / 1000000000000) (-4724327978 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (76087599660039 / 800000000000) 4 (IntervalRat.scale (885 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (81583487145 / 1000000000000) (81583487239 / 1000000000000), orderedInterval (-6559849358 / 1000000000000) (-6559849263 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (204381995293083 / 800000000000) 4 (IntervalRat.scale (885 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-48687031516 / 1000000000000) (-48687029801 / 1000000000000), orderedInterval (11115754625 / 1000000000000) (11115756340 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (554936875180911 / 800000000000) 4 (IntervalRat.scale (885 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-4956077080 / 1000000000000) (-4956077079 / 1000000000000), orderedInterval (-29882746122 / 1000000000000) (-29882746121 / 1000000000000)))) (orderedInterval (1965611884 / 1000000000000) (1965612084 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (408763990586343 / 800000000000) 4 (IntervalRat.scale (885 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (11753442178 / 1000000000000) (11753442228 / 1000000000000), orderedInterval (-33295102034 / 1000000000000) (-33295101984 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (700424065028739 / 800000000000) 4 (IntervalRat.scale (885 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (5066507364 / 1000000000000) (5066507365 / 1000000000000), orderedInterval (-26487899906 / 1000000000000) (-26487899905 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (515929196145801 / 800000000000) 4 (IntervalRat.scale (885 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-31263711137 / 1000000000000) (-31263707246 / 1000000000000), orderedInterval (3142416537 / 1000000000000) (3142420427 / 1000000000000)))) (orderedInterval (-5774345224 / 1000000000000) (-5774344540 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate571_chunkChecks4_1 :
    compactCertificate571.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (791568064034823 / 800000000000) 4 (IntervalRat.scale (885 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-15222556963 / 1000000000000) (-15222556962 / 1000000000000), orderedInterval (-20282082207 / 1000000000000) (-20282082206 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (457012034852367 / 800000000000) 4 (IntervalRat.scale (885 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (9237039164 / 1000000000000) (9237039165 / 1000000000000), orderedInterval (32071207414 / 1000000000000) (32071207415 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (810975875640603 / 800000000000) 4 (IntervalRat.scale (885 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (5696223207 / 1000000000000) (5696223208 / 1000000000000), orderedInterval (-24406841392 / 1000000000000) (-24406841391 / 1000000000000)))) (orderedInterval (91842455952 / 1000000000000) (91842459751 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (757718860047207 / 800000000000) 4 (IntervalRat.scale (885 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-19081293302 / 1000000000000) (-19081291702 / 1000000000000), orderedInterval (17561362272 / 1000000000000) (17561363872 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (540743932004631 / 800000000000) 4 (IntervalRat.scale (885 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-29336037187 / 1000000000000) (-29336037158 / 1000000000000), orderedInterval (-8991599791 / 1000000000000) (-8991599761 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (613145985879249 / 800000000000) 4 (IntervalRat.scale (885 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (17877076986 / 1000000000000) (17877076987 / 1000000000000), orderedInterval (22594475957 / 1000000000000) (22594475958 / 1000000000000)))) (orderedInterval (-8717332186 / 1000000000000) (-8717331147 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (511177199343681 / 800000000000) 4 (IntervalRat.scale (885 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-28523095323 / 1000000000000) (-28522998378 / 1000000000000), orderedInterval (13540962598 / 1000000000000) (13541059543 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (451640558069301 / 800000000000) 4 (IntervalRat.scale (885 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-5044893868 / 1000000000000) (-5044893866 / 1000000000000), orderedInterval (33203969094 / 1000000000000) (33203969096 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (130903037264799 / 160000000000) 4 (IntervalRat.scale (885 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (23863206409 / 1000000000000) (23863230975 / 1000000000000), orderedInterval (-14460132498 / 1000000000000) (-14460107931 / 1000000000000)))) (orderedInterval (6446583306 / 1000000000000) (6446595780 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate571_chunkChecks4_2 :
    compactCertificate571.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (362084690123853 / 800000000000) 4 (IntervalRat.scale (885 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (31591932274 / 1000000000000) (31591932275 / 1000000000000), orderedInterval (20176851851 / 1000000000000) (20176851852 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (306943201796133 / 800000000000) 4 (IntervalRat.scale (885 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (37812607501 / 1000000000000) (37812607503 / 1000000000000), orderedInterval (15098552139 / 1000000000000) (15098552141 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (192070803854199 / 800000000000) 4 (IntervalRat.scale (885 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (44125614698 / 1000000000000) (44125654391 / 1000000000000), orderedInterval (-26634900467 / 1000000000000) (-26634860773 / 1000000000000)))) (orderedInterval (-6632649204 / 1000000000000) (-6632648996 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (103296317111433 / 800000000000) 4 (IntervalRat.scale (885 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-62562675474 / 1000000000000) (-62562675473 / 1000000000000), orderedInterval (-31637596133 / 1000000000000) (-31637596132 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (280469594953299 / 800000000000) 4 (IntervalRat.scale (885 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-19917099097 / 1000000000000) (-19917098075 / 1000000000000), orderedInterval (37700389339 / 1000000000000) (37700390361 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (382957253825523 / 800000000000) 4 (IntervalRat.scale (885 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (33745673120 / 1000000000000) (33745702826 / 1000000000000), orderedInterval (-13860258160 / 1000000000000) (-13860228454 / 1000000000000)))) (orderedInterval (-3351376239 / 1000000000000) (-3351373047 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (161929196145801 / 800000000000) 4 (IntervalRat.scale (885 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (47409513575 / 1000000000000) (47409554347 / 1000000000000), orderedInterval (-30075566388 / 1000000000000) (-30075525616 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (658233192292521 / 800000000000) 4 (IntervalRat.scale (885 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (12831571412 / 1000000000000) (12831571413 / 1000000000000), orderedInterval (24671798290 / 1000000000000) (24671798291 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (439669267250439 / 800000000000) 4 (IntervalRat.scale (885 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-19021477264 / 1000000000000) (-19021477263 / 1000000000000), orderedInterval (-28205819632 / 1000000000000) (-28205819631 / 1000000000000)))) (orderedInterval (-3993634448 / 1000000000000) (-3993633806 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate571_chunkChecks4 :
    compactCertificate571.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate571.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate571_chunkChecks4_0
    compactCertificate571_chunkChecks4_1 compactCertificate571_chunkChecks4_2

theorem compactCertificate571_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate571.chunkCheck r b = true :=
  compactCertificate571.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate571_chunkChecks0
    · exact compactCertificate571_chunkChecks1
    · exact compactCertificate571_chunkChecks2
    · exact compactCertificate571_chunkChecks3
    · exact compactCertificate571_chunkChecks4)

theorem compactCertificate571_coefficient0 :
    compactCertificate571.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate571_coefficient1 :
    compactCertificate571.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate571_coefficient2 :
    compactCertificate571.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate571_coefficient3 :
    compactCertificate571.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate571_coefficient4 :
    compactCertificate571.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate571_coefficients : ∀ r : Fin 5,
    compactCertificate571.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate571_coefficient0
  · exact compactCertificate571_coefficient1
  · exact compactCertificate571_coefficient2
  · exact compactCertificate571_coefficient3
  · exact compactCertificate571_coefficient4

theorem compactCertificate571_lower : (1 : ℚ) ≤ compactCertificate571.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate571, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate571_proves {t : ℝ} (ht : t ∈ compactCertificate571.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate571.proves compactCertificate571_states compactCertificate571_chunks
    compactCertificate571_coefficients compactCertificate571_lower ht

end Erdos232
