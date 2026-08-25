/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate529 : CompactCertificate where
  left := 400
  right := 401
  center := 801 / 2
  grid := fun i =>
    match i.val with
    | 0 => 128
    | 1 => 94
    | 2 => 152
    | 3 => 27
    | 4 => 74
    | 5 => 200
    | 6 => 147
    | 7 => 252
    | 8 => 186
    | 9 => 285
    | 10 => 165
    | 11 => 292
    | 12 => 273
    | 13 => 195
    | 14 => 221
    | 15 => 184
    | 16 => 163
    | 17 => 236
    | 18 => 130
    | 19 => 111
    | 20 => 69
    | 21 => 37
    | 22 => 101
    | 23 => 138
    | 24 => 58
    | 25 => 237
    | _ => 158
  point := fun i =>
    match i.val with
    | 0 => 801 / 2
    | 1 => 1180025949268701 / 4000000000000
    | 2 => 381596146830333 / 800000000000
    | 3 => 344328628970007 / 4000000000000
    | 4 => 924915131241579 / 4000000000000
    | 5 => 2511324502937343 / 4000000000000
    | 6 => 1849830262483959 / 4000000000000
    | 7 => 3169715684113107 / 4000000000000
    | 8 => 2334798226625913 / 4000000000000
    | 9 => 3582180899954199 / 4000000000000
    | 10 => 2068173106874271 / 4000000000000
    | 11 => 3670009471119339 / 4000000000000
    | 12 => 3428998909027191 / 4000000000000
    | 13 => 2447095421105703 / 4000000000000
    | 14 => 2774745393724737 / 4000000000000
    | 15 => 2313293427538353 / 4000000000000
    | 16 => 2043864898381413 / 4000000000000
    | 17 => 592391711011887 / 800000000000
    | 18 => 1638586648526589 / 4000000000000
    | 19 => 1389048048806229 / 4000000000000
    | 20 => 869201773374087 / 4000000000000
    | 21 => 467459604555129 / 4000000000000
    | 22 => 1269243760212387 / 4000000000000
    | 23 => 1733043843583299 / 4000000000000
    | 24 => 732798226625913 / 4000000000000
    | 25 => 2978784107493273 / 4000000000000
    | _ => 1989689734845207 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-29655757943 / 1000000000000) (-29655727287 / 1000000000000), orderedInterval (26684695131 / 1000000000000) (26684725787 / 1000000000000))
    | 1 => (orderedInterval (21523702671 / 1000000000000) (21523702672 / 1000000000000), orderedInterval (41130468722 / 1000000000000) (41130468723 / 1000000000000))
    | 2 => (orderedInterval (9329590170 / 1000000000000) (9329590171 / 1000000000000), orderedInterval (35311680060 / 1000000000000) (35311680061 / 1000000000000))
    | 3 => (orderedInterval (-76581597331 / 1000000000000) (-76581587391 / 1000000000000), orderedInterval (39568664379 / 1000000000000) (39568674320 / 1000000000000))
    | 4 => (orderedInterval (-23492376191 / 1000000000000) (-23492374595 / 1000000000000), orderedInterval (46968972723 / 1000000000000) (46968974320 / 1000000000000))
    | 5 => (orderedInterval (9343220192 / 1000000000000) (9343220193 / 1000000000000), orderedInterval (30434354862 / 1000000000000) (30434354863 / 1000000000000))
    | 6 => (orderedInterval (-36727958399 / 1000000000000) (-36727958339 / 1000000000000), orderedInterval (-5219357789 / 1000000000000) (-5219357729 / 1000000000000))
    | 7 => (orderedInterval (28323471303 / 1000000000000) (28323473256 / 1000000000000), orderedInterval (1058472585 / 1000000000000) (1058474538 / 1000000000000))
    | 8 => (orderedInterval (4886467314 / 1000000000000) (4886467315 / 1000000000000), orderedInterval (32657508461 / 1000000000000) (32657508462 / 1000000000000))
    | 9 => (orderedInterval (-22091939805 / 1000000000000) (-22091939803 / 1000000000000), orderedInterval (-14914825643 / 1000000000000) (-14914825640 / 1000000000000))
    | 10 => (orderedInterval (17870556918 / 1000000000000) (17870557577 / 1000000000000), orderedInterval (-30215183402 / 1000000000000) (-30215182743 / 1000000000000))
    | 11 => (orderedInterval (21312024138 / 1000000000000) (21312024140 / 1000000000000), orderedInterval (15469319825 / 1000000000000) (15469319826 / 1000000000000))
    | 12 => (orderedInterval (-10112730656 / 1000000000000) (-10112730655 / 1000000000000), orderedInterval (-25299501177 / 1000000000000) (-25299501176 / 1000000000000))
    | 13 => (orderedInterval (1661170503 / 1000000000000) (1661170504 / 1000000000000), orderedInterval (-32217095578 / 1000000000000) (-32217095577 / 1000000000000))
    | 14 => (orderedInterval (-5411322777 / 1000000000000) (-5411322776 / 1000000000000), orderedInterval (-29803013781 / 1000000000000) (-29803013780 / 1000000000000))
    | 15 => (orderedInterval (28869868594 / 1000000000000) (28869868595 / 1000000000000), orderedInterval (16325359097 / 1000000000000) (16325359098 / 1000000000000))
    | 16 => (orderedInterval (11378596378 / 1000000000000) (11378596420 / 1000000000000), orderedInterval (-33424329765 / 1000000000000) (-33424329723 / 1000000000000))
    | 17 => (orderedInterval (-4120537854 / 1000000000000) (-4120537853 / 1000000000000), orderedInterval (29032930185 / 1000000000000) (29032930186 / 1000000000000))
    | 18 => (orderedInterval (35429739437 / 1000000000000) (35429778479 / 1000000000000), orderedInterval (-17329149857 / 1000000000000) (-17329110815 / 1000000000000))
    | 19 => (orderedInterval (26579521266 / 1000000000000) (26579529058 / 1000000000000), orderedInterval (-33605879267 / 1000000000000) (-33605871475 / 1000000000000))
    | 20 => (orderedInterval (-52370353128 / 1000000000000) (-52370353126 / 1000000000000), orderedInterval (-13554833561 / 1000000000000) (-13554833559 / 1000000000000))
    | 21 => (orderedInterval (-72858201047 / 1000000000000) (-72858201043 / 1000000000000), orderedInterval (-11483201471 / 1000000000000) (-11483201467 / 1000000000000))
    | 22 => (orderedInterval (-31977849987 / 1000000000000) (-31977849986 / 1000000000000), orderedInterval (-31313816780 / 1000000000000) (-31313816779 / 1000000000000))
    | 23 => (orderedInterval (18588534563 / 1000000000000) (18588534564 / 1000000000000), orderedInterval (33502194368 / 1000000000000) (33502194369 / 1000000000000))
    | 24 => (orderedInterval (57761079946 / 1000000000000) (57761080816 / 1000000000000), orderedInterval (-11932738935 / 1000000000000) (-11932738066 / 1000000000000))
    | 25 => (orderedInterval (-23329063215 / 1000000000000) (-23329063214 / 1000000000000), orderedInterval (-17608942739 / 1000000000000) (-17608942737 / 1000000000000))
    | _ => (orderedInterval (34524631465 / 1000000000000) (34524641433 / 1000000000000), orderedInterval (-9409471632 / 1000000000000) (-9409461664 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-11006474164 / 1000000000000) (-11006461985 / 1000000000000)
      | 1 => orderedInterval (-691097939 / 1000000000000) (-691097724 / 1000000000000)
      | 2 => orderedInterval (-755512975 / 1000000000000) (-755512892 / 1000000000000)
      | 3 => orderedInterval (8279161898 / 1000000000000) (8279162106 / 1000000000000)
      | 4 => orderedInterval (367035426 / 1000000000000) (367035474 / 1000000000000)
      | 5 => orderedInterval (-423281611 / 1000000000000) (-423281570 / 1000000000000)
      | 6 => orderedInterval (-8874285065 / 1000000000000) (-8874278280 / 1000000000000)
      | 7 => orderedInterval (646207968 / 1000000000000) (646208017 / 1000000000000)
      | _ => orderedInterval (-4230508687 / 1000000000000) (-4230506700 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (13327088512 / 1000000000000) (13327100695 / 1000000000000)
      | 1 => orderedInterval (-2493809364 / 1000000000000) (-2493809252 / 1000000000000)
      | 2 => orderedInterval (1085703407 / 1000000000000) (1085703566 / 1000000000000)
      | 3 => orderedInterval (8073645776 / 1000000000000) (8073646170 / 1000000000000)
      | 4 => orderedInterval (-3414823623 / 1000000000000) (-3414823545 / 1000000000000)
      | 5 => orderedInterval (4086970160 / 1000000000000) (4086970219 / 1000000000000)
      | 6 => orderedInterval (4243894404 / 1000000000000) (4243901265 / 1000000000000)
      | 7 => orderedInterval (-2152875255 / 1000000000000) (-2152875212 / 1000000000000)
      | _ => orderedInterval (4825093689 / 1000000000000) (4825096171 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (10835821842 / 1000000000000) (10835834059 / 1000000000000)
      | 1 => orderedInterval (1885997102 / 1000000000000) (1885997203 / 1000000000000)
      | 2 => orderedInterval (3166494104 / 1000000000000) (3166494411 / 1000000000000)
      | 3 => orderedInterval (-37754348266 / 1000000000000) (-37754347476 / 1000000000000)
      | 4 => orderedInterval (-1276588587 / 1000000000000) (-1276588458 / 1000000000000)
      | 5 => orderedInterval (715210607 / 1000000000000) (715210694 / 1000000000000)
      | 6 => orderedInterval (7548992250 / 1000000000000) (7548999219 / 1000000000000)
      | 7 => orderedInterval (1102632702 / 1000000000000) (1102632745 / 1000000000000)
      | _ => orderedInterval (3341727325 / 1000000000000) (3341730447 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-14257706137 / 1000000000000) (-14257693913 / 1000000000000)
      | 1 => orderedInterval (8004228793 / 1000000000000) (8004228919 / 1000000000000)
      | 2 => orderedInterval (-2198359165 / 1000000000000) (-2198358572 / 1000000000000)
      | 3 => orderedInterval (-51158046605 / 1000000000000) (-51158044947 / 1000000000000)
      | 4 => orderedInterval (5599071535 / 1000000000000) (5599071753 / 1000000000000)
      | 5 => orderedInterval (-9239948133 / 1000000000000) (-9239948001 / 1000000000000)
      | 6 => orderedInterval (-4153272409 / 1000000000000) (-4153265338 / 1000000000000)
      | 7 => orderedInterval (2889253028 / 1000000000000) (2889253073 / 1000000000000)
      | _ => orderedInterval (-12598882004 / 1000000000000) (-12598878057 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-10522638751 / 1000000000000) (-10522626490 / 1000000000000)
      | 1 => orderedInterval (-4144598036 / 1000000000000) (-4144597854 / 1000000000000)
      | 2 => orderedInterval (-12845186725 / 1000000000000) (-12845185566 / 1000000000000)
      | 3 => orderedInterval (185516480876 / 1000000000000) (185516484460 / 1000000000000)
      | 4 => orderedInterval (4905853146 / 1000000000000) (4905853524 / 1000000000000)
      | 5 => orderedInterval (-1462496865 / 1000000000000) (-1462496657 / 1000000000000)
      | 6 => orderedInterval (-7177747535 / 1000000000000) (-7177740333 / 1000000000000)
      | 7 => orderedInterval (-1669920556 / 1000000000000) (-1669920509 / 1000000000000)
      | _ => orderedInterval (7364795938 / 1000000000000) (7364800978 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-16688755149 / 1000000000000) (-16688733554 / 1000000000000)
    | 1 => orderedInterval (27580887706 / 1000000000000) (27580910077 / 1000000000000)
    | 2 => orderedInterval (-10434060921 / 1000000000000) (-10434037156 / 1000000000000)
    | 3 => orderedInterval (-77113661097 / 1000000000000) (-77113635083 / 1000000000000)
    | _ => orderedInterval (159964541492 / 1000000000000) (159964571553 / 1000000000000)

theorem compactCertificate529_stateChecks0 :
    compactCertificate529.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 128 12 (801 / 2)) (orderedInterval (-29655757943 / 1000000000000) (-29655727287 / 1000000000000), orderedInterval (26684695131 / 1000000000000) (26684725787 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 94 12 (1180025949268701 / 4000000000000)) (orderedInterval (21523702671 / 1000000000000) (21523702672 / 1000000000000), orderedInterval (41130468722 / 1000000000000) (41130468723 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 152 12 (381596146830333 / 800000000000)) (orderedInterval (9329590170 / 1000000000000) (9329590171 / 1000000000000), orderedInterval (35311680060 / 1000000000000) (35311680061 / 1000000000000))) = true
  rfl'

theorem compactCertificate529_stateChecks1 :
    compactCertificate529.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (344328628970007 / 4000000000000)) (orderedInterval (-76581597331 / 1000000000000) (-76581587391 / 1000000000000), orderedInterval (39568664379 / 1000000000000) (39568674320 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (924915131241579 / 4000000000000)) (orderedInterval (-23492376191 / 1000000000000) (-23492374595 / 1000000000000), orderedInterval (46968972723 / 1000000000000) (46968974320 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 200 12 (2511324502937343 / 4000000000000)) (orderedInterval (9343220192 / 1000000000000) (9343220193 / 1000000000000), orderedInterval (30434354862 / 1000000000000) (30434354863 / 1000000000000))) = true
  rfl'

theorem compactCertificate529_stateChecks2 :
    compactCertificate529.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 147 12 (1849830262483959 / 4000000000000)) (orderedInterval (-36727958399 / 1000000000000) (-36727958339 / 1000000000000), orderedInterval (-5219357789 / 1000000000000) (-5219357729 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 252 12 (3169715684113107 / 4000000000000)) (orderedInterval (28323471303 / 1000000000000) (28323473256 / 1000000000000), orderedInterval (1058472585 / 1000000000000) (1058474538 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 186 12 (2334798226625913 / 4000000000000)) (orderedInterval (4886467314 / 1000000000000) (4886467315 / 1000000000000), orderedInterval (32657508461 / 1000000000000) (32657508462 / 1000000000000))) = true
  rfl'

theorem compactCertificate529_stateChecks3 :
    compactCertificate529.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 285 12 (3582180899954199 / 4000000000000)) (orderedInterval (-22091939805 / 1000000000000) (-22091939803 / 1000000000000), orderedInterval (-14914825643 / 1000000000000) (-14914825640 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 165 12 (2068173106874271 / 4000000000000)) (orderedInterval (17870556918 / 1000000000000) (17870557577 / 1000000000000), orderedInterval (-30215183402 / 1000000000000) (-30215182743 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 292 12 (3670009471119339 / 4000000000000)) (orderedInterval (21312024138 / 1000000000000) (21312024140 / 1000000000000), orderedInterval (15469319825 / 1000000000000) (15469319826 / 1000000000000))) = true
  rfl'

theorem compactCertificate529_stateChecks4 :
    compactCertificate529.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 273 12 (3428998909027191 / 4000000000000)) (orderedInterval (-10112730656 / 1000000000000) (-10112730655 / 1000000000000), orderedInterval (-25299501177 / 1000000000000) (-25299501176 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 195 12 (2447095421105703 / 4000000000000)) (orderedInterval (1661170503 / 1000000000000) (1661170504 / 1000000000000), orderedInterval (-32217095578 / 1000000000000) (-32217095577 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 221 12 (2774745393724737 / 4000000000000)) (orderedInterval (-5411322777 / 1000000000000) (-5411322776 / 1000000000000), orderedInterval (-29803013781 / 1000000000000) (-29803013780 / 1000000000000))) = true
  rfl'

theorem compactCertificate529_stateChecks5 :
    compactCertificate529.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 184 12 (2313293427538353 / 4000000000000)) (orderedInterval (28869868594 / 1000000000000) (28869868595 / 1000000000000), orderedInterval (16325359097 / 1000000000000) (16325359098 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 163 12 (2043864898381413 / 4000000000000)) (orderedInterval (11378596378 / 1000000000000) (11378596420 / 1000000000000), orderedInterval (-33424329765 / 1000000000000) (-33424329723 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 236 12 (592391711011887 / 800000000000)) (orderedInterval (-4120537854 / 1000000000000) (-4120537853 / 1000000000000), orderedInterval (29032930185 / 1000000000000) (29032930186 / 1000000000000))) = true
  rfl'

theorem compactCertificate529_stateChecks6 :
    compactCertificate529.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 130 12 (1638586648526589 / 4000000000000)) (orderedInterval (35429739437 / 1000000000000) (35429778479 / 1000000000000), orderedInterval (-17329149857 / 1000000000000) (-17329110815 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 111 12 (1389048048806229 / 4000000000000)) (orderedInterval (26579521266 / 1000000000000) (26579529058 / 1000000000000), orderedInterval (-33605879267 / 1000000000000) (-33605871475 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (869201773374087 / 4000000000000)) (orderedInterval (-52370353128 / 1000000000000) (-52370353126 / 1000000000000), orderedInterval (-13554833561 / 1000000000000) (-13554833559 / 1000000000000))) = true
  rfl'

theorem compactCertificate529_stateChecks7 :
    compactCertificate529.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (467459604555129 / 4000000000000)) (orderedInterval (-72858201047 / 1000000000000) (-72858201043 / 1000000000000), orderedInterval (-11483201471 / 1000000000000) (-11483201467 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 101 12 (1269243760212387 / 4000000000000)) (orderedInterval (-31977849987 / 1000000000000) (-31977849986 / 1000000000000), orderedInterval (-31313816780 / 1000000000000) (-31313816779 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 138 12 (1733043843583299 / 4000000000000)) (orderedInterval (18588534563 / 1000000000000) (18588534564 / 1000000000000), orderedInterval (33502194368 / 1000000000000) (33502194369 / 1000000000000))) = true
  rfl'

theorem compactCertificate529_stateChecks8 :
    compactCertificate529.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (732798226625913 / 4000000000000)) (orderedInterval (57761079946 / 1000000000000) (57761080816 / 1000000000000), orderedInterval (-11932738935 / 1000000000000) (-11932738066 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 237 12 (2978784107493273 / 4000000000000)) (orderedInterval (-23329063215 / 1000000000000) (-23329063214 / 1000000000000), orderedInterval (-17608942739 / 1000000000000) (-17608942737 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 158 12 (1989689734845207 / 4000000000000)) (orderedInterval (34524631465 / 1000000000000) (34524641433 / 1000000000000), orderedInterval (-9409471632 / 1000000000000) (-9409461664 / 1000000000000))) = true
  rfl'

theorem compactCertificate529_states : ∀ j,
    BesselStateValid (compactCertificate529.point j) (compactCertificate529.state j) :=
  compactCertificate529.statesValid_of_checks3 compactCertificate529_stateChecks0
    compactCertificate529_stateChecks1 compactCertificate529_stateChecks2
    compactCertificate529_stateChecks3 compactCertificate529_stateChecks4
    compactCertificate529_stateChecks5 compactCertificate529_stateChecks6
    compactCertificate529_stateChecks7 compactCertificate529_stateChecks8

theorem compactCertificate529_chunkChecks0_0 :
    compactCertificate529.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (801 / 2) 0 (IntervalRat.scale (801 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-29655757943 / 1000000000000) (-29655727287 / 1000000000000), orderedInterval (26684695131 / 1000000000000) (26684725787 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1180025949268701 / 4000000000000) 0 (IntervalRat.scale (801 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (21523702671 / 1000000000000) (21523702672 / 1000000000000), orderedInterval (41130468722 / 1000000000000) (41130468723 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (381596146830333 / 800000000000) 0 (IntervalRat.scale (801 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (9329590170 / 1000000000000) (9329590171 / 1000000000000), orderedInterval (35311680060 / 1000000000000) (35311680061 / 1000000000000)))) (orderedInterval (-11006474164 / 1000000000000) (-11006461985 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (344328628970007 / 4000000000000) 0 (IntervalRat.scale (801 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-76581597331 / 1000000000000) (-76581587391 / 1000000000000), orderedInterval (39568664379 / 1000000000000) (39568674320 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (924915131241579 / 4000000000000) 0 (IntervalRat.scale (801 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-23492376191 / 1000000000000) (-23492374595 / 1000000000000), orderedInterval (46968972723 / 1000000000000) (46968974320 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2511324502937343 / 4000000000000) 0 (IntervalRat.scale (801 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (9343220192 / 1000000000000) (9343220193 / 1000000000000), orderedInterval (30434354862 / 1000000000000) (30434354863 / 1000000000000)))) (orderedInterval (-691097939 / 1000000000000) (-691097724 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1849830262483959 / 4000000000000) 0 (IntervalRat.scale (801 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-36727958399 / 1000000000000) (-36727958339 / 1000000000000), orderedInterval (-5219357789 / 1000000000000) (-5219357729 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3169715684113107 / 4000000000000) 0 (IntervalRat.scale (801 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (28323471303 / 1000000000000) (28323473256 / 1000000000000), orderedInterval (1058472585 / 1000000000000) (1058474538 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2334798226625913 / 4000000000000) 0 (IntervalRat.scale (801 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (4886467314 / 1000000000000) (4886467315 / 1000000000000), orderedInterval (32657508461 / 1000000000000) (32657508462 / 1000000000000)))) (orderedInterval (-755512975 / 1000000000000) (-755512892 / 1000000000000))) = true
  rfl'

theorem compactCertificate529_chunkChecks0_1 :
    compactCertificate529.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3582180899954199 / 4000000000000) 0 (IntervalRat.scale (801 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-22091939805 / 1000000000000) (-22091939803 / 1000000000000), orderedInterval (-14914825643 / 1000000000000) (-14914825640 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2068173106874271 / 4000000000000) 0 (IntervalRat.scale (801 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (17870556918 / 1000000000000) (17870557577 / 1000000000000), orderedInterval (-30215183402 / 1000000000000) (-30215182743 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3670009471119339 / 4000000000000) 0 (IntervalRat.scale (801 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (21312024138 / 1000000000000) (21312024140 / 1000000000000), orderedInterval (15469319825 / 1000000000000) (15469319826 / 1000000000000)))) (orderedInterval (8279161898 / 1000000000000) (8279162106 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3428998909027191 / 4000000000000) 0 (IntervalRat.scale (801 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-10112730656 / 1000000000000) (-10112730655 / 1000000000000), orderedInterval (-25299501177 / 1000000000000) (-25299501176 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2447095421105703 / 4000000000000) 0 (IntervalRat.scale (801 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (1661170503 / 1000000000000) (1661170504 / 1000000000000), orderedInterval (-32217095578 / 1000000000000) (-32217095577 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2774745393724737 / 4000000000000) 0 (IntervalRat.scale (801 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-5411322777 / 1000000000000) (-5411322776 / 1000000000000), orderedInterval (-29803013781 / 1000000000000) (-29803013780 / 1000000000000)))) (orderedInterval (367035426 / 1000000000000) (367035474 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2313293427538353 / 4000000000000) 0 (IntervalRat.scale (801 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (28869868594 / 1000000000000) (28869868595 / 1000000000000), orderedInterval (16325359097 / 1000000000000) (16325359098 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2043864898381413 / 4000000000000) 0 (IntervalRat.scale (801 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (11378596378 / 1000000000000) (11378596420 / 1000000000000), orderedInterval (-33424329765 / 1000000000000) (-33424329723 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (592391711011887 / 800000000000) 0 (IntervalRat.scale (801 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-4120537854 / 1000000000000) (-4120537853 / 1000000000000), orderedInterval (29032930185 / 1000000000000) (29032930186 / 1000000000000)))) (orderedInterval (-423281611 / 1000000000000) (-423281570 / 1000000000000))) = true
  rfl'

theorem compactCertificate529_chunkChecks0_2 :
    compactCertificate529.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1638586648526589 / 4000000000000) 0 (IntervalRat.scale (801 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (35429739437 / 1000000000000) (35429778479 / 1000000000000), orderedInterval (-17329149857 / 1000000000000) (-17329110815 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1389048048806229 / 4000000000000) 0 (IntervalRat.scale (801 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (26579521266 / 1000000000000) (26579529058 / 1000000000000), orderedInterval (-33605879267 / 1000000000000) (-33605871475 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (869201773374087 / 4000000000000) 0 (IntervalRat.scale (801 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-52370353128 / 1000000000000) (-52370353126 / 1000000000000), orderedInterval (-13554833561 / 1000000000000) (-13554833559 / 1000000000000)))) (orderedInterval (-8874285065 / 1000000000000) (-8874278280 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (467459604555129 / 4000000000000) 0 (IntervalRat.scale (801 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-72858201047 / 1000000000000) (-72858201043 / 1000000000000), orderedInterval (-11483201471 / 1000000000000) (-11483201467 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1269243760212387 / 4000000000000) 0 (IntervalRat.scale (801 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-31977849987 / 1000000000000) (-31977849986 / 1000000000000), orderedInterval (-31313816780 / 1000000000000) (-31313816779 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1733043843583299 / 4000000000000) 0 (IntervalRat.scale (801 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (18588534563 / 1000000000000) (18588534564 / 1000000000000), orderedInterval (33502194368 / 1000000000000) (33502194369 / 1000000000000)))) (orderedInterval (646207968 / 1000000000000) (646208017 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (732798226625913 / 4000000000000) 0 (IntervalRat.scale (801 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (57761079946 / 1000000000000) (57761080816 / 1000000000000), orderedInterval (-11932738935 / 1000000000000) (-11932738066 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2978784107493273 / 4000000000000) 0 (IntervalRat.scale (801 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-23329063215 / 1000000000000) (-23329063214 / 1000000000000), orderedInterval (-17608942739 / 1000000000000) (-17608942737 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1989689734845207 / 4000000000000) 0 (IntervalRat.scale (801 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (34524631465 / 1000000000000) (34524641433 / 1000000000000), orderedInterval (-9409471632 / 1000000000000) (-9409461664 / 1000000000000)))) (orderedInterval (-4230508687 / 1000000000000) (-4230506700 / 1000000000000))) = true
  rfl'

theorem compactCertificate529_chunkChecks0 :
    compactCertificate529.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate529.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate529_chunkChecks0_0
    compactCertificate529_chunkChecks0_1 compactCertificate529_chunkChecks0_2

theorem compactCertificate529_chunkChecks1_0 :
    compactCertificate529.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (801 / 2) 1 (IntervalRat.scale (801 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-29655757943 / 1000000000000) (-29655727287 / 1000000000000), orderedInterval (26684695131 / 1000000000000) (26684725787 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1180025949268701 / 4000000000000) 1 (IntervalRat.scale (801 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (21523702671 / 1000000000000) (21523702672 / 1000000000000), orderedInterval (41130468722 / 1000000000000) (41130468723 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (381596146830333 / 800000000000) 1 (IntervalRat.scale (801 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (9329590170 / 1000000000000) (9329590171 / 1000000000000), orderedInterval (35311680060 / 1000000000000) (35311680061 / 1000000000000)))) (orderedInterval (13327088512 / 1000000000000) (13327100695 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (344328628970007 / 4000000000000) 1 (IntervalRat.scale (801 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-76581597331 / 1000000000000) (-76581587391 / 1000000000000), orderedInterval (39568664379 / 1000000000000) (39568674320 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (924915131241579 / 4000000000000) 1 (IntervalRat.scale (801 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-23492376191 / 1000000000000) (-23492374595 / 1000000000000), orderedInterval (46968972723 / 1000000000000) (46968974320 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2511324502937343 / 4000000000000) 1 (IntervalRat.scale (801 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (9343220192 / 1000000000000) (9343220193 / 1000000000000), orderedInterval (30434354862 / 1000000000000) (30434354863 / 1000000000000)))) (orderedInterval (-2493809364 / 1000000000000) (-2493809252 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1849830262483959 / 4000000000000) 1 (IntervalRat.scale (801 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-36727958399 / 1000000000000) (-36727958339 / 1000000000000), orderedInterval (-5219357789 / 1000000000000) (-5219357729 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3169715684113107 / 4000000000000) 1 (IntervalRat.scale (801 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (28323471303 / 1000000000000) (28323473256 / 1000000000000), orderedInterval (1058472585 / 1000000000000) (1058474538 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2334798226625913 / 4000000000000) 1 (IntervalRat.scale (801 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (4886467314 / 1000000000000) (4886467315 / 1000000000000), orderedInterval (32657508461 / 1000000000000) (32657508462 / 1000000000000)))) (orderedInterval (1085703407 / 1000000000000) (1085703566 / 1000000000000))) = true
  rfl'

theorem compactCertificate529_chunkChecks1_1 :
    compactCertificate529.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3582180899954199 / 4000000000000) 1 (IntervalRat.scale (801 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-22091939805 / 1000000000000) (-22091939803 / 1000000000000), orderedInterval (-14914825643 / 1000000000000) (-14914825640 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2068173106874271 / 4000000000000) 1 (IntervalRat.scale (801 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (17870556918 / 1000000000000) (17870557577 / 1000000000000), orderedInterval (-30215183402 / 1000000000000) (-30215182743 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3670009471119339 / 4000000000000) 1 (IntervalRat.scale (801 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (21312024138 / 1000000000000) (21312024140 / 1000000000000), orderedInterval (15469319825 / 1000000000000) (15469319826 / 1000000000000)))) (orderedInterval (8073645776 / 1000000000000) (8073646170 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3428998909027191 / 4000000000000) 1 (IntervalRat.scale (801 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-10112730656 / 1000000000000) (-10112730655 / 1000000000000), orderedInterval (-25299501177 / 1000000000000) (-25299501176 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2447095421105703 / 4000000000000) 1 (IntervalRat.scale (801 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (1661170503 / 1000000000000) (1661170504 / 1000000000000), orderedInterval (-32217095578 / 1000000000000) (-32217095577 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2774745393724737 / 4000000000000) 1 (IntervalRat.scale (801 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-5411322777 / 1000000000000) (-5411322776 / 1000000000000), orderedInterval (-29803013781 / 1000000000000) (-29803013780 / 1000000000000)))) (orderedInterval (-3414823623 / 1000000000000) (-3414823545 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2313293427538353 / 4000000000000) 1 (IntervalRat.scale (801 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (28869868594 / 1000000000000) (28869868595 / 1000000000000), orderedInterval (16325359097 / 1000000000000) (16325359098 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2043864898381413 / 4000000000000) 1 (IntervalRat.scale (801 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (11378596378 / 1000000000000) (11378596420 / 1000000000000), orderedInterval (-33424329765 / 1000000000000) (-33424329723 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (592391711011887 / 800000000000) 1 (IntervalRat.scale (801 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-4120537854 / 1000000000000) (-4120537853 / 1000000000000), orderedInterval (29032930185 / 1000000000000) (29032930186 / 1000000000000)))) (orderedInterval (4086970160 / 1000000000000) (4086970219 / 1000000000000))) = true
  rfl'

theorem compactCertificate529_chunkChecks1_2 :
    compactCertificate529.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1638586648526589 / 4000000000000) 1 (IntervalRat.scale (801 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (35429739437 / 1000000000000) (35429778479 / 1000000000000), orderedInterval (-17329149857 / 1000000000000) (-17329110815 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1389048048806229 / 4000000000000) 1 (IntervalRat.scale (801 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (26579521266 / 1000000000000) (26579529058 / 1000000000000), orderedInterval (-33605879267 / 1000000000000) (-33605871475 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (869201773374087 / 4000000000000) 1 (IntervalRat.scale (801 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-52370353128 / 1000000000000) (-52370353126 / 1000000000000), orderedInterval (-13554833561 / 1000000000000) (-13554833559 / 1000000000000)))) (orderedInterval (4243894404 / 1000000000000) (4243901265 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (467459604555129 / 4000000000000) 1 (IntervalRat.scale (801 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-72858201047 / 1000000000000) (-72858201043 / 1000000000000), orderedInterval (-11483201471 / 1000000000000) (-11483201467 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1269243760212387 / 4000000000000) 1 (IntervalRat.scale (801 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-31977849987 / 1000000000000) (-31977849986 / 1000000000000), orderedInterval (-31313816780 / 1000000000000) (-31313816779 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1733043843583299 / 4000000000000) 1 (IntervalRat.scale (801 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (18588534563 / 1000000000000) (18588534564 / 1000000000000), orderedInterval (33502194368 / 1000000000000) (33502194369 / 1000000000000)))) (orderedInterval (-2152875255 / 1000000000000) (-2152875212 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (732798226625913 / 4000000000000) 1 (IntervalRat.scale (801 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (57761079946 / 1000000000000) (57761080816 / 1000000000000), orderedInterval (-11932738935 / 1000000000000) (-11932738066 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2978784107493273 / 4000000000000) 1 (IntervalRat.scale (801 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-23329063215 / 1000000000000) (-23329063214 / 1000000000000), orderedInterval (-17608942739 / 1000000000000) (-17608942737 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1989689734845207 / 4000000000000) 1 (IntervalRat.scale (801 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (34524631465 / 1000000000000) (34524641433 / 1000000000000), orderedInterval (-9409471632 / 1000000000000) (-9409461664 / 1000000000000)))) (orderedInterval (4825093689 / 1000000000000) (4825096171 / 1000000000000))) = true
  rfl'

theorem compactCertificate529_chunkChecks1 :
    compactCertificate529.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate529.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate529_chunkChecks1_0
    compactCertificate529_chunkChecks1_1 compactCertificate529_chunkChecks1_2

theorem compactCertificate529_chunkChecks2_0 :
    compactCertificate529.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (801 / 2) 2 (IntervalRat.scale (801 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-29655757943 / 1000000000000) (-29655727287 / 1000000000000), orderedInterval (26684695131 / 1000000000000) (26684725787 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1180025949268701 / 4000000000000) 2 (IntervalRat.scale (801 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (21523702671 / 1000000000000) (21523702672 / 1000000000000), orderedInterval (41130468722 / 1000000000000) (41130468723 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (381596146830333 / 800000000000) 2 (IntervalRat.scale (801 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (9329590170 / 1000000000000) (9329590171 / 1000000000000), orderedInterval (35311680060 / 1000000000000) (35311680061 / 1000000000000)))) (orderedInterval (10835821842 / 1000000000000) (10835834059 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (344328628970007 / 4000000000000) 2 (IntervalRat.scale (801 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-76581597331 / 1000000000000) (-76581587391 / 1000000000000), orderedInterval (39568664379 / 1000000000000) (39568674320 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (924915131241579 / 4000000000000) 2 (IntervalRat.scale (801 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-23492376191 / 1000000000000) (-23492374595 / 1000000000000), orderedInterval (46968972723 / 1000000000000) (46968974320 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2511324502937343 / 4000000000000) 2 (IntervalRat.scale (801 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (9343220192 / 1000000000000) (9343220193 / 1000000000000), orderedInterval (30434354862 / 1000000000000) (30434354863 / 1000000000000)))) (orderedInterval (1885997102 / 1000000000000) (1885997203 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1849830262483959 / 4000000000000) 2 (IntervalRat.scale (801 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-36727958399 / 1000000000000) (-36727958339 / 1000000000000), orderedInterval (-5219357789 / 1000000000000) (-5219357729 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3169715684113107 / 4000000000000) 2 (IntervalRat.scale (801 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (28323471303 / 1000000000000) (28323473256 / 1000000000000), orderedInterval (1058472585 / 1000000000000) (1058474538 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2334798226625913 / 4000000000000) 2 (IntervalRat.scale (801 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (4886467314 / 1000000000000) (4886467315 / 1000000000000), orderedInterval (32657508461 / 1000000000000) (32657508462 / 1000000000000)))) (orderedInterval (3166494104 / 1000000000000) (3166494411 / 1000000000000))) = true
  rfl'

theorem compactCertificate529_chunkChecks2_1 :
    compactCertificate529.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3582180899954199 / 4000000000000) 2 (IntervalRat.scale (801 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-22091939805 / 1000000000000) (-22091939803 / 1000000000000), orderedInterval (-14914825643 / 1000000000000) (-14914825640 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2068173106874271 / 4000000000000) 2 (IntervalRat.scale (801 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (17870556918 / 1000000000000) (17870557577 / 1000000000000), orderedInterval (-30215183402 / 1000000000000) (-30215182743 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3670009471119339 / 4000000000000) 2 (IntervalRat.scale (801 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (21312024138 / 1000000000000) (21312024140 / 1000000000000), orderedInterval (15469319825 / 1000000000000) (15469319826 / 1000000000000)))) (orderedInterval (-37754348266 / 1000000000000) (-37754347476 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3428998909027191 / 4000000000000) 2 (IntervalRat.scale (801 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-10112730656 / 1000000000000) (-10112730655 / 1000000000000), orderedInterval (-25299501177 / 1000000000000) (-25299501176 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2447095421105703 / 4000000000000) 2 (IntervalRat.scale (801 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (1661170503 / 1000000000000) (1661170504 / 1000000000000), orderedInterval (-32217095578 / 1000000000000) (-32217095577 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2774745393724737 / 4000000000000) 2 (IntervalRat.scale (801 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-5411322777 / 1000000000000) (-5411322776 / 1000000000000), orderedInterval (-29803013781 / 1000000000000) (-29803013780 / 1000000000000)))) (orderedInterval (-1276588587 / 1000000000000) (-1276588458 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2313293427538353 / 4000000000000) 2 (IntervalRat.scale (801 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (28869868594 / 1000000000000) (28869868595 / 1000000000000), orderedInterval (16325359097 / 1000000000000) (16325359098 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2043864898381413 / 4000000000000) 2 (IntervalRat.scale (801 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (11378596378 / 1000000000000) (11378596420 / 1000000000000), orderedInterval (-33424329765 / 1000000000000) (-33424329723 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (592391711011887 / 800000000000) 2 (IntervalRat.scale (801 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-4120537854 / 1000000000000) (-4120537853 / 1000000000000), orderedInterval (29032930185 / 1000000000000) (29032930186 / 1000000000000)))) (orderedInterval (715210607 / 1000000000000) (715210694 / 1000000000000))) = true
  rfl'

theorem compactCertificate529_chunkChecks2_2 :
    compactCertificate529.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1638586648526589 / 4000000000000) 2 (IntervalRat.scale (801 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (35429739437 / 1000000000000) (35429778479 / 1000000000000), orderedInterval (-17329149857 / 1000000000000) (-17329110815 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1389048048806229 / 4000000000000) 2 (IntervalRat.scale (801 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (26579521266 / 1000000000000) (26579529058 / 1000000000000), orderedInterval (-33605879267 / 1000000000000) (-33605871475 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (869201773374087 / 4000000000000) 2 (IntervalRat.scale (801 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-52370353128 / 1000000000000) (-52370353126 / 1000000000000), orderedInterval (-13554833561 / 1000000000000) (-13554833559 / 1000000000000)))) (orderedInterval (7548992250 / 1000000000000) (7548999219 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (467459604555129 / 4000000000000) 2 (IntervalRat.scale (801 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-72858201047 / 1000000000000) (-72858201043 / 1000000000000), orderedInterval (-11483201471 / 1000000000000) (-11483201467 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1269243760212387 / 4000000000000) 2 (IntervalRat.scale (801 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-31977849987 / 1000000000000) (-31977849986 / 1000000000000), orderedInterval (-31313816780 / 1000000000000) (-31313816779 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1733043843583299 / 4000000000000) 2 (IntervalRat.scale (801 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (18588534563 / 1000000000000) (18588534564 / 1000000000000), orderedInterval (33502194368 / 1000000000000) (33502194369 / 1000000000000)))) (orderedInterval (1102632702 / 1000000000000) (1102632745 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (732798226625913 / 4000000000000) 2 (IntervalRat.scale (801 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (57761079946 / 1000000000000) (57761080816 / 1000000000000), orderedInterval (-11932738935 / 1000000000000) (-11932738066 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2978784107493273 / 4000000000000) 2 (IntervalRat.scale (801 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-23329063215 / 1000000000000) (-23329063214 / 1000000000000), orderedInterval (-17608942739 / 1000000000000) (-17608942737 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1989689734845207 / 4000000000000) 2 (IntervalRat.scale (801 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (34524631465 / 1000000000000) (34524641433 / 1000000000000), orderedInterval (-9409471632 / 1000000000000) (-9409461664 / 1000000000000)))) (orderedInterval (3341727325 / 1000000000000) (3341730447 / 1000000000000))) = true
  rfl'

theorem compactCertificate529_chunkChecks2 :
    compactCertificate529.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate529.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate529_chunkChecks2_0
    compactCertificate529_chunkChecks2_1 compactCertificate529_chunkChecks2_2

theorem compactCertificate529_chunkChecks3_0 :
    compactCertificate529.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (801 / 2) 3 (IntervalRat.scale (801 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-29655757943 / 1000000000000) (-29655727287 / 1000000000000), orderedInterval (26684695131 / 1000000000000) (26684725787 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1180025949268701 / 4000000000000) 3 (IntervalRat.scale (801 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (21523702671 / 1000000000000) (21523702672 / 1000000000000), orderedInterval (41130468722 / 1000000000000) (41130468723 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (381596146830333 / 800000000000) 3 (IntervalRat.scale (801 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (9329590170 / 1000000000000) (9329590171 / 1000000000000), orderedInterval (35311680060 / 1000000000000) (35311680061 / 1000000000000)))) (orderedInterval (-14257706137 / 1000000000000) (-14257693913 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (344328628970007 / 4000000000000) 3 (IntervalRat.scale (801 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-76581597331 / 1000000000000) (-76581587391 / 1000000000000), orderedInterval (39568664379 / 1000000000000) (39568674320 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (924915131241579 / 4000000000000) 3 (IntervalRat.scale (801 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-23492376191 / 1000000000000) (-23492374595 / 1000000000000), orderedInterval (46968972723 / 1000000000000) (46968974320 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2511324502937343 / 4000000000000) 3 (IntervalRat.scale (801 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (9343220192 / 1000000000000) (9343220193 / 1000000000000), orderedInterval (30434354862 / 1000000000000) (30434354863 / 1000000000000)))) (orderedInterval (8004228793 / 1000000000000) (8004228919 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1849830262483959 / 4000000000000) 3 (IntervalRat.scale (801 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-36727958399 / 1000000000000) (-36727958339 / 1000000000000), orderedInterval (-5219357789 / 1000000000000) (-5219357729 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3169715684113107 / 4000000000000) 3 (IntervalRat.scale (801 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (28323471303 / 1000000000000) (28323473256 / 1000000000000), orderedInterval (1058472585 / 1000000000000) (1058474538 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2334798226625913 / 4000000000000) 3 (IntervalRat.scale (801 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (4886467314 / 1000000000000) (4886467315 / 1000000000000), orderedInterval (32657508461 / 1000000000000) (32657508462 / 1000000000000)))) (orderedInterval (-2198359165 / 1000000000000) (-2198358572 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate529_chunkChecks3_1 :
    compactCertificate529.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3582180899954199 / 4000000000000) 3 (IntervalRat.scale (801 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-22091939805 / 1000000000000) (-22091939803 / 1000000000000), orderedInterval (-14914825643 / 1000000000000) (-14914825640 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2068173106874271 / 4000000000000) 3 (IntervalRat.scale (801 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (17870556918 / 1000000000000) (17870557577 / 1000000000000), orderedInterval (-30215183402 / 1000000000000) (-30215182743 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3670009471119339 / 4000000000000) 3 (IntervalRat.scale (801 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (21312024138 / 1000000000000) (21312024140 / 1000000000000), orderedInterval (15469319825 / 1000000000000) (15469319826 / 1000000000000)))) (orderedInterval (-51158046605 / 1000000000000) (-51158044947 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3428998909027191 / 4000000000000) 3 (IntervalRat.scale (801 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-10112730656 / 1000000000000) (-10112730655 / 1000000000000), orderedInterval (-25299501177 / 1000000000000) (-25299501176 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2447095421105703 / 4000000000000) 3 (IntervalRat.scale (801 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (1661170503 / 1000000000000) (1661170504 / 1000000000000), orderedInterval (-32217095578 / 1000000000000) (-32217095577 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2774745393724737 / 4000000000000) 3 (IntervalRat.scale (801 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-5411322777 / 1000000000000) (-5411322776 / 1000000000000), orderedInterval (-29803013781 / 1000000000000) (-29803013780 / 1000000000000)))) (orderedInterval (5599071535 / 1000000000000) (5599071753 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2313293427538353 / 4000000000000) 3 (IntervalRat.scale (801 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (28869868594 / 1000000000000) (28869868595 / 1000000000000), orderedInterval (16325359097 / 1000000000000) (16325359098 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2043864898381413 / 4000000000000) 3 (IntervalRat.scale (801 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (11378596378 / 1000000000000) (11378596420 / 1000000000000), orderedInterval (-33424329765 / 1000000000000) (-33424329723 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (592391711011887 / 800000000000) 3 (IntervalRat.scale (801 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-4120537854 / 1000000000000) (-4120537853 / 1000000000000), orderedInterval (29032930185 / 1000000000000) (29032930186 / 1000000000000)))) (orderedInterval (-9239948133 / 1000000000000) (-9239948001 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate529_chunkChecks3_2 :
    compactCertificate529.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1638586648526589 / 4000000000000) 3 (IntervalRat.scale (801 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (35429739437 / 1000000000000) (35429778479 / 1000000000000), orderedInterval (-17329149857 / 1000000000000) (-17329110815 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1389048048806229 / 4000000000000) 3 (IntervalRat.scale (801 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (26579521266 / 1000000000000) (26579529058 / 1000000000000), orderedInterval (-33605879267 / 1000000000000) (-33605871475 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (869201773374087 / 4000000000000) 3 (IntervalRat.scale (801 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-52370353128 / 1000000000000) (-52370353126 / 1000000000000), orderedInterval (-13554833561 / 1000000000000) (-13554833559 / 1000000000000)))) (orderedInterval (-4153272409 / 1000000000000) (-4153265338 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (467459604555129 / 4000000000000) 3 (IntervalRat.scale (801 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-72858201047 / 1000000000000) (-72858201043 / 1000000000000), orderedInterval (-11483201471 / 1000000000000) (-11483201467 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1269243760212387 / 4000000000000) 3 (IntervalRat.scale (801 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-31977849987 / 1000000000000) (-31977849986 / 1000000000000), orderedInterval (-31313816780 / 1000000000000) (-31313816779 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1733043843583299 / 4000000000000) 3 (IntervalRat.scale (801 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (18588534563 / 1000000000000) (18588534564 / 1000000000000), orderedInterval (33502194368 / 1000000000000) (33502194369 / 1000000000000)))) (orderedInterval (2889253028 / 1000000000000) (2889253073 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (732798226625913 / 4000000000000) 3 (IntervalRat.scale (801 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (57761079946 / 1000000000000) (57761080816 / 1000000000000), orderedInterval (-11932738935 / 1000000000000) (-11932738066 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2978784107493273 / 4000000000000) 3 (IntervalRat.scale (801 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-23329063215 / 1000000000000) (-23329063214 / 1000000000000), orderedInterval (-17608942739 / 1000000000000) (-17608942737 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1989689734845207 / 4000000000000) 3 (IntervalRat.scale (801 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (34524631465 / 1000000000000) (34524641433 / 1000000000000), orderedInterval (-9409471632 / 1000000000000) (-9409461664 / 1000000000000)))) (orderedInterval (-12598882004 / 1000000000000) (-12598878057 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate529_chunkChecks3 :
    compactCertificate529.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate529.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate529_chunkChecks3_0
    compactCertificate529_chunkChecks3_1 compactCertificate529_chunkChecks3_2

theorem compactCertificate529_chunkChecks4_0 :
    compactCertificate529.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (801 / 2) 4 (IntervalRat.scale (801 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-29655757943 / 1000000000000) (-29655727287 / 1000000000000), orderedInterval (26684695131 / 1000000000000) (26684725787 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1180025949268701 / 4000000000000) 4 (IntervalRat.scale (801 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (21523702671 / 1000000000000) (21523702672 / 1000000000000), orderedInterval (41130468722 / 1000000000000) (41130468723 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (381596146830333 / 800000000000) 4 (IntervalRat.scale (801 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (9329590170 / 1000000000000) (9329590171 / 1000000000000), orderedInterval (35311680060 / 1000000000000) (35311680061 / 1000000000000)))) (orderedInterval (-10522638751 / 1000000000000) (-10522626490 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (344328628970007 / 4000000000000) 4 (IntervalRat.scale (801 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-76581597331 / 1000000000000) (-76581587391 / 1000000000000), orderedInterval (39568664379 / 1000000000000) (39568674320 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (924915131241579 / 4000000000000) 4 (IntervalRat.scale (801 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-23492376191 / 1000000000000) (-23492374595 / 1000000000000), orderedInterval (46968972723 / 1000000000000) (46968974320 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2511324502937343 / 4000000000000) 4 (IntervalRat.scale (801 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (9343220192 / 1000000000000) (9343220193 / 1000000000000), orderedInterval (30434354862 / 1000000000000) (30434354863 / 1000000000000)))) (orderedInterval (-4144598036 / 1000000000000) (-4144597854 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1849830262483959 / 4000000000000) 4 (IntervalRat.scale (801 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-36727958399 / 1000000000000) (-36727958339 / 1000000000000), orderedInterval (-5219357789 / 1000000000000) (-5219357729 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3169715684113107 / 4000000000000) 4 (IntervalRat.scale (801 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (28323471303 / 1000000000000) (28323473256 / 1000000000000), orderedInterval (1058472585 / 1000000000000) (1058474538 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2334798226625913 / 4000000000000) 4 (IntervalRat.scale (801 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (4886467314 / 1000000000000) (4886467315 / 1000000000000), orderedInterval (32657508461 / 1000000000000) (32657508462 / 1000000000000)))) (orderedInterval (-12845186725 / 1000000000000) (-12845185566 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate529_chunkChecks4_1 :
    compactCertificate529.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3582180899954199 / 4000000000000) 4 (IntervalRat.scale (801 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-22091939805 / 1000000000000) (-22091939803 / 1000000000000), orderedInterval (-14914825643 / 1000000000000) (-14914825640 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2068173106874271 / 4000000000000) 4 (IntervalRat.scale (801 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (17870556918 / 1000000000000) (17870557577 / 1000000000000), orderedInterval (-30215183402 / 1000000000000) (-30215182743 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3670009471119339 / 4000000000000) 4 (IntervalRat.scale (801 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (21312024138 / 1000000000000) (21312024140 / 1000000000000), orderedInterval (15469319825 / 1000000000000) (15469319826 / 1000000000000)))) (orderedInterval (185516480876 / 1000000000000) (185516484460 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3428998909027191 / 4000000000000) 4 (IntervalRat.scale (801 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-10112730656 / 1000000000000) (-10112730655 / 1000000000000), orderedInterval (-25299501177 / 1000000000000) (-25299501176 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2447095421105703 / 4000000000000) 4 (IntervalRat.scale (801 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (1661170503 / 1000000000000) (1661170504 / 1000000000000), orderedInterval (-32217095578 / 1000000000000) (-32217095577 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2774745393724737 / 4000000000000) 4 (IntervalRat.scale (801 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-5411322777 / 1000000000000) (-5411322776 / 1000000000000), orderedInterval (-29803013781 / 1000000000000) (-29803013780 / 1000000000000)))) (orderedInterval (4905853146 / 1000000000000) (4905853524 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2313293427538353 / 4000000000000) 4 (IntervalRat.scale (801 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (28869868594 / 1000000000000) (28869868595 / 1000000000000), orderedInterval (16325359097 / 1000000000000) (16325359098 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2043864898381413 / 4000000000000) 4 (IntervalRat.scale (801 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (11378596378 / 1000000000000) (11378596420 / 1000000000000), orderedInterval (-33424329765 / 1000000000000) (-33424329723 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (592391711011887 / 800000000000) 4 (IntervalRat.scale (801 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-4120537854 / 1000000000000) (-4120537853 / 1000000000000), orderedInterval (29032930185 / 1000000000000) (29032930186 / 1000000000000)))) (orderedInterval (-1462496865 / 1000000000000) (-1462496657 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate529_chunkChecks4_2 :
    compactCertificate529.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1638586648526589 / 4000000000000) 4 (IntervalRat.scale (801 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (35429739437 / 1000000000000) (35429778479 / 1000000000000), orderedInterval (-17329149857 / 1000000000000) (-17329110815 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1389048048806229 / 4000000000000) 4 (IntervalRat.scale (801 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (26579521266 / 1000000000000) (26579529058 / 1000000000000), orderedInterval (-33605879267 / 1000000000000) (-33605871475 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (869201773374087 / 4000000000000) 4 (IntervalRat.scale (801 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-52370353128 / 1000000000000) (-52370353126 / 1000000000000), orderedInterval (-13554833561 / 1000000000000) (-13554833559 / 1000000000000)))) (orderedInterval (-7177747535 / 1000000000000) (-7177740333 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (467459604555129 / 4000000000000) 4 (IntervalRat.scale (801 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-72858201047 / 1000000000000) (-72858201043 / 1000000000000), orderedInterval (-11483201471 / 1000000000000) (-11483201467 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1269243760212387 / 4000000000000) 4 (IntervalRat.scale (801 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-31977849987 / 1000000000000) (-31977849986 / 1000000000000), orderedInterval (-31313816780 / 1000000000000) (-31313816779 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1733043843583299 / 4000000000000) 4 (IntervalRat.scale (801 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (18588534563 / 1000000000000) (18588534564 / 1000000000000), orderedInterval (33502194368 / 1000000000000) (33502194369 / 1000000000000)))) (orderedInterval (-1669920556 / 1000000000000) (-1669920509 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (732798226625913 / 4000000000000) 4 (IntervalRat.scale (801 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (57761079946 / 1000000000000) (57761080816 / 1000000000000), orderedInterval (-11932738935 / 1000000000000) (-11932738066 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2978784107493273 / 4000000000000) 4 (IntervalRat.scale (801 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-23329063215 / 1000000000000) (-23329063214 / 1000000000000), orderedInterval (-17608942739 / 1000000000000) (-17608942737 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1989689734845207 / 4000000000000) 4 (IntervalRat.scale (801 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (34524631465 / 1000000000000) (34524641433 / 1000000000000), orderedInterval (-9409471632 / 1000000000000) (-9409461664 / 1000000000000)))) (orderedInterval (7364795938 / 1000000000000) (7364800978 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate529_chunkChecks4 :
    compactCertificate529.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate529.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate529_chunkChecks4_0
    compactCertificate529_chunkChecks4_1 compactCertificate529_chunkChecks4_2

theorem compactCertificate529_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate529.chunkCheck r b = true :=
  compactCertificate529.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate529_chunkChecks0
    · exact compactCertificate529_chunkChecks1
    · exact compactCertificate529_chunkChecks2
    · exact compactCertificate529_chunkChecks3
    · exact compactCertificate529_chunkChecks4)

theorem compactCertificate529_coefficient0 :
    compactCertificate529.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate529_coefficient1 :
    compactCertificate529.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate529_coefficient2 :
    compactCertificate529.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate529_coefficient3 :
    compactCertificate529.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate529_coefficient4 :
    compactCertificate529.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate529_coefficients : ∀ r : Fin 5,
    compactCertificate529.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate529_coefficient0
  · exact compactCertificate529_coefficient1
  · exact compactCertificate529_coefficient2
  · exact compactCertificate529_coefficient3
  · exact compactCertificate529_coefficient4

theorem compactCertificate529_lower : (1 : ℚ) ≤ compactCertificate529.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate529, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate529_proves {t : ℝ} (ht : t ∈ compactCertificate529.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate529.proves compactCertificate529_states compactCertificate529_chunks
    compactCertificate529_coefficients compactCertificate529_lower ht

end Erdos232
