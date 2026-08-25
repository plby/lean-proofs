/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate428 : CompactCertificate where
  left := 299
  right := 300
  center := 599 / 2
  grid := fun i =>
    match i.val with
    | 0 => 95
    | 1 => 70
    | 2 => 114
    | 3 => 21
    | 4 => 55
    | 5 => 150
    | 6 => 110
    | 7 => 189
    | 8 => 139
    | 9 => 213
    | 10 => 123
    | 11 => 219
    | 12 => 204
    | 13 => 146
    | 14 => 165
    | 15 => 138
    | 16 => 122
    | 17 => 176
    | 18 => 98
    | 19 => 83
    | 20 => 52
    | 21 => 28
    | 22 => 76
    | 23 => 103
    | 24 => 44
    | 25 => 177
    | _ => 118
  point := fun i =>
    match i.val with
    | 0 => 599 / 2
    | 1 => 882441377792699 / 4000000000000
    | 2 => 285363410675867 / 800000000000
    | 3 => 257494193199793 / 4000000000000
    | 4 => 691665622489021 / 4000000000000
    | 5 => 1878006713182857 / 4000000000000
    | 6 => 1383331244978641 / 4000000000000
    | 7 => 2370361666396693 / 4000000000000
    | 8 => 1745997675092287 / 4000000000000
    | 9 => 2678809437044401 / 4000000000000
    | 10 => 1546611349585129 / 4000000000000
    | 11 => 2744488980275261 / 4000000000000
    | 12 => 2564257611120209 / 4000000000000
    | 13 => 1829975227518497 / 4000000000000
    | 14 => 2074996867467063 / 4000000000000
    | 15 => 1729916058795847 / 4000000000000
    | 16 => 1528433301036787 / 4000000000000
    | 17 => 442999544189913 / 800000000000
    | 18 => 1225360053018011 / 4000000000000
    | 19 => 1038751287434371 / 4000000000000
    | 20 => 650002324907713 / 4000000000000
    | 21 => 349573412145471 / 4000000000000
    | 22 => 949159815689413 / 4000000000000
    | 23 => 1295996582155301 / 4000000000000
    | 24 => 547997675092287 / 4000000000000
    | 25 => 2227580125328927 / 4000000000000
    | _ => 1487920288604593 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-44520377643 / 1000000000000) (-44520374205 / 1000000000000), orderedInterval (12055230219 / 1000000000000) (12055233656 / 1000000000000))
    | 1 => (orderedInterval (53515166623 / 1000000000000) (53515166645 / 1000000000000), orderedInterval (4552045136 / 1000000000000) (4552045158 / 1000000000000))
    | 2 => (orderedInterval (-25642367771 / 1000000000000) (-25642361570 / 1000000000000), orderedInterval (33609690512 / 1000000000000) (33609696713 / 1000000000000))
    | 3 => (orderedInterval (72466282598 / 1000000000000) (72466392416 / 1000000000000), orderedInterval (-68666275178 / 1000000000000) (-68666165360 / 1000000000000))
    | 4 => (orderedInterval (-48033871055 / 1000000000000) (-48033871054 / 1000000000000), orderedInterval (-36934081879 / 1000000000000) (-36934081878 / 1000000000000))
    | 5 => (orderedInterval (-29997234925 / 1000000000000) (-29997173320 / 1000000000000), orderedInterval (21388769147 / 1000000000000) (21388830752 / 1000000000000))
    | 6 => (orderedInterval (37058911168 / 1000000000000) (37058911169 / 1000000000000), orderedInterval (21567410515 / 1000000000000) (21567410516 / 1000000000000))
    | 7 => (orderedInterval (12321900630 / 1000000000000) (12321900683 / 1000000000000), orderedInterval (-30382601869 / 1000000000000) (-30382601815 / 1000000000000))
    | 8 => (orderedInterval (-21662851092 / 1000000000000) (-21662851091 / 1000000000000), orderedInterval (-31426540354 / 1000000000000) (-31426540353 / 1000000000000))
    | 9 => (orderedInterval (-29929987305 / 1000000000000) (-29929987241 / 1000000000000), orderedInterval (-7380132747 / 1000000000000) (-7380132683 / 1000000000000))
    | 10 => (orderedInterval (-34618675164 / 1000000000000) (-34618675163 / 1000000000000), orderedInterval (-21122094677 / 1000000000000) (-21122094676 / 1000000000000))
    | 11 => (orderedInterval (27165070094 / 1000000000000) (27165156449 / 1000000000000), orderedInterval (-13800558220 / 1000000000000) (-13800471865 / 1000000000000))
    | 12 => (orderedInterval (25899891234 / 1000000000000) (25899891235 / 1000000000000), orderedInterval (17931465642 / 1000000000000) (17931465643 / 1000000000000))
    | 13 => (orderedInterval (-14306249164 / 1000000000000) (-14306249007 / 1000000000000), orderedInterval (34466604703 / 1000000000000) (34466604860 / 1000000000000))
    | 14 => (orderedInterval (-32277099652 / 1000000000000) (-32277099650 / 1000000000000), orderedInterval (-13585391694 / 1000000000000) (-13585391692 / 1000000000000))
    | 15 => (orderedInterval (-10442886374 / 1000000000000) (-10442886339 / 1000000000000), orderedInterval (36930518743 / 1000000000000) (36930518778 / 1000000000000))
    | 16 => (orderedInterval (-15174445420 / 1000000000000) (-15174445198 / 1000000000000), orderedInterval (37911922431 / 1000000000000) (37911922653 / 1000000000000))
    | 17 => (orderedInterval (33874454103 / 1000000000000) (33874455343 / 1000000000000), orderedInterval (-1505033089 / 1000000000000) (-1505031849 / 1000000000000))
    | 18 => (orderedInterval (-31109548973 / 1000000000000) (-31109527831 / 1000000000000), orderedInterval (33372596100 / 1000000000000) (33372617242 / 1000000000000))
    | 19 => (orderedInterval (13656929186 / 1000000000000) (13656929316 / 1000000000000), orderedInterval (-47618029216 / 1000000000000) (-47618029086 / 1000000000000))
    | 20 => (orderedInterval (-4852672181 / 1000000000000) (-4852672168 / 1000000000000), orderedInterval (62417783746 / 1000000000000) (62417783760 / 1000000000000))
    | 21 => (orderedInterval (18019337638 / 1000000000000) (18019337639 / 1000000000000), orderedInterval (83323195718 / 1000000000000) (83323195719 / 1000000000000))
    | 22 => (orderedInterval (-32818983400 / 1000000000000) (-32818967503 / 1000000000000), orderedInterval (40141493017 / 1000000000000) (40141508914 / 1000000000000))
    | 23 => (orderedInterval (-41316292075 / 1000000000000) (-41316292074 / 1000000000000), orderedInterval (-15993740269 / 1000000000000) (-15993740268 / 1000000000000))
    | 24 => (orderedInterval (-29415470692 / 1000000000000) (-29415468465 / 1000000000000), orderedInterval (61602304069 / 1000000000000) (61602306296 / 1000000000000))
    | 25 => (orderedInterval (-33772483762 / 1000000000000) (-33772482438 / 1000000000000), orderedInterval (1636028085 / 1000000000000) (1636029409 / 1000000000000))
    | _ => (orderedInterval (36571386374 / 1000000000000) (36571430391 / 1000000000000), orderedInterval (-19387387972 / 1000000000000) (-19387343954 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-18652385023 / 1000000000000) (-18652383275 / 1000000000000)
      | 1 => orderedInterval (-407521214 / 1000000000000) (-407515607 / 1000000000000)
      | 2 => orderedInterval (-903605096 / 1000000000000) (-903605077 / 1000000000000)
      | 3 => orderedInterval (6614913116 / 1000000000000) (6614925523 / 1000000000000)
      | 4 => orderedInterval (-1657072189 / 1000000000000) (-1657072138 / 1000000000000)
      | 5 => orderedInterval (1615111883 / 1000000000000) (1615111957 / 1000000000000)
      | 6 => orderedInterval (4043216680 / 1000000000000) (4043220144 / 1000000000000)
      | 7 => orderedInterval (3578264128 / 1000000000000) (3578264525 / 1000000000000)
      | _ => orderedInterval (-4289956535 / 1000000000000) (-4289948071 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (7158468924 / 1000000000000) (7158470744 / 1000000000000)
      | 1 => orderedInterval (-3002051234 / 1000000000000) (-3002044071 / 1000000000000)
      | 2 => orderedInterval (747245352 / 1000000000000) (747245386 / 1000000000000)
      | 3 => orderedInterval (-3582423713 / 1000000000000) (-3582395319 / 1000000000000)
      | 4 => orderedInterval (4404779183 / 1000000000000) (4404779265 / 1000000000000)
      | 5 => orderedInterval (-2223422506 / 1000000000000) (-2223422389 / 1000000000000)
      | 6 => orderedInterval (-2018459373 / 1000000000000) (-2018455838 / 1000000000000)
      | 7 => orderedInterval (155532648 / 1000000000000) (155532967 / 1000000000000)
      | _ => orderedInterval (4440127963 / 1000000000000) (4440138544 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (19486276498 / 1000000000000) (19486278410 / 1000000000000)
      | 1 => orderedInterval (-4609500551 / 1000000000000) (-4609489653 / 1000000000000)
      | 2 => orderedInterval (2597437465 / 1000000000000) (2597437524 / 1000000000000)
      | 3 => orderedInterval (-42570952144 / 1000000000000) (-42570887039 / 1000000000000)
      | 4 => orderedInterval (4794092444 / 1000000000000) (4794092576 / 1000000000000)
      | 5 => orderedInterval (-4119524626 / 1000000000000) (-4119524433 / 1000000000000)
      | 6 => orderedInterval (-4569594398 / 1000000000000) (-4569590778 / 1000000000000)
      | 7 => orderedInterval (-4145213838 / 1000000000000) (-4145213578 / 1000000000000)
      | _ => orderedInterval (1102094937 / 1000000000000) (1102108259 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-8192150390 / 1000000000000) (-8192148374 / 1000000000000)
      | 1 => orderedInterval (6124994619 / 1000000000000) (6125011623 / 1000000000000)
      | 2 => orderedInterval (-4916287780 / 1000000000000) (-4916287672 / 1000000000000)
      | 3 => orderedInterval (12434936240 / 1000000000000) (12435085331 / 1000000000000)
      | 4 => orderedInterval (-8815387153 / 1000000000000) (-8815386937 / 1000000000000)
      | 5 => orderedInterval (3478734080 / 1000000000000) (3478734405 / 1000000000000)
      | 6 => orderedInterval (3643782141 / 1000000000000) (3643785840 / 1000000000000)
      | 7 => orderedInterval (-1046833800 / 1000000000000) (-1046833586 / 1000000000000)
      | _ => orderedInterval (-6152201829 / 1000000000000) (-6152185002 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-20472227583 / 1000000000000) (-20472225437 / 1000000000000)
      | 1 => orderedInterval (12640488227 / 1000000000000) (12640514921 / 1000000000000)
      | 2 => orderedInterval (-8154054294 / 1000000000000) (-8154054094 / 1000000000000)
      | 3 => orderedInterval (232110466299 / 1000000000000) (232110808254 / 1000000000000)
      | 4 => orderedInterval (-15650987350 / 1000000000000) (-15650986986 / 1000000000000)
      | 5 => orderedInterval (11888666571 / 1000000000000) (11888667130 / 1000000000000)
      | 6 => orderedInterval (4969406070 / 1000000000000) (4969409862 / 1000000000000)
      | 7 => orderedInterval (4634603422 / 1000000000000) (4634603600 / 1000000000000)
      | _ => orderedInterval (16568211771 / 1000000000000) (16568233248 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-10059034250 / 1000000000000) (-10059002019 / 1000000000000)
    | 1 => orderedInterval (6079797244 / 1000000000000) (6079849289 / 1000000000000)
    | 2 => orderedInterval (-32034884213 / 1000000000000) (-32034788712 / 1000000000000)
    | 3 => orderedInterval (-3440413872 / 1000000000000) (-3440224372 / 1000000000000)
    | _ => orderedInterval (238534573133 / 1000000000000) (238534970498 / 1000000000000)

theorem compactCertificate428_stateChecks0 :
    compactCertificate428.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 95 12 (599 / 2)) (orderedInterval (-44520377643 / 1000000000000) (-44520374205 / 1000000000000), orderedInterval (12055230219 / 1000000000000) (12055233656 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (882441377792699 / 4000000000000)) (orderedInterval (53515166623 / 1000000000000) (53515166645 / 1000000000000), orderedInterval (4552045136 / 1000000000000) (4552045158 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 114 12 (285363410675867 / 800000000000)) (orderedInterval (-25642367771 / 1000000000000) (-25642361570 / 1000000000000), orderedInterval (33609690512 / 1000000000000) (33609696713 / 1000000000000))) = true
  rfl'

theorem compactCertificate428_stateChecks1 :
    compactCertificate428.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 21 12 (257494193199793 / 4000000000000)) (orderedInterval (72466282598 / 1000000000000) (72466392416 / 1000000000000), orderedInterval (-68666275178 / 1000000000000) (-68666165360 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (691665622489021 / 4000000000000)) (orderedInterval (-48033871055 / 1000000000000) (-48033871054 / 1000000000000), orderedInterval (-36934081879 / 1000000000000) (-36934081878 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 150 12 (1878006713182857 / 4000000000000)) (orderedInterval (-29997234925 / 1000000000000) (-29997173320 / 1000000000000), orderedInterval (21388769147 / 1000000000000) (21388830752 / 1000000000000))) = true
  rfl'

theorem compactCertificate428_stateChecks2 :
    compactCertificate428.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 110 12 (1383331244978641 / 4000000000000)) (orderedInterval (37058911168 / 1000000000000) (37058911169 / 1000000000000), orderedInterval (21567410515 / 1000000000000) (21567410516 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 189 12 (2370361666396693 / 4000000000000)) (orderedInterval (12321900630 / 1000000000000) (12321900683 / 1000000000000), orderedInterval (-30382601869 / 1000000000000) (-30382601815 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 139 12 (1745997675092287 / 4000000000000)) (orderedInterval (-21662851092 / 1000000000000) (-21662851091 / 1000000000000), orderedInterval (-31426540354 / 1000000000000) (-31426540353 / 1000000000000))) = true
  rfl'

theorem compactCertificate428_stateChecks3 :
    compactCertificate428.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 213 12 (2678809437044401 / 4000000000000)) (orderedInterval (-29929987305 / 1000000000000) (-29929987241 / 1000000000000), orderedInterval (-7380132747 / 1000000000000) (-7380132683 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 123 12 (1546611349585129 / 4000000000000)) (orderedInterval (-34618675164 / 1000000000000) (-34618675163 / 1000000000000), orderedInterval (-21122094677 / 1000000000000) (-21122094676 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 219 12 (2744488980275261 / 4000000000000)) (orderedInterval (27165070094 / 1000000000000) (27165156449 / 1000000000000), orderedInterval (-13800558220 / 1000000000000) (-13800471865 / 1000000000000))) = true
  rfl'

theorem compactCertificate428_stateChecks4 :
    compactCertificate428.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 204 12 (2564257611120209 / 4000000000000)) (orderedInterval (25899891234 / 1000000000000) (25899891235 / 1000000000000), orderedInterval (17931465642 / 1000000000000) (17931465643 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 146 12 (1829975227518497 / 4000000000000)) (orderedInterval (-14306249164 / 1000000000000) (-14306249007 / 1000000000000), orderedInterval (34466604703 / 1000000000000) (34466604860 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 165 12 (2074996867467063 / 4000000000000)) (orderedInterval (-32277099652 / 1000000000000) (-32277099650 / 1000000000000), orderedInterval (-13585391694 / 1000000000000) (-13585391692 / 1000000000000))) = true
  rfl'

theorem compactCertificate428_stateChecks5 :
    compactCertificate428.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 138 12 (1729916058795847 / 4000000000000)) (orderedInterval (-10442886374 / 1000000000000) (-10442886339 / 1000000000000), orderedInterval (36930518743 / 1000000000000) (36930518778 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 122 12 (1528433301036787 / 4000000000000)) (orderedInterval (-15174445420 / 1000000000000) (-15174445198 / 1000000000000), orderedInterval (37911922431 / 1000000000000) (37911922653 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 176 12 (442999544189913 / 800000000000)) (orderedInterval (33874454103 / 1000000000000) (33874455343 / 1000000000000), orderedInterval (-1505033089 / 1000000000000) (-1505031849 / 1000000000000))) = true
  rfl'

theorem compactCertificate428_stateChecks6 :
    compactCertificate428.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 98 12 (1225360053018011 / 4000000000000)) (orderedInterval (-31109548973 / 1000000000000) (-31109527831 / 1000000000000), orderedInterval (33372596100 / 1000000000000) (33372617242 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (1038751287434371 / 4000000000000)) (orderedInterval (13656929186 / 1000000000000) (13656929316 / 1000000000000), orderedInterval (-47618029216 / 1000000000000) (-47618029086 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (650002324907713 / 4000000000000)) (orderedInterval (-4852672181 / 1000000000000) (-4852672168 / 1000000000000), orderedInterval (62417783746 / 1000000000000) (62417783760 / 1000000000000))) = true
  rfl'

theorem compactCertificate428_stateChecks7 :
    compactCertificate428.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 28 12 (349573412145471 / 4000000000000)) (orderedInterval (18019337638 / 1000000000000) (18019337639 / 1000000000000), orderedInterval (83323195718 / 1000000000000) (83323195719 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (949159815689413 / 4000000000000)) (orderedInterval (-32818983400 / 1000000000000) (-32818967503 / 1000000000000), orderedInterval (40141493017 / 1000000000000) (40141508914 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 103 12 (1295996582155301 / 4000000000000)) (orderedInterval (-41316292075 / 1000000000000) (-41316292074 / 1000000000000), orderedInterval (-15993740269 / 1000000000000) (-15993740268 / 1000000000000))) = true
  rfl'

theorem compactCertificate428_stateChecks8 :
    compactCertificate428.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (547997675092287 / 4000000000000)) (orderedInterval (-29415470692 / 1000000000000) (-29415468465 / 1000000000000), orderedInterval (61602304069 / 1000000000000) (61602306296 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 177 12 (2227580125328927 / 4000000000000)) (orderedInterval (-33772483762 / 1000000000000) (-33772482438 / 1000000000000), orderedInterval (1636028085 / 1000000000000) (1636029409 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 118 12 (1487920288604593 / 4000000000000)) (orderedInterval (36571386374 / 1000000000000) (36571430391 / 1000000000000), orderedInterval (-19387387972 / 1000000000000) (-19387343954 / 1000000000000))) = true
  rfl'

theorem compactCertificate428_states : ∀ j,
    BesselStateValid (compactCertificate428.point j) (compactCertificate428.state j) :=
  compactCertificate428.statesValid_of_checks3 compactCertificate428_stateChecks0
    compactCertificate428_stateChecks1 compactCertificate428_stateChecks2
    compactCertificate428_stateChecks3 compactCertificate428_stateChecks4
    compactCertificate428_stateChecks5 compactCertificate428_stateChecks6
    compactCertificate428_stateChecks7 compactCertificate428_stateChecks8

theorem compactCertificate428_chunkChecks0_0 :
    compactCertificate428.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (599 / 2) 0 (IntervalRat.scale (599 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-44520377643 / 1000000000000) (-44520374205 / 1000000000000), orderedInterval (12055230219 / 1000000000000) (12055233656 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (882441377792699 / 4000000000000) 0 (IntervalRat.scale (599 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (53515166623 / 1000000000000) (53515166645 / 1000000000000), orderedInterval (4552045136 / 1000000000000) (4552045158 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (285363410675867 / 800000000000) 0 (IntervalRat.scale (599 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-25642367771 / 1000000000000) (-25642361570 / 1000000000000), orderedInterval (33609690512 / 1000000000000) (33609696713 / 1000000000000)))) (orderedInterval (-18652385023 / 1000000000000) (-18652383275 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (257494193199793 / 4000000000000) 0 (IntervalRat.scale (599 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (72466282598 / 1000000000000) (72466392416 / 1000000000000), orderedInterval (-68666275178 / 1000000000000) (-68666165360 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (691665622489021 / 4000000000000) 0 (IntervalRat.scale (599 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-48033871055 / 1000000000000) (-48033871054 / 1000000000000), orderedInterval (-36934081879 / 1000000000000) (-36934081878 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1878006713182857 / 4000000000000) 0 (IntervalRat.scale (599 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29997234925 / 1000000000000) (-29997173320 / 1000000000000), orderedInterval (21388769147 / 1000000000000) (21388830752 / 1000000000000)))) (orderedInterval (-407521214 / 1000000000000) (-407515607 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1383331244978641 / 4000000000000) 0 (IntervalRat.scale (599 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (37058911168 / 1000000000000) (37058911169 / 1000000000000), orderedInterval (21567410515 / 1000000000000) (21567410516 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2370361666396693 / 4000000000000) 0 (IntervalRat.scale (599 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (12321900630 / 1000000000000) (12321900683 / 1000000000000), orderedInterval (-30382601869 / 1000000000000) (-30382601815 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1745997675092287 / 4000000000000) 0 (IntervalRat.scale (599 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-21662851092 / 1000000000000) (-21662851091 / 1000000000000), orderedInterval (-31426540354 / 1000000000000) (-31426540353 / 1000000000000)))) (orderedInterval (-903605096 / 1000000000000) (-903605077 / 1000000000000))) = true
  rfl'

theorem compactCertificate428_chunkChecks0_1 :
    compactCertificate428.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2678809437044401 / 4000000000000) 0 (IntervalRat.scale (599 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-29929987305 / 1000000000000) (-29929987241 / 1000000000000), orderedInterval (-7380132747 / 1000000000000) (-7380132683 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1546611349585129 / 4000000000000) 0 (IntervalRat.scale (599 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-34618675164 / 1000000000000) (-34618675163 / 1000000000000), orderedInterval (-21122094677 / 1000000000000) (-21122094676 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2744488980275261 / 4000000000000) 0 (IntervalRat.scale (599 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (27165070094 / 1000000000000) (27165156449 / 1000000000000), orderedInterval (-13800558220 / 1000000000000) (-13800471865 / 1000000000000)))) (orderedInterval (6614913116 / 1000000000000) (6614925523 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2564257611120209 / 4000000000000) 0 (IntervalRat.scale (599 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25899891234 / 1000000000000) (25899891235 / 1000000000000), orderedInterval (17931465642 / 1000000000000) (17931465643 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1829975227518497 / 4000000000000) 0 (IntervalRat.scale (599 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14306249164 / 1000000000000) (-14306249007 / 1000000000000), orderedInterval (34466604703 / 1000000000000) (34466604860 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2074996867467063 / 4000000000000) 0 (IntervalRat.scale (599 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-32277099652 / 1000000000000) (-32277099650 / 1000000000000), orderedInterval (-13585391694 / 1000000000000) (-13585391692 / 1000000000000)))) (orderedInterval (-1657072189 / 1000000000000) (-1657072138 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1729916058795847 / 4000000000000) 0 (IntervalRat.scale (599 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-10442886374 / 1000000000000) (-10442886339 / 1000000000000), orderedInterval (36930518743 / 1000000000000) (36930518778 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1528433301036787 / 4000000000000) 0 (IntervalRat.scale (599 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-15174445420 / 1000000000000) (-15174445198 / 1000000000000), orderedInterval (37911922431 / 1000000000000) (37911922653 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (442999544189913 / 800000000000) 0 (IntervalRat.scale (599 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (33874454103 / 1000000000000) (33874455343 / 1000000000000), orderedInterval (-1505033089 / 1000000000000) (-1505031849 / 1000000000000)))) (orderedInterval (1615111883 / 1000000000000) (1615111957 / 1000000000000))) = true
  rfl'

theorem compactCertificate428_chunkChecks0_2 :
    compactCertificate428.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1225360053018011 / 4000000000000) 0 (IntervalRat.scale (599 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-31109548973 / 1000000000000) (-31109527831 / 1000000000000), orderedInterval (33372596100 / 1000000000000) (33372617242 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1038751287434371 / 4000000000000) 0 (IntervalRat.scale (599 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (13656929186 / 1000000000000) (13656929316 / 1000000000000), orderedInterval (-47618029216 / 1000000000000) (-47618029086 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (650002324907713 / 4000000000000) 0 (IntervalRat.scale (599 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-4852672181 / 1000000000000) (-4852672168 / 1000000000000), orderedInterval (62417783746 / 1000000000000) (62417783760 / 1000000000000)))) (orderedInterval (4043216680 / 1000000000000) (4043220144 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (349573412145471 / 4000000000000) 0 (IntervalRat.scale (599 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (18019337638 / 1000000000000) (18019337639 / 1000000000000), orderedInterval (83323195718 / 1000000000000) (83323195719 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (949159815689413 / 4000000000000) 0 (IntervalRat.scale (599 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-32818983400 / 1000000000000) (-32818967503 / 1000000000000), orderedInterval (40141493017 / 1000000000000) (40141508914 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1295996582155301 / 4000000000000) 0 (IntervalRat.scale (599 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-41316292075 / 1000000000000) (-41316292074 / 1000000000000), orderedInterval (-15993740269 / 1000000000000) (-15993740268 / 1000000000000)))) (orderedInterval (3578264128 / 1000000000000) (3578264525 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (547997675092287 / 4000000000000) 0 (IntervalRat.scale (599 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-29415470692 / 1000000000000) (-29415468465 / 1000000000000), orderedInterval (61602304069 / 1000000000000) (61602306296 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2227580125328927 / 4000000000000) 0 (IntervalRat.scale (599 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-33772483762 / 1000000000000) (-33772482438 / 1000000000000), orderedInterval (1636028085 / 1000000000000) (1636029409 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1487920288604593 / 4000000000000) 0 (IntervalRat.scale (599 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (36571386374 / 1000000000000) (36571430391 / 1000000000000), orderedInterval (-19387387972 / 1000000000000) (-19387343954 / 1000000000000)))) (orderedInterval (-4289956535 / 1000000000000) (-4289948071 / 1000000000000))) = true
  rfl'

theorem compactCertificate428_chunkChecks0 :
    compactCertificate428.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate428.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate428_chunkChecks0_0
    compactCertificate428_chunkChecks0_1 compactCertificate428_chunkChecks0_2

theorem compactCertificate428_chunkChecks1_0 :
    compactCertificate428.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (599 / 2) 1 (IntervalRat.scale (599 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-44520377643 / 1000000000000) (-44520374205 / 1000000000000), orderedInterval (12055230219 / 1000000000000) (12055233656 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (882441377792699 / 4000000000000) 1 (IntervalRat.scale (599 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (53515166623 / 1000000000000) (53515166645 / 1000000000000), orderedInterval (4552045136 / 1000000000000) (4552045158 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (285363410675867 / 800000000000) 1 (IntervalRat.scale (599 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-25642367771 / 1000000000000) (-25642361570 / 1000000000000), orderedInterval (33609690512 / 1000000000000) (33609696713 / 1000000000000)))) (orderedInterval (7158468924 / 1000000000000) (7158470744 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (257494193199793 / 4000000000000) 1 (IntervalRat.scale (599 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (72466282598 / 1000000000000) (72466392416 / 1000000000000), orderedInterval (-68666275178 / 1000000000000) (-68666165360 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (691665622489021 / 4000000000000) 1 (IntervalRat.scale (599 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-48033871055 / 1000000000000) (-48033871054 / 1000000000000), orderedInterval (-36934081879 / 1000000000000) (-36934081878 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1878006713182857 / 4000000000000) 1 (IntervalRat.scale (599 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29997234925 / 1000000000000) (-29997173320 / 1000000000000), orderedInterval (21388769147 / 1000000000000) (21388830752 / 1000000000000)))) (orderedInterval (-3002051234 / 1000000000000) (-3002044071 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1383331244978641 / 4000000000000) 1 (IntervalRat.scale (599 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (37058911168 / 1000000000000) (37058911169 / 1000000000000), orderedInterval (21567410515 / 1000000000000) (21567410516 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2370361666396693 / 4000000000000) 1 (IntervalRat.scale (599 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (12321900630 / 1000000000000) (12321900683 / 1000000000000), orderedInterval (-30382601869 / 1000000000000) (-30382601815 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1745997675092287 / 4000000000000) 1 (IntervalRat.scale (599 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-21662851092 / 1000000000000) (-21662851091 / 1000000000000), orderedInterval (-31426540354 / 1000000000000) (-31426540353 / 1000000000000)))) (orderedInterval (747245352 / 1000000000000) (747245386 / 1000000000000))) = true
  rfl'

theorem compactCertificate428_chunkChecks1_1 :
    compactCertificate428.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2678809437044401 / 4000000000000) 1 (IntervalRat.scale (599 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-29929987305 / 1000000000000) (-29929987241 / 1000000000000), orderedInterval (-7380132747 / 1000000000000) (-7380132683 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1546611349585129 / 4000000000000) 1 (IntervalRat.scale (599 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-34618675164 / 1000000000000) (-34618675163 / 1000000000000), orderedInterval (-21122094677 / 1000000000000) (-21122094676 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2744488980275261 / 4000000000000) 1 (IntervalRat.scale (599 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (27165070094 / 1000000000000) (27165156449 / 1000000000000), orderedInterval (-13800558220 / 1000000000000) (-13800471865 / 1000000000000)))) (orderedInterval (-3582423713 / 1000000000000) (-3582395319 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2564257611120209 / 4000000000000) 1 (IntervalRat.scale (599 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25899891234 / 1000000000000) (25899891235 / 1000000000000), orderedInterval (17931465642 / 1000000000000) (17931465643 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1829975227518497 / 4000000000000) 1 (IntervalRat.scale (599 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14306249164 / 1000000000000) (-14306249007 / 1000000000000), orderedInterval (34466604703 / 1000000000000) (34466604860 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2074996867467063 / 4000000000000) 1 (IntervalRat.scale (599 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-32277099652 / 1000000000000) (-32277099650 / 1000000000000), orderedInterval (-13585391694 / 1000000000000) (-13585391692 / 1000000000000)))) (orderedInterval (4404779183 / 1000000000000) (4404779265 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1729916058795847 / 4000000000000) 1 (IntervalRat.scale (599 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-10442886374 / 1000000000000) (-10442886339 / 1000000000000), orderedInterval (36930518743 / 1000000000000) (36930518778 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1528433301036787 / 4000000000000) 1 (IntervalRat.scale (599 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-15174445420 / 1000000000000) (-15174445198 / 1000000000000), orderedInterval (37911922431 / 1000000000000) (37911922653 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (442999544189913 / 800000000000) 1 (IntervalRat.scale (599 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (33874454103 / 1000000000000) (33874455343 / 1000000000000), orderedInterval (-1505033089 / 1000000000000) (-1505031849 / 1000000000000)))) (orderedInterval (-2223422506 / 1000000000000) (-2223422389 / 1000000000000))) = true
  rfl'

theorem compactCertificate428_chunkChecks1_2 :
    compactCertificate428.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1225360053018011 / 4000000000000) 1 (IntervalRat.scale (599 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-31109548973 / 1000000000000) (-31109527831 / 1000000000000), orderedInterval (33372596100 / 1000000000000) (33372617242 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1038751287434371 / 4000000000000) 1 (IntervalRat.scale (599 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (13656929186 / 1000000000000) (13656929316 / 1000000000000), orderedInterval (-47618029216 / 1000000000000) (-47618029086 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (650002324907713 / 4000000000000) 1 (IntervalRat.scale (599 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-4852672181 / 1000000000000) (-4852672168 / 1000000000000), orderedInterval (62417783746 / 1000000000000) (62417783760 / 1000000000000)))) (orderedInterval (-2018459373 / 1000000000000) (-2018455838 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (349573412145471 / 4000000000000) 1 (IntervalRat.scale (599 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (18019337638 / 1000000000000) (18019337639 / 1000000000000), orderedInterval (83323195718 / 1000000000000) (83323195719 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (949159815689413 / 4000000000000) 1 (IntervalRat.scale (599 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-32818983400 / 1000000000000) (-32818967503 / 1000000000000), orderedInterval (40141493017 / 1000000000000) (40141508914 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1295996582155301 / 4000000000000) 1 (IntervalRat.scale (599 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-41316292075 / 1000000000000) (-41316292074 / 1000000000000), orderedInterval (-15993740269 / 1000000000000) (-15993740268 / 1000000000000)))) (orderedInterval (155532648 / 1000000000000) (155532967 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (547997675092287 / 4000000000000) 1 (IntervalRat.scale (599 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-29415470692 / 1000000000000) (-29415468465 / 1000000000000), orderedInterval (61602304069 / 1000000000000) (61602306296 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2227580125328927 / 4000000000000) 1 (IntervalRat.scale (599 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-33772483762 / 1000000000000) (-33772482438 / 1000000000000), orderedInterval (1636028085 / 1000000000000) (1636029409 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1487920288604593 / 4000000000000) 1 (IntervalRat.scale (599 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (36571386374 / 1000000000000) (36571430391 / 1000000000000), orderedInterval (-19387387972 / 1000000000000) (-19387343954 / 1000000000000)))) (orderedInterval (4440127963 / 1000000000000) (4440138544 / 1000000000000))) = true
  rfl'

theorem compactCertificate428_chunkChecks1 :
    compactCertificate428.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate428.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate428_chunkChecks1_0
    compactCertificate428_chunkChecks1_1 compactCertificate428_chunkChecks1_2

theorem compactCertificate428_chunkChecks2_0 :
    compactCertificate428.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (599 / 2) 2 (IntervalRat.scale (599 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-44520377643 / 1000000000000) (-44520374205 / 1000000000000), orderedInterval (12055230219 / 1000000000000) (12055233656 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (882441377792699 / 4000000000000) 2 (IntervalRat.scale (599 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (53515166623 / 1000000000000) (53515166645 / 1000000000000), orderedInterval (4552045136 / 1000000000000) (4552045158 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (285363410675867 / 800000000000) 2 (IntervalRat.scale (599 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-25642367771 / 1000000000000) (-25642361570 / 1000000000000), orderedInterval (33609690512 / 1000000000000) (33609696713 / 1000000000000)))) (orderedInterval (19486276498 / 1000000000000) (19486278410 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (257494193199793 / 4000000000000) 2 (IntervalRat.scale (599 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (72466282598 / 1000000000000) (72466392416 / 1000000000000), orderedInterval (-68666275178 / 1000000000000) (-68666165360 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (691665622489021 / 4000000000000) 2 (IntervalRat.scale (599 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-48033871055 / 1000000000000) (-48033871054 / 1000000000000), orderedInterval (-36934081879 / 1000000000000) (-36934081878 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1878006713182857 / 4000000000000) 2 (IntervalRat.scale (599 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29997234925 / 1000000000000) (-29997173320 / 1000000000000), orderedInterval (21388769147 / 1000000000000) (21388830752 / 1000000000000)))) (orderedInterval (-4609500551 / 1000000000000) (-4609489653 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1383331244978641 / 4000000000000) 2 (IntervalRat.scale (599 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (37058911168 / 1000000000000) (37058911169 / 1000000000000), orderedInterval (21567410515 / 1000000000000) (21567410516 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2370361666396693 / 4000000000000) 2 (IntervalRat.scale (599 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (12321900630 / 1000000000000) (12321900683 / 1000000000000), orderedInterval (-30382601869 / 1000000000000) (-30382601815 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1745997675092287 / 4000000000000) 2 (IntervalRat.scale (599 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-21662851092 / 1000000000000) (-21662851091 / 1000000000000), orderedInterval (-31426540354 / 1000000000000) (-31426540353 / 1000000000000)))) (orderedInterval (2597437465 / 1000000000000) (2597437524 / 1000000000000))) = true
  rfl'

theorem compactCertificate428_chunkChecks2_1 :
    compactCertificate428.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2678809437044401 / 4000000000000) 2 (IntervalRat.scale (599 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-29929987305 / 1000000000000) (-29929987241 / 1000000000000), orderedInterval (-7380132747 / 1000000000000) (-7380132683 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1546611349585129 / 4000000000000) 2 (IntervalRat.scale (599 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-34618675164 / 1000000000000) (-34618675163 / 1000000000000), orderedInterval (-21122094677 / 1000000000000) (-21122094676 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2744488980275261 / 4000000000000) 2 (IntervalRat.scale (599 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (27165070094 / 1000000000000) (27165156449 / 1000000000000), orderedInterval (-13800558220 / 1000000000000) (-13800471865 / 1000000000000)))) (orderedInterval (-42570952144 / 1000000000000) (-42570887039 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2564257611120209 / 4000000000000) 2 (IntervalRat.scale (599 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25899891234 / 1000000000000) (25899891235 / 1000000000000), orderedInterval (17931465642 / 1000000000000) (17931465643 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1829975227518497 / 4000000000000) 2 (IntervalRat.scale (599 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14306249164 / 1000000000000) (-14306249007 / 1000000000000), orderedInterval (34466604703 / 1000000000000) (34466604860 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2074996867467063 / 4000000000000) 2 (IntervalRat.scale (599 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-32277099652 / 1000000000000) (-32277099650 / 1000000000000), orderedInterval (-13585391694 / 1000000000000) (-13585391692 / 1000000000000)))) (orderedInterval (4794092444 / 1000000000000) (4794092576 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1729916058795847 / 4000000000000) 2 (IntervalRat.scale (599 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-10442886374 / 1000000000000) (-10442886339 / 1000000000000), orderedInterval (36930518743 / 1000000000000) (36930518778 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1528433301036787 / 4000000000000) 2 (IntervalRat.scale (599 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-15174445420 / 1000000000000) (-15174445198 / 1000000000000), orderedInterval (37911922431 / 1000000000000) (37911922653 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (442999544189913 / 800000000000) 2 (IntervalRat.scale (599 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (33874454103 / 1000000000000) (33874455343 / 1000000000000), orderedInterval (-1505033089 / 1000000000000) (-1505031849 / 1000000000000)))) (orderedInterval (-4119524626 / 1000000000000) (-4119524433 / 1000000000000))) = true
  rfl'

theorem compactCertificate428_chunkChecks2_2 :
    compactCertificate428.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1225360053018011 / 4000000000000) 2 (IntervalRat.scale (599 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-31109548973 / 1000000000000) (-31109527831 / 1000000000000), orderedInterval (33372596100 / 1000000000000) (33372617242 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1038751287434371 / 4000000000000) 2 (IntervalRat.scale (599 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (13656929186 / 1000000000000) (13656929316 / 1000000000000), orderedInterval (-47618029216 / 1000000000000) (-47618029086 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (650002324907713 / 4000000000000) 2 (IntervalRat.scale (599 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-4852672181 / 1000000000000) (-4852672168 / 1000000000000), orderedInterval (62417783746 / 1000000000000) (62417783760 / 1000000000000)))) (orderedInterval (-4569594398 / 1000000000000) (-4569590778 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (349573412145471 / 4000000000000) 2 (IntervalRat.scale (599 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (18019337638 / 1000000000000) (18019337639 / 1000000000000), orderedInterval (83323195718 / 1000000000000) (83323195719 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (949159815689413 / 4000000000000) 2 (IntervalRat.scale (599 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-32818983400 / 1000000000000) (-32818967503 / 1000000000000), orderedInterval (40141493017 / 1000000000000) (40141508914 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1295996582155301 / 4000000000000) 2 (IntervalRat.scale (599 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-41316292075 / 1000000000000) (-41316292074 / 1000000000000), orderedInterval (-15993740269 / 1000000000000) (-15993740268 / 1000000000000)))) (orderedInterval (-4145213838 / 1000000000000) (-4145213578 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (547997675092287 / 4000000000000) 2 (IntervalRat.scale (599 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-29415470692 / 1000000000000) (-29415468465 / 1000000000000), orderedInterval (61602304069 / 1000000000000) (61602306296 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2227580125328927 / 4000000000000) 2 (IntervalRat.scale (599 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-33772483762 / 1000000000000) (-33772482438 / 1000000000000), orderedInterval (1636028085 / 1000000000000) (1636029409 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1487920288604593 / 4000000000000) 2 (IntervalRat.scale (599 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (36571386374 / 1000000000000) (36571430391 / 1000000000000), orderedInterval (-19387387972 / 1000000000000) (-19387343954 / 1000000000000)))) (orderedInterval (1102094937 / 1000000000000) (1102108259 / 1000000000000))) = true
  rfl'

theorem compactCertificate428_chunkChecks2 :
    compactCertificate428.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate428.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate428_chunkChecks2_0
    compactCertificate428_chunkChecks2_1 compactCertificate428_chunkChecks2_2

theorem compactCertificate428_chunkChecks3_0 :
    compactCertificate428.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (599 / 2) 3 (IntervalRat.scale (599 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-44520377643 / 1000000000000) (-44520374205 / 1000000000000), orderedInterval (12055230219 / 1000000000000) (12055233656 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (882441377792699 / 4000000000000) 3 (IntervalRat.scale (599 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (53515166623 / 1000000000000) (53515166645 / 1000000000000), orderedInterval (4552045136 / 1000000000000) (4552045158 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (285363410675867 / 800000000000) 3 (IntervalRat.scale (599 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-25642367771 / 1000000000000) (-25642361570 / 1000000000000), orderedInterval (33609690512 / 1000000000000) (33609696713 / 1000000000000)))) (orderedInterval (-8192150390 / 1000000000000) (-8192148374 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (257494193199793 / 4000000000000) 3 (IntervalRat.scale (599 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (72466282598 / 1000000000000) (72466392416 / 1000000000000), orderedInterval (-68666275178 / 1000000000000) (-68666165360 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (691665622489021 / 4000000000000) 3 (IntervalRat.scale (599 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-48033871055 / 1000000000000) (-48033871054 / 1000000000000), orderedInterval (-36934081879 / 1000000000000) (-36934081878 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1878006713182857 / 4000000000000) 3 (IntervalRat.scale (599 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29997234925 / 1000000000000) (-29997173320 / 1000000000000), orderedInterval (21388769147 / 1000000000000) (21388830752 / 1000000000000)))) (orderedInterval (6124994619 / 1000000000000) (6125011623 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1383331244978641 / 4000000000000) 3 (IntervalRat.scale (599 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (37058911168 / 1000000000000) (37058911169 / 1000000000000), orderedInterval (21567410515 / 1000000000000) (21567410516 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2370361666396693 / 4000000000000) 3 (IntervalRat.scale (599 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (12321900630 / 1000000000000) (12321900683 / 1000000000000), orderedInterval (-30382601869 / 1000000000000) (-30382601815 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1745997675092287 / 4000000000000) 3 (IntervalRat.scale (599 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-21662851092 / 1000000000000) (-21662851091 / 1000000000000), orderedInterval (-31426540354 / 1000000000000) (-31426540353 / 1000000000000)))) (orderedInterval (-4916287780 / 1000000000000) (-4916287672 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate428_chunkChecks3_1 :
    compactCertificate428.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2678809437044401 / 4000000000000) 3 (IntervalRat.scale (599 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-29929987305 / 1000000000000) (-29929987241 / 1000000000000), orderedInterval (-7380132747 / 1000000000000) (-7380132683 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1546611349585129 / 4000000000000) 3 (IntervalRat.scale (599 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-34618675164 / 1000000000000) (-34618675163 / 1000000000000), orderedInterval (-21122094677 / 1000000000000) (-21122094676 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2744488980275261 / 4000000000000) 3 (IntervalRat.scale (599 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (27165070094 / 1000000000000) (27165156449 / 1000000000000), orderedInterval (-13800558220 / 1000000000000) (-13800471865 / 1000000000000)))) (orderedInterval (12434936240 / 1000000000000) (12435085331 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2564257611120209 / 4000000000000) 3 (IntervalRat.scale (599 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25899891234 / 1000000000000) (25899891235 / 1000000000000), orderedInterval (17931465642 / 1000000000000) (17931465643 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1829975227518497 / 4000000000000) 3 (IntervalRat.scale (599 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14306249164 / 1000000000000) (-14306249007 / 1000000000000), orderedInterval (34466604703 / 1000000000000) (34466604860 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2074996867467063 / 4000000000000) 3 (IntervalRat.scale (599 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-32277099652 / 1000000000000) (-32277099650 / 1000000000000), orderedInterval (-13585391694 / 1000000000000) (-13585391692 / 1000000000000)))) (orderedInterval (-8815387153 / 1000000000000) (-8815386937 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1729916058795847 / 4000000000000) 3 (IntervalRat.scale (599 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-10442886374 / 1000000000000) (-10442886339 / 1000000000000), orderedInterval (36930518743 / 1000000000000) (36930518778 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1528433301036787 / 4000000000000) 3 (IntervalRat.scale (599 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-15174445420 / 1000000000000) (-15174445198 / 1000000000000), orderedInterval (37911922431 / 1000000000000) (37911922653 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (442999544189913 / 800000000000) 3 (IntervalRat.scale (599 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (33874454103 / 1000000000000) (33874455343 / 1000000000000), orderedInterval (-1505033089 / 1000000000000) (-1505031849 / 1000000000000)))) (orderedInterval (3478734080 / 1000000000000) (3478734405 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate428_chunkChecks3_2 :
    compactCertificate428.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1225360053018011 / 4000000000000) 3 (IntervalRat.scale (599 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-31109548973 / 1000000000000) (-31109527831 / 1000000000000), orderedInterval (33372596100 / 1000000000000) (33372617242 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1038751287434371 / 4000000000000) 3 (IntervalRat.scale (599 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (13656929186 / 1000000000000) (13656929316 / 1000000000000), orderedInterval (-47618029216 / 1000000000000) (-47618029086 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (650002324907713 / 4000000000000) 3 (IntervalRat.scale (599 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-4852672181 / 1000000000000) (-4852672168 / 1000000000000), orderedInterval (62417783746 / 1000000000000) (62417783760 / 1000000000000)))) (orderedInterval (3643782141 / 1000000000000) (3643785840 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (349573412145471 / 4000000000000) 3 (IntervalRat.scale (599 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (18019337638 / 1000000000000) (18019337639 / 1000000000000), orderedInterval (83323195718 / 1000000000000) (83323195719 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (949159815689413 / 4000000000000) 3 (IntervalRat.scale (599 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-32818983400 / 1000000000000) (-32818967503 / 1000000000000), orderedInterval (40141493017 / 1000000000000) (40141508914 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1295996582155301 / 4000000000000) 3 (IntervalRat.scale (599 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-41316292075 / 1000000000000) (-41316292074 / 1000000000000), orderedInterval (-15993740269 / 1000000000000) (-15993740268 / 1000000000000)))) (orderedInterval (-1046833800 / 1000000000000) (-1046833586 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (547997675092287 / 4000000000000) 3 (IntervalRat.scale (599 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-29415470692 / 1000000000000) (-29415468465 / 1000000000000), orderedInterval (61602304069 / 1000000000000) (61602306296 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2227580125328927 / 4000000000000) 3 (IntervalRat.scale (599 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-33772483762 / 1000000000000) (-33772482438 / 1000000000000), orderedInterval (1636028085 / 1000000000000) (1636029409 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1487920288604593 / 4000000000000) 3 (IntervalRat.scale (599 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (36571386374 / 1000000000000) (36571430391 / 1000000000000), orderedInterval (-19387387972 / 1000000000000) (-19387343954 / 1000000000000)))) (orderedInterval (-6152201829 / 1000000000000) (-6152185002 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate428_chunkChecks3 :
    compactCertificate428.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate428.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate428_chunkChecks3_0
    compactCertificate428_chunkChecks3_1 compactCertificate428_chunkChecks3_2

theorem compactCertificate428_chunkChecks4_0 :
    compactCertificate428.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (599 / 2) 4 (IntervalRat.scale (599 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-44520377643 / 1000000000000) (-44520374205 / 1000000000000), orderedInterval (12055230219 / 1000000000000) (12055233656 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (882441377792699 / 4000000000000) 4 (IntervalRat.scale (599 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (53515166623 / 1000000000000) (53515166645 / 1000000000000), orderedInterval (4552045136 / 1000000000000) (4552045158 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (285363410675867 / 800000000000) 4 (IntervalRat.scale (599 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-25642367771 / 1000000000000) (-25642361570 / 1000000000000), orderedInterval (33609690512 / 1000000000000) (33609696713 / 1000000000000)))) (orderedInterval (-20472227583 / 1000000000000) (-20472225437 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (257494193199793 / 4000000000000) 4 (IntervalRat.scale (599 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (72466282598 / 1000000000000) (72466392416 / 1000000000000), orderedInterval (-68666275178 / 1000000000000) (-68666165360 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (691665622489021 / 4000000000000) 4 (IntervalRat.scale (599 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-48033871055 / 1000000000000) (-48033871054 / 1000000000000), orderedInterval (-36934081879 / 1000000000000) (-36934081878 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1878006713182857 / 4000000000000) 4 (IntervalRat.scale (599 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29997234925 / 1000000000000) (-29997173320 / 1000000000000), orderedInterval (21388769147 / 1000000000000) (21388830752 / 1000000000000)))) (orderedInterval (12640488227 / 1000000000000) (12640514921 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1383331244978641 / 4000000000000) 4 (IntervalRat.scale (599 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (37058911168 / 1000000000000) (37058911169 / 1000000000000), orderedInterval (21567410515 / 1000000000000) (21567410516 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2370361666396693 / 4000000000000) 4 (IntervalRat.scale (599 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (12321900630 / 1000000000000) (12321900683 / 1000000000000), orderedInterval (-30382601869 / 1000000000000) (-30382601815 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1745997675092287 / 4000000000000) 4 (IntervalRat.scale (599 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-21662851092 / 1000000000000) (-21662851091 / 1000000000000), orderedInterval (-31426540354 / 1000000000000) (-31426540353 / 1000000000000)))) (orderedInterval (-8154054294 / 1000000000000) (-8154054094 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate428_chunkChecks4_1 :
    compactCertificate428.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2678809437044401 / 4000000000000) 4 (IntervalRat.scale (599 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-29929987305 / 1000000000000) (-29929987241 / 1000000000000), orderedInterval (-7380132747 / 1000000000000) (-7380132683 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1546611349585129 / 4000000000000) 4 (IntervalRat.scale (599 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-34618675164 / 1000000000000) (-34618675163 / 1000000000000), orderedInterval (-21122094677 / 1000000000000) (-21122094676 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2744488980275261 / 4000000000000) 4 (IntervalRat.scale (599 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (27165070094 / 1000000000000) (27165156449 / 1000000000000), orderedInterval (-13800558220 / 1000000000000) (-13800471865 / 1000000000000)))) (orderedInterval (232110466299 / 1000000000000) (232110808254 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2564257611120209 / 4000000000000) 4 (IntervalRat.scale (599 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25899891234 / 1000000000000) (25899891235 / 1000000000000), orderedInterval (17931465642 / 1000000000000) (17931465643 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1829975227518497 / 4000000000000) 4 (IntervalRat.scale (599 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14306249164 / 1000000000000) (-14306249007 / 1000000000000), orderedInterval (34466604703 / 1000000000000) (34466604860 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2074996867467063 / 4000000000000) 4 (IntervalRat.scale (599 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-32277099652 / 1000000000000) (-32277099650 / 1000000000000), orderedInterval (-13585391694 / 1000000000000) (-13585391692 / 1000000000000)))) (orderedInterval (-15650987350 / 1000000000000) (-15650986986 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1729916058795847 / 4000000000000) 4 (IntervalRat.scale (599 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-10442886374 / 1000000000000) (-10442886339 / 1000000000000), orderedInterval (36930518743 / 1000000000000) (36930518778 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1528433301036787 / 4000000000000) 4 (IntervalRat.scale (599 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-15174445420 / 1000000000000) (-15174445198 / 1000000000000), orderedInterval (37911922431 / 1000000000000) (37911922653 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (442999544189913 / 800000000000) 4 (IntervalRat.scale (599 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (33874454103 / 1000000000000) (33874455343 / 1000000000000), orderedInterval (-1505033089 / 1000000000000) (-1505031849 / 1000000000000)))) (orderedInterval (11888666571 / 1000000000000) (11888667130 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate428_chunkChecks4_2 :
    compactCertificate428.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1225360053018011 / 4000000000000) 4 (IntervalRat.scale (599 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-31109548973 / 1000000000000) (-31109527831 / 1000000000000), orderedInterval (33372596100 / 1000000000000) (33372617242 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1038751287434371 / 4000000000000) 4 (IntervalRat.scale (599 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (13656929186 / 1000000000000) (13656929316 / 1000000000000), orderedInterval (-47618029216 / 1000000000000) (-47618029086 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (650002324907713 / 4000000000000) 4 (IntervalRat.scale (599 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-4852672181 / 1000000000000) (-4852672168 / 1000000000000), orderedInterval (62417783746 / 1000000000000) (62417783760 / 1000000000000)))) (orderedInterval (4969406070 / 1000000000000) (4969409862 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (349573412145471 / 4000000000000) 4 (IntervalRat.scale (599 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (18019337638 / 1000000000000) (18019337639 / 1000000000000), orderedInterval (83323195718 / 1000000000000) (83323195719 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (949159815689413 / 4000000000000) 4 (IntervalRat.scale (599 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-32818983400 / 1000000000000) (-32818967503 / 1000000000000), orderedInterval (40141493017 / 1000000000000) (40141508914 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1295996582155301 / 4000000000000) 4 (IntervalRat.scale (599 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-41316292075 / 1000000000000) (-41316292074 / 1000000000000), orderedInterval (-15993740269 / 1000000000000) (-15993740268 / 1000000000000)))) (orderedInterval (4634603422 / 1000000000000) (4634603600 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (547997675092287 / 4000000000000) 4 (IntervalRat.scale (599 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-29415470692 / 1000000000000) (-29415468465 / 1000000000000), orderedInterval (61602304069 / 1000000000000) (61602306296 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2227580125328927 / 4000000000000) 4 (IntervalRat.scale (599 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-33772483762 / 1000000000000) (-33772482438 / 1000000000000), orderedInterval (1636028085 / 1000000000000) (1636029409 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1487920288604593 / 4000000000000) 4 (IntervalRat.scale (599 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (36571386374 / 1000000000000) (36571430391 / 1000000000000), orderedInterval (-19387387972 / 1000000000000) (-19387343954 / 1000000000000)))) (orderedInterval (16568211771 / 1000000000000) (16568233248 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate428_chunkChecks4 :
    compactCertificate428.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate428.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate428_chunkChecks4_0
    compactCertificate428_chunkChecks4_1 compactCertificate428_chunkChecks4_2

theorem compactCertificate428_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate428.chunkCheck r b = true :=
  compactCertificate428.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate428_chunkChecks0
    · exact compactCertificate428_chunkChecks1
    · exact compactCertificate428_chunkChecks2
    · exact compactCertificate428_chunkChecks3
    · exact compactCertificate428_chunkChecks4)

theorem compactCertificate428_coefficient0 :
    compactCertificate428.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate428_coefficient1 :
    compactCertificate428.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate428_coefficient2 :
    compactCertificate428.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate428_coefficient3 :
    compactCertificate428.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate428_coefficient4 :
    compactCertificate428.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate428_coefficients : ∀ r : Fin 5,
    compactCertificate428.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate428_coefficient0
  · exact compactCertificate428_coefficient1
  · exact compactCertificate428_coefficient2
  · exact compactCertificate428_coefficient3
  · exact compactCertificate428_coefficient4

theorem compactCertificate428_lower : (1 : ℚ) ≤ compactCertificate428.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate428, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate428_proves {t : ℝ} (ht : t ∈ compactCertificate428.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate428.proves compactCertificate428_states compactCertificate428_chunks
    compactCertificate428_coefficients compactCertificate428_lower ht

end Erdos232
