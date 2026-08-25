/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate352 : CompactCertificate where
  left := 223
  right := 224
  center := 447 / 2
  grid := fun i =>
    match i.val with
    | 0 => 71
    | 1 => 52
    | 2 => 85
    | 3 => 15
    | 4 => 41
    | 5 => 112
    | 6 => 82
    | 7 => 141
    | 8 => 104
    | 9 => 159
    | 10 => 92
    | 11 => 163
    | 12 => 152
    | 13 => 109
    | 14 => 123
    | 15 => 103
    | 16 => 91
    | 17 => 132
    | 18 => 73
    | 19 => 62
    | 20 => 39
    | 21 => 21
    | 22 => 56
    | 23 => 77
    | 24 => 33
    | 25 => 132
    | _ => 88
  point := fun i =>
    match i.val with
    | 0 => 447 / 2
    | 1 => 658516353711747 / 4000000000000
    | 2 => 212950658718051 / 800000000000
    | 3 => 192153429649929 / 4000000000000
    | 4 => 516151140655413 / 4000000000000
    | 5 => 1401450752575521 / 4000000000000
    | 6 => 1032302281311273 / 4000000000000
    | 7 => 1768867554055629 / 4000000000000
    | 8 => 1302939834334311 / 4000000000000
    | 9 => 1999044771884553 / 4000000000000
    | 10 => 1154149037169537 / 4000000000000
    | 11 => 2048057719838133 / 4000000000000
    | 12 => 1913561188932777 / 4000000000000
    | 13 => 1365607557096441 / 4000000000000
    | 14 => 1548453421966239 / 4000000000000
    | 15 => 1290939028850991 / 4000000000000
    | 16 => 1140583782242811 / 4000000000000
    | 17 => 330585636482289 / 800000000000
    | 18 => 914417268278883 / 4000000000000
    | 19 => 775161645213963 / 4000000000000
    | 20 => 485060165665689 / 4000000000000
    | 21 => 260866970332263 / 4000000000000
    | 22 => 708304570305789 / 4000000000000
    | 23 => 967129335932253 / 4000000000000
    | 24 => 408939834334311 / 4000000000000
    | 25 => 1662317722908231 / 4000000000000
    | _ => 1110351200344329 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-50332364920 / 1000000000000) (-50332364918 / 1000000000000), orderedInterval (-17637276404 / 1000000000000) (-17637276403 / 1000000000000))
    | 1 => (orderedInterval (55154542657 / 1000000000000) (55154558408 / 1000000000000), orderedInterval (-28889630113 / 1000000000000) (-28889614363 / 1000000000000))
    | 2 => (orderedInterval (3036143469 / 1000000000000) (3036143474 / 1000000000000), orderedInterval (-48815540235 / 1000000000000) (-48815540231 / 1000000000000))
    | 3 => (orderedInterval (-114196252412 / 1000000000000) (-114196252271 / 1000000000000), orderedInterval (15708909542 / 1000000000000) (15708909683 / 1000000000000))
    | 4 => (orderedInterval (-59737783987 / 1000000000000) (-59737783986 / 1000000000000), orderedInterval (-36714064094 / 1000000000000) (-36714064093 / 1000000000000))
    | 5 => (orderedInterval (-27806408079 / 1000000000000) (-27806396525 / 1000000000000), orderedInterval (32348111586 / 1000000000000) (32348123141 / 1000000000000))
    | 6 => (orderedInterval (47131255060 / 1000000000000) (47131255061 / 1000000000000), orderedInterval (15575117824 / 1000000000000) (15575117826 / 1000000000000))
    | 7 => (orderedInterval (-1420217810 / 1000000000000) (-1420217808 / 1000000000000), orderedInterval (-37914007252 / 1000000000000) (-37914007251 / 1000000000000))
    | 8 => (orderedInterval (-9028130390 / 1000000000000) (-9028130362 / 1000000000000), orderedInterval (43290934149 / 1000000000000) (43290934176 / 1000000000000))
    | 9 => (orderedInterval (-30654835996 / 1000000000000) (-30654835995 / 1000000000000), orderedInterval (-18248517602 / 1000000000000) (-18248517601 / 1000000000000))
    | 10 => (orderedInterval (13688085365 / 1000000000000) (13688085366 / 1000000000000), orderedInterval (44909658119 / 1000000000000) (44909658120 / 1000000000000))
    | 11 => (orderedInterval (-23250297894 / 1000000000000) (-23250297893 / 1000000000000), orderedInterval (-26487419317 / 1000000000000) (-26487419316 / 1000000000000))
    | 12 => (orderedInterval (36355252096 / 1000000000000) (36355253349 / 1000000000000), orderedInterval (-3046123726 / 1000000000000) (-3046122473 / 1000000000000))
    | 13 => (orderedInterval (10544445369 / 1000000000000) (10544445414 / 1000000000000), orderedInterval (-41890720729 / 1000000000000) (-41890720684 / 1000000000000))
    | 14 => (orderedInterval (-40394941873 / 1000000000000) (-40394941798 / 1000000000000), orderedInterval (-3522452628 / 1000000000000) (-3522452553 / 1000000000000))
    | 15 => (orderedInterval (2852736605 / 1000000000000) (2852736608 / 1000000000000), orderedInterval (-44326458626 / 1000000000000) (-44326458623 / 1000000000000))
    | 16 => (orderedInterval (-2171522185 / 1000000000000) (-2171522183 / 1000000000000), orderedInterval (-47196808793 / 1000000000000) (-47196808791 / 1000000000000))
    | 17 => (orderedInterval (-24468802228 / 1000000000000) (-24468796508 / 1000000000000), orderedInterval (30719418783 / 1000000000000) (30719424504 / 1000000000000))
    | 18 => (orderedInterval (-2790546229 / 1000000000000) (-2790546227 / 1000000000000), orderedInterval (-52691432402 / 1000000000000) (-52691432400 / 1000000000000))
    | 19 => (orderedInterval (-11587891798 / 1000000000000) (-11587891727 / 1000000000000), orderedInterval (56162108554 / 1000000000000) (56162108625 / 1000000000000))
    | 20 => (orderedInterval (32988627296 / 1000000000000) (32988630551 / 1000000000000), orderedInterval (-64646463393 / 1000000000000) (-64646460139 / 1000000000000))
    | 21 => (orderedInterval (-2645389373 / 1000000000000) (-2645389367 / 1000000000000), orderedInterval (-98746559060 / 1000000000000) (-98746559055 / 1000000000000))
    | 22 => (orderedInterval (56098081414 / 1000000000000) (56098086469 / 1000000000000), orderedInterval (-21328416323 / 1000000000000) (-21328411268 / 1000000000000))
    | 23 => (orderedInterval (-31646220136 / 1000000000000) (-31646220135 / 1000000000000), orderedInterval (-40326964152 / 1000000000000) (-40326964151 / 1000000000000))
    | 24 => (orderedInterval (47970654468 / 1000000000000) (47970676639 / 1000000000000), orderedInterval (-62891305403 / 1000000000000) (-62891283232 / 1000000000000))
    | 25 => (orderedInterval (38929830040 / 1000000000000) (38929831142 / 1000000000000), orderedInterval (-4090587451 / 1000000000000) (-4090586349 / 1000000000000))
    | _ => (orderedInterval (45119175170 / 1000000000000) (45119182192 / 1000000000000), orderedInterval (-16132955437 / 1000000000000) (-16132948414 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-19257889780 / 1000000000000) (-19257889616 / 1000000000000)
      | 1 => orderedInterval (1034564309 / 1000000000000) (1034565160 / 1000000000000)
      | 2 => orderedInterval (-174386906 / 1000000000000) (-174386892 / 1000000000000)
      | 3 => orderedInterval (3156001835 / 1000000000000) (3156001925 / 1000000000000)
      | 4 => orderedInterval (545210119 / 1000000000000) (545210173 / 1000000000000)
      | 5 => orderedInterval (-469286540 / 1000000000000) (-469286372 / 1000000000000)
      | 6 => orderedInterval (2176015086 / 1000000000000) (2176015253 / 1000000000000)
      | 7 => orderedInterval (1201488415 / 1000000000000) (1201488557 / 1000000000000)
      | _ => orderedInterval (-11345330081 / 1000000000000) (-11345328477 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-10600765625 / 1000000000000) (-10600765499 / 1000000000000)
      | 1 => orderedInterval (-4415487532 / 1000000000000) (-4415486212 / 1000000000000)
      | 2 => orderedInterval (3838655191 / 1000000000000) (3838655214 / 1000000000000)
      | 3 => orderedInterval (2920249433 / 1000000000000) (2920249618 / 1000000000000)
      | 4 => orderedInterval (-5902413541 / 1000000000000) (-5902413441 / 1000000000000)
      | 5 => orderedInterval (4160988450 / 1000000000000) (4160988753 / 1000000000000)
      | 6 => orderedInterval (4719259813 / 1000000000000) (4719259927 / 1000000000000)
      | 7 => orderedInterval (4258847084 / 1000000000000) (4258847200 / 1000000000000)
      | _ => orderedInterval (4205232446 / 1000000000000) (4205234398 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (19465849375 / 1000000000000) (19465849477 / 1000000000000)
      | 1 => orderedInterval (-4168150073 / 1000000000000) (-4168148006 / 1000000000000)
      | 2 => orderedInterval (274794297 / 1000000000000) (274794338 / 1000000000000)
      | 3 => orderedInterval (-11592192714 / 1000000000000) (-11592192318 / 1000000000000)
      | 4 => orderedInterval (93511371 / 1000000000000) (93511558 / 1000000000000)
      | 5 => orderedInterval (1852087565 / 1000000000000) (1852088114 / 1000000000000)
      | 6 => orderedInterval (-1297166025 / 1000000000000) (-1297165940 / 1000000000000)
      | 7 => orderedInterval (-2062667379 / 1000000000000) (-2062667282 / 1000000000000)
      | _ => orderedInterval (23935849406 / 1000000000000) (23935851914 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (11850471742 / 1000000000000) (11850471826 / 1000000000000)
      | 1 => orderedInterval (9137058615 / 1000000000000) (9137061852 / 1000000000000)
      | 2 => orderedInterval (-12298300505 / 1000000000000) (-12298300432 / 1000000000000)
      | 3 => orderedInterval (1910546638 / 1000000000000) (1910547505 / 1000000000000)
      | 4 => orderedInterval (13486549841 / 1000000000000) (13486550202 / 1000000000000)
      | 5 => orderedInterval (-9047218758 / 1000000000000) (-9047217758 / 1000000000000)
      | 6 => orderedInterval (-6601259342 / 1000000000000) (-6601259273 / 1000000000000)
      | 7 => orderedInterval (-4189417813 / 1000000000000) (-4189417730 / 1000000000000)
      | _ => orderedInterval (-8010706535 / 1000000000000) (-8010703212 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-19545865412 / 1000000000000) (-19545865339 / 1000000000000)
      | 1 => orderedInterval (11615920621 / 1000000000000) (11615925707 / 1000000000000)
      | 2 => orderedInterval (-203014375 / 1000000000000) (-203014240 / 1000000000000)
      | 3 => orderedInterval (47938905169 / 1000000000000) (47938907093 / 1000000000000)
      | 4 => orderedInterval (-6628631987 / 1000000000000) (-6628631273 / 1000000000000)
      | 5 => orderedInterval (-6767784016 / 1000000000000) (-6767782183 / 1000000000000)
      | 6 => orderedInterval (1011196751 / 1000000000000) (1011196811 / 1000000000000)
      | 7 => orderedInterval (2858012775 / 1000000000000) (2858012847 / 1000000000000)
      | _ => orderedInterval (-57940319522 / 1000000000000) (-57940314963 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-23133613543 / 1000000000000) (-23133610289 / 1000000000000)
    | 1 => orderedInterval (3184565719 / 1000000000000) (3184569958 / 1000000000000)
    | 2 => orderedInterval (26501915823 / 1000000000000) (26501921855 / 1000000000000)
    | 3 => orderedInterval (-3762276117 / 1000000000000) (-3762267020 / 1000000000000)
    | _ => orderedInterval (-27661579996 / 1000000000000) (-27661565540 / 1000000000000)

theorem compactCertificate352_stateChecks0 :
    compactCertificate352.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (447 / 2)) (orderedInterval (-50332364920 / 1000000000000) (-50332364918 / 1000000000000), orderedInterval (-17637276404 / 1000000000000) (-17637276403 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (658516353711747 / 4000000000000)) (orderedInterval (55154542657 / 1000000000000) (55154558408 / 1000000000000), orderedInterval (-28889630113 / 1000000000000) (-28889614363 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (212950658718051 / 800000000000)) (orderedInterval (3036143469 / 1000000000000) (3036143474 / 1000000000000), orderedInterval (-48815540235 / 1000000000000) (-48815540231 / 1000000000000))) = true
  rfl'

theorem compactCertificate352_stateChecks1 :
    compactCertificate352.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 15 12 (192153429649929 / 4000000000000)) (orderedInterval (-114196252412 / 1000000000000) (-114196252271 / 1000000000000), orderedInterval (15708909542 / 1000000000000) (15708909683 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (516151140655413 / 4000000000000)) (orderedInterval (-59737783987 / 1000000000000) (-59737783986 / 1000000000000), orderedInterval (-36714064094 / 1000000000000) (-36714064093 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 112 12 (1401450752575521 / 4000000000000)) (orderedInterval (-27806408079 / 1000000000000) (-27806396525 / 1000000000000), orderedInterval (32348111586 / 1000000000000) (32348123141 / 1000000000000))) = true
  rfl'

theorem compactCertificate352_stateChecks2 :
    compactCertificate352.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (1032302281311273 / 4000000000000)) (orderedInterval (47131255060 / 1000000000000) (47131255061 / 1000000000000), orderedInterval (15575117824 / 1000000000000) (15575117826 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 141 12 (1768867554055629 / 4000000000000)) (orderedInterval (-1420217810 / 1000000000000) (-1420217808 / 1000000000000), orderedInterval (-37914007252 / 1000000000000) (-37914007251 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 104 12 (1302939834334311 / 4000000000000)) (orderedInterval (-9028130390 / 1000000000000) (-9028130362 / 1000000000000), orderedInterval (43290934149 / 1000000000000) (43290934176 / 1000000000000))) = true
  rfl'

theorem compactCertificate352_stateChecks3 :
    compactCertificate352.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 159 12 (1999044771884553 / 4000000000000)) (orderedInterval (-30654835996 / 1000000000000) (-30654835995 / 1000000000000), orderedInterval (-18248517602 / 1000000000000) (-18248517601 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 92 12 (1154149037169537 / 4000000000000)) (orderedInterval (13688085365 / 1000000000000) (13688085366 / 1000000000000), orderedInterval (44909658119 / 1000000000000) (44909658120 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 163 12 (2048057719838133 / 4000000000000)) (orderedInterval (-23250297894 / 1000000000000) (-23250297893 / 1000000000000), orderedInterval (-26487419317 / 1000000000000) (-26487419316 / 1000000000000))) = true
  rfl'

theorem compactCertificate352_stateChecks4 :
    compactCertificate352.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 152 12 (1913561188932777 / 4000000000000)) (orderedInterval (36355252096 / 1000000000000) (36355253349 / 1000000000000), orderedInterval (-3046123726 / 1000000000000) (-3046122473 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 109 12 (1365607557096441 / 4000000000000)) (orderedInterval (10544445369 / 1000000000000) (10544445414 / 1000000000000), orderedInterval (-41890720729 / 1000000000000) (-41890720684 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 123 12 (1548453421966239 / 4000000000000)) (orderedInterval (-40394941873 / 1000000000000) (-40394941798 / 1000000000000), orderedInterval (-3522452628 / 1000000000000) (-3522452553 / 1000000000000))) = true
  rfl'

theorem compactCertificate352_stateChecks5 :
    compactCertificate352.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 103 12 (1290939028850991 / 4000000000000)) (orderedInterval (2852736605 / 1000000000000) (2852736608 / 1000000000000), orderedInterval (-44326458626 / 1000000000000) (-44326458623 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 91 12 (1140583782242811 / 4000000000000)) (orderedInterval (-2171522185 / 1000000000000) (-2171522183 / 1000000000000), orderedInterval (-47196808793 / 1000000000000) (-47196808791 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 132 12 (330585636482289 / 800000000000)) (orderedInterval (-24468802228 / 1000000000000) (-24468796508 / 1000000000000), orderedInterval (30719418783 / 1000000000000) (30719424504 / 1000000000000))) = true
  rfl'

theorem compactCertificate352_stateChecks6 :
    compactCertificate352.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (914417268278883 / 4000000000000)) (orderedInterval (-2790546229 / 1000000000000) (-2790546227 / 1000000000000), orderedInterval (-52691432402 / 1000000000000) (-52691432400 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (775161645213963 / 4000000000000)) (orderedInterval (-11587891798 / 1000000000000) (-11587891727 / 1000000000000), orderedInterval (56162108554 / 1000000000000) (56162108625 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (485060165665689 / 4000000000000)) (orderedInterval (32988627296 / 1000000000000) (32988630551 / 1000000000000), orderedInterval (-64646463393 / 1000000000000) (-64646460139 / 1000000000000))) = true
  rfl'

theorem compactCertificate352_stateChecks7 :
    compactCertificate352.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 21 12 (260866970332263 / 4000000000000)) (orderedInterval (-2645389373 / 1000000000000) (-2645389367 / 1000000000000), orderedInterval (-98746559060 / 1000000000000) (-98746559055 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (708304570305789 / 4000000000000)) (orderedInterval (56098081414 / 1000000000000) (56098086469 / 1000000000000), orderedInterval (-21328416323 / 1000000000000) (-21328411268 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (967129335932253 / 4000000000000)) (orderedInterval (-31646220136 / 1000000000000) (-31646220135 / 1000000000000), orderedInterval (-40326964152 / 1000000000000) (-40326964151 / 1000000000000))) = true
  rfl'

theorem compactCertificate352_stateChecks8 :
    compactCertificate352.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (408939834334311 / 4000000000000)) (orderedInterval (47970654468 / 1000000000000) (47970676639 / 1000000000000), orderedInterval (-62891305403 / 1000000000000) (-62891283232 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 132 12 (1662317722908231 / 4000000000000)) (orderedInterval (38929830040 / 1000000000000) (38929831142 / 1000000000000), orderedInterval (-4090587451 / 1000000000000) (-4090586349 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 88 12 (1110351200344329 / 4000000000000)) (orderedInterval (45119175170 / 1000000000000) (45119182192 / 1000000000000), orderedInterval (-16132955437 / 1000000000000) (-16132948414 / 1000000000000))) = true
  rfl'

theorem compactCertificate352_states : ∀ j,
    BesselStateValid (compactCertificate352.point j) (compactCertificate352.state j) :=
  compactCertificate352.statesValid_of_checks3 compactCertificate352_stateChecks0
    compactCertificate352_stateChecks1 compactCertificate352_stateChecks2
    compactCertificate352_stateChecks3 compactCertificate352_stateChecks4
    compactCertificate352_stateChecks5 compactCertificate352_stateChecks6
    compactCertificate352_stateChecks7 compactCertificate352_stateChecks8

theorem compactCertificate352_chunkChecks0_0 :
    compactCertificate352.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (447 / 2) 0 (IntervalRat.scale (447 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-50332364920 / 1000000000000) (-50332364918 / 1000000000000), orderedInterval (-17637276404 / 1000000000000) (-17637276403 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (658516353711747 / 4000000000000) 0 (IntervalRat.scale (447 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (55154542657 / 1000000000000) (55154558408 / 1000000000000), orderedInterval (-28889630113 / 1000000000000) (-28889614363 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (212950658718051 / 800000000000) 0 (IntervalRat.scale (447 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (3036143469 / 1000000000000) (3036143474 / 1000000000000), orderedInterval (-48815540235 / 1000000000000) (-48815540231 / 1000000000000)))) (orderedInterval (-19257889780 / 1000000000000) (-19257889616 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (192153429649929 / 4000000000000) 0 (IntervalRat.scale (447 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-114196252412 / 1000000000000) (-114196252271 / 1000000000000), orderedInterval (15708909542 / 1000000000000) (15708909683 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (516151140655413 / 4000000000000) 0 (IntervalRat.scale (447 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-59737783987 / 1000000000000) (-59737783986 / 1000000000000), orderedInterval (-36714064094 / 1000000000000) (-36714064093 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1401450752575521 / 4000000000000) 0 (IntervalRat.scale (447 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-27806408079 / 1000000000000) (-27806396525 / 1000000000000), orderedInterval (32348111586 / 1000000000000) (32348123141 / 1000000000000)))) (orderedInterval (1034564309 / 1000000000000) (1034565160 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1032302281311273 / 4000000000000) 0 (IntervalRat.scale (447 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (47131255060 / 1000000000000) (47131255061 / 1000000000000), orderedInterval (15575117824 / 1000000000000) (15575117826 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1768867554055629 / 4000000000000) 0 (IntervalRat.scale (447 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-1420217810 / 1000000000000) (-1420217808 / 1000000000000), orderedInterval (-37914007252 / 1000000000000) (-37914007251 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1302939834334311 / 4000000000000) 0 (IntervalRat.scale (447 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-9028130390 / 1000000000000) (-9028130362 / 1000000000000), orderedInterval (43290934149 / 1000000000000) (43290934176 / 1000000000000)))) (orderedInterval (-174386906 / 1000000000000) (-174386892 / 1000000000000))) = true
  rfl'

theorem compactCertificate352_chunkChecks0_1 :
    compactCertificate352.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1999044771884553 / 4000000000000) 0 (IntervalRat.scale (447 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-30654835996 / 1000000000000) (-30654835995 / 1000000000000), orderedInterval (-18248517602 / 1000000000000) (-18248517601 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1154149037169537 / 4000000000000) 0 (IntervalRat.scale (447 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (13688085365 / 1000000000000) (13688085366 / 1000000000000), orderedInterval (44909658119 / 1000000000000) (44909658120 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2048057719838133 / 4000000000000) 0 (IntervalRat.scale (447 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-23250297894 / 1000000000000) (-23250297893 / 1000000000000), orderedInterval (-26487419317 / 1000000000000) (-26487419316 / 1000000000000)))) (orderedInterval (3156001835 / 1000000000000) (3156001925 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1913561188932777 / 4000000000000) 0 (IntervalRat.scale (447 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (36355252096 / 1000000000000) (36355253349 / 1000000000000), orderedInterval (-3046123726 / 1000000000000) (-3046122473 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1365607557096441 / 4000000000000) 0 (IntervalRat.scale (447 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (10544445369 / 1000000000000) (10544445414 / 1000000000000), orderedInterval (-41890720729 / 1000000000000) (-41890720684 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1548453421966239 / 4000000000000) 0 (IntervalRat.scale (447 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-40394941873 / 1000000000000) (-40394941798 / 1000000000000), orderedInterval (-3522452628 / 1000000000000) (-3522452553 / 1000000000000)))) (orderedInterval (545210119 / 1000000000000) (545210173 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1290939028850991 / 4000000000000) 0 (IntervalRat.scale (447 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (2852736605 / 1000000000000) (2852736608 / 1000000000000), orderedInterval (-44326458626 / 1000000000000) (-44326458623 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1140583782242811 / 4000000000000) 0 (IntervalRat.scale (447 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-2171522185 / 1000000000000) (-2171522183 / 1000000000000), orderedInterval (-47196808793 / 1000000000000) (-47196808791 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (330585636482289 / 800000000000) 0 (IntervalRat.scale (447 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-24468802228 / 1000000000000) (-24468796508 / 1000000000000), orderedInterval (30719418783 / 1000000000000) (30719424504 / 1000000000000)))) (orderedInterval (-469286540 / 1000000000000) (-469286372 / 1000000000000))) = true
  rfl'

theorem compactCertificate352_chunkChecks0_2 :
    compactCertificate352.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (914417268278883 / 4000000000000) 0 (IntervalRat.scale (447 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-2790546229 / 1000000000000) (-2790546227 / 1000000000000), orderedInterval (-52691432402 / 1000000000000) (-52691432400 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (775161645213963 / 4000000000000) 0 (IntervalRat.scale (447 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-11587891798 / 1000000000000) (-11587891727 / 1000000000000), orderedInterval (56162108554 / 1000000000000) (56162108625 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (485060165665689 / 4000000000000) 0 (IntervalRat.scale (447 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (32988627296 / 1000000000000) (32988630551 / 1000000000000), orderedInterval (-64646463393 / 1000000000000) (-64646460139 / 1000000000000)))) (orderedInterval (2176015086 / 1000000000000) (2176015253 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (260866970332263 / 4000000000000) 0 (IntervalRat.scale (447 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-2645389373 / 1000000000000) (-2645389367 / 1000000000000), orderedInterval (-98746559060 / 1000000000000) (-98746559055 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (708304570305789 / 4000000000000) 0 (IntervalRat.scale (447 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (56098081414 / 1000000000000) (56098086469 / 1000000000000), orderedInterval (-21328416323 / 1000000000000) (-21328411268 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (967129335932253 / 4000000000000) 0 (IntervalRat.scale (447 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-31646220136 / 1000000000000) (-31646220135 / 1000000000000), orderedInterval (-40326964152 / 1000000000000) (-40326964151 / 1000000000000)))) (orderedInterval (1201488415 / 1000000000000) (1201488557 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (408939834334311 / 4000000000000) 0 (IntervalRat.scale (447 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (47970654468 / 1000000000000) (47970676639 / 1000000000000), orderedInterval (-62891305403 / 1000000000000) (-62891283232 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1662317722908231 / 4000000000000) 0 (IntervalRat.scale (447 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (38929830040 / 1000000000000) (38929831142 / 1000000000000), orderedInterval (-4090587451 / 1000000000000) (-4090586349 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1110351200344329 / 4000000000000) 0 (IntervalRat.scale (447 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (45119175170 / 1000000000000) (45119182192 / 1000000000000), orderedInterval (-16132955437 / 1000000000000) (-16132948414 / 1000000000000)))) (orderedInterval (-11345330081 / 1000000000000) (-11345328477 / 1000000000000))) = true
  rfl'

theorem compactCertificate352_chunkChecks0 :
    compactCertificate352.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate352.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate352_chunkChecks0_0
    compactCertificate352_chunkChecks0_1 compactCertificate352_chunkChecks0_2

theorem compactCertificate352_chunkChecks1_0 :
    compactCertificate352.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (447 / 2) 1 (IntervalRat.scale (447 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-50332364920 / 1000000000000) (-50332364918 / 1000000000000), orderedInterval (-17637276404 / 1000000000000) (-17637276403 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (658516353711747 / 4000000000000) 1 (IntervalRat.scale (447 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (55154542657 / 1000000000000) (55154558408 / 1000000000000), orderedInterval (-28889630113 / 1000000000000) (-28889614363 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (212950658718051 / 800000000000) 1 (IntervalRat.scale (447 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (3036143469 / 1000000000000) (3036143474 / 1000000000000), orderedInterval (-48815540235 / 1000000000000) (-48815540231 / 1000000000000)))) (orderedInterval (-10600765625 / 1000000000000) (-10600765499 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (192153429649929 / 4000000000000) 1 (IntervalRat.scale (447 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-114196252412 / 1000000000000) (-114196252271 / 1000000000000), orderedInterval (15708909542 / 1000000000000) (15708909683 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (516151140655413 / 4000000000000) 1 (IntervalRat.scale (447 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-59737783987 / 1000000000000) (-59737783986 / 1000000000000), orderedInterval (-36714064094 / 1000000000000) (-36714064093 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1401450752575521 / 4000000000000) 1 (IntervalRat.scale (447 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-27806408079 / 1000000000000) (-27806396525 / 1000000000000), orderedInterval (32348111586 / 1000000000000) (32348123141 / 1000000000000)))) (orderedInterval (-4415487532 / 1000000000000) (-4415486212 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1032302281311273 / 4000000000000) 1 (IntervalRat.scale (447 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (47131255060 / 1000000000000) (47131255061 / 1000000000000), orderedInterval (15575117824 / 1000000000000) (15575117826 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1768867554055629 / 4000000000000) 1 (IntervalRat.scale (447 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-1420217810 / 1000000000000) (-1420217808 / 1000000000000), orderedInterval (-37914007252 / 1000000000000) (-37914007251 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1302939834334311 / 4000000000000) 1 (IntervalRat.scale (447 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-9028130390 / 1000000000000) (-9028130362 / 1000000000000), orderedInterval (43290934149 / 1000000000000) (43290934176 / 1000000000000)))) (orderedInterval (3838655191 / 1000000000000) (3838655214 / 1000000000000))) = true
  rfl'

theorem compactCertificate352_chunkChecks1_1 :
    compactCertificate352.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1999044771884553 / 4000000000000) 1 (IntervalRat.scale (447 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-30654835996 / 1000000000000) (-30654835995 / 1000000000000), orderedInterval (-18248517602 / 1000000000000) (-18248517601 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1154149037169537 / 4000000000000) 1 (IntervalRat.scale (447 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (13688085365 / 1000000000000) (13688085366 / 1000000000000), orderedInterval (44909658119 / 1000000000000) (44909658120 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2048057719838133 / 4000000000000) 1 (IntervalRat.scale (447 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-23250297894 / 1000000000000) (-23250297893 / 1000000000000), orderedInterval (-26487419317 / 1000000000000) (-26487419316 / 1000000000000)))) (orderedInterval (2920249433 / 1000000000000) (2920249618 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1913561188932777 / 4000000000000) 1 (IntervalRat.scale (447 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (36355252096 / 1000000000000) (36355253349 / 1000000000000), orderedInterval (-3046123726 / 1000000000000) (-3046122473 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1365607557096441 / 4000000000000) 1 (IntervalRat.scale (447 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (10544445369 / 1000000000000) (10544445414 / 1000000000000), orderedInterval (-41890720729 / 1000000000000) (-41890720684 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1548453421966239 / 4000000000000) 1 (IntervalRat.scale (447 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-40394941873 / 1000000000000) (-40394941798 / 1000000000000), orderedInterval (-3522452628 / 1000000000000) (-3522452553 / 1000000000000)))) (orderedInterval (-5902413541 / 1000000000000) (-5902413441 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1290939028850991 / 4000000000000) 1 (IntervalRat.scale (447 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (2852736605 / 1000000000000) (2852736608 / 1000000000000), orderedInterval (-44326458626 / 1000000000000) (-44326458623 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1140583782242811 / 4000000000000) 1 (IntervalRat.scale (447 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-2171522185 / 1000000000000) (-2171522183 / 1000000000000), orderedInterval (-47196808793 / 1000000000000) (-47196808791 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (330585636482289 / 800000000000) 1 (IntervalRat.scale (447 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-24468802228 / 1000000000000) (-24468796508 / 1000000000000), orderedInterval (30719418783 / 1000000000000) (30719424504 / 1000000000000)))) (orderedInterval (4160988450 / 1000000000000) (4160988753 / 1000000000000))) = true
  rfl'

theorem compactCertificate352_chunkChecks1_2 :
    compactCertificate352.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (914417268278883 / 4000000000000) 1 (IntervalRat.scale (447 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-2790546229 / 1000000000000) (-2790546227 / 1000000000000), orderedInterval (-52691432402 / 1000000000000) (-52691432400 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (775161645213963 / 4000000000000) 1 (IntervalRat.scale (447 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-11587891798 / 1000000000000) (-11587891727 / 1000000000000), orderedInterval (56162108554 / 1000000000000) (56162108625 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (485060165665689 / 4000000000000) 1 (IntervalRat.scale (447 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (32988627296 / 1000000000000) (32988630551 / 1000000000000), orderedInterval (-64646463393 / 1000000000000) (-64646460139 / 1000000000000)))) (orderedInterval (4719259813 / 1000000000000) (4719259927 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (260866970332263 / 4000000000000) 1 (IntervalRat.scale (447 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-2645389373 / 1000000000000) (-2645389367 / 1000000000000), orderedInterval (-98746559060 / 1000000000000) (-98746559055 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (708304570305789 / 4000000000000) 1 (IntervalRat.scale (447 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (56098081414 / 1000000000000) (56098086469 / 1000000000000), orderedInterval (-21328416323 / 1000000000000) (-21328411268 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (967129335932253 / 4000000000000) 1 (IntervalRat.scale (447 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-31646220136 / 1000000000000) (-31646220135 / 1000000000000), orderedInterval (-40326964152 / 1000000000000) (-40326964151 / 1000000000000)))) (orderedInterval (4258847084 / 1000000000000) (4258847200 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (408939834334311 / 4000000000000) 1 (IntervalRat.scale (447 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (47970654468 / 1000000000000) (47970676639 / 1000000000000), orderedInterval (-62891305403 / 1000000000000) (-62891283232 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1662317722908231 / 4000000000000) 1 (IntervalRat.scale (447 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (38929830040 / 1000000000000) (38929831142 / 1000000000000), orderedInterval (-4090587451 / 1000000000000) (-4090586349 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1110351200344329 / 4000000000000) 1 (IntervalRat.scale (447 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (45119175170 / 1000000000000) (45119182192 / 1000000000000), orderedInterval (-16132955437 / 1000000000000) (-16132948414 / 1000000000000)))) (orderedInterval (4205232446 / 1000000000000) (4205234398 / 1000000000000))) = true
  rfl'

theorem compactCertificate352_chunkChecks1 :
    compactCertificate352.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate352.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate352_chunkChecks1_0
    compactCertificate352_chunkChecks1_1 compactCertificate352_chunkChecks1_2

theorem compactCertificate352_chunkChecks2_0 :
    compactCertificate352.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (447 / 2) 2 (IntervalRat.scale (447 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-50332364920 / 1000000000000) (-50332364918 / 1000000000000), orderedInterval (-17637276404 / 1000000000000) (-17637276403 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (658516353711747 / 4000000000000) 2 (IntervalRat.scale (447 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (55154542657 / 1000000000000) (55154558408 / 1000000000000), orderedInterval (-28889630113 / 1000000000000) (-28889614363 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (212950658718051 / 800000000000) 2 (IntervalRat.scale (447 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (3036143469 / 1000000000000) (3036143474 / 1000000000000), orderedInterval (-48815540235 / 1000000000000) (-48815540231 / 1000000000000)))) (orderedInterval (19465849375 / 1000000000000) (19465849477 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (192153429649929 / 4000000000000) 2 (IntervalRat.scale (447 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-114196252412 / 1000000000000) (-114196252271 / 1000000000000), orderedInterval (15708909542 / 1000000000000) (15708909683 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (516151140655413 / 4000000000000) 2 (IntervalRat.scale (447 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-59737783987 / 1000000000000) (-59737783986 / 1000000000000), orderedInterval (-36714064094 / 1000000000000) (-36714064093 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1401450752575521 / 4000000000000) 2 (IntervalRat.scale (447 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-27806408079 / 1000000000000) (-27806396525 / 1000000000000), orderedInterval (32348111586 / 1000000000000) (32348123141 / 1000000000000)))) (orderedInterval (-4168150073 / 1000000000000) (-4168148006 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1032302281311273 / 4000000000000) 2 (IntervalRat.scale (447 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (47131255060 / 1000000000000) (47131255061 / 1000000000000), orderedInterval (15575117824 / 1000000000000) (15575117826 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1768867554055629 / 4000000000000) 2 (IntervalRat.scale (447 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-1420217810 / 1000000000000) (-1420217808 / 1000000000000), orderedInterval (-37914007252 / 1000000000000) (-37914007251 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1302939834334311 / 4000000000000) 2 (IntervalRat.scale (447 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-9028130390 / 1000000000000) (-9028130362 / 1000000000000), orderedInterval (43290934149 / 1000000000000) (43290934176 / 1000000000000)))) (orderedInterval (274794297 / 1000000000000) (274794338 / 1000000000000))) = true
  rfl'

theorem compactCertificate352_chunkChecks2_1 :
    compactCertificate352.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1999044771884553 / 4000000000000) 2 (IntervalRat.scale (447 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-30654835996 / 1000000000000) (-30654835995 / 1000000000000), orderedInterval (-18248517602 / 1000000000000) (-18248517601 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1154149037169537 / 4000000000000) 2 (IntervalRat.scale (447 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (13688085365 / 1000000000000) (13688085366 / 1000000000000), orderedInterval (44909658119 / 1000000000000) (44909658120 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2048057719838133 / 4000000000000) 2 (IntervalRat.scale (447 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-23250297894 / 1000000000000) (-23250297893 / 1000000000000), orderedInterval (-26487419317 / 1000000000000) (-26487419316 / 1000000000000)))) (orderedInterval (-11592192714 / 1000000000000) (-11592192318 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1913561188932777 / 4000000000000) 2 (IntervalRat.scale (447 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (36355252096 / 1000000000000) (36355253349 / 1000000000000), orderedInterval (-3046123726 / 1000000000000) (-3046122473 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1365607557096441 / 4000000000000) 2 (IntervalRat.scale (447 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (10544445369 / 1000000000000) (10544445414 / 1000000000000), orderedInterval (-41890720729 / 1000000000000) (-41890720684 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1548453421966239 / 4000000000000) 2 (IntervalRat.scale (447 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-40394941873 / 1000000000000) (-40394941798 / 1000000000000), orderedInterval (-3522452628 / 1000000000000) (-3522452553 / 1000000000000)))) (orderedInterval (93511371 / 1000000000000) (93511558 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1290939028850991 / 4000000000000) 2 (IntervalRat.scale (447 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (2852736605 / 1000000000000) (2852736608 / 1000000000000), orderedInterval (-44326458626 / 1000000000000) (-44326458623 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1140583782242811 / 4000000000000) 2 (IntervalRat.scale (447 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-2171522185 / 1000000000000) (-2171522183 / 1000000000000), orderedInterval (-47196808793 / 1000000000000) (-47196808791 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (330585636482289 / 800000000000) 2 (IntervalRat.scale (447 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-24468802228 / 1000000000000) (-24468796508 / 1000000000000), orderedInterval (30719418783 / 1000000000000) (30719424504 / 1000000000000)))) (orderedInterval (1852087565 / 1000000000000) (1852088114 / 1000000000000))) = true
  rfl'

theorem compactCertificate352_chunkChecks2_2 :
    compactCertificate352.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (914417268278883 / 4000000000000) 2 (IntervalRat.scale (447 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-2790546229 / 1000000000000) (-2790546227 / 1000000000000), orderedInterval (-52691432402 / 1000000000000) (-52691432400 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (775161645213963 / 4000000000000) 2 (IntervalRat.scale (447 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-11587891798 / 1000000000000) (-11587891727 / 1000000000000), orderedInterval (56162108554 / 1000000000000) (56162108625 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (485060165665689 / 4000000000000) 2 (IntervalRat.scale (447 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (32988627296 / 1000000000000) (32988630551 / 1000000000000), orderedInterval (-64646463393 / 1000000000000) (-64646460139 / 1000000000000)))) (orderedInterval (-1297166025 / 1000000000000) (-1297165940 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (260866970332263 / 4000000000000) 2 (IntervalRat.scale (447 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-2645389373 / 1000000000000) (-2645389367 / 1000000000000), orderedInterval (-98746559060 / 1000000000000) (-98746559055 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (708304570305789 / 4000000000000) 2 (IntervalRat.scale (447 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (56098081414 / 1000000000000) (56098086469 / 1000000000000), orderedInterval (-21328416323 / 1000000000000) (-21328411268 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (967129335932253 / 4000000000000) 2 (IntervalRat.scale (447 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-31646220136 / 1000000000000) (-31646220135 / 1000000000000), orderedInterval (-40326964152 / 1000000000000) (-40326964151 / 1000000000000)))) (orderedInterval (-2062667379 / 1000000000000) (-2062667282 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (408939834334311 / 4000000000000) 2 (IntervalRat.scale (447 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (47970654468 / 1000000000000) (47970676639 / 1000000000000), orderedInterval (-62891305403 / 1000000000000) (-62891283232 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1662317722908231 / 4000000000000) 2 (IntervalRat.scale (447 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (38929830040 / 1000000000000) (38929831142 / 1000000000000), orderedInterval (-4090587451 / 1000000000000) (-4090586349 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1110351200344329 / 4000000000000) 2 (IntervalRat.scale (447 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (45119175170 / 1000000000000) (45119182192 / 1000000000000), orderedInterval (-16132955437 / 1000000000000) (-16132948414 / 1000000000000)))) (orderedInterval (23935849406 / 1000000000000) (23935851914 / 1000000000000))) = true
  rfl'

theorem compactCertificate352_chunkChecks2 :
    compactCertificate352.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate352.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate352_chunkChecks2_0
    compactCertificate352_chunkChecks2_1 compactCertificate352_chunkChecks2_2

theorem compactCertificate352_chunkChecks3_0 :
    compactCertificate352.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (447 / 2) 3 (IntervalRat.scale (447 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-50332364920 / 1000000000000) (-50332364918 / 1000000000000), orderedInterval (-17637276404 / 1000000000000) (-17637276403 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (658516353711747 / 4000000000000) 3 (IntervalRat.scale (447 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (55154542657 / 1000000000000) (55154558408 / 1000000000000), orderedInterval (-28889630113 / 1000000000000) (-28889614363 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (212950658718051 / 800000000000) 3 (IntervalRat.scale (447 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (3036143469 / 1000000000000) (3036143474 / 1000000000000), orderedInterval (-48815540235 / 1000000000000) (-48815540231 / 1000000000000)))) (orderedInterval (11850471742 / 1000000000000) (11850471826 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (192153429649929 / 4000000000000) 3 (IntervalRat.scale (447 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-114196252412 / 1000000000000) (-114196252271 / 1000000000000), orderedInterval (15708909542 / 1000000000000) (15708909683 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (516151140655413 / 4000000000000) 3 (IntervalRat.scale (447 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-59737783987 / 1000000000000) (-59737783986 / 1000000000000), orderedInterval (-36714064094 / 1000000000000) (-36714064093 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1401450752575521 / 4000000000000) 3 (IntervalRat.scale (447 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-27806408079 / 1000000000000) (-27806396525 / 1000000000000), orderedInterval (32348111586 / 1000000000000) (32348123141 / 1000000000000)))) (orderedInterval (9137058615 / 1000000000000) (9137061852 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1032302281311273 / 4000000000000) 3 (IntervalRat.scale (447 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (47131255060 / 1000000000000) (47131255061 / 1000000000000), orderedInterval (15575117824 / 1000000000000) (15575117826 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1768867554055629 / 4000000000000) 3 (IntervalRat.scale (447 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-1420217810 / 1000000000000) (-1420217808 / 1000000000000), orderedInterval (-37914007252 / 1000000000000) (-37914007251 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1302939834334311 / 4000000000000) 3 (IntervalRat.scale (447 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-9028130390 / 1000000000000) (-9028130362 / 1000000000000), orderedInterval (43290934149 / 1000000000000) (43290934176 / 1000000000000)))) (orderedInterval (-12298300505 / 1000000000000) (-12298300432 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate352_chunkChecks3_1 :
    compactCertificate352.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1999044771884553 / 4000000000000) 3 (IntervalRat.scale (447 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-30654835996 / 1000000000000) (-30654835995 / 1000000000000), orderedInterval (-18248517602 / 1000000000000) (-18248517601 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1154149037169537 / 4000000000000) 3 (IntervalRat.scale (447 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (13688085365 / 1000000000000) (13688085366 / 1000000000000), orderedInterval (44909658119 / 1000000000000) (44909658120 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2048057719838133 / 4000000000000) 3 (IntervalRat.scale (447 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-23250297894 / 1000000000000) (-23250297893 / 1000000000000), orderedInterval (-26487419317 / 1000000000000) (-26487419316 / 1000000000000)))) (orderedInterval (1910546638 / 1000000000000) (1910547505 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1913561188932777 / 4000000000000) 3 (IntervalRat.scale (447 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (36355252096 / 1000000000000) (36355253349 / 1000000000000), orderedInterval (-3046123726 / 1000000000000) (-3046122473 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1365607557096441 / 4000000000000) 3 (IntervalRat.scale (447 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (10544445369 / 1000000000000) (10544445414 / 1000000000000), orderedInterval (-41890720729 / 1000000000000) (-41890720684 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1548453421966239 / 4000000000000) 3 (IntervalRat.scale (447 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-40394941873 / 1000000000000) (-40394941798 / 1000000000000), orderedInterval (-3522452628 / 1000000000000) (-3522452553 / 1000000000000)))) (orderedInterval (13486549841 / 1000000000000) (13486550202 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1290939028850991 / 4000000000000) 3 (IntervalRat.scale (447 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (2852736605 / 1000000000000) (2852736608 / 1000000000000), orderedInterval (-44326458626 / 1000000000000) (-44326458623 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1140583782242811 / 4000000000000) 3 (IntervalRat.scale (447 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-2171522185 / 1000000000000) (-2171522183 / 1000000000000), orderedInterval (-47196808793 / 1000000000000) (-47196808791 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (330585636482289 / 800000000000) 3 (IntervalRat.scale (447 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-24468802228 / 1000000000000) (-24468796508 / 1000000000000), orderedInterval (30719418783 / 1000000000000) (30719424504 / 1000000000000)))) (orderedInterval (-9047218758 / 1000000000000) (-9047217758 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate352_chunkChecks3_2 :
    compactCertificate352.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (914417268278883 / 4000000000000) 3 (IntervalRat.scale (447 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-2790546229 / 1000000000000) (-2790546227 / 1000000000000), orderedInterval (-52691432402 / 1000000000000) (-52691432400 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (775161645213963 / 4000000000000) 3 (IntervalRat.scale (447 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-11587891798 / 1000000000000) (-11587891727 / 1000000000000), orderedInterval (56162108554 / 1000000000000) (56162108625 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (485060165665689 / 4000000000000) 3 (IntervalRat.scale (447 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (32988627296 / 1000000000000) (32988630551 / 1000000000000), orderedInterval (-64646463393 / 1000000000000) (-64646460139 / 1000000000000)))) (orderedInterval (-6601259342 / 1000000000000) (-6601259273 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (260866970332263 / 4000000000000) 3 (IntervalRat.scale (447 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-2645389373 / 1000000000000) (-2645389367 / 1000000000000), orderedInterval (-98746559060 / 1000000000000) (-98746559055 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (708304570305789 / 4000000000000) 3 (IntervalRat.scale (447 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (56098081414 / 1000000000000) (56098086469 / 1000000000000), orderedInterval (-21328416323 / 1000000000000) (-21328411268 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (967129335932253 / 4000000000000) 3 (IntervalRat.scale (447 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-31646220136 / 1000000000000) (-31646220135 / 1000000000000), orderedInterval (-40326964152 / 1000000000000) (-40326964151 / 1000000000000)))) (orderedInterval (-4189417813 / 1000000000000) (-4189417730 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (408939834334311 / 4000000000000) 3 (IntervalRat.scale (447 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (47970654468 / 1000000000000) (47970676639 / 1000000000000), orderedInterval (-62891305403 / 1000000000000) (-62891283232 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1662317722908231 / 4000000000000) 3 (IntervalRat.scale (447 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (38929830040 / 1000000000000) (38929831142 / 1000000000000), orderedInterval (-4090587451 / 1000000000000) (-4090586349 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1110351200344329 / 4000000000000) 3 (IntervalRat.scale (447 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (45119175170 / 1000000000000) (45119182192 / 1000000000000), orderedInterval (-16132955437 / 1000000000000) (-16132948414 / 1000000000000)))) (orderedInterval (-8010706535 / 1000000000000) (-8010703212 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate352_chunkChecks3 :
    compactCertificate352.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate352.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate352_chunkChecks3_0
    compactCertificate352_chunkChecks3_1 compactCertificate352_chunkChecks3_2

theorem compactCertificate352_chunkChecks4_0 :
    compactCertificate352.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (447 / 2) 4 (IntervalRat.scale (447 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-50332364920 / 1000000000000) (-50332364918 / 1000000000000), orderedInterval (-17637276404 / 1000000000000) (-17637276403 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (658516353711747 / 4000000000000) 4 (IntervalRat.scale (447 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (55154542657 / 1000000000000) (55154558408 / 1000000000000), orderedInterval (-28889630113 / 1000000000000) (-28889614363 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (212950658718051 / 800000000000) 4 (IntervalRat.scale (447 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (3036143469 / 1000000000000) (3036143474 / 1000000000000), orderedInterval (-48815540235 / 1000000000000) (-48815540231 / 1000000000000)))) (orderedInterval (-19545865412 / 1000000000000) (-19545865339 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (192153429649929 / 4000000000000) 4 (IntervalRat.scale (447 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-114196252412 / 1000000000000) (-114196252271 / 1000000000000), orderedInterval (15708909542 / 1000000000000) (15708909683 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (516151140655413 / 4000000000000) 4 (IntervalRat.scale (447 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-59737783987 / 1000000000000) (-59737783986 / 1000000000000), orderedInterval (-36714064094 / 1000000000000) (-36714064093 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1401450752575521 / 4000000000000) 4 (IntervalRat.scale (447 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-27806408079 / 1000000000000) (-27806396525 / 1000000000000), orderedInterval (32348111586 / 1000000000000) (32348123141 / 1000000000000)))) (orderedInterval (11615920621 / 1000000000000) (11615925707 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1032302281311273 / 4000000000000) 4 (IntervalRat.scale (447 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (47131255060 / 1000000000000) (47131255061 / 1000000000000), orderedInterval (15575117824 / 1000000000000) (15575117826 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1768867554055629 / 4000000000000) 4 (IntervalRat.scale (447 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-1420217810 / 1000000000000) (-1420217808 / 1000000000000), orderedInterval (-37914007252 / 1000000000000) (-37914007251 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1302939834334311 / 4000000000000) 4 (IntervalRat.scale (447 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-9028130390 / 1000000000000) (-9028130362 / 1000000000000), orderedInterval (43290934149 / 1000000000000) (43290934176 / 1000000000000)))) (orderedInterval (-203014375 / 1000000000000) (-203014240 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate352_chunkChecks4_1 :
    compactCertificate352.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1999044771884553 / 4000000000000) 4 (IntervalRat.scale (447 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-30654835996 / 1000000000000) (-30654835995 / 1000000000000), orderedInterval (-18248517602 / 1000000000000) (-18248517601 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1154149037169537 / 4000000000000) 4 (IntervalRat.scale (447 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (13688085365 / 1000000000000) (13688085366 / 1000000000000), orderedInterval (44909658119 / 1000000000000) (44909658120 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2048057719838133 / 4000000000000) 4 (IntervalRat.scale (447 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-23250297894 / 1000000000000) (-23250297893 / 1000000000000), orderedInterval (-26487419317 / 1000000000000) (-26487419316 / 1000000000000)))) (orderedInterval (47938905169 / 1000000000000) (47938907093 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1913561188932777 / 4000000000000) 4 (IntervalRat.scale (447 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (36355252096 / 1000000000000) (36355253349 / 1000000000000), orderedInterval (-3046123726 / 1000000000000) (-3046122473 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1365607557096441 / 4000000000000) 4 (IntervalRat.scale (447 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (10544445369 / 1000000000000) (10544445414 / 1000000000000), orderedInterval (-41890720729 / 1000000000000) (-41890720684 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1548453421966239 / 4000000000000) 4 (IntervalRat.scale (447 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-40394941873 / 1000000000000) (-40394941798 / 1000000000000), orderedInterval (-3522452628 / 1000000000000) (-3522452553 / 1000000000000)))) (orderedInterval (-6628631987 / 1000000000000) (-6628631273 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1290939028850991 / 4000000000000) 4 (IntervalRat.scale (447 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (2852736605 / 1000000000000) (2852736608 / 1000000000000), orderedInterval (-44326458626 / 1000000000000) (-44326458623 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1140583782242811 / 4000000000000) 4 (IntervalRat.scale (447 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-2171522185 / 1000000000000) (-2171522183 / 1000000000000), orderedInterval (-47196808793 / 1000000000000) (-47196808791 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (330585636482289 / 800000000000) 4 (IntervalRat.scale (447 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-24468802228 / 1000000000000) (-24468796508 / 1000000000000), orderedInterval (30719418783 / 1000000000000) (30719424504 / 1000000000000)))) (orderedInterval (-6767784016 / 1000000000000) (-6767782183 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate352_chunkChecks4_2 :
    compactCertificate352.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (914417268278883 / 4000000000000) 4 (IntervalRat.scale (447 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-2790546229 / 1000000000000) (-2790546227 / 1000000000000), orderedInterval (-52691432402 / 1000000000000) (-52691432400 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (775161645213963 / 4000000000000) 4 (IntervalRat.scale (447 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-11587891798 / 1000000000000) (-11587891727 / 1000000000000), orderedInterval (56162108554 / 1000000000000) (56162108625 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (485060165665689 / 4000000000000) 4 (IntervalRat.scale (447 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (32988627296 / 1000000000000) (32988630551 / 1000000000000), orderedInterval (-64646463393 / 1000000000000) (-64646460139 / 1000000000000)))) (orderedInterval (1011196751 / 1000000000000) (1011196811 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (260866970332263 / 4000000000000) 4 (IntervalRat.scale (447 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-2645389373 / 1000000000000) (-2645389367 / 1000000000000), orderedInterval (-98746559060 / 1000000000000) (-98746559055 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (708304570305789 / 4000000000000) 4 (IntervalRat.scale (447 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (56098081414 / 1000000000000) (56098086469 / 1000000000000), orderedInterval (-21328416323 / 1000000000000) (-21328411268 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (967129335932253 / 4000000000000) 4 (IntervalRat.scale (447 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-31646220136 / 1000000000000) (-31646220135 / 1000000000000), orderedInterval (-40326964152 / 1000000000000) (-40326964151 / 1000000000000)))) (orderedInterval (2858012775 / 1000000000000) (2858012847 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (408939834334311 / 4000000000000) 4 (IntervalRat.scale (447 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (47970654468 / 1000000000000) (47970676639 / 1000000000000), orderedInterval (-62891305403 / 1000000000000) (-62891283232 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1662317722908231 / 4000000000000) 4 (IntervalRat.scale (447 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (38929830040 / 1000000000000) (38929831142 / 1000000000000), orderedInterval (-4090587451 / 1000000000000) (-4090586349 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1110351200344329 / 4000000000000) 4 (IntervalRat.scale (447 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (45119175170 / 1000000000000) (45119182192 / 1000000000000), orderedInterval (-16132955437 / 1000000000000) (-16132948414 / 1000000000000)))) (orderedInterval (-57940319522 / 1000000000000) (-57940314963 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate352_chunkChecks4 :
    compactCertificate352.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate352.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate352_chunkChecks4_0
    compactCertificate352_chunkChecks4_1 compactCertificate352_chunkChecks4_2

theorem compactCertificate352_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate352.chunkCheck r b = true :=
  compactCertificate352.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate352_chunkChecks0
    · exact compactCertificate352_chunkChecks1
    · exact compactCertificate352_chunkChecks2
    · exact compactCertificate352_chunkChecks3
    · exact compactCertificate352_chunkChecks4)

theorem compactCertificate352_coefficient0 :
    compactCertificate352.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate352_coefficient1 :
    compactCertificate352.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate352_coefficient2 :
    compactCertificate352.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate352_coefficient3 :
    compactCertificate352.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate352_coefficient4 :
    compactCertificate352.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate352_coefficients : ∀ r : Fin 5,
    compactCertificate352.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate352_coefficient0
  · exact compactCertificate352_coefficient1
  · exact compactCertificate352_coefficient2
  · exact compactCertificate352_coefficient3
  · exact compactCertificate352_coefficient4

theorem compactCertificate352_lower : (1 : ℚ) ≤ compactCertificate352.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate352, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate352_proves {t : ℝ} (ht : t ∈ compactCertificate352.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate352.proves compactCertificate352_states compactCertificate352_chunks
    compactCertificate352_coefficients compactCertificate352_lower ht

end Erdos232
