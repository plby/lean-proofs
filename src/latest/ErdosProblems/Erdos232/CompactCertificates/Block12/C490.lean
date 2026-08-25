/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate490 : CompactCertificate where
  left := 361
  right := 362
  center := 723 / 2
  grid := fun i =>
    match i.val with
    | 0 => 115
    | 1 => 85
    | 2 => 137
    | 3 => 25
    | 4 => 66
    | 5 => 180
    | 6 => 133
    | 7 => 228
    | 8 => 168
    | 9 => 257
    | 10 => 149
    | 11 => 264
    | 12 => 246
    | 13 => 176
    | 14 => 199
    | 15 => 166
    | 16 => 147
    | 17 => 213
    | 18 => 118
    | 19 => 100
    | 20 => 62
    | 21 => 34
    | 22 => 91
    | 23 => 125
    | 24 => 53
    | 25 => 214
    | _ => 143
  point := fun i =>
    match i.val with
    | 0 => 723 / 2
    | 1 => 1065117055332423 / 4000000000000
    | 2 => 344436971483559 / 800000000000
    | 3 => 310798500306261 / 4000000000000
    | 4 => 834848489248017 / 4000000000000
    | 5 => 2266776049467789 / 4000000000000
    | 6 => 1669696978496757 / 4000000000000
    | 7 => 2861054231727561 / 4000000000000
    | 8 => 2107439597815899 / 4000000000000
    | 9 => 3233354295464277 / 4000000000000
    | 10 => 1866777972871533 / 4000000000000
    | 11 => 3312630271684497 / 4000000000000
    | 12 => 3095088902904693 / 4000000000000
    | 13 => 2208801484968069 / 4000000000000
    | 14 => 2504545467744051 / 4000000000000
    | 15 => 2088028899014019 / 4000000000000
    | 16 => 1844836855842399 / 4000000000000
    | 17 => 534705626793501 / 800000000000
    | 18 => 1479023903726247 / 4000000000000
    | 19 => 1253784942929967 / 4000000000000
    | 20 => 784560402184101 / 4000000000000
    | 21 => 421939193624667 / 4000000000000
    | 22 => 1145646989555001 / 4000000000000
    | 23 => 1564283019863577 / 4000000000000
    | 24 => 661439597815899 / 4000000000000
    | 25 => 2688715243093179 / 4000000000000
    | _ => 1795937176395861 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-35355159366 / 1000000000000) (-35355159365 / 1000000000000), orderedInterval (-22557791951 / 1000000000000) (-22557791950 / 1000000000000))
    | 1 => (orderedInterval (-1408834103 / 1000000000000) (-1408834101 / 1000000000000), orderedInterval (-48872878098 / 1000000000000) (-48872878096 / 1000000000000))
    | 2 => (orderedInterval (-30896449307 / 1000000000000) (-30896449306 / 1000000000000), orderedInterval (-22856082555 / 1000000000000) (-22856082554 / 1000000000000))
    | 3 => (orderedInterval (5102560606 / 1000000000000) (5102560625 / 1000000000000), orderedInterval (-90406926313 / 1000000000000) (-90406926294 / 1000000000000))
    | 4 => (orderedInterval (46166206171 / 1000000000000) (46166255152 / 1000000000000), orderedInterval (-30424060043 / 1000000000000) (-30424011062 / 1000000000000))
    | 5 => (orderedInterval (30580511355 / 1000000000000) (30580570697 / 1000000000000), orderedInterval (-13746435367 / 1000000000000) (-13746376025 / 1000000000000))
    | 6 => (orderedInterval (-14395474451 / 1000000000000) (-14395474450 / 1000000000000), orderedInterval (-36285451229 / 1000000000000) (-36285451228 / 1000000000000))
    | 7 => (orderedInterval (-6927521581 / 1000000000000) (-6927521579 / 1000000000000), orderedInterval (29023093088 / 1000000000000) (29023093090 / 1000000000000))
    | 8 => (orderedInterval (-4936883864 / 1000000000000) (-4936883862 / 1000000000000), orderedInterval (34413348150 / 1000000000000) (34413348153 / 1000000000000))
    | 9 => (orderedInterval (-27688385094 / 1000000000000) (-27688367842 / 1000000000000), orderedInterval (4590891098 / 1000000000000) (4590908350 / 1000000000000))
    | 10 => (orderedInterval (21390075276 / 1000000000000) (21390077629 / 1000000000000), orderedInterval (-30132198211 / 1000000000000) (-30132195857 / 1000000000000))
    | 11 => (orderedInterval (-11750399779 / 1000000000000) (-11750399760 / 1000000000000), orderedInterval (25119767739 / 1000000000000) (25119767759 / 1000000000000))
    | 12 => (orderedInterval (28340268115 / 1000000000000) (28340281490 / 1000000000000), orderedInterval (-4442902890 / 1000000000000) (-4442889515 / 1000000000000))
    | 13 => (orderedInterval (2213456090 / 1000000000000) (2213456091 / 1000000000000), orderedInterval (33879838785 / 1000000000000) (33879838786 / 1000000000000))
    | 14 => (orderedInterval (-31405858849 / 1000000000000) (-31405851184 / 1000000000000), orderedInterval (5540051710 / 1000000000000) (5540059375 / 1000000000000))
    | 15 => (orderedInterval (33535089166 / 1000000000000) (33535089177 / 1000000000000), orderedInterval (9712546537 / 1000000000000) (9712546548 / 1000000000000))
    | 16 => (orderedInterval (-6659519377 / 1000000000000) (-6659519376 / 1000000000000), orderedInterval (-36543828035 / 1000000000000) (-36543828034 / 1000000000000))
    | 17 => (orderedInterval (-247186162 / 1000000000000) (-247186161 / 1000000000000), orderedInterval (-30861086091 / 1000000000000) (-30861086090 / 1000000000000))
    | 18 => (orderedInterval (-6893074316 / 1000000000000) (-6893074306 / 1000000000000), orderedInterval (40926512049 / 1000000000000) (40926512060 / 1000000000000))
    | 19 => (orderedInterval (3240658363 / 1000000000000) (3240658364 / 1000000000000), orderedInterval (44945181955 / 1000000000000) (44945181956 / 1000000000000))
    | 20 => (orderedInterval (47799922175 / 1000000000000) (47799966203 / 1000000000000), orderedInterval (-31120274459 / 1000000000000) (-31120230430 / 1000000000000))
    | 21 => (orderedInterval (-40283031366 / 1000000000000) (-40283023792 / 1000000000000), orderedInterval (66617504505 / 1000000000000) (66617512080 / 1000000000000))
    | 22 => (orderedInterval (-45573237734 / 1000000000000) (-45573237731 / 1000000000000), orderedInterval (-11996048503 / 1000000000000) (-11996048501 / 1000000000000))
    | 23 => (orderedInterval (30131481579 / 1000000000000) (30131514933 / 1000000000000), orderedInterval (-26871013585 / 1000000000000) (-26870980231 / 1000000000000))
    | 24 => (orderedInterval (21850107983 / 1000000000000) (21850108670 / 1000000000000), orderedInterval (-58139213365 / 1000000000000) (-58139212678 / 1000000000000))
    | 25 => (orderedInterval (18946233664 / 1000000000000) (18946233665 / 1000000000000), orderedInterval (24237486887 / 1000000000000) (24237486888 / 1000000000000))
    | _ => (orderedInterval (-18764457720 / 1000000000000) (-18764457719 / 1000000000000), orderedInterval (-32625796643 / 1000000000000) (-32625796642 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-15839713975 / 1000000000000) (-15839713949 / 1000000000000)
      | 1 => orderedInterval (-543712186 / 1000000000000) (-543706135 / 1000000000000)
      | 2 => orderedInterval (94357730 / 1000000000000) (94357751 / 1000000000000)
      | 3 => orderedInterval (4834328582 / 1000000000000) (4834331967 / 1000000000000)
      | 4 => orderedInterval (-143387112 / 1000000000000) (-143386788 / 1000000000000)
      | 5 => orderedInterval (762025348 / 1000000000000) (762025383 / 1000000000000)
      | 6 => orderedInterval (2474868738 / 1000000000000) (2474870264 / 1000000000000)
      | 7 => orderedInterval (-531500775 / 1000000000000) (-531498035 / 1000000000000)
      | _ => orderedInterval (2110172513 / 1000000000000) (2110172617 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-10873958072 / 1000000000000) (-10873958043 / 1000000000000)
      | 1 => orderedInterval (1101395365 / 1000000000000) (1101403061 / 1000000000000)
      | 2 => orderedInterval (-559072665 / 1000000000000) (-559072629 / 1000000000000)
      | 3 => orderedInterval (3474322685 / 1000000000000) (3474330068 / 1000000000000)
      | 4 => orderedInterval (5016967827 / 1000000000000) (5016968481 / 1000000000000)
      | 5 => orderedInterval (1369108705 / 1000000000000) (1369108756 / 1000000000000)
      | 6 => orderedInterval (-9448723581 / 1000000000000) (-9448722718 / 1000000000000)
      | 7 => orderedInterval (2084500514 / 1000000000000) (2084503360 / 1000000000000)
      | _ => orderedInterval (3773981228 / 1000000000000) (3773981371 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (16622508036 / 1000000000000) (16622508070 / 1000000000000)
      | 1 => orderedInterval (4779982758 / 1000000000000) (4779993811 / 1000000000000)
      | 2 => orderedInterval (-581514413 / 1000000000000) (-581514350 / 1000000000000)
      | 3 => orderedInterval (-18483938582 / 1000000000000) (-18483922293 / 1000000000000)
      | 4 => orderedInterval (1364975094 / 1000000000000) (1364976435 / 1000000000000)
      | 5 => orderedInterval (-1409956265 / 1000000000000) (-1409956190 / 1000000000000)
      | 6 => orderedInterval (-1447136679 / 1000000000000) (-1447136172 / 1000000000000)
      | 7 => orderedInterval (1984379943 / 1000000000000) (1984382993 / 1000000000000)
      | _ => orderedInterval (-136711238 / 1000000000000) (-136711029 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (11342926415 / 1000000000000) (11342926454 / 1000000000000)
      | 1 => orderedInterval (-3573761077 / 1000000000000) (-3573744348 / 1000000000000)
      | 2 => orderedInterval (4360955475 / 1000000000000) (4360955590 / 1000000000000)
      | 3 => orderedInterval (-28958171450 / 1000000000000) (-28958135329 / 1000000000000)
      | 4 => orderedInterval (-12063596131 / 1000000000000) (-12063593362 / 1000000000000)
      | 5 => orderedInterval (317511214 / 1000000000000) (317511329 / 1000000000000)
      | 6 => orderedInterval (8826558724 / 1000000000000) (8826559034 / 1000000000000)
      | 7 => orderedInterval (-2717461193 / 1000000000000) (-2717457905 / 1000000000000)
      | _ => orderedInterval (989801338 / 1000000000000) (989801660 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-17728024139 / 1000000000000) (-17728024094 / 1000000000000)
      | 1 => orderedInterval (-12921462252 / 1000000000000) (-12921436328 / 1000000000000)
      | 2 => orderedInterval (2712309573 / 1000000000000) (2712309786 / 1000000000000)
      | 3 => orderedInterval (81551284381 / 1000000000000) (81551364865 / 1000000000000)
      | 4 => orderedInterval (-8102556629 / 1000000000000) (-8102550857 / 1000000000000)
      | 5 => orderedInterval (2617698093 / 1000000000000) (2617698276 / 1000000000000)
      | 6 => orderedInterval (1188678341 / 1000000000000) (1188678546 / 1000000000000)
      | 7 => orderedInterval (-2734865667 / 1000000000000) (-2734862105 / 1000000000000)
      | _ => orderedInterval (-10057907683 / 1000000000000) (-10057907167 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-6782561137 / 1000000000000) (-6782546925 / 1000000000000)
    | 1 => orderedInterval (-4061477994 / 1000000000000) (-4061458293 / 1000000000000)
    | 2 => orderedInterval (2692588654 / 1000000000000) (2692621275 / 1000000000000)
    | 3 => orderedInterval (-21475236685 / 1000000000000) (-21475176877 / 1000000000000)
    | _ => orderedInterval (36525154018 / 1000000000000) (36525270922 / 1000000000000)

theorem compactCertificate490_stateChecks0 :
    compactCertificate490.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 115 12 (723 / 2)) (orderedInterval (-35355159366 / 1000000000000) (-35355159365 / 1000000000000), orderedInterval (-22557791951 / 1000000000000) (-22557791950 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (1065117055332423 / 4000000000000)) (orderedInterval (-1408834103 / 1000000000000) (-1408834101 / 1000000000000), orderedInterval (-48872878098 / 1000000000000) (-48872878096 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 137 12 (344436971483559 / 800000000000)) (orderedInterval (-30896449307 / 1000000000000) (-30896449306 / 1000000000000), orderedInterval (-22856082555 / 1000000000000) (-22856082554 / 1000000000000))) = true
  rfl'

theorem compactCertificate490_stateChecks1 :
    compactCertificate490.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (310798500306261 / 4000000000000)) (orderedInterval (5102560606 / 1000000000000) (5102560625 / 1000000000000), orderedInterval (-90406926313 / 1000000000000) (-90406926294 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (834848489248017 / 4000000000000)) (orderedInterval (46166206171 / 1000000000000) (46166255152 / 1000000000000), orderedInterval (-30424060043 / 1000000000000) (-30424011062 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 180 12 (2266776049467789 / 4000000000000)) (orderedInterval (30580511355 / 1000000000000) (30580570697 / 1000000000000), orderedInterval (-13746435367 / 1000000000000) (-13746376025 / 1000000000000))) = true
  rfl'

theorem compactCertificate490_stateChecks2 :
    compactCertificate490.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 133 12 (1669696978496757 / 4000000000000)) (orderedInterval (-14395474451 / 1000000000000) (-14395474450 / 1000000000000), orderedInterval (-36285451229 / 1000000000000) (-36285451228 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 228 12 (2861054231727561 / 4000000000000)) (orderedInterval (-6927521581 / 1000000000000) (-6927521579 / 1000000000000), orderedInterval (29023093088 / 1000000000000) (29023093090 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 168 12 (2107439597815899 / 4000000000000)) (orderedInterval (-4936883864 / 1000000000000) (-4936883862 / 1000000000000), orderedInterval (34413348150 / 1000000000000) (34413348153 / 1000000000000))) = true
  rfl'

theorem compactCertificate490_stateChecks3 :
    compactCertificate490.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 257 12 (3233354295464277 / 4000000000000)) (orderedInterval (-27688385094 / 1000000000000) (-27688367842 / 1000000000000), orderedInterval (4590891098 / 1000000000000) (4590908350 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 149 12 (1866777972871533 / 4000000000000)) (orderedInterval (21390075276 / 1000000000000) (21390077629 / 1000000000000), orderedInterval (-30132198211 / 1000000000000) (-30132195857 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 264 12 (3312630271684497 / 4000000000000)) (orderedInterval (-11750399779 / 1000000000000) (-11750399760 / 1000000000000), orderedInterval (25119767739 / 1000000000000) (25119767759 / 1000000000000))) = true
  rfl'

theorem compactCertificate490_stateChecks4 :
    compactCertificate490.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 246 12 (3095088902904693 / 4000000000000)) (orderedInterval (28340268115 / 1000000000000) (28340281490 / 1000000000000), orderedInterval (-4442902890 / 1000000000000) (-4442889515 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 176 12 (2208801484968069 / 4000000000000)) (orderedInterval (2213456090 / 1000000000000) (2213456091 / 1000000000000), orderedInterval (33879838785 / 1000000000000) (33879838786 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 199 12 (2504545467744051 / 4000000000000)) (orderedInterval (-31405858849 / 1000000000000) (-31405851184 / 1000000000000), orderedInterval (5540051710 / 1000000000000) (5540059375 / 1000000000000))) = true
  rfl'

theorem compactCertificate490_stateChecks5 :
    compactCertificate490.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 166 12 (2088028899014019 / 4000000000000)) (orderedInterval (33535089166 / 1000000000000) (33535089177 / 1000000000000), orderedInterval (9712546537 / 1000000000000) (9712546548 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 147 12 (1844836855842399 / 4000000000000)) (orderedInterval (-6659519377 / 1000000000000) (-6659519376 / 1000000000000), orderedInterval (-36543828035 / 1000000000000) (-36543828034 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 213 12 (534705626793501 / 800000000000)) (orderedInterval (-247186162 / 1000000000000) (-247186161 / 1000000000000), orderedInterval (-30861086091 / 1000000000000) (-30861086090 / 1000000000000))) = true
  rfl'

theorem compactCertificate490_stateChecks6 :
    compactCertificate490.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 118 12 (1479023903726247 / 4000000000000)) (orderedInterval (-6893074316 / 1000000000000) (-6893074306 / 1000000000000), orderedInterval (40926512049 / 1000000000000) (40926512060 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 100 12 (1253784942929967 / 4000000000000)) (orderedInterval (3240658363 / 1000000000000) (3240658364 / 1000000000000), orderedInterval (44945181955 / 1000000000000) (44945181956 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (784560402184101 / 4000000000000)) (orderedInterval (47799922175 / 1000000000000) (47799966203 / 1000000000000), orderedInterval (-31120274459 / 1000000000000) (-31120230430 / 1000000000000))) = true
  rfl'

theorem compactCertificate490_stateChecks7 :
    compactCertificate490.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (421939193624667 / 4000000000000)) (orderedInterval (-40283031366 / 1000000000000) (-40283023792 / 1000000000000), orderedInterval (66617504505 / 1000000000000) (66617512080 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 91 12 (1145646989555001 / 4000000000000)) (orderedInterval (-45573237734 / 1000000000000) (-45573237731 / 1000000000000), orderedInterval (-11996048503 / 1000000000000) (-11996048501 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 125 12 (1564283019863577 / 4000000000000)) (orderedInterval (30131481579 / 1000000000000) (30131514933 / 1000000000000), orderedInterval (-26871013585 / 1000000000000) (-26870980231 / 1000000000000))) = true
  rfl'

theorem compactCertificate490_stateChecks8 :
    compactCertificate490.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (661439597815899 / 4000000000000)) (orderedInterval (21850107983 / 1000000000000) (21850108670 / 1000000000000), orderedInterval (-58139213365 / 1000000000000) (-58139212678 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 214 12 (2688715243093179 / 4000000000000)) (orderedInterval (18946233664 / 1000000000000) (18946233665 / 1000000000000), orderedInterval (24237486887 / 1000000000000) (24237486888 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 143 12 (1795937176395861 / 4000000000000)) (orderedInterval (-18764457720 / 1000000000000) (-18764457719 / 1000000000000), orderedInterval (-32625796643 / 1000000000000) (-32625796642 / 1000000000000))) = true
  rfl'

theorem compactCertificate490_states : ∀ j,
    BesselStateValid (compactCertificate490.point j) (compactCertificate490.state j) :=
  compactCertificate490.statesValid_of_checks3 compactCertificate490_stateChecks0
    compactCertificate490_stateChecks1 compactCertificate490_stateChecks2
    compactCertificate490_stateChecks3 compactCertificate490_stateChecks4
    compactCertificate490_stateChecks5 compactCertificate490_stateChecks6
    compactCertificate490_stateChecks7 compactCertificate490_stateChecks8

theorem compactCertificate490_chunkChecks0_0 :
    compactCertificate490.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (723 / 2) 0 (IntervalRat.scale (723 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-35355159366 / 1000000000000) (-35355159365 / 1000000000000), orderedInterval (-22557791951 / 1000000000000) (-22557791950 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1065117055332423 / 4000000000000) 0 (IntervalRat.scale (723 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-1408834103 / 1000000000000) (-1408834101 / 1000000000000), orderedInterval (-48872878098 / 1000000000000) (-48872878096 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (344436971483559 / 800000000000) 0 (IntervalRat.scale (723 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-30896449307 / 1000000000000) (-30896449306 / 1000000000000), orderedInterval (-22856082555 / 1000000000000) (-22856082554 / 1000000000000)))) (orderedInterval (-15839713975 / 1000000000000) (-15839713949 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (310798500306261 / 4000000000000) 0 (IntervalRat.scale (723 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (5102560606 / 1000000000000) (5102560625 / 1000000000000), orderedInterval (-90406926313 / 1000000000000) (-90406926294 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (834848489248017 / 4000000000000) 0 (IntervalRat.scale (723 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (46166206171 / 1000000000000) (46166255152 / 1000000000000), orderedInterval (-30424060043 / 1000000000000) (-30424011062 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2266776049467789 / 4000000000000) 0 (IntervalRat.scale (723 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30580511355 / 1000000000000) (30580570697 / 1000000000000), orderedInterval (-13746435367 / 1000000000000) (-13746376025 / 1000000000000)))) (orderedInterval (-543712186 / 1000000000000) (-543706135 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1669696978496757 / 4000000000000) 0 (IntervalRat.scale (723 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-14395474451 / 1000000000000) (-14395474450 / 1000000000000), orderedInterval (-36285451229 / 1000000000000) (-36285451228 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2861054231727561 / 4000000000000) 0 (IntervalRat.scale (723 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-6927521581 / 1000000000000) (-6927521579 / 1000000000000), orderedInterval (29023093088 / 1000000000000) (29023093090 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2107439597815899 / 4000000000000) 0 (IntervalRat.scale (723 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-4936883864 / 1000000000000) (-4936883862 / 1000000000000), orderedInterval (34413348150 / 1000000000000) (34413348153 / 1000000000000)))) (orderedInterval (94357730 / 1000000000000) (94357751 / 1000000000000))) = true
  rfl'

theorem compactCertificate490_chunkChecks0_1 :
    compactCertificate490.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3233354295464277 / 4000000000000) 0 (IntervalRat.scale (723 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-27688385094 / 1000000000000) (-27688367842 / 1000000000000), orderedInterval (4590891098 / 1000000000000) (4590908350 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1866777972871533 / 4000000000000) 0 (IntervalRat.scale (723 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (21390075276 / 1000000000000) (21390077629 / 1000000000000), orderedInterval (-30132198211 / 1000000000000) (-30132195857 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3312630271684497 / 4000000000000) 0 (IntervalRat.scale (723 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-11750399779 / 1000000000000) (-11750399760 / 1000000000000), orderedInterval (25119767739 / 1000000000000) (25119767759 / 1000000000000)))) (orderedInterval (4834328582 / 1000000000000) (4834331967 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3095088902904693 / 4000000000000) 0 (IntervalRat.scale (723 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (28340268115 / 1000000000000) (28340281490 / 1000000000000), orderedInterval (-4442902890 / 1000000000000) (-4442889515 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2208801484968069 / 4000000000000) 0 (IntervalRat.scale (723 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (2213456090 / 1000000000000) (2213456091 / 1000000000000), orderedInterval (33879838785 / 1000000000000) (33879838786 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2504545467744051 / 4000000000000) 0 (IntervalRat.scale (723 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-31405858849 / 1000000000000) (-31405851184 / 1000000000000), orderedInterval (5540051710 / 1000000000000) (5540059375 / 1000000000000)))) (orderedInterval (-143387112 / 1000000000000) (-143386788 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2088028899014019 / 4000000000000) 0 (IntervalRat.scale (723 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (33535089166 / 1000000000000) (33535089177 / 1000000000000), orderedInterval (9712546537 / 1000000000000) (9712546548 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1844836855842399 / 4000000000000) 0 (IntervalRat.scale (723 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-6659519377 / 1000000000000) (-6659519376 / 1000000000000), orderedInterval (-36543828035 / 1000000000000) (-36543828034 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (534705626793501 / 800000000000) 0 (IntervalRat.scale (723 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-247186162 / 1000000000000) (-247186161 / 1000000000000), orderedInterval (-30861086091 / 1000000000000) (-30861086090 / 1000000000000)))) (orderedInterval (762025348 / 1000000000000) (762025383 / 1000000000000))) = true
  rfl'

theorem compactCertificate490_chunkChecks0_2 :
    compactCertificate490.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1479023903726247 / 4000000000000) 0 (IntervalRat.scale (723 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-6893074316 / 1000000000000) (-6893074306 / 1000000000000), orderedInterval (40926512049 / 1000000000000) (40926512060 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1253784942929967 / 4000000000000) 0 (IntervalRat.scale (723 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (3240658363 / 1000000000000) (3240658364 / 1000000000000), orderedInterval (44945181955 / 1000000000000) (44945181956 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (784560402184101 / 4000000000000) 0 (IntervalRat.scale (723 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (47799922175 / 1000000000000) (47799966203 / 1000000000000), orderedInterval (-31120274459 / 1000000000000) (-31120230430 / 1000000000000)))) (orderedInterval (2474868738 / 1000000000000) (2474870264 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (421939193624667 / 4000000000000) 0 (IntervalRat.scale (723 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-40283031366 / 1000000000000) (-40283023792 / 1000000000000), orderedInterval (66617504505 / 1000000000000) (66617512080 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1145646989555001 / 4000000000000) 0 (IntervalRat.scale (723 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-45573237734 / 1000000000000) (-45573237731 / 1000000000000), orderedInterval (-11996048503 / 1000000000000) (-11996048501 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1564283019863577 / 4000000000000) 0 (IntervalRat.scale (723 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (30131481579 / 1000000000000) (30131514933 / 1000000000000), orderedInterval (-26871013585 / 1000000000000) (-26870980231 / 1000000000000)))) (orderedInterval (-531500775 / 1000000000000) (-531498035 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (661439597815899 / 4000000000000) 0 (IntervalRat.scale (723 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (21850107983 / 1000000000000) (21850108670 / 1000000000000), orderedInterval (-58139213365 / 1000000000000) (-58139212678 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2688715243093179 / 4000000000000) 0 (IntervalRat.scale (723 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (18946233664 / 1000000000000) (18946233665 / 1000000000000), orderedInterval (24237486887 / 1000000000000) (24237486888 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1795937176395861 / 4000000000000) 0 (IntervalRat.scale (723 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-18764457720 / 1000000000000) (-18764457719 / 1000000000000), orderedInterval (-32625796643 / 1000000000000) (-32625796642 / 1000000000000)))) (orderedInterval (2110172513 / 1000000000000) (2110172617 / 1000000000000))) = true
  rfl'

theorem compactCertificate490_chunkChecks0 :
    compactCertificate490.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate490.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate490_chunkChecks0_0
    compactCertificate490_chunkChecks0_1 compactCertificate490_chunkChecks0_2

theorem compactCertificate490_chunkChecks1_0 :
    compactCertificate490.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (723 / 2) 1 (IntervalRat.scale (723 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-35355159366 / 1000000000000) (-35355159365 / 1000000000000), orderedInterval (-22557791951 / 1000000000000) (-22557791950 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1065117055332423 / 4000000000000) 1 (IntervalRat.scale (723 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-1408834103 / 1000000000000) (-1408834101 / 1000000000000), orderedInterval (-48872878098 / 1000000000000) (-48872878096 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (344436971483559 / 800000000000) 1 (IntervalRat.scale (723 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-30896449307 / 1000000000000) (-30896449306 / 1000000000000), orderedInterval (-22856082555 / 1000000000000) (-22856082554 / 1000000000000)))) (orderedInterval (-10873958072 / 1000000000000) (-10873958043 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (310798500306261 / 4000000000000) 1 (IntervalRat.scale (723 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (5102560606 / 1000000000000) (5102560625 / 1000000000000), orderedInterval (-90406926313 / 1000000000000) (-90406926294 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (834848489248017 / 4000000000000) 1 (IntervalRat.scale (723 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (46166206171 / 1000000000000) (46166255152 / 1000000000000), orderedInterval (-30424060043 / 1000000000000) (-30424011062 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2266776049467789 / 4000000000000) 1 (IntervalRat.scale (723 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30580511355 / 1000000000000) (30580570697 / 1000000000000), orderedInterval (-13746435367 / 1000000000000) (-13746376025 / 1000000000000)))) (orderedInterval (1101395365 / 1000000000000) (1101403061 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1669696978496757 / 4000000000000) 1 (IntervalRat.scale (723 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-14395474451 / 1000000000000) (-14395474450 / 1000000000000), orderedInterval (-36285451229 / 1000000000000) (-36285451228 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2861054231727561 / 4000000000000) 1 (IntervalRat.scale (723 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-6927521581 / 1000000000000) (-6927521579 / 1000000000000), orderedInterval (29023093088 / 1000000000000) (29023093090 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2107439597815899 / 4000000000000) 1 (IntervalRat.scale (723 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-4936883864 / 1000000000000) (-4936883862 / 1000000000000), orderedInterval (34413348150 / 1000000000000) (34413348153 / 1000000000000)))) (orderedInterval (-559072665 / 1000000000000) (-559072629 / 1000000000000))) = true
  rfl'

theorem compactCertificate490_chunkChecks1_1 :
    compactCertificate490.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3233354295464277 / 4000000000000) 1 (IntervalRat.scale (723 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-27688385094 / 1000000000000) (-27688367842 / 1000000000000), orderedInterval (4590891098 / 1000000000000) (4590908350 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1866777972871533 / 4000000000000) 1 (IntervalRat.scale (723 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (21390075276 / 1000000000000) (21390077629 / 1000000000000), orderedInterval (-30132198211 / 1000000000000) (-30132195857 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3312630271684497 / 4000000000000) 1 (IntervalRat.scale (723 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-11750399779 / 1000000000000) (-11750399760 / 1000000000000), orderedInterval (25119767739 / 1000000000000) (25119767759 / 1000000000000)))) (orderedInterval (3474322685 / 1000000000000) (3474330068 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3095088902904693 / 4000000000000) 1 (IntervalRat.scale (723 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (28340268115 / 1000000000000) (28340281490 / 1000000000000), orderedInterval (-4442902890 / 1000000000000) (-4442889515 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2208801484968069 / 4000000000000) 1 (IntervalRat.scale (723 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (2213456090 / 1000000000000) (2213456091 / 1000000000000), orderedInterval (33879838785 / 1000000000000) (33879838786 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2504545467744051 / 4000000000000) 1 (IntervalRat.scale (723 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-31405858849 / 1000000000000) (-31405851184 / 1000000000000), orderedInterval (5540051710 / 1000000000000) (5540059375 / 1000000000000)))) (orderedInterval (5016967827 / 1000000000000) (5016968481 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2088028899014019 / 4000000000000) 1 (IntervalRat.scale (723 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (33535089166 / 1000000000000) (33535089177 / 1000000000000), orderedInterval (9712546537 / 1000000000000) (9712546548 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1844836855842399 / 4000000000000) 1 (IntervalRat.scale (723 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-6659519377 / 1000000000000) (-6659519376 / 1000000000000), orderedInterval (-36543828035 / 1000000000000) (-36543828034 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (534705626793501 / 800000000000) 1 (IntervalRat.scale (723 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-247186162 / 1000000000000) (-247186161 / 1000000000000), orderedInterval (-30861086091 / 1000000000000) (-30861086090 / 1000000000000)))) (orderedInterval (1369108705 / 1000000000000) (1369108756 / 1000000000000))) = true
  rfl'

theorem compactCertificate490_chunkChecks1_2 :
    compactCertificate490.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1479023903726247 / 4000000000000) 1 (IntervalRat.scale (723 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-6893074316 / 1000000000000) (-6893074306 / 1000000000000), orderedInterval (40926512049 / 1000000000000) (40926512060 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1253784942929967 / 4000000000000) 1 (IntervalRat.scale (723 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (3240658363 / 1000000000000) (3240658364 / 1000000000000), orderedInterval (44945181955 / 1000000000000) (44945181956 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (784560402184101 / 4000000000000) 1 (IntervalRat.scale (723 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (47799922175 / 1000000000000) (47799966203 / 1000000000000), orderedInterval (-31120274459 / 1000000000000) (-31120230430 / 1000000000000)))) (orderedInterval (-9448723581 / 1000000000000) (-9448722718 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (421939193624667 / 4000000000000) 1 (IntervalRat.scale (723 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-40283031366 / 1000000000000) (-40283023792 / 1000000000000), orderedInterval (66617504505 / 1000000000000) (66617512080 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1145646989555001 / 4000000000000) 1 (IntervalRat.scale (723 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-45573237734 / 1000000000000) (-45573237731 / 1000000000000), orderedInterval (-11996048503 / 1000000000000) (-11996048501 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1564283019863577 / 4000000000000) 1 (IntervalRat.scale (723 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (30131481579 / 1000000000000) (30131514933 / 1000000000000), orderedInterval (-26871013585 / 1000000000000) (-26870980231 / 1000000000000)))) (orderedInterval (2084500514 / 1000000000000) (2084503360 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (661439597815899 / 4000000000000) 1 (IntervalRat.scale (723 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (21850107983 / 1000000000000) (21850108670 / 1000000000000), orderedInterval (-58139213365 / 1000000000000) (-58139212678 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2688715243093179 / 4000000000000) 1 (IntervalRat.scale (723 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (18946233664 / 1000000000000) (18946233665 / 1000000000000), orderedInterval (24237486887 / 1000000000000) (24237486888 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1795937176395861 / 4000000000000) 1 (IntervalRat.scale (723 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-18764457720 / 1000000000000) (-18764457719 / 1000000000000), orderedInterval (-32625796643 / 1000000000000) (-32625796642 / 1000000000000)))) (orderedInterval (3773981228 / 1000000000000) (3773981371 / 1000000000000))) = true
  rfl'

theorem compactCertificate490_chunkChecks1 :
    compactCertificate490.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate490.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate490_chunkChecks1_0
    compactCertificate490_chunkChecks1_1 compactCertificate490_chunkChecks1_2

theorem compactCertificate490_chunkChecks2_0 :
    compactCertificate490.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (723 / 2) 2 (IntervalRat.scale (723 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-35355159366 / 1000000000000) (-35355159365 / 1000000000000), orderedInterval (-22557791951 / 1000000000000) (-22557791950 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1065117055332423 / 4000000000000) 2 (IntervalRat.scale (723 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-1408834103 / 1000000000000) (-1408834101 / 1000000000000), orderedInterval (-48872878098 / 1000000000000) (-48872878096 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (344436971483559 / 800000000000) 2 (IntervalRat.scale (723 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-30896449307 / 1000000000000) (-30896449306 / 1000000000000), orderedInterval (-22856082555 / 1000000000000) (-22856082554 / 1000000000000)))) (orderedInterval (16622508036 / 1000000000000) (16622508070 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (310798500306261 / 4000000000000) 2 (IntervalRat.scale (723 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (5102560606 / 1000000000000) (5102560625 / 1000000000000), orderedInterval (-90406926313 / 1000000000000) (-90406926294 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (834848489248017 / 4000000000000) 2 (IntervalRat.scale (723 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (46166206171 / 1000000000000) (46166255152 / 1000000000000), orderedInterval (-30424060043 / 1000000000000) (-30424011062 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2266776049467789 / 4000000000000) 2 (IntervalRat.scale (723 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30580511355 / 1000000000000) (30580570697 / 1000000000000), orderedInterval (-13746435367 / 1000000000000) (-13746376025 / 1000000000000)))) (orderedInterval (4779982758 / 1000000000000) (4779993811 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1669696978496757 / 4000000000000) 2 (IntervalRat.scale (723 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-14395474451 / 1000000000000) (-14395474450 / 1000000000000), orderedInterval (-36285451229 / 1000000000000) (-36285451228 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2861054231727561 / 4000000000000) 2 (IntervalRat.scale (723 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-6927521581 / 1000000000000) (-6927521579 / 1000000000000), orderedInterval (29023093088 / 1000000000000) (29023093090 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2107439597815899 / 4000000000000) 2 (IntervalRat.scale (723 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-4936883864 / 1000000000000) (-4936883862 / 1000000000000), orderedInterval (34413348150 / 1000000000000) (34413348153 / 1000000000000)))) (orderedInterval (-581514413 / 1000000000000) (-581514350 / 1000000000000))) = true
  rfl'

theorem compactCertificate490_chunkChecks2_1 :
    compactCertificate490.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3233354295464277 / 4000000000000) 2 (IntervalRat.scale (723 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-27688385094 / 1000000000000) (-27688367842 / 1000000000000), orderedInterval (4590891098 / 1000000000000) (4590908350 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1866777972871533 / 4000000000000) 2 (IntervalRat.scale (723 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (21390075276 / 1000000000000) (21390077629 / 1000000000000), orderedInterval (-30132198211 / 1000000000000) (-30132195857 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3312630271684497 / 4000000000000) 2 (IntervalRat.scale (723 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-11750399779 / 1000000000000) (-11750399760 / 1000000000000), orderedInterval (25119767739 / 1000000000000) (25119767759 / 1000000000000)))) (orderedInterval (-18483938582 / 1000000000000) (-18483922293 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3095088902904693 / 4000000000000) 2 (IntervalRat.scale (723 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (28340268115 / 1000000000000) (28340281490 / 1000000000000), orderedInterval (-4442902890 / 1000000000000) (-4442889515 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2208801484968069 / 4000000000000) 2 (IntervalRat.scale (723 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (2213456090 / 1000000000000) (2213456091 / 1000000000000), orderedInterval (33879838785 / 1000000000000) (33879838786 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2504545467744051 / 4000000000000) 2 (IntervalRat.scale (723 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-31405858849 / 1000000000000) (-31405851184 / 1000000000000), orderedInterval (5540051710 / 1000000000000) (5540059375 / 1000000000000)))) (orderedInterval (1364975094 / 1000000000000) (1364976435 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2088028899014019 / 4000000000000) 2 (IntervalRat.scale (723 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (33535089166 / 1000000000000) (33535089177 / 1000000000000), orderedInterval (9712546537 / 1000000000000) (9712546548 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1844836855842399 / 4000000000000) 2 (IntervalRat.scale (723 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-6659519377 / 1000000000000) (-6659519376 / 1000000000000), orderedInterval (-36543828035 / 1000000000000) (-36543828034 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (534705626793501 / 800000000000) 2 (IntervalRat.scale (723 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-247186162 / 1000000000000) (-247186161 / 1000000000000), orderedInterval (-30861086091 / 1000000000000) (-30861086090 / 1000000000000)))) (orderedInterval (-1409956265 / 1000000000000) (-1409956190 / 1000000000000))) = true
  rfl'

theorem compactCertificate490_chunkChecks2_2 :
    compactCertificate490.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1479023903726247 / 4000000000000) 2 (IntervalRat.scale (723 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-6893074316 / 1000000000000) (-6893074306 / 1000000000000), orderedInterval (40926512049 / 1000000000000) (40926512060 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1253784942929967 / 4000000000000) 2 (IntervalRat.scale (723 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (3240658363 / 1000000000000) (3240658364 / 1000000000000), orderedInterval (44945181955 / 1000000000000) (44945181956 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (784560402184101 / 4000000000000) 2 (IntervalRat.scale (723 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (47799922175 / 1000000000000) (47799966203 / 1000000000000), orderedInterval (-31120274459 / 1000000000000) (-31120230430 / 1000000000000)))) (orderedInterval (-1447136679 / 1000000000000) (-1447136172 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (421939193624667 / 4000000000000) 2 (IntervalRat.scale (723 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-40283031366 / 1000000000000) (-40283023792 / 1000000000000), orderedInterval (66617504505 / 1000000000000) (66617512080 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1145646989555001 / 4000000000000) 2 (IntervalRat.scale (723 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-45573237734 / 1000000000000) (-45573237731 / 1000000000000), orderedInterval (-11996048503 / 1000000000000) (-11996048501 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1564283019863577 / 4000000000000) 2 (IntervalRat.scale (723 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (30131481579 / 1000000000000) (30131514933 / 1000000000000), orderedInterval (-26871013585 / 1000000000000) (-26870980231 / 1000000000000)))) (orderedInterval (1984379943 / 1000000000000) (1984382993 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (661439597815899 / 4000000000000) 2 (IntervalRat.scale (723 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (21850107983 / 1000000000000) (21850108670 / 1000000000000), orderedInterval (-58139213365 / 1000000000000) (-58139212678 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2688715243093179 / 4000000000000) 2 (IntervalRat.scale (723 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (18946233664 / 1000000000000) (18946233665 / 1000000000000), orderedInterval (24237486887 / 1000000000000) (24237486888 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1795937176395861 / 4000000000000) 2 (IntervalRat.scale (723 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-18764457720 / 1000000000000) (-18764457719 / 1000000000000), orderedInterval (-32625796643 / 1000000000000) (-32625796642 / 1000000000000)))) (orderedInterval (-136711238 / 1000000000000) (-136711029 / 1000000000000))) = true
  rfl'

theorem compactCertificate490_chunkChecks2 :
    compactCertificate490.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate490.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate490_chunkChecks2_0
    compactCertificate490_chunkChecks2_1 compactCertificate490_chunkChecks2_2

theorem compactCertificate490_chunkChecks3_0 :
    compactCertificate490.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (723 / 2) 3 (IntervalRat.scale (723 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-35355159366 / 1000000000000) (-35355159365 / 1000000000000), orderedInterval (-22557791951 / 1000000000000) (-22557791950 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1065117055332423 / 4000000000000) 3 (IntervalRat.scale (723 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-1408834103 / 1000000000000) (-1408834101 / 1000000000000), orderedInterval (-48872878098 / 1000000000000) (-48872878096 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (344436971483559 / 800000000000) 3 (IntervalRat.scale (723 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-30896449307 / 1000000000000) (-30896449306 / 1000000000000), orderedInterval (-22856082555 / 1000000000000) (-22856082554 / 1000000000000)))) (orderedInterval (11342926415 / 1000000000000) (11342926454 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (310798500306261 / 4000000000000) 3 (IntervalRat.scale (723 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (5102560606 / 1000000000000) (5102560625 / 1000000000000), orderedInterval (-90406926313 / 1000000000000) (-90406926294 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (834848489248017 / 4000000000000) 3 (IntervalRat.scale (723 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (46166206171 / 1000000000000) (46166255152 / 1000000000000), orderedInterval (-30424060043 / 1000000000000) (-30424011062 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2266776049467789 / 4000000000000) 3 (IntervalRat.scale (723 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30580511355 / 1000000000000) (30580570697 / 1000000000000), orderedInterval (-13746435367 / 1000000000000) (-13746376025 / 1000000000000)))) (orderedInterval (-3573761077 / 1000000000000) (-3573744348 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1669696978496757 / 4000000000000) 3 (IntervalRat.scale (723 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-14395474451 / 1000000000000) (-14395474450 / 1000000000000), orderedInterval (-36285451229 / 1000000000000) (-36285451228 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2861054231727561 / 4000000000000) 3 (IntervalRat.scale (723 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-6927521581 / 1000000000000) (-6927521579 / 1000000000000), orderedInterval (29023093088 / 1000000000000) (29023093090 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2107439597815899 / 4000000000000) 3 (IntervalRat.scale (723 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-4936883864 / 1000000000000) (-4936883862 / 1000000000000), orderedInterval (34413348150 / 1000000000000) (34413348153 / 1000000000000)))) (orderedInterval (4360955475 / 1000000000000) (4360955590 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate490_chunkChecks3_1 :
    compactCertificate490.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3233354295464277 / 4000000000000) 3 (IntervalRat.scale (723 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-27688385094 / 1000000000000) (-27688367842 / 1000000000000), orderedInterval (4590891098 / 1000000000000) (4590908350 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1866777972871533 / 4000000000000) 3 (IntervalRat.scale (723 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (21390075276 / 1000000000000) (21390077629 / 1000000000000), orderedInterval (-30132198211 / 1000000000000) (-30132195857 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3312630271684497 / 4000000000000) 3 (IntervalRat.scale (723 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-11750399779 / 1000000000000) (-11750399760 / 1000000000000), orderedInterval (25119767739 / 1000000000000) (25119767759 / 1000000000000)))) (orderedInterval (-28958171450 / 1000000000000) (-28958135329 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3095088902904693 / 4000000000000) 3 (IntervalRat.scale (723 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (28340268115 / 1000000000000) (28340281490 / 1000000000000), orderedInterval (-4442902890 / 1000000000000) (-4442889515 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2208801484968069 / 4000000000000) 3 (IntervalRat.scale (723 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (2213456090 / 1000000000000) (2213456091 / 1000000000000), orderedInterval (33879838785 / 1000000000000) (33879838786 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2504545467744051 / 4000000000000) 3 (IntervalRat.scale (723 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-31405858849 / 1000000000000) (-31405851184 / 1000000000000), orderedInterval (5540051710 / 1000000000000) (5540059375 / 1000000000000)))) (orderedInterval (-12063596131 / 1000000000000) (-12063593362 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2088028899014019 / 4000000000000) 3 (IntervalRat.scale (723 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (33535089166 / 1000000000000) (33535089177 / 1000000000000), orderedInterval (9712546537 / 1000000000000) (9712546548 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1844836855842399 / 4000000000000) 3 (IntervalRat.scale (723 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-6659519377 / 1000000000000) (-6659519376 / 1000000000000), orderedInterval (-36543828035 / 1000000000000) (-36543828034 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (534705626793501 / 800000000000) 3 (IntervalRat.scale (723 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-247186162 / 1000000000000) (-247186161 / 1000000000000), orderedInterval (-30861086091 / 1000000000000) (-30861086090 / 1000000000000)))) (orderedInterval (317511214 / 1000000000000) (317511329 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate490_chunkChecks3_2 :
    compactCertificate490.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1479023903726247 / 4000000000000) 3 (IntervalRat.scale (723 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-6893074316 / 1000000000000) (-6893074306 / 1000000000000), orderedInterval (40926512049 / 1000000000000) (40926512060 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1253784942929967 / 4000000000000) 3 (IntervalRat.scale (723 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (3240658363 / 1000000000000) (3240658364 / 1000000000000), orderedInterval (44945181955 / 1000000000000) (44945181956 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (784560402184101 / 4000000000000) 3 (IntervalRat.scale (723 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (47799922175 / 1000000000000) (47799966203 / 1000000000000), orderedInterval (-31120274459 / 1000000000000) (-31120230430 / 1000000000000)))) (orderedInterval (8826558724 / 1000000000000) (8826559034 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (421939193624667 / 4000000000000) 3 (IntervalRat.scale (723 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-40283031366 / 1000000000000) (-40283023792 / 1000000000000), orderedInterval (66617504505 / 1000000000000) (66617512080 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1145646989555001 / 4000000000000) 3 (IntervalRat.scale (723 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-45573237734 / 1000000000000) (-45573237731 / 1000000000000), orderedInterval (-11996048503 / 1000000000000) (-11996048501 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1564283019863577 / 4000000000000) 3 (IntervalRat.scale (723 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (30131481579 / 1000000000000) (30131514933 / 1000000000000), orderedInterval (-26871013585 / 1000000000000) (-26870980231 / 1000000000000)))) (orderedInterval (-2717461193 / 1000000000000) (-2717457905 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (661439597815899 / 4000000000000) 3 (IntervalRat.scale (723 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (21850107983 / 1000000000000) (21850108670 / 1000000000000), orderedInterval (-58139213365 / 1000000000000) (-58139212678 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2688715243093179 / 4000000000000) 3 (IntervalRat.scale (723 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (18946233664 / 1000000000000) (18946233665 / 1000000000000), orderedInterval (24237486887 / 1000000000000) (24237486888 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1795937176395861 / 4000000000000) 3 (IntervalRat.scale (723 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-18764457720 / 1000000000000) (-18764457719 / 1000000000000), orderedInterval (-32625796643 / 1000000000000) (-32625796642 / 1000000000000)))) (orderedInterval (989801338 / 1000000000000) (989801660 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate490_chunkChecks3 :
    compactCertificate490.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate490.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate490_chunkChecks3_0
    compactCertificate490_chunkChecks3_1 compactCertificate490_chunkChecks3_2

theorem compactCertificate490_chunkChecks4_0 :
    compactCertificate490.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (723 / 2) 4 (IntervalRat.scale (723 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-35355159366 / 1000000000000) (-35355159365 / 1000000000000), orderedInterval (-22557791951 / 1000000000000) (-22557791950 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1065117055332423 / 4000000000000) 4 (IntervalRat.scale (723 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-1408834103 / 1000000000000) (-1408834101 / 1000000000000), orderedInterval (-48872878098 / 1000000000000) (-48872878096 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (344436971483559 / 800000000000) 4 (IntervalRat.scale (723 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-30896449307 / 1000000000000) (-30896449306 / 1000000000000), orderedInterval (-22856082555 / 1000000000000) (-22856082554 / 1000000000000)))) (orderedInterval (-17728024139 / 1000000000000) (-17728024094 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (310798500306261 / 4000000000000) 4 (IntervalRat.scale (723 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (5102560606 / 1000000000000) (5102560625 / 1000000000000), orderedInterval (-90406926313 / 1000000000000) (-90406926294 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (834848489248017 / 4000000000000) 4 (IntervalRat.scale (723 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (46166206171 / 1000000000000) (46166255152 / 1000000000000), orderedInterval (-30424060043 / 1000000000000) (-30424011062 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2266776049467789 / 4000000000000) 4 (IntervalRat.scale (723 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30580511355 / 1000000000000) (30580570697 / 1000000000000), orderedInterval (-13746435367 / 1000000000000) (-13746376025 / 1000000000000)))) (orderedInterval (-12921462252 / 1000000000000) (-12921436328 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1669696978496757 / 4000000000000) 4 (IntervalRat.scale (723 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-14395474451 / 1000000000000) (-14395474450 / 1000000000000), orderedInterval (-36285451229 / 1000000000000) (-36285451228 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2861054231727561 / 4000000000000) 4 (IntervalRat.scale (723 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-6927521581 / 1000000000000) (-6927521579 / 1000000000000), orderedInterval (29023093088 / 1000000000000) (29023093090 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2107439597815899 / 4000000000000) 4 (IntervalRat.scale (723 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-4936883864 / 1000000000000) (-4936883862 / 1000000000000), orderedInterval (34413348150 / 1000000000000) (34413348153 / 1000000000000)))) (orderedInterval (2712309573 / 1000000000000) (2712309786 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate490_chunkChecks4_1 :
    compactCertificate490.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3233354295464277 / 4000000000000) 4 (IntervalRat.scale (723 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-27688385094 / 1000000000000) (-27688367842 / 1000000000000), orderedInterval (4590891098 / 1000000000000) (4590908350 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1866777972871533 / 4000000000000) 4 (IntervalRat.scale (723 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (21390075276 / 1000000000000) (21390077629 / 1000000000000), orderedInterval (-30132198211 / 1000000000000) (-30132195857 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3312630271684497 / 4000000000000) 4 (IntervalRat.scale (723 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-11750399779 / 1000000000000) (-11750399760 / 1000000000000), orderedInterval (25119767739 / 1000000000000) (25119767759 / 1000000000000)))) (orderedInterval (81551284381 / 1000000000000) (81551364865 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3095088902904693 / 4000000000000) 4 (IntervalRat.scale (723 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (28340268115 / 1000000000000) (28340281490 / 1000000000000), orderedInterval (-4442902890 / 1000000000000) (-4442889515 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2208801484968069 / 4000000000000) 4 (IntervalRat.scale (723 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (2213456090 / 1000000000000) (2213456091 / 1000000000000), orderedInterval (33879838785 / 1000000000000) (33879838786 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2504545467744051 / 4000000000000) 4 (IntervalRat.scale (723 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-31405858849 / 1000000000000) (-31405851184 / 1000000000000), orderedInterval (5540051710 / 1000000000000) (5540059375 / 1000000000000)))) (orderedInterval (-8102556629 / 1000000000000) (-8102550857 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2088028899014019 / 4000000000000) 4 (IntervalRat.scale (723 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (33535089166 / 1000000000000) (33535089177 / 1000000000000), orderedInterval (9712546537 / 1000000000000) (9712546548 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1844836855842399 / 4000000000000) 4 (IntervalRat.scale (723 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-6659519377 / 1000000000000) (-6659519376 / 1000000000000), orderedInterval (-36543828035 / 1000000000000) (-36543828034 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (534705626793501 / 800000000000) 4 (IntervalRat.scale (723 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-247186162 / 1000000000000) (-247186161 / 1000000000000), orderedInterval (-30861086091 / 1000000000000) (-30861086090 / 1000000000000)))) (orderedInterval (2617698093 / 1000000000000) (2617698276 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate490_chunkChecks4_2 :
    compactCertificate490.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1479023903726247 / 4000000000000) 4 (IntervalRat.scale (723 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-6893074316 / 1000000000000) (-6893074306 / 1000000000000), orderedInterval (40926512049 / 1000000000000) (40926512060 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1253784942929967 / 4000000000000) 4 (IntervalRat.scale (723 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (3240658363 / 1000000000000) (3240658364 / 1000000000000), orderedInterval (44945181955 / 1000000000000) (44945181956 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (784560402184101 / 4000000000000) 4 (IntervalRat.scale (723 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (47799922175 / 1000000000000) (47799966203 / 1000000000000), orderedInterval (-31120274459 / 1000000000000) (-31120230430 / 1000000000000)))) (orderedInterval (1188678341 / 1000000000000) (1188678546 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (421939193624667 / 4000000000000) 4 (IntervalRat.scale (723 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-40283031366 / 1000000000000) (-40283023792 / 1000000000000), orderedInterval (66617504505 / 1000000000000) (66617512080 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1145646989555001 / 4000000000000) 4 (IntervalRat.scale (723 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-45573237734 / 1000000000000) (-45573237731 / 1000000000000), orderedInterval (-11996048503 / 1000000000000) (-11996048501 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1564283019863577 / 4000000000000) 4 (IntervalRat.scale (723 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (30131481579 / 1000000000000) (30131514933 / 1000000000000), orderedInterval (-26871013585 / 1000000000000) (-26870980231 / 1000000000000)))) (orderedInterval (-2734865667 / 1000000000000) (-2734862105 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (661439597815899 / 4000000000000) 4 (IntervalRat.scale (723 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (21850107983 / 1000000000000) (21850108670 / 1000000000000), orderedInterval (-58139213365 / 1000000000000) (-58139212678 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2688715243093179 / 4000000000000) 4 (IntervalRat.scale (723 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (18946233664 / 1000000000000) (18946233665 / 1000000000000), orderedInterval (24237486887 / 1000000000000) (24237486888 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1795937176395861 / 4000000000000) 4 (IntervalRat.scale (723 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-18764457720 / 1000000000000) (-18764457719 / 1000000000000), orderedInterval (-32625796643 / 1000000000000) (-32625796642 / 1000000000000)))) (orderedInterval (-10057907683 / 1000000000000) (-10057907167 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate490_chunkChecks4 :
    compactCertificate490.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate490.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate490_chunkChecks4_0
    compactCertificate490_chunkChecks4_1 compactCertificate490_chunkChecks4_2

theorem compactCertificate490_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate490.chunkCheck r b = true :=
  compactCertificate490.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate490_chunkChecks0
    · exact compactCertificate490_chunkChecks1
    · exact compactCertificate490_chunkChecks2
    · exact compactCertificate490_chunkChecks3
    · exact compactCertificate490_chunkChecks4)

theorem compactCertificate490_coefficient0 :
    compactCertificate490.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate490_coefficient1 :
    compactCertificate490.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate490_coefficient2 :
    compactCertificate490.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate490_coefficient3 :
    compactCertificate490.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate490_coefficient4 :
    compactCertificate490.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate490_coefficients : ∀ r : Fin 5,
    compactCertificate490.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate490_coefficient0
  · exact compactCertificate490_coefficient1
  · exact compactCertificate490_coefficient2
  · exact compactCertificate490_coefficient3
  · exact compactCertificate490_coefficient4

theorem compactCertificate490_lower : (1 : ℚ) ≤ compactCertificate490.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate490, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate490_proves {t : ℝ} (ht : t ∈ compactCertificate490.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate490.proves compactCertificate490_states compactCertificate490_chunks
    compactCertificate490_coefficients compactCertificate490_lower ht

end Erdos232
