/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate548 : CompactCertificate where
  left := 419
  right := 420
  center := 839 / 2
  grid := fun i =>
    match i.val with
    | 0 => 134
    | 1 => 98
    | 2 => 159
    | 3 => 29
    | 4 => 77
    | 5 => 209
    | 6 => 154
    | 7 => 264
    | 8 => 195
    | 9 => 299
    | 10 => 172
    | 11 => 306
    | 12 => 286
    | 13 => 204
    | 14 => 231
    | 15 => 193
    | 16 => 170
    | 17 => 247
    | 18 => 137
    | 19 => 116
    | 20 => 72
    | 21 => 39
    | 22 => 106
    | 23 => 145
    | 24 => 61
    | 25 => 248
    | _ => 166
  point := fun i =>
    match i.val with
    | 0 => 839 / 2
    | 1 => 1236007205288939 / 4000000000000
    | 2 => 399699334819787 / 800000000000
    | 3 => 360663819857473 / 4000000000000
    | 4 => 968793751699981 / 4000000000000
    | 5 => 2630463493089177 / 4000000000000
    | 6 => 1937587503400801 / 4000000000000
    | 7 => 3320089212198373 / 4000000000000
    | 8 => 2445562686815407 / 4000000000000
    | 9 => 3752122066244161 / 4000000000000
    | 10 => 2166288684978169 / 4000000000000
    | 11 => 3844117286228621 / 4000000000000
    | 12 => 3591673014574049 / 4000000000000
    | 13 => 2563187338711217 / 4000000000000
    | 14 => 2906381255099943 / 4000000000000
    | 15 => 2423037685024567 / 4000000000000
    | 16 => 2140827278079907 / 4000000000000
    | 17 => 620495187938793 / 800000000000
    | 18 => 1716322344711371 / 4000000000000
    | 19 => 1454945459361331 / 4000000000000
    | 20 => 910437313184593 / 4000000000000
    | 21 => 489636215008431 / 4000000000000
    | 22 => 1329457571558293 / 4000000000000
    | 23 => 1815260655139061 / 4000000000000
    | 24 => 767562686815407 / 4000000000000
    | 25 => 3120099708098447 / 4000000000000
    | _ => 2084082006910273 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-24746272277 / 1000000000000) (-24746265796 / 1000000000000), orderedInterval (30115873296 / 1000000000000) (30115879777 / 1000000000000))
    | 1 => (orderedInterval (42792772606 / 1000000000000) (42792780706 / 1000000000000), orderedInterval (-15202730383 / 1000000000000) (-15202722284 / 1000000000000))
    | 2 => (orderedInterval (-27874459352 / 1000000000000) (-27874459351 / 1000000000000), orderedInterval (-22270348644 / 1000000000000) (-22270348643 / 1000000000000))
    | 3 => (orderedInterval (13073273474 / 1000000000000) (13073273550 / 1000000000000), orderedInterval (-83076870416 / 1000000000000) (-83076870340 / 1000000000000))
    | 4 => (orderedInterval (-45233557362 / 1000000000000) (-45233557361 / 1000000000000), orderedInterval (-24040144323 / 1000000000000) (-24040144322 / 1000000000000))
    | 5 => (orderedInterval (-30241056827 / 1000000000000) (-30241040015 / 1000000000000), orderedInterval (7340847569 / 1000000000000) (7340864382 / 1000000000000))
    | 6 => (orderedInterval (35572202674 / 1000000000000) (35572202707 / 1000000000000), orderedInterval (6954002990 / 1000000000000) (6954003022 / 1000000000000))
    | 7 => (orderedInterval (27409126854 / 1000000000000) (27409127560 / 1000000000000), orderedInterval (3949692787 / 1000000000000) (3949693492 / 1000000000000))
    | 8 => (orderedInterval (13589617962 / 1000000000000) (13589618057 / 1000000000000), orderedInterval (-29278631781 / 1000000000000) (-29278631687 / 1000000000000))
    | 9 => (orderedInterval (12953975924 / 1000000000000) (12953975953 / 1000000000000), orderedInterval (-22609373650 / 1000000000000) (-22609373621 / 1000000000000))
    | 10 => (orderedInterval (31127058943 / 1000000000000) (31127117342 / 1000000000000), orderedInterval (-14402600864 / 1000000000000) (-14402542466 / 1000000000000))
    | 11 => (orderedInterval (12050105947 / 1000000000000) (12050105948 / 1000000000000), orderedInterval (22736428871 / 1000000000000) (22736428872 / 1000000000000))
    | 12 => (orderedInterval (5498915026 / 1000000000000) (5498915027 / 1000000000000), orderedInterval (26049908606 / 1000000000000) (26049908607 / 1000000000000))
    | 13 => (orderedInterval (20236326266 / 1000000000000) (20236326267 / 1000000000000), orderedInterval (24149735243 / 1000000000000) (24149735244 / 1000000000000))
    | 14 => (orderedInterval (-29446773116 / 1000000000000) (-29446766941 / 1000000000000), orderedInterval (3029548571 / 1000000000000) (3029554746 / 1000000000000))
    | 15 => (orderedInterval (-6986995873 / 1000000000000) (-6986995872 / 1000000000000), orderedInterval (-31650624166 / 1000000000000) (-31650624165 / 1000000000000))
    | 16 => (orderedInterval (32392735528 / 1000000000000) (32392762684 / 1000000000000), orderedInterval (-11870589997 / 1000000000000) (-11870562841 / 1000000000000))
    | 17 => (orderedInterval (-11964884897 / 1000000000000) (-11964884896 / 1000000000000), orderedInterval (-26023632443 / 1000000000000) (-26023632442 / 1000000000000))
    | 18 => (orderedInterval (19555477058 / 1000000000000) (19555478160 / 1000000000000), orderedInterval (-33208135098 / 1000000000000) (-33208133996 / 1000000000000))
    | 19 => (orderedInterval (4038019847 / 1000000000000) (4038019848 / 1000000000000), orderedInterval (41634803188 / 1000000000000) (41634803189 / 1000000000000))
    | 20 => (orderedInterval (42773835194 / 1000000000000) (42773915595 / 1000000000000), orderedInterval (-31196701104 / 1000000000000) (-31196620702 / 1000000000000))
    | 21 => (orderedInterval (-44857432555 / 1000000000000) (-44857432554 / 1000000000000), orderedInterval (-56284268729 / 1000000000000) (-56284268728 / 1000000000000))
    | 22 => (orderedInterval (6132911183 / 1000000000000) (6132911185 / 1000000000000), orderedInterval (43324555163 / 1000000000000) (43324555164 / 1000000000000))
    | 23 => (orderedInterval (30038507797 / 1000000000000) (30038562572 / 1000000000000), orderedInterval (-22405056355 / 1000000000000) (-22405001581 / 1000000000000))
    | 24 => (orderedInterval (-49622712793 / 1000000000000) (-49622712792 / 1000000000000), orderedInterval (-29114470210 / 1000000000000) (-29114470209 / 1000000000000))
    | 25 => (orderedInterval (28347650893 / 1000000000000) (28347661112 / 1000000000000), orderedInterval (-3562656569 / 1000000000000) (-3562646350 / 1000000000000))
    | _ => (orderedInterval (10372704687 / 1000000000000) (10372704688 / 1000000000000), orderedInterval (33370853574 / 1000000000000) (33370853575 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-11045515482 / 1000000000000) (-11045512808 / 1000000000000)
      | 1 => orderedInterval (356432747 / 1000000000000) (356433993 / 1000000000000)
      | 2 => orderedInterval (-516972916 / 1000000000000) (-516972868 / 1000000000000)
      | 3 => orderedInterval (1717487279 / 1000000000000) (1717491777 / 1000000000000)
      | 4 => orderedInterval (1963350200 / 1000000000000) (1963350282 / 1000000000000)
      | 5 => orderedInterval (-2240762025 / 1000000000000) (-2240760430 / 1000000000000)
      | 6 => orderedInterval (-1962811159 / 1000000000000) (-1962808260 / 1000000000000)
      | 7 => orderedInterval (-1612960286 / 1000000000000) (-1612956038 / 1000000000000)
      | _ => orderedInterval (-4552886592 / 1000000000000) (-4552885643 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (10276075152 / 1000000000000) (10276077810 / 1000000000000)
      | 1 => orderedInterval (-1131116358 / 1000000000000) (-1131114426 / 1000000000000)
      | 2 => orderedInterval (-1272326843 / 1000000000000) (-1272326755 / 1000000000000)
      | 3 => orderedInterval (15010001930 / 1000000000000) (15010007872 / 1000000000000)
      | 4 => orderedInterval (2455193248 / 1000000000000) (2455193384 / 1000000000000)
      | 5 => orderedInterval (-893033839 / 1000000000000) (-893031798 / 1000000000000)
      | 6 => orderedInterval (2836669917 / 1000000000000) (2836671615 / 1000000000000)
      | 7 => orderedInterval (1382078936 / 1000000000000) (1382083523 / 1000000000000)
      | _ => orderedInterval (-7317546627 / 1000000000000) (-7317544917 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (11887922288 / 1000000000000) (11887924942 / 1000000000000)
      | 1 => orderedInterval (-4723272860 / 1000000000000) (-4723269839 / 1000000000000)
      | 2 => orderedInterval (2615053455 / 1000000000000) (2615053619 / 1000000000000)
      | 3 => orderedInterval (-1360839057 / 1000000000000) (-1360831067 / 1000000000000)
      | 4 => orderedInterval (-4463165479 / 1000000000000) (-4463165250 / 1000000000000)
      | 5 => orderedInterval (4234959666 / 1000000000000) (4234962287 / 1000000000000)
      | 6 => orderedInterval (3026352546 / 1000000000000) (3026353598 / 1000000000000)
      | 7 => orderedInterval (2707666365 / 1000000000000) (2707671334 / 1000000000000)
      | _ => orderedInterval (11060365681 / 1000000000000) (11060368802 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-9700743833 / 1000000000000) (-9700741183 / 1000000000000)
      | 1 => orderedInterval (2181584034 / 1000000000000) (2181588765 / 1000000000000)
      | 2 => orderedInterval (3127947932 / 1000000000000) (3127948241 / 1000000000000)
      | 3 => orderedInterval (-81476507845 / 1000000000000) (-81476496840 / 1000000000000)
      | 4 => orderedInterval (-3437373785 / 1000000000000) (-3437373394 / 1000000000000)
      | 5 => orderedInterval (3891039112 / 1000000000000) (3891042479 / 1000000000000)
      | 6 => orderedInterval (-3990711013 / 1000000000000) (-3990710313 / 1000000000000)
      | 7 => orderedInterval (-1717323689 / 1000000000000) (-1717318316 / 1000000000000)
      | _ => orderedInterval (10121822819 / 1000000000000) (10121828546 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-12936029059 / 1000000000000) (-12936026404 / 1000000000000)
      | 1 => orderedInterval (12788442653 / 1000000000000) (12788450075 / 1000000000000)
      | 2 => orderedInterval (-11489857461 / 1000000000000) (-11489856871 / 1000000000000)
      | 3 => orderedInterval (-3567626119 / 1000000000000) (-3567610329 / 1000000000000)
      | 4 => orderedInterval (9692276444 / 1000000000000) (9692277122 / 1000000000000)
      | 5 => orderedInterval (-8860710536 / 1000000000000) (-8860706192 / 1000000000000)
      | 6 => orderedInterval (-3411806749 / 1000000000000) (-3411806238 / 1000000000000)
      | 7 => orderedInterval (-3193561246 / 1000000000000) (-3193555422 / 1000000000000)
      | _ => orderedInterval (-32276317440 / 1000000000000) (-32276306874 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-17894638234 / 1000000000000) (-17894619995 / 1000000000000)
    | 1 => orderedInterval (21345995516 / 1000000000000) (21346016308 / 1000000000000)
    | 2 => orderedInterval (24985042605 / 1000000000000) (24985068426 / 1000000000000)
    | 3 => orderedInterval (-81000266268 / 1000000000000) (-81000232015 / 1000000000000)
    | _ => orderedInterval (-53255189513 / 1000000000000) (-53255141133 / 1000000000000)

theorem compactCertificate548_stateChecks0 :
    compactCertificate548.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 134 12 (839 / 2)) (orderedInterval (-24746272277 / 1000000000000) (-24746265796 / 1000000000000), orderedInterval (30115873296 / 1000000000000) (30115879777 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 98 12 (1236007205288939 / 4000000000000)) (orderedInterval (42792772606 / 1000000000000) (42792780706 / 1000000000000), orderedInterval (-15202730383 / 1000000000000) (-15202722284 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 159 12 (399699334819787 / 800000000000)) (orderedInterval (-27874459352 / 1000000000000) (-27874459351 / 1000000000000), orderedInterval (-22270348644 / 1000000000000) (-22270348643 / 1000000000000))) = true
  rfl'

theorem compactCertificate548_stateChecks1 :
    compactCertificate548.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (360663819857473 / 4000000000000)) (orderedInterval (13073273474 / 1000000000000) (13073273550 / 1000000000000), orderedInterval (-83076870416 / 1000000000000) (-83076870340 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (968793751699981 / 4000000000000)) (orderedInterval (-45233557362 / 1000000000000) (-45233557361 / 1000000000000), orderedInterval (-24040144323 / 1000000000000) (-24040144322 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 209 12 (2630463493089177 / 4000000000000)) (orderedInterval (-30241056827 / 1000000000000) (-30241040015 / 1000000000000), orderedInterval (7340847569 / 1000000000000) (7340864382 / 1000000000000))) = true
  rfl'

theorem compactCertificate548_stateChecks2 :
    compactCertificate548.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 154 12 (1937587503400801 / 4000000000000)) (orderedInterval (35572202674 / 1000000000000) (35572202707 / 1000000000000), orderedInterval (6954002990 / 1000000000000) (6954003022 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 264 12 (3320089212198373 / 4000000000000)) (orderedInterval (27409126854 / 1000000000000) (27409127560 / 1000000000000), orderedInterval (3949692787 / 1000000000000) (3949693492 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 195 12 (2445562686815407 / 4000000000000)) (orderedInterval (13589617962 / 1000000000000) (13589618057 / 1000000000000), orderedInterval (-29278631781 / 1000000000000) (-29278631687 / 1000000000000))) = true
  rfl'

theorem compactCertificate548_stateChecks3 :
    compactCertificate548.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 299 12 (3752122066244161 / 4000000000000)) (orderedInterval (12953975924 / 1000000000000) (12953975953 / 1000000000000), orderedInterval (-22609373650 / 1000000000000) (-22609373621 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 172 12 (2166288684978169 / 4000000000000)) (orderedInterval (31127058943 / 1000000000000) (31127117342 / 1000000000000), orderedInterval (-14402600864 / 1000000000000) (-14402542466 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 306 12 (3844117286228621 / 4000000000000)) (orderedInterval (12050105947 / 1000000000000) (12050105948 / 1000000000000), orderedInterval (22736428871 / 1000000000000) (22736428872 / 1000000000000))) = true
  rfl'

theorem compactCertificate548_stateChecks4 :
    compactCertificate548.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 286 12 (3591673014574049 / 4000000000000)) (orderedInterval (5498915026 / 1000000000000) (5498915027 / 1000000000000), orderedInterval (26049908606 / 1000000000000) (26049908607 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 204 12 (2563187338711217 / 4000000000000)) (orderedInterval (20236326266 / 1000000000000) (20236326267 / 1000000000000), orderedInterval (24149735243 / 1000000000000) (24149735244 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 231 12 (2906381255099943 / 4000000000000)) (orderedInterval (-29446773116 / 1000000000000) (-29446766941 / 1000000000000), orderedInterval (3029548571 / 1000000000000) (3029554746 / 1000000000000))) = true
  rfl'

theorem compactCertificate548_stateChecks5 :
    compactCertificate548.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 193 12 (2423037685024567 / 4000000000000)) (orderedInterval (-6986995873 / 1000000000000) (-6986995872 / 1000000000000), orderedInterval (-31650624166 / 1000000000000) (-31650624165 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 170 12 (2140827278079907 / 4000000000000)) (orderedInterval (32392735528 / 1000000000000) (32392762684 / 1000000000000), orderedInterval (-11870589997 / 1000000000000) (-11870562841 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 247 12 (620495187938793 / 800000000000)) (orderedInterval (-11964884897 / 1000000000000) (-11964884896 / 1000000000000), orderedInterval (-26023632443 / 1000000000000) (-26023632442 / 1000000000000))) = true
  rfl'

theorem compactCertificate548_stateChecks6 :
    compactCertificate548.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 137 12 (1716322344711371 / 4000000000000)) (orderedInterval (19555477058 / 1000000000000) (19555478160 / 1000000000000), orderedInterval (-33208135098 / 1000000000000) (-33208133996 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 116 12 (1454945459361331 / 4000000000000)) (orderedInterval (4038019847 / 1000000000000) (4038019848 / 1000000000000), orderedInterval (41634803188 / 1000000000000) (41634803189 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (910437313184593 / 4000000000000)) (orderedInterval (42773835194 / 1000000000000) (42773915595 / 1000000000000), orderedInterval (-31196701104 / 1000000000000) (-31196620702 / 1000000000000))) = true
  rfl'

theorem compactCertificate548_stateChecks7 :
    compactCertificate548.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (489636215008431 / 4000000000000)) (orderedInterval (-44857432555 / 1000000000000) (-44857432554 / 1000000000000), orderedInterval (-56284268729 / 1000000000000) (-56284268728 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 106 12 (1329457571558293 / 4000000000000)) (orderedInterval (6132911183 / 1000000000000) (6132911185 / 1000000000000), orderedInterval (43324555163 / 1000000000000) (43324555164 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 145 12 (1815260655139061 / 4000000000000)) (orderedInterval (30038507797 / 1000000000000) (30038562572 / 1000000000000), orderedInterval (-22405056355 / 1000000000000) (-22405001581 / 1000000000000))) = true
  rfl'

theorem compactCertificate548_stateChecks8 :
    compactCertificate548.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (767562686815407 / 4000000000000)) (orderedInterval (-49622712793 / 1000000000000) (-49622712792 / 1000000000000), orderedInterval (-29114470210 / 1000000000000) (-29114470209 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 248 12 (3120099708098447 / 4000000000000)) (orderedInterval (28347650893 / 1000000000000) (28347661112 / 1000000000000), orderedInterval (-3562656569 / 1000000000000) (-3562646350 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 166 12 (2084082006910273 / 4000000000000)) (orderedInterval (10372704687 / 1000000000000) (10372704688 / 1000000000000), orderedInterval (33370853574 / 1000000000000) (33370853575 / 1000000000000))) = true
  rfl'

theorem compactCertificate548_states : ∀ j,
    BesselStateValid (compactCertificate548.point j) (compactCertificate548.state j) :=
  compactCertificate548.statesValid_of_checks3 compactCertificate548_stateChecks0
    compactCertificate548_stateChecks1 compactCertificate548_stateChecks2
    compactCertificate548_stateChecks3 compactCertificate548_stateChecks4
    compactCertificate548_stateChecks5 compactCertificate548_stateChecks6
    compactCertificate548_stateChecks7 compactCertificate548_stateChecks8

theorem compactCertificate548_chunkChecks0_0 :
    compactCertificate548.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (839 / 2) 0 (IntervalRat.scale (839 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-24746272277 / 1000000000000) (-24746265796 / 1000000000000), orderedInterval (30115873296 / 1000000000000) (30115879777 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1236007205288939 / 4000000000000) 0 (IntervalRat.scale (839 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42792772606 / 1000000000000) (42792780706 / 1000000000000), orderedInterval (-15202730383 / 1000000000000) (-15202722284 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (399699334819787 / 800000000000) 0 (IntervalRat.scale (839 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-27874459352 / 1000000000000) (-27874459351 / 1000000000000), orderedInterval (-22270348644 / 1000000000000) (-22270348643 / 1000000000000)))) (orderedInterval (-11045515482 / 1000000000000) (-11045512808 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (360663819857473 / 4000000000000) 0 (IntervalRat.scale (839 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (13073273474 / 1000000000000) (13073273550 / 1000000000000), orderedInterval (-83076870416 / 1000000000000) (-83076870340 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (968793751699981 / 4000000000000) 0 (IntervalRat.scale (839 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-45233557362 / 1000000000000) (-45233557361 / 1000000000000), orderedInterval (-24040144323 / 1000000000000) (-24040144322 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2630463493089177 / 4000000000000) 0 (IntervalRat.scale (839 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30241056827 / 1000000000000) (-30241040015 / 1000000000000), orderedInterval (7340847569 / 1000000000000) (7340864382 / 1000000000000)))) (orderedInterval (356432747 / 1000000000000) (356433993 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1937587503400801 / 4000000000000) 0 (IntervalRat.scale (839 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (35572202674 / 1000000000000) (35572202707 / 1000000000000), orderedInterval (6954002990 / 1000000000000) (6954003022 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3320089212198373 / 4000000000000) 0 (IntervalRat.scale (839 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (27409126854 / 1000000000000) (27409127560 / 1000000000000), orderedInterval (3949692787 / 1000000000000) (3949693492 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2445562686815407 / 4000000000000) 0 (IntervalRat.scale (839 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (13589617962 / 1000000000000) (13589618057 / 1000000000000), orderedInterval (-29278631781 / 1000000000000) (-29278631687 / 1000000000000)))) (orderedInterval (-516972916 / 1000000000000) (-516972868 / 1000000000000))) = true
  rfl'

theorem compactCertificate548_chunkChecks0_1 :
    compactCertificate548.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3752122066244161 / 4000000000000) 0 (IntervalRat.scale (839 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (12953975924 / 1000000000000) (12953975953 / 1000000000000), orderedInterval (-22609373650 / 1000000000000) (-22609373621 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2166288684978169 / 4000000000000) 0 (IntervalRat.scale (839 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (31127058943 / 1000000000000) (31127117342 / 1000000000000), orderedInterval (-14402600864 / 1000000000000) (-14402542466 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3844117286228621 / 4000000000000) 0 (IntervalRat.scale (839 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (12050105947 / 1000000000000) (12050105948 / 1000000000000), orderedInterval (22736428871 / 1000000000000) (22736428872 / 1000000000000)))) (orderedInterval (1717487279 / 1000000000000) (1717491777 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3591673014574049 / 4000000000000) 0 (IntervalRat.scale (839 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (5498915026 / 1000000000000) (5498915027 / 1000000000000), orderedInterval (26049908606 / 1000000000000) (26049908607 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2563187338711217 / 4000000000000) 0 (IntervalRat.scale (839 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (20236326266 / 1000000000000) (20236326267 / 1000000000000), orderedInterval (24149735243 / 1000000000000) (24149735244 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2906381255099943 / 4000000000000) 0 (IntervalRat.scale (839 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-29446773116 / 1000000000000) (-29446766941 / 1000000000000), orderedInterval (3029548571 / 1000000000000) (3029554746 / 1000000000000)))) (orderedInterval (1963350200 / 1000000000000) (1963350282 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2423037685024567 / 4000000000000) 0 (IntervalRat.scale (839 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-6986995873 / 1000000000000) (-6986995872 / 1000000000000), orderedInterval (-31650624166 / 1000000000000) (-31650624165 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2140827278079907 / 4000000000000) 0 (IntervalRat.scale (839 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (32392735528 / 1000000000000) (32392762684 / 1000000000000), orderedInterval (-11870589997 / 1000000000000) (-11870562841 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (620495187938793 / 800000000000) 0 (IntervalRat.scale (839 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-11964884897 / 1000000000000) (-11964884896 / 1000000000000), orderedInterval (-26023632443 / 1000000000000) (-26023632442 / 1000000000000)))) (orderedInterval (-2240762025 / 1000000000000) (-2240760430 / 1000000000000))) = true
  rfl'

theorem compactCertificate548_chunkChecks0_2 :
    compactCertificate548.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1716322344711371 / 4000000000000) 0 (IntervalRat.scale (839 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (19555477058 / 1000000000000) (19555478160 / 1000000000000), orderedInterval (-33208135098 / 1000000000000) (-33208133996 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1454945459361331 / 4000000000000) 0 (IntervalRat.scale (839 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (4038019847 / 1000000000000) (4038019848 / 1000000000000), orderedInterval (41634803188 / 1000000000000) (41634803189 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (910437313184593 / 4000000000000) 0 (IntervalRat.scale (839 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (42773835194 / 1000000000000) (42773915595 / 1000000000000), orderedInterval (-31196701104 / 1000000000000) (-31196620702 / 1000000000000)))) (orderedInterval (-1962811159 / 1000000000000) (-1962808260 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (489636215008431 / 4000000000000) 0 (IntervalRat.scale (839 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-44857432555 / 1000000000000) (-44857432554 / 1000000000000), orderedInterval (-56284268729 / 1000000000000) (-56284268728 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1329457571558293 / 4000000000000) 0 (IntervalRat.scale (839 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (6132911183 / 1000000000000) (6132911185 / 1000000000000), orderedInterval (43324555163 / 1000000000000) (43324555164 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1815260655139061 / 4000000000000) 0 (IntervalRat.scale (839 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (30038507797 / 1000000000000) (30038562572 / 1000000000000), orderedInterval (-22405056355 / 1000000000000) (-22405001581 / 1000000000000)))) (orderedInterval (-1612960286 / 1000000000000) (-1612956038 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (767562686815407 / 4000000000000) 0 (IntervalRat.scale (839 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-49622712793 / 1000000000000) (-49622712792 / 1000000000000), orderedInterval (-29114470210 / 1000000000000) (-29114470209 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3120099708098447 / 4000000000000) 0 (IntervalRat.scale (839 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (28347650893 / 1000000000000) (28347661112 / 1000000000000), orderedInterval (-3562656569 / 1000000000000) (-3562646350 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2084082006910273 / 4000000000000) 0 (IntervalRat.scale (839 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (10372704687 / 1000000000000) (10372704688 / 1000000000000), orderedInterval (33370853574 / 1000000000000) (33370853575 / 1000000000000)))) (orderedInterval (-4552886592 / 1000000000000) (-4552885643 / 1000000000000))) = true
  rfl'

theorem compactCertificate548_chunkChecks0 :
    compactCertificate548.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate548.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate548_chunkChecks0_0
    compactCertificate548_chunkChecks0_1 compactCertificate548_chunkChecks0_2

theorem compactCertificate548_chunkChecks1_0 :
    compactCertificate548.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (839 / 2) 1 (IntervalRat.scale (839 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-24746272277 / 1000000000000) (-24746265796 / 1000000000000), orderedInterval (30115873296 / 1000000000000) (30115879777 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1236007205288939 / 4000000000000) 1 (IntervalRat.scale (839 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42792772606 / 1000000000000) (42792780706 / 1000000000000), orderedInterval (-15202730383 / 1000000000000) (-15202722284 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (399699334819787 / 800000000000) 1 (IntervalRat.scale (839 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-27874459352 / 1000000000000) (-27874459351 / 1000000000000), orderedInterval (-22270348644 / 1000000000000) (-22270348643 / 1000000000000)))) (orderedInterval (10276075152 / 1000000000000) (10276077810 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (360663819857473 / 4000000000000) 1 (IntervalRat.scale (839 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (13073273474 / 1000000000000) (13073273550 / 1000000000000), orderedInterval (-83076870416 / 1000000000000) (-83076870340 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (968793751699981 / 4000000000000) 1 (IntervalRat.scale (839 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-45233557362 / 1000000000000) (-45233557361 / 1000000000000), orderedInterval (-24040144323 / 1000000000000) (-24040144322 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2630463493089177 / 4000000000000) 1 (IntervalRat.scale (839 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30241056827 / 1000000000000) (-30241040015 / 1000000000000), orderedInterval (7340847569 / 1000000000000) (7340864382 / 1000000000000)))) (orderedInterval (-1131116358 / 1000000000000) (-1131114426 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1937587503400801 / 4000000000000) 1 (IntervalRat.scale (839 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (35572202674 / 1000000000000) (35572202707 / 1000000000000), orderedInterval (6954002990 / 1000000000000) (6954003022 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3320089212198373 / 4000000000000) 1 (IntervalRat.scale (839 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (27409126854 / 1000000000000) (27409127560 / 1000000000000), orderedInterval (3949692787 / 1000000000000) (3949693492 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2445562686815407 / 4000000000000) 1 (IntervalRat.scale (839 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (13589617962 / 1000000000000) (13589618057 / 1000000000000), orderedInterval (-29278631781 / 1000000000000) (-29278631687 / 1000000000000)))) (orderedInterval (-1272326843 / 1000000000000) (-1272326755 / 1000000000000))) = true
  rfl'

theorem compactCertificate548_chunkChecks1_1 :
    compactCertificate548.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3752122066244161 / 4000000000000) 1 (IntervalRat.scale (839 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (12953975924 / 1000000000000) (12953975953 / 1000000000000), orderedInterval (-22609373650 / 1000000000000) (-22609373621 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2166288684978169 / 4000000000000) 1 (IntervalRat.scale (839 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (31127058943 / 1000000000000) (31127117342 / 1000000000000), orderedInterval (-14402600864 / 1000000000000) (-14402542466 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3844117286228621 / 4000000000000) 1 (IntervalRat.scale (839 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (12050105947 / 1000000000000) (12050105948 / 1000000000000), orderedInterval (22736428871 / 1000000000000) (22736428872 / 1000000000000)))) (orderedInterval (15010001930 / 1000000000000) (15010007872 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3591673014574049 / 4000000000000) 1 (IntervalRat.scale (839 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (5498915026 / 1000000000000) (5498915027 / 1000000000000), orderedInterval (26049908606 / 1000000000000) (26049908607 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2563187338711217 / 4000000000000) 1 (IntervalRat.scale (839 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (20236326266 / 1000000000000) (20236326267 / 1000000000000), orderedInterval (24149735243 / 1000000000000) (24149735244 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2906381255099943 / 4000000000000) 1 (IntervalRat.scale (839 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-29446773116 / 1000000000000) (-29446766941 / 1000000000000), orderedInterval (3029548571 / 1000000000000) (3029554746 / 1000000000000)))) (orderedInterval (2455193248 / 1000000000000) (2455193384 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2423037685024567 / 4000000000000) 1 (IntervalRat.scale (839 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-6986995873 / 1000000000000) (-6986995872 / 1000000000000), orderedInterval (-31650624166 / 1000000000000) (-31650624165 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2140827278079907 / 4000000000000) 1 (IntervalRat.scale (839 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (32392735528 / 1000000000000) (32392762684 / 1000000000000), orderedInterval (-11870589997 / 1000000000000) (-11870562841 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (620495187938793 / 800000000000) 1 (IntervalRat.scale (839 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-11964884897 / 1000000000000) (-11964884896 / 1000000000000), orderedInterval (-26023632443 / 1000000000000) (-26023632442 / 1000000000000)))) (orderedInterval (-893033839 / 1000000000000) (-893031798 / 1000000000000))) = true
  rfl'

theorem compactCertificate548_chunkChecks1_2 :
    compactCertificate548.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1716322344711371 / 4000000000000) 1 (IntervalRat.scale (839 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (19555477058 / 1000000000000) (19555478160 / 1000000000000), orderedInterval (-33208135098 / 1000000000000) (-33208133996 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1454945459361331 / 4000000000000) 1 (IntervalRat.scale (839 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (4038019847 / 1000000000000) (4038019848 / 1000000000000), orderedInterval (41634803188 / 1000000000000) (41634803189 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (910437313184593 / 4000000000000) 1 (IntervalRat.scale (839 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (42773835194 / 1000000000000) (42773915595 / 1000000000000), orderedInterval (-31196701104 / 1000000000000) (-31196620702 / 1000000000000)))) (orderedInterval (2836669917 / 1000000000000) (2836671615 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (489636215008431 / 4000000000000) 1 (IntervalRat.scale (839 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-44857432555 / 1000000000000) (-44857432554 / 1000000000000), orderedInterval (-56284268729 / 1000000000000) (-56284268728 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1329457571558293 / 4000000000000) 1 (IntervalRat.scale (839 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (6132911183 / 1000000000000) (6132911185 / 1000000000000), orderedInterval (43324555163 / 1000000000000) (43324555164 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1815260655139061 / 4000000000000) 1 (IntervalRat.scale (839 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (30038507797 / 1000000000000) (30038562572 / 1000000000000), orderedInterval (-22405056355 / 1000000000000) (-22405001581 / 1000000000000)))) (orderedInterval (1382078936 / 1000000000000) (1382083523 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (767562686815407 / 4000000000000) 1 (IntervalRat.scale (839 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-49622712793 / 1000000000000) (-49622712792 / 1000000000000), orderedInterval (-29114470210 / 1000000000000) (-29114470209 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3120099708098447 / 4000000000000) 1 (IntervalRat.scale (839 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (28347650893 / 1000000000000) (28347661112 / 1000000000000), orderedInterval (-3562656569 / 1000000000000) (-3562646350 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2084082006910273 / 4000000000000) 1 (IntervalRat.scale (839 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (10372704687 / 1000000000000) (10372704688 / 1000000000000), orderedInterval (33370853574 / 1000000000000) (33370853575 / 1000000000000)))) (orderedInterval (-7317546627 / 1000000000000) (-7317544917 / 1000000000000))) = true
  rfl'

theorem compactCertificate548_chunkChecks1 :
    compactCertificate548.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate548.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate548_chunkChecks1_0
    compactCertificate548_chunkChecks1_1 compactCertificate548_chunkChecks1_2

theorem compactCertificate548_chunkChecks2_0 :
    compactCertificate548.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (839 / 2) 2 (IntervalRat.scale (839 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-24746272277 / 1000000000000) (-24746265796 / 1000000000000), orderedInterval (30115873296 / 1000000000000) (30115879777 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1236007205288939 / 4000000000000) 2 (IntervalRat.scale (839 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42792772606 / 1000000000000) (42792780706 / 1000000000000), orderedInterval (-15202730383 / 1000000000000) (-15202722284 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (399699334819787 / 800000000000) 2 (IntervalRat.scale (839 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-27874459352 / 1000000000000) (-27874459351 / 1000000000000), orderedInterval (-22270348644 / 1000000000000) (-22270348643 / 1000000000000)))) (orderedInterval (11887922288 / 1000000000000) (11887924942 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (360663819857473 / 4000000000000) 2 (IntervalRat.scale (839 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (13073273474 / 1000000000000) (13073273550 / 1000000000000), orderedInterval (-83076870416 / 1000000000000) (-83076870340 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (968793751699981 / 4000000000000) 2 (IntervalRat.scale (839 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-45233557362 / 1000000000000) (-45233557361 / 1000000000000), orderedInterval (-24040144323 / 1000000000000) (-24040144322 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2630463493089177 / 4000000000000) 2 (IntervalRat.scale (839 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30241056827 / 1000000000000) (-30241040015 / 1000000000000), orderedInterval (7340847569 / 1000000000000) (7340864382 / 1000000000000)))) (orderedInterval (-4723272860 / 1000000000000) (-4723269839 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1937587503400801 / 4000000000000) 2 (IntervalRat.scale (839 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (35572202674 / 1000000000000) (35572202707 / 1000000000000), orderedInterval (6954002990 / 1000000000000) (6954003022 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3320089212198373 / 4000000000000) 2 (IntervalRat.scale (839 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (27409126854 / 1000000000000) (27409127560 / 1000000000000), orderedInterval (3949692787 / 1000000000000) (3949693492 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2445562686815407 / 4000000000000) 2 (IntervalRat.scale (839 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (13589617962 / 1000000000000) (13589618057 / 1000000000000), orderedInterval (-29278631781 / 1000000000000) (-29278631687 / 1000000000000)))) (orderedInterval (2615053455 / 1000000000000) (2615053619 / 1000000000000))) = true
  rfl'

theorem compactCertificate548_chunkChecks2_1 :
    compactCertificate548.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3752122066244161 / 4000000000000) 2 (IntervalRat.scale (839 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (12953975924 / 1000000000000) (12953975953 / 1000000000000), orderedInterval (-22609373650 / 1000000000000) (-22609373621 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2166288684978169 / 4000000000000) 2 (IntervalRat.scale (839 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (31127058943 / 1000000000000) (31127117342 / 1000000000000), orderedInterval (-14402600864 / 1000000000000) (-14402542466 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3844117286228621 / 4000000000000) 2 (IntervalRat.scale (839 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (12050105947 / 1000000000000) (12050105948 / 1000000000000), orderedInterval (22736428871 / 1000000000000) (22736428872 / 1000000000000)))) (orderedInterval (-1360839057 / 1000000000000) (-1360831067 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3591673014574049 / 4000000000000) 2 (IntervalRat.scale (839 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (5498915026 / 1000000000000) (5498915027 / 1000000000000), orderedInterval (26049908606 / 1000000000000) (26049908607 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2563187338711217 / 4000000000000) 2 (IntervalRat.scale (839 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (20236326266 / 1000000000000) (20236326267 / 1000000000000), orderedInterval (24149735243 / 1000000000000) (24149735244 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2906381255099943 / 4000000000000) 2 (IntervalRat.scale (839 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-29446773116 / 1000000000000) (-29446766941 / 1000000000000), orderedInterval (3029548571 / 1000000000000) (3029554746 / 1000000000000)))) (orderedInterval (-4463165479 / 1000000000000) (-4463165250 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2423037685024567 / 4000000000000) 2 (IntervalRat.scale (839 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-6986995873 / 1000000000000) (-6986995872 / 1000000000000), orderedInterval (-31650624166 / 1000000000000) (-31650624165 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2140827278079907 / 4000000000000) 2 (IntervalRat.scale (839 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (32392735528 / 1000000000000) (32392762684 / 1000000000000), orderedInterval (-11870589997 / 1000000000000) (-11870562841 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (620495187938793 / 800000000000) 2 (IntervalRat.scale (839 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-11964884897 / 1000000000000) (-11964884896 / 1000000000000), orderedInterval (-26023632443 / 1000000000000) (-26023632442 / 1000000000000)))) (orderedInterval (4234959666 / 1000000000000) (4234962287 / 1000000000000))) = true
  rfl'

theorem compactCertificate548_chunkChecks2_2 :
    compactCertificate548.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1716322344711371 / 4000000000000) 2 (IntervalRat.scale (839 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (19555477058 / 1000000000000) (19555478160 / 1000000000000), orderedInterval (-33208135098 / 1000000000000) (-33208133996 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1454945459361331 / 4000000000000) 2 (IntervalRat.scale (839 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (4038019847 / 1000000000000) (4038019848 / 1000000000000), orderedInterval (41634803188 / 1000000000000) (41634803189 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (910437313184593 / 4000000000000) 2 (IntervalRat.scale (839 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (42773835194 / 1000000000000) (42773915595 / 1000000000000), orderedInterval (-31196701104 / 1000000000000) (-31196620702 / 1000000000000)))) (orderedInterval (3026352546 / 1000000000000) (3026353598 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (489636215008431 / 4000000000000) 2 (IntervalRat.scale (839 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-44857432555 / 1000000000000) (-44857432554 / 1000000000000), orderedInterval (-56284268729 / 1000000000000) (-56284268728 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1329457571558293 / 4000000000000) 2 (IntervalRat.scale (839 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (6132911183 / 1000000000000) (6132911185 / 1000000000000), orderedInterval (43324555163 / 1000000000000) (43324555164 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1815260655139061 / 4000000000000) 2 (IntervalRat.scale (839 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (30038507797 / 1000000000000) (30038562572 / 1000000000000), orderedInterval (-22405056355 / 1000000000000) (-22405001581 / 1000000000000)))) (orderedInterval (2707666365 / 1000000000000) (2707671334 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (767562686815407 / 4000000000000) 2 (IntervalRat.scale (839 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-49622712793 / 1000000000000) (-49622712792 / 1000000000000), orderedInterval (-29114470210 / 1000000000000) (-29114470209 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3120099708098447 / 4000000000000) 2 (IntervalRat.scale (839 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (28347650893 / 1000000000000) (28347661112 / 1000000000000), orderedInterval (-3562656569 / 1000000000000) (-3562646350 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2084082006910273 / 4000000000000) 2 (IntervalRat.scale (839 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (10372704687 / 1000000000000) (10372704688 / 1000000000000), orderedInterval (33370853574 / 1000000000000) (33370853575 / 1000000000000)))) (orderedInterval (11060365681 / 1000000000000) (11060368802 / 1000000000000))) = true
  rfl'

theorem compactCertificate548_chunkChecks2 :
    compactCertificate548.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate548.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate548_chunkChecks2_0
    compactCertificate548_chunkChecks2_1 compactCertificate548_chunkChecks2_2

theorem compactCertificate548_chunkChecks3_0 :
    compactCertificate548.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (839 / 2) 3 (IntervalRat.scale (839 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-24746272277 / 1000000000000) (-24746265796 / 1000000000000), orderedInterval (30115873296 / 1000000000000) (30115879777 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1236007205288939 / 4000000000000) 3 (IntervalRat.scale (839 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42792772606 / 1000000000000) (42792780706 / 1000000000000), orderedInterval (-15202730383 / 1000000000000) (-15202722284 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (399699334819787 / 800000000000) 3 (IntervalRat.scale (839 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-27874459352 / 1000000000000) (-27874459351 / 1000000000000), orderedInterval (-22270348644 / 1000000000000) (-22270348643 / 1000000000000)))) (orderedInterval (-9700743833 / 1000000000000) (-9700741183 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (360663819857473 / 4000000000000) 3 (IntervalRat.scale (839 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (13073273474 / 1000000000000) (13073273550 / 1000000000000), orderedInterval (-83076870416 / 1000000000000) (-83076870340 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (968793751699981 / 4000000000000) 3 (IntervalRat.scale (839 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-45233557362 / 1000000000000) (-45233557361 / 1000000000000), orderedInterval (-24040144323 / 1000000000000) (-24040144322 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2630463493089177 / 4000000000000) 3 (IntervalRat.scale (839 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30241056827 / 1000000000000) (-30241040015 / 1000000000000), orderedInterval (7340847569 / 1000000000000) (7340864382 / 1000000000000)))) (orderedInterval (2181584034 / 1000000000000) (2181588765 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1937587503400801 / 4000000000000) 3 (IntervalRat.scale (839 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (35572202674 / 1000000000000) (35572202707 / 1000000000000), orderedInterval (6954002990 / 1000000000000) (6954003022 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3320089212198373 / 4000000000000) 3 (IntervalRat.scale (839 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (27409126854 / 1000000000000) (27409127560 / 1000000000000), orderedInterval (3949692787 / 1000000000000) (3949693492 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2445562686815407 / 4000000000000) 3 (IntervalRat.scale (839 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (13589617962 / 1000000000000) (13589618057 / 1000000000000), orderedInterval (-29278631781 / 1000000000000) (-29278631687 / 1000000000000)))) (orderedInterval (3127947932 / 1000000000000) (3127948241 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate548_chunkChecks3_1 :
    compactCertificate548.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3752122066244161 / 4000000000000) 3 (IntervalRat.scale (839 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (12953975924 / 1000000000000) (12953975953 / 1000000000000), orderedInterval (-22609373650 / 1000000000000) (-22609373621 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2166288684978169 / 4000000000000) 3 (IntervalRat.scale (839 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (31127058943 / 1000000000000) (31127117342 / 1000000000000), orderedInterval (-14402600864 / 1000000000000) (-14402542466 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3844117286228621 / 4000000000000) 3 (IntervalRat.scale (839 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (12050105947 / 1000000000000) (12050105948 / 1000000000000), orderedInterval (22736428871 / 1000000000000) (22736428872 / 1000000000000)))) (orderedInterval (-81476507845 / 1000000000000) (-81476496840 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3591673014574049 / 4000000000000) 3 (IntervalRat.scale (839 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (5498915026 / 1000000000000) (5498915027 / 1000000000000), orderedInterval (26049908606 / 1000000000000) (26049908607 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2563187338711217 / 4000000000000) 3 (IntervalRat.scale (839 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (20236326266 / 1000000000000) (20236326267 / 1000000000000), orderedInterval (24149735243 / 1000000000000) (24149735244 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2906381255099943 / 4000000000000) 3 (IntervalRat.scale (839 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-29446773116 / 1000000000000) (-29446766941 / 1000000000000), orderedInterval (3029548571 / 1000000000000) (3029554746 / 1000000000000)))) (orderedInterval (-3437373785 / 1000000000000) (-3437373394 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2423037685024567 / 4000000000000) 3 (IntervalRat.scale (839 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-6986995873 / 1000000000000) (-6986995872 / 1000000000000), orderedInterval (-31650624166 / 1000000000000) (-31650624165 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2140827278079907 / 4000000000000) 3 (IntervalRat.scale (839 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (32392735528 / 1000000000000) (32392762684 / 1000000000000), orderedInterval (-11870589997 / 1000000000000) (-11870562841 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (620495187938793 / 800000000000) 3 (IntervalRat.scale (839 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-11964884897 / 1000000000000) (-11964884896 / 1000000000000), orderedInterval (-26023632443 / 1000000000000) (-26023632442 / 1000000000000)))) (orderedInterval (3891039112 / 1000000000000) (3891042479 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate548_chunkChecks3_2 :
    compactCertificate548.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1716322344711371 / 4000000000000) 3 (IntervalRat.scale (839 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (19555477058 / 1000000000000) (19555478160 / 1000000000000), orderedInterval (-33208135098 / 1000000000000) (-33208133996 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1454945459361331 / 4000000000000) 3 (IntervalRat.scale (839 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (4038019847 / 1000000000000) (4038019848 / 1000000000000), orderedInterval (41634803188 / 1000000000000) (41634803189 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (910437313184593 / 4000000000000) 3 (IntervalRat.scale (839 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (42773835194 / 1000000000000) (42773915595 / 1000000000000), orderedInterval (-31196701104 / 1000000000000) (-31196620702 / 1000000000000)))) (orderedInterval (-3990711013 / 1000000000000) (-3990710313 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (489636215008431 / 4000000000000) 3 (IntervalRat.scale (839 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-44857432555 / 1000000000000) (-44857432554 / 1000000000000), orderedInterval (-56284268729 / 1000000000000) (-56284268728 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1329457571558293 / 4000000000000) 3 (IntervalRat.scale (839 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (6132911183 / 1000000000000) (6132911185 / 1000000000000), orderedInterval (43324555163 / 1000000000000) (43324555164 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1815260655139061 / 4000000000000) 3 (IntervalRat.scale (839 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (30038507797 / 1000000000000) (30038562572 / 1000000000000), orderedInterval (-22405056355 / 1000000000000) (-22405001581 / 1000000000000)))) (orderedInterval (-1717323689 / 1000000000000) (-1717318316 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (767562686815407 / 4000000000000) 3 (IntervalRat.scale (839 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-49622712793 / 1000000000000) (-49622712792 / 1000000000000), orderedInterval (-29114470210 / 1000000000000) (-29114470209 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3120099708098447 / 4000000000000) 3 (IntervalRat.scale (839 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (28347650893 / 1000000000000) (28347661112 / 1000000000000), orderedInterval (-3562656569 / 1000000000000) (-3562646350 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2084082006910273 / 4000000000000) 3 (IntervalRat.scale (839 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (10372704687 / 1000000000000) (10372704688 / 1000000000000), orderedInterval (33370853574 / 1000000000000) (33370853575 / 1000000000000)))) (orderedInterval (10121822819 / 1000000000000) (10121828546 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate548_chunkChecks3 :
    compactCertificate548.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate548.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate548_chunkChecks3_0
    compactCertificate548_chunkChecks3_1 compactCertificate548_chunkChecks3_2

theorem compactCertificate548_chunkChecks4_0 :
    compactCertificate548.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (839 / 2) 4 (IntervalRat.scale (839 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-24746272277 / 1000000000000) (-24746265796 / 1000000000000), orderedInterval (30115873296 / 1000000000000) (30115879777 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1236007205288939 / 4000000000000) 4 (IntervalRat.scale (839 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42792772606 / 1000000000000) (42792780706 / 1000000000000), orderedInterval (-15202730383 / 1000000000000) (-15202722284 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (399699334819787 / 800000000000) 4 (IntervalRat.scale (839 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-27874459352 / 1000000000000) (-27874459351 / 1000000000000), orderedInterval (-22270348644 / 1000000000000) (-22270348643 / 1000000000000)))) (orderedInterval (-12936029059 / 1000000000000) (-12936026404 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (360663819857473 / 4000000000000) 4 (IntervalRat.scale (839 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (13073273474 / 1000000000000) (13073273550 / 1000000000000), orderedInterval (-83076870416 / 1000000000000) (-83076870340 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (968793751699981 / 4000000000000) 4 (IntervalRat.scale (839 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-45233557362 / 1000000000000) (-45233557361 / 1000000000000), orderedInterval (-24040144323 / 1000000000000) (-24040144322 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2630463493089177 / 4000000000000) 4 (IntervalRat.scale (839 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30241056827 / 1000000000000) (-30241040015 / 1000000000000), orderedInterval (7340847569 / 1000000000000) (7340864382 / 1000000000000)))) (orderedInterval (12788442653 / 1000000000000) (12788450075 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1937587503400801 / 4000000000000) 4 (IntervalRat.scale (839 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (35572202674 / 1000000000000) (35572202707 / 1000000000000), orderedInterval (6954002990 / 1000000000000) (6954003022 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3320089212198373 / 4000000000000) 4 (IntervalRat.scale (839 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (27409126854 / 1000000000000) (27409127560 / 1000000000000), orderedInterval (3949692787 / 1000000000000) (3949693492 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2445562686815407 / 4000000000000) 4 (IntervalRat.scale (839 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (13589617962 / 1000000000000) (13589618057 / 1000000000000), orderedInterval (-29278631781 / 1000000000000) (-29278631687 / 1000000000000)))) (orderedInterval (-11489857461 / 1000000000000) (-11489856871 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate548_chunkChecks4_1 :
    compactCertificate548.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3752122066244161 / 4000000000000) 4 (IntervalRat.scale (839 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (12953975924 / 1000000000000) (12953975953 / 1000000000000), orderedInterval (-22609373650 / 1000000000000) (-22609373621 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2166288684978169 / 4000000000000) 4 (IntervalRat.scale (839 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (31127058943 / 1000000000000) (31127117342 / 1000000000000), orderedInterval (-14402600864 / 1000000000000) (-14402542466 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3844117286228621 / 4000000000000) 4 (IntervalRat.scale (839 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (12050105947 / 1000000000000) (12050105948 / 1000000000000), orderedInterval (22736428871 / 1000000000000) (22736428872 / 1000000000000)))) (orderedInterval (-3567626119 / 1000000000000) (-3567610329 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3591673014574049 / 4000000000000) 4 (IntervalRat.scale (839 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (5498915026 / 1000000000000) (5498915027 / 1000000000000), orderedInterval (26049908606 / 1000000000000) (26049908607 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2563187338711217 / 4000000000000) 4 (IntervalRat.scale (839 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (20236326266 / 1000000000000) (20236326267 / 1000000000000), orderedInterval (24149735243 / 1000000000000) (24149735244 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2906381255099943 / 4000000000000) 4 (IntervalRat.scale (839 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-29446773116 / 1000000000000) (-29446766941 / 1000000000000), orderedInterval (3029548571 / 1000000000000) (3029554746 / 1000000000000)))) (orderedInterval (9692276444 / 1000000000000) (9692277122 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2423037685024567 / 4000000000000) 4 (IntervalRat.scale (839 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-6986995873 / 1000000000000) (-6986995872 / 1000000000000), orderedInterval (-31650624166 / 1000000000000) (-31650624165 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2140827278079907 / 4000000000000) 4 (IntervalRat.scale (839 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (32392735528 / 1000000000000) (32392762684 / 1000000000000), orderedInterval (-11870589997 / 1000000000000) (-11870562841 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (620495187938793 / 800000000000) 4 (IntervalRat.scale (839 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-11964884897 / 1000000000000) (-11964884896 / 1000000000000), orderedInterval (-26023632443 / 1000000000000) (-26023632442 / 1000000000000)))) (orderedInterval (-8860710536 / 1000000000000) (-8860706192 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate548_chunkChecks4_2 :
    compactCertificate548.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1716322344711371 / 4000000000000) 4 (IntervalRat.scale (839 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (19555477058 / 1000000000000) (19555478160 / 1000000000000), orderedInterval (-33208135098 / 1000000000000) (-33208133996 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1454945459361331 / 4000000000000) 4 (IntervalRat.scale (839 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (4038019847 / 1000000000000) (4038019848 / 1000000000000), orderedInterval (41634803188 / 1000000000000) (41634803189 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (910437313184593 / 4000000000000) 4 (IntervalRat.scale (839 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (42773835194 / 1000000000000) (42773915595 / 1000000000000), orderedInterval (-31196701104 / 1000000000000) (-31196620702 / 1000000000000)))) (orderedInterval (-3411806749 / 1000000000000) (-3411806238 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (489636215008431 / 4000000000000) 4 (IntervalRat.scale (839 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-44857432555 / 1000000000000) (-44857432554 / 1000000000000), orderedInterval (-56284268729 / 1000000000000) (-56284268728 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1329457571558293 / 4000000000000) 4 (IntervalRat.scale (839 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (6132911183 / 1000000000000) (6132911185 / 1000000000000), orderedInterval (43324555163 / 1000000000000) (43324555164 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1815260655139061 / 4000000000000) 4 (IntervalRat.scale (839 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (30038507797 / 1000000000000) (30038562572 / 1000000000000), orderedInterval (-22405056355 / 1000000000000) (-22405001581 / 1000000000000)))) (orderedInterval (-3193561246 / 1000000000000) (-3193555422 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (767562686815407 / 4000000000000) 4 (IntervalRat.scale (839 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-49622712793 / 1000000000000) (-49622712792 / 1000000000000), orderedInterval (-29114470210 / 1000000000000) (-29114470209 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3120099708098447 / 4000000000000) 4 (IntervalRat.scale (839 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (28347650893 / 1000000000000) (28347661112 / 1000000000000), orderedInterval (-3562656569 / 1000000000000) (-3562646350 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2084082006910273 / 4000000000000) 4 (IntervalRat.scale (839 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (10372704687 / 1000000000000) (10372704688 / 1000000000000), orderedInterval (33370853574 / 1000000000000) (33370853575 / 1000000000000)))) (orderedInterval (-32276317440 / 1000000000000) (-32276306874 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate548_chunkChecks4 :
    compactCertificate548.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate548.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate548_chunkChecks4_0
    compactCertificate548_chunkChecks4_1 compactCertificate548_chunkChecks4_2

theorem compactCertificate548_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate548.chunkCheck r b = true :=
  compactCertificate548.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate548_chunkChecks0
    · exact compactCertificate548_chunkChecks1
    · exact compactCertificate548_chunkChecks2
    · exact compactCertificate548_chunkChecks3
    · exact compactCertificate548_chunkChecks4)

theorem compactCertificate548_coefficient0 :
    compactCertificate548.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate548_coefficient1 :
    compactCertificate548.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate548_coefficient2 :
    compactCertificate548.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate548_coefficient3 :
    compactCertificate548.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate548_coefficient4 :
    compactCertificate548.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate548_coefficients : ∀ r : Fin 5,
    compactCertificate548.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate548_coefficient0
  · exact compactCertificate548_coefficient1
  · exact compactCertificate548_coefficient2
  · exact compactCertificate548_coefficient3
  · exact compactCertificate548_coefficient4

theorem compactCertificate548_lower : (1 : ℚ) ≤ compactCertificate548.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate548, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate548_proves {t : ℝ} (ht : t ∈ compactCertificate548.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate548.proves compactCertificate548_states compactCertificate548_chunks
    compactCertificate548_coefficients compactCertificate548_lower ht

end Erdos232
