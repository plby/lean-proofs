/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate576 : CompactCertificate where
  left := 447
  right := 448
  center := 895 / 2
  grid := fun i =>
    match i.val with
    | 0 => 143
    | 1 => 105
    | 2 => 170
    | 3 => 31
    | 4 => 82
    | 5 => 223
    | 6 => 165
    | 7 => 282
    | 8 => 208
    | 9 => 319
    | 10 => 184
    | 11 => 326
    | 12 => 305
    | 13 => 218
    | 14 => 247
    | 15 => 206
    | 16 => 182
    | 17 => 263
    | 18 => 146
    | 19 => 124
    | 20 => 77
    | 21 => 42
    | 22 => 113
    | 23 => 154
    | 24 => 65
    | 25 => 265
    | _ => 177
  point := fun i =>
    match i.val with
    | 0 => 895 / 2
    | 1 => 263701179674279 / 800000000000
    | 2 => 85275543424007 / 160000000000
    | 3 => 76947346548853 / 800000000000
    | 4 => 206691396369841 / 800000000000
    | 5 => 561207348346797 / 800000000000
    | 6 => 413382792739861 / 800000000000
    | 7 => 708338461243753 / 800000000000
    | 8 => 521758904576827 / 800000000000
    | 9 => 800512335944821 / 800000000000
    | 10 => 462176012647309 / 800000000000
    | 11 => 820139444856881 / 800000000000
    | 12 => 766280655075989 / 800000000000
    | 13 => 546854032931237 / 800000000000
    | 14 => 620074189109523 / 800000000000
    | 15 => 516953212895587 / 800000000000
    | 16 => 456743841211327 / 800000000000
    | 17 => 132382167629373 / 160000000000
    | 18 => 366176042554631 / 800000000000
    | 19 => 310411486562191 / 800000000000
    | 20 => 194241095423173 / 800000000000
    | 21 => 104463507135291 / 800000000000
    | 22 => 283638742918873 / 800000000000
    | 23 => 387284454433721 / 800000000000
    | 24 => 163758904576827 / 800000000000
    | 25 => 665670855482267 / 800000000000
    | _ => 444637281569653 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (30954653854 / 1000000000000) (30954728108 / 1000000000000), orderedInterval (-21585045849 / 1000000000000) (-21584971594 / 1000000000000))
    | 1 => (orderedInterval (-22755264578 / 1000000000000) (-22755264577 / 1000000000000), orderedInterval (-37562502644 / 1000000000000) (-37562502643 / 1000000000000))
    | 2 => (orderedInterval (-10656361827 / 1000000000000) (-10656361798 / 1000000000000), orderedInterval (32887244203 / 1000000000000) (32887244232 / 1000000000000))
    | 3 => (orderedInterval (33254412832 / 1000000000000) (33254414943 / 1000000000000), orderedInterval (-74422180354 / 1000000000000) (-74422178242 / 1000000000000))
    | 4 => (orderedInterval (49613262343 / 1000000000000) (49613262409 / 1000000000000), orderedInterval (1503782360 / 1000000000000) (1503782426 / 1000000000000))
    | 5 => (orderedInterval (-29793430999 / 1000000000000) (-29793422271 / 1000000000000), orderedInterval (4476763105 / 1000000000000) (4476771832 / 1000000000000))
    | 6 => (orderedInterval (26350114929 / 1000000000000) (26350134443 / 1000000000000), orderedInterval (-23213665652 / 1000000000000) (-23213646137 / 1000000000000))
    | 7 => (orderedInterval (7389768121 / 1000000000000) (7389768122 / 1000000000000), orderedInterval (25771631139 / 1000000000000) (25771631140 / 1000000000000))
    | 8 => (orderedInterval (-14077936637 / 1000000000000) (-14077936525 / 1000000000000), orderedInterval (27902102988 / 1000000000000) (27902103100 / 1000000000000))
    | 9 => (orderedInterval (17051704176 / 1000000000000) (17051704591 / 1000000000000), orderedInterval (-18594851964 / 1000000000000) (-18594851549 / 1000000000000))
    | 10 => (orderedInterval (14503179338 / 1000000000000) (14503179339 / 1000000000000), orderedInterval (29847289235 / 1000000000000) (29847289236 / 1000000000000))
    | 11 => (orderedInterval (24265719252 / 1000000000000) (24265803122 / 1000000000000), orderedInterval (-5682818215 / 1000000000000) (-5682734344 / 1000000000000))
    | 12 => (orderedInterval (-11221216867 / 1000000000000) (-11221216866 / 1000000000000), orderedInterval (-23204439353 / 1000000000000) (-23204439352 / 1000000000000))
    | 13 => (orderedInterval (-15016122045 / 1000000000000) (-15016121873 / 1000000000000), orderedInterval (26578552080 / 1000000000000) (26578552251 / 1000000000000))
    | 14 => (orderedInterval (2730283636 / 1000000000000) (2730283637 / 1000000000000), orderedInterval (-28530559071 / 1000000000000) (-28530559070 / 1000000000000))
    | 15 => (orderedInterval (-5969936890 / 1000000000000) (-5969936888 / 1000000000000), orderedInterval (30819349203 / 1000000000000) (30819349205 / 1000000000000))
    | 16 => (orderedInterval (-1831733225 / 1000000000000) (-1831733224 / 1000000000000), orderedInterval (33343815480 / 1000000000000) (33343815481 / 1000000000000))
    | 17 => (orderedInterval (-25919982395 / 1000000000000) (-25919870651 / 1000000000000), orderedInterval (9894366888 / 1000000000000) (9894478632 / 1000000000000))
    | 18 => (orderedInterval (-6212043363 / 1000000000000) (-6212043358 / 1000000000000), orderedInterval (36779886659 / 1000000000000) (36779886665 / 1000000000000))
    | 19 => (orderedInterval (-27848079634 / 1000000000000) (-27848064398 / 1000000000000), orderedInterval (29450106033 / 1000000000000) (29450121268 / 1000000000000))
    | 20 => (orderedInterval (-50879651755 / 1000000000000) (-50879651331 / 1000000000000), orderedInterval (5869610881 / 1000000000000) (5869611305 / 1000000000000))
    | 21 => (orderedInterval (-38443838374 / 1000000000000) (-38443828585 / 1000000000000), orderedInterval (58434695779 / 1000000000000) (58434705568 / 1000000000000))
    | 22 => (orderedInterval (-13871480601 / 1000000000000) (-13871480600 / 1000000000000), orderedInterval (-40019950797 / 1000000000000) (-40019950796 / 1000000000000))
    | 23 => (orderedInterval (32075386655 / 1000000000000) (32075386656 / 1000000000000), orderedInterval (16884686145 / 1000000000000) (16884686146 / 1000000000000))
    | 24 => (orderedInterval (-53424576979 / 1000000000000) (-53424576978 / 1000000000000), orderedInterval (-15864540910 / 1000000000000) (-15864540909 / 1000000000000))
    | 25 => (orderedInterval (-9530442364 / 1000000000000) (-9530442363 / 1000000000000), orderedInterval (-25960738540 / 1000000000000) (-25960738539 / 1000000000000))
    | _ => (orderedInterval (-16812769051 / 1000000000000) (-16812769050 / 1000000000000), orderedInterval (-29357475301 / 1000000000000) (-29357475300 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (11431978762 / 1000000000000) (11432008226 / 1000000000000)
      | 1 => orderedInterval (3568683675 / 1000000000000) (3568684374 / 1000000000000)
      | 2 => orderedInterval (-568165981 / 1000000000000) (-568165953 / 1000000000000)
      | 3 => orderedInterval (1494199095 / 1000000000000) (1494211269 / 1000000000000)
      | 4 => orderedInterval (-1231206778 / 1000000000000) (-1231206708 / 1000000000000)
      | 5 => orderedInterval (-627768810 / 1000000000000) (-627765906 / 1000000000000)
      | 6 => orderedInterval (913057094 / 1000000000000) (913058084 / 1000000000000)
      | 7 => orderedInterval (-1433651256 / 1000000000000) (-1433651022 / 1000000000000)
      | _ => orderedInterval (3608255475 / 1000000000000) (3608255599 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-6514909187 / 1000000000000) (-6514879718 / 1000000000000)
      | 1 => orderedInterval (-293652116 / 1000000000000) (-293651076 / 1000000000000)
      | 2 => orderedInterval (-589989223 / 1000000000000) (-589989175 / 1000000000000)
      | 3 => orderedInterval (8392415110 / 1000000000000) (8392442956 / 1000000000000)
      | 4 => orderedInterval (4985930870 / 1000000000000) (4985930981 / 1000000000000)
      | 5 => orderedInterval (-1452161894 / 1000000000000) (-1452156541 / 1000000000000)
      | 6 => orderedInterval (-7356754164 / 1000000000000) (-7356753304 / 1000000000000)
      | 7 => orderedInterval (-995386341 / 1000000000000) (-995386239 / 1000000000000)
      | _ => orderedInterval (10726919216 / 1000000000000) (10726919390 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-11252753878 / 1000000000000) (-11252724337 / 1000000000000)
      | 1 => orderedInterval (-5791339778 / 1000000000000) (-5791338164 / 1000000000000)
      | 2 => orderedInterval (1616324217 / 1000000000000) (1616324301 / 1000000000000)
      | 3 => orderedInterval (-4764052507 / 1000000000000) (-4763988717 / 1000000000000)
      | 4 => orderedInterval (2415452681 / 1000000000000) (2415452863 / 1000000000000)
      | 5 => orderedInterval (2245045912 / 1000000000000) (2245055797 / 1000000000000)
      | 6 => orderedInterval (-1720092243 / 1000000000000) (-1720091489 / 1000000000000)
      | 7 => orderedInterval (2621074335 / 1000000000000) (2621074399 / 1000000000000)
      | _ => orderedInterval (-7504916794 / 1000000000000) (-7504916537 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (5460202392 / 1000000000000) (5460231940 / 1000000000000)
      | 1 => orderedInterval (1220358588 / 1000000000000) (1220361109 / 1000000000000)
      | 2 => orderedInterval (4066065461 / 1000000000000) (4066065611 / 1000000000000)
      | 3 => orderedInterval (-31975699821 / 1000000000000) (-31975553783 / 1000000000000)
      | 4 => orderedInterval (-13821786479 / 1000000000000) (-13821786179 / 1000000000000)
      | 5 => orderedInterval (1284811203 / 1000000000000) (1284829451 / 1000000000000)
      | 6 => orderedInterval (7352898073 / 1000000000000) (7352898736 / 1000000000000)
      | 7 => orderedInterval (1207665034 / 1000000000000) (1207665088 / 1000000000000)
      | _ => orderedInterval (-24112808890 / 1000000000000) (-24112808493 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (10924251011 / 1000000000000) (10924280632 / 1000000000000)
      | 1 => orderedInterval (12985535094 / 1000000000000) (12985539047 / 1000000000000)
      | 2 => orderedInterval (-5046506715 / 1000000000000) (-5046506441 / 1000000000000)
      | 3 => orderedInterval (22392358098 / 1000000000000) (22392692808 / 1000000000000)
      | 4 => orderedInterval (-3541329238 / 1000000000000) (-3541328727 / 1000000000000)
      | 5 => orderedInterval (-7783197451 / 1000000000000) (-7783163710 / 1000000000000)
      | 6 => orderedInterval (1801634884 / 1000000000000) (1801635471 / 1000000000000)
      | 7 => orderedInterval (-3242972919 / 1000000000000) (-3242972865 / 1000000000000)
      | _ => orderedInterval (16873609953 / 1000000000000) (16873610591 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (17155381276 / 1000000000000) (17155427963 / 1000000000000)
    | 1 => orderedInterval (6902412271 / 1000000000000) (6902477274 / 1000000000000)
    | 2 => orderedInterval (-22135258055 / 1000000000000) (-22135151884 / 1000000000000)
    | 3 => orderedInterval (-49318294439 / 1000000000000) (-49318096520 / 1000000000000)
    | _ => orderedInterval (45363382717 / 1000000000000) (45363786806 / 1000000000000)

theorem compactCertificate576_stateChecks0 :
    compactCertificate576.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 143 12 (895 / 2)) (orderedInterval (30954653854 / 1000000000000) (30954728108 / 1000000000000), orderedInterval (-21585045849 / 1000000000000) (-21584971594 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 105 12 (263701179674279 / 800000000000)) (orderedInterval (-22755264578 / 1000000000000) (-22755264577 / 1000000000000), orderedInterval (-37562502644 / 1000000000000) (-37562502643 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 170 12 (85275543424007 / 160000000000)) (orderedInterval (-10656361827 / 1000000000000) (-10656361798 / 1000000000000), orderedInterval (32887244203 / 1000000000000) (32887244232 / 1000000000000))) = true
  rfl'

theorem compactCertificate576_stateChecks1 :
    compactCertificate576.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (76947346548853 / 800000000000)) (orderedInterval (33254412832 / 1000000000000) (33254414943 / 1000000000000), orderedInterval (-74422180354 / 1000000000000) (-74422178242 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (206691396369841 / 800000000000)) (orderedInterval (49613262343 / 1000000000000) (49613262409 / 1000000000000), orderedInterval (1503782360 / 1000000000000) (1503782426 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 223 12 (561207348346797 / 800000000000)) (orderedInterval (-29793430999 / 1000000000000) (-29793422271 / 1000000000000), orderedInterval (4476763105 / 1000000000000) (4476771832 / 1000000000000))) = true
  rfl'

theorem compactCertificate576_stateChecks2 :
    compactCertificate576.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 165 12 (413382792739861 / 800000000000)) (orderedInterval (26350114929 / 1000000000000) (26350134443 / 1000000000000), orderedInterval (-23213665652 / 1000000000000) (-23213646137 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 282 12 (708338461243753 / 800000000000)) (orderedInterval (7389768121 / 1000000000000) (7389768122 / 1000000000000), orderedInterval (25771631139 / 1000000000000) (25771631140 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 208 12 (521758904576827 / 800000000000)) (orderedInterval (-14077936637 / 1000000000000) (-14077936525 / 1000000000000), orderedInterval (27902102988 / 1000000000000) (27902103100 / 1000000000000))) = true
  rfl'

theorem compactCertificate576_stateChecks3 :
    compactCertificate576.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 319 12 (800512335944821 / 800000000000)) (orderedInterval (17051704176 / 1000000000000) (17051704591 / 1000000000000), orderedInterval (-18594851964 / 1000000000000) (-18594851549 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 184 12 (462176012647309 / 800000000000)) (orderedInterval (14503179338 / 1000000000000) (14503179339 / 1000000000000), orderedInterval (29847289235 / 1000000000000) (29847289236 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 326 12 (820139444856881 / 800000000000)) (orderedInterval (24265719252 / 1000000000000) (24265803122 / 1000000000000), orderedInterval (-5682818215 / 1000000000000) (-5682734344 / 1000000000000))) = true
  rfl'

theorem compactCertificate576_stateChecks4 :
    compactCertificate576.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 305 12 (766280655075989 / 800000000000)) (orderedInterval (-11221216867 / 1000000000000) (-11221216866 / 1000000000000), orderedInterval (-23204439353 / 1000000000000) (-23204439352 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 218 12 (546854032931237 / 800000000000)) (orderedInterval (-15016122045 / 1000000000000) (-15016121873 / 1000000000000), orderedInterval (26578552080 / 1000000000000) (26578552251 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 247 12 (620074189109523 / 800000000000)) (orderedInterval (2730283636 / 1000000000000) (2730283637 / 1000000000000), orderedInterval (-28530559071 / 1000000000000) (-28530559070 / 1000000000000))) = true
  rfl'

theorem compactCertificate576_stateChecks5 :
    compactCertificate576.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 206 12 (516953212895587 / 800000000000)) (orderedInterval (-5969936890 / 1000000000000) (-5969936888 / 1000000000000), orderedInterval (30819349203 / 1000000000000) (30819349205 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 182 12 (456743841211327 / 800000000000)) (orderedInterval (-1831733225 / 1000000000000) (-1831733224 / 1000000000000), orderedInterval (33343815480 / 1000000000000) (33343815481 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 263 12 (132382167629373 / 160000000000)) (orderedInterval (-25919982395 / 1000000000000) (-25919870651 / 1000000000000), orderedInterval (9894366888 / 1000000000000) (9894478632 / 1000000000000))) = true
  rfl'

theorem compactCertificate576_stateChecks6 :
    compactCertificate576.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 146 12 (366176042554631 / 800000000000)) (orderedInterval (-6212043363 / 1000000000000) (-6212043358 / 1000000000000), orderedInterval (36779886659 / 1000000000000) (36779886665 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 124 12 (310411486562191 / 800000000000)) (orderedInterval (-27848079634 / 1000000000000) (-27848064398 / 1000000000000), orderedInterval (29450106033 / 1000000000000) (29450121268 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (194241095423173 / 800000000000)) (orderedInterval (-50879651755 / 1000000000000) (-50879651331 / 1000000000000), orderedInterval (5869610881 / 1000000000000) (5869611305 / 1000000000000))) = true
  rfl'

theorem compactCertificate576_stateChecks7 :
    compactCertificate576.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (104463507135291 / 800000000000)) (orderedInterval (-38443838374 / 1000000000000) (-38443828585 / 1000000000000), orderedInterval (58434695779 / 1000000000000) (58434705568 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 113 12 (283638742918873 / 800000000000)) (orderedInterval (-13871480601 / 1000000000000) (-13871480600 / 1000000000000), orderedInterval (-40019950797 / 1000000000000) (-40019950796 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 154 12 (387284454433721 / 800000000000)) (orderedInterval (32075386655 / 1000000000000) (32075386656 / 1000000000000), orderedInterval (16884686145 / 1000000000000) (16884686146 / 1000000000000))) = true
  rfl'

theorem compactCertificate576_stateChecks8 :
    compactCertificate576.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (163758904576827 / 800000000000)) (orderedInterval (-53424576979 / 1000000000000) (-53424576978 / 1000000000000), orderedInterval (-15864540910 / 1000000000000) (-15864540909 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 265 12 (665670855482267 / 800000000000)) (orderedInterval (-9530442364 / 1000000000000) (-9530442363 / 1000000000000), orderedInterval (-25960738540 / 1000000000000) (-25960738539 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 177 12 (444637281569653 / 800000000000)) (orderedInterval (-16812769051 / 1000000000000) (-16812769050 / 1000000000000), orderedInterval (-29357475301 / 1000000000000) (-29357475300 / 1000000000000))) = true
  rfl'

theorem compactCertificate576_states : ∀ j,
    BesselStateValid (compactCertificate576.point j) (compactCertificate576.state j) :=
  compactCertificate576.statesValid_of_checks3 compactCertificate576_stateChecks0
    compactCertificate576_stateChecks1 compactCertificate576_stateChecks2
    compactCertificate576_stateChecks3 compactCertificate576_stateChecks4
    compactCertificate576_stateChecks5 compactCertificate576_stateChecks6
    compactCertificate576_stateChecks7 compactCertificate576_stateChecks8

theorem compactCertificate576_chunkChecks0_0 :
    compactCertificate576.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (895 / 2) 0 (IntervalRat.scale (895 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (30954653854 / 1000000000000) (30954728108 / 1000000000000), orderedInterval (-21585045849 / 1000000000000) (-21584971594 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (263701179674279 / 800000000000) 0 (IntervalRat.scale (895 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-22755264578 / 1000000000000) (-22755264577 / 1000000000000), orderedInterval (-37562502644 / 1000000000000) (-37562502643 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (85275543424007 / 160000000000) 0 (IntervalRat.scale (895 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-10656361827 / 1000000000000) (-10656361798 / 1000000000000), orderedInterval (32887244203 / 1000000000000) (32887244232 / 1000000000000)))) (orderedInterval (11431978762 / 1000000000000) (11432008226 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (76947346548853 / 800000000000) 0 (IntervalRat.scale (895 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (33254412832 / 1000000000000) (33254414943 / 1000000000000), orderedInterval (-74422180354 / 1000000000000) (-74422178242 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (206691396369841 / 800000000000) 0 (IntervalRat.scale (895 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (49613262343 / 1000000000000) (49613262409 / 1000000000000), orderedInterval (1503782360 / 1000000000000) (1503782426 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (561207348346797 / 800000000000) 0 (IntervalRat.scale (895 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29793430999 / 1000000000000) (-29793422271 / 1000000000000), orderedInterval (4476763105 / 1000000000000) (4476771832 / 1000000000000)))) (orderedInterval (3568683675 / 1000000000000) (3568684374 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (413382792739861 / 800000000000) 0 (IntervalRat.scale (895 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (26350114929 / 1000000000000) (26350134443 / 1000000000000), orderedInterval (-23213665652 / 1000000000000) (-23213646137 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (708338461243753 / 800000000000) 0 (IntervalRat.scale (895 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (7389768121 / 1000000000000) (7389768122 / 1000000000000), orderedInterval (25771631139 / 1000000000000) (25771631140 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (521758904576827 / 800000000000) 0 (IntervalRat.scale (895 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-14077936637 / 1000000000000) (-14077936525 / 1000000000000), orderedInterval (27902102988 / 1000000000000) (27902103100 / 1000000000000)))) (orderedInterval (-568165981 / 1000000000000) (-568165953 / 1000000000000))) = true
  rfl'

theorem compactCertificate576_chunkChecks0_1 :
    compactCertificate576.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (800512335944821 / 800000000000) 0 (IntervalRat.scale (895 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (17051704176 / 1000000000000) (17051704591 / 1000000000000), orderedInterval (-18594851964 / 1000000000000) (-18594851549 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (462176012647309 / 800000000000) 0 (IntervalRat.scale (895 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (14503179338 / 1000000000000) (14503179339 / 1000000000000), orderedInterval (29847289235 / 1000000000000) (29847289236 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (820139444856881 / 800000000000) 0 (IntervalRat.scale (895 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (24265719252 / 1000000000000) (24265803122 / 1000000000000), orderedInterval (-5682818215 / 1000000000000) (-5682734344 / 1000000000000)))) (orderedInterval (1494199095 / 1000000000000) (1494211269 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (766280655075989 / 800000000000) 0 (IntervalRat.scale (895 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-11221216867 / 1000000000000) (-11221216866 / 1000000000000), orderedInterval (-23204439353 / 1000000000000) (-23204439352 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (546854032931237 / 800000000000) 0 (IntervalRat.scale (895 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-15016122045 / 1000000000000) (-15016121873 / 1000000000000), orderedInterval (26578552080 / 1000000000000) (26578552251 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (620074189109523 / 800000000000) 0 (IntervalRat.scale (895 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (2730283636 / 1000000000000) (2730283637 / 1000000000000), orderedInterval (-28530559071 / 1000000000000) (-28530559070 / 1000000000000)))) (orderedInterval (-1231206778 / 1000000000000) (-1231206708 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (516953212895587 / 800000000000) 0 (IntervalRat.scale (895 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-5969936890 / 1000000000000) (-5969936888 / 1000000000000), orderedInterval (30819349203 / 1000000000000) (30819349205 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (456743841211327 / 800000000000) 0 (IntervalRat.scale (895 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-1831733225 / 1000000000000) (-1831733224 / 1000000000000), orderedInterval (33343815480 / 1000000000000) (33343815481 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (132382167629373 / 160000000000) 0 (IntervalRat.scale (895 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-25919982395 / 1000000000000) (-25919870651 / 1000000000000), orderedInterval (9894366888 / 1000000000000) (9894478632 / 1000000000000)))) (orderedInterval (-627768810 / 1000000000000) (-627765906 / 1000000000000))) = true
  rfl'

theorem compactCertificate576_chunkChecks0_2 :
    compactCertificate576.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (366176042554631 / 800000000000) 0 (IntervalRat.scale (895 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-6212043363 / 1000000000000) (-6212043358 / 1000000000000), orderedInterval (36779886659 / 1000000000000) (36779886665 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (310411486562191 / 800000000000) 0 (IntervalRat.scale (895 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-27848079634 / 1000000000000) (-27848064398 / 1000000000000), orderedInterval (29450106033 / 1000000000000) (29450121268 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (194241095423173 / 800000000000) 0 (IntervalRat.scale (895 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-50879651755 / 1000000000000) (-50879651331 / 1000000000000), orderedInterval (5869610881 / 1000000000000) (5869611305 / 1000000000000)))) (orderedInterval (913057094 / 1000000000000) (913058084 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (104463507135291 / 800000000000) 0 (IntervalRat.scale (895 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-38443838374 / 1000000000000) (-38443828585 / 1000000000000), orderedInterval (58434695779 / 1000000000000) (58434705568 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (283638742918873 / 800000000000) 0 (IntervalRat.scale (895 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-13871480601 / 1000000000000) (-13871480600 / 1000000000000), orderedInterval (-40019950797 / 1000000000000) (-40019950796 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (387284454433721 / 800000000000) 0 (IntervalRat.scale (895 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (32075386655 / 1000000000000) (32075386656 / 1000000000000), orderedInterval (16884686145 / 1000000000000) (16884686146 / 1000000000000)))) (orderedInterval (-1433651256 / 1000000000000) (-1433651022 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (163758904576827 / 800000000000) 0 (IntervalRat.scale (895 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-53424576979 / 1000000000000) (-53424576978 / 1000000000000), orderedInterval (-15864540910 / 1000000000000) (-15864540909 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (665670855482267 / 800000000000) 0 (IntervalRat.scale (895 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-9530442364 / 1000000000000) (-9530442363 / 1000000000000), orderedInterval (-25960738540 / 1000000000000) (-25960738539 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (444637281569653 / 800000000000) 0 (IntervalRat.scale (895 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-16812769051 / 1000000000000) (-16812769050 / 1000000000000), orderedInterval (-29357475301 / 1000000000000) (-29357475300 / 1000000000000)))) (orderedInterval (3608255475 / 1000000000000) (3608255599 / 1000000000000))) = true
  rfl'

theorem compactCertificate576_chunkChecks0 :
    compactCertificate576.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate576.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate576_chunkChecks0_0
    compactCertificate576_chunkChecks0_1 compactCertificate576_chunkChecks0_2

theorem compactCertificate576_chunkChecks1_0 :
    compactCertificate576.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (895 / 2) 1 (IntervalRat.scale (895 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (30954653854 / 1000000000000) (30954728108 / 1000000000000), orderedInterval (-21585045849 / 1000000000000) (-21584971594 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (263701179674279 / 800000000000) 1 (IntervalRat.scale (895 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-22755264578 / 1000000000000) (-22755264577 / 1000000000000), orderedInterval (-37562502644 / 1000000000000) (-37562502643 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (85275543424007 / 160000000000) 1 (IntervalRat.scale (895 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-10656361827 / 1000000000000) (-10656361798 / 1000000000000), orderedInterval (32887244203 / 1000000000000) (32887244232 / 1000000000000)))) (orderedInterval (-6514909187 / 1000000000000) (-6514879718 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (76947346548853 / 800000000000) 1 (IntervalRat.scale (895 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (33254412832 / 1000000000000) (33254414943 / 1000000000000), orderedInterval (-74422180354 / 1000000000000) (-74422178242 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (206691396369841 / 800000000000) 1 (IntervalRat.scale (895 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (49613262343 / 1000000000000) (49613262409 / 1000000000000), orderedInterval (1503782360 / 1000000000000) (1503782426 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (561207348346797 / 800000000000) 1 (IntervalRat.scale (895 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29793430999 / 1000000000000) (-29793422271 / 1000000000000), orderedInterval (4476763105 / 1000000000000) (4476771832 / 1000000000000)))) (orderedInterval (-293652116 / 1000000000000) (-293651076 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (413382792739861 / 800000000000) 1 (IntervalRat.scale (895 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (26350114929 / 1000000000000) (26350134443 / 1000000000000), orderedInterval (-23213665652 / 1000000000000) (-23213646137 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (708338461243753 / 800000000000) 1 (IntervalRat.scale (895 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (7389768121 / 1000000000000) (7389768122 / 1000000000000), orderedInterval (25771631139 / 1000000000000) (25771631140 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (521758904576827 / 800000000000) 1 (IntervalRat.scale (895 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-14077936637 / 1000000000000) (-14077936525 / 1000000000000), orderedInterval (27902102988 / 1000000000000) (27902103100 / 1000000000000)))) (orderedInterval (-589989223 / 1000000000000) (-589989175 / 1000000000000))) = true
  rfl'

theorem compactCertificate576_chunkChecks1_1 :
    compactCertificate576.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (800512335944821 / 800000000000) 1 (IntervalRat.scale (895 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (17051704176 / 1000000000000) (17051704591 / 1000000000000), orderedInterval (-18594851964 / 1000000000000) (-18594851549 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (462176012647309 / 800000000000) 1 (IntervalRat.scale (895 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (14503179338 / 1000000000000) (14503179339 / 1000000000000), orderedInterval (29847289235 / 1000000000000) (29847289236 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (820139444856881 / 800000000000) 1 (IntervalRat.scale (895 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (24265719252 / 1000000000000) (24265803122 / 1000000000000), orderedInterval (-5682818215 / 1000000000000) (-5682734344 / 1000000000000)))) (orderedInterval (8392415110 / 1000000000000) (8392442956 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (766280655075989 / 800000000000) 1 (IntervalRat.scale (895 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-11221216867 / 1000000000000) (-11221216866 / 1000000000000), orderedInterval (-23204439353 / 1000000000000) (-23204439352 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (546854032931237 / 800000000000) 1 (IntervalRat.scale (895 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-15016122045 / 1000000000000) (-15016121873 / 1000000000000), orderedInterval (26578552080 / 1000000000000) (26578552251 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (620074189109523 / 800000000000) 1 (IntervalRat.scale (895 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (2730283636 / 1000000000000) (2730283637 / 1000000000000), orderedInterval (-28530559071 / 1000000000000) (-28530559070 / 1000000000000)))) (orderedInterval (4985930870 / 1000000000000) (4985930981 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (516953212895587 / 800000000000) 1 (IntervalRat.scale (895 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-5969936890 / 1000000000000) (-5969936888 / 1000000000000), orderedInterval (30819349203 / 1000000000000) (30819349205 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (456743841211327 / 800000000000) 1 (IntervalRat.scale (895 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-1831733225 / 1000000000000) (-1831733224 / 1000000000000), orderedInterval (33343815480 / 1000000000000) (33343815481 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (132382167629373 / 160000000000) 1 (IntervalRat.scale (895 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-25919982395 / 1000000000000) (-25919870651 / 1000000000000), orderedInterval (9894366888 / 1000000000000) (9894478632 / 1000000000000)))) (orderedInterval (-1452161894 / 1000000000000) (-1452156541 / 1000000000000))) = true
  rfl'

theorem compactCertificate576_chunkChecks1_2 :
    compactCertificate576.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (366176042554631 / 800000000000) 1 (IntervalRat.scale (895 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-6212043363 / 1000000000000) (-6212043358 / 1000000000000), orderedInterval (36779886659 / 1000000000000) (36779886665 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (310411486562191 / 800000000000) 1 (IntervalRat.scale (895 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-27848079634 / 1000000000000) (-27848064398 / 1000000000000), orderedInterval (29450106033 / 1000000000000) (29450121268 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (194241095423173 / 800000000000) 1 (IntervalRat.scale (895 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-50879651755 / 1000000000000) (-50879651331 / 1000000000000), orderedInterval (5869610881 / 1000000000000) (5869611305 / 1000000000000)))) (orderedInterval (-7356754164 / 1000000000000) (-7356753304 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (104463507135291 / 800000000000) 1 (IntervalRat.scale (895 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-38443838374 / 1000000000000) (-38443828585 / 1000000000000), orderedInterval (58434695779 / 1000000000000) (58434705568 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (283638742918873 / 800000000000) 1 (IntervalRat.scale (895 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-13871480601 / 1000000000000) (-13871480600 / 1000000000000), orderedInterval (-40019950797 / 1000000000000) (-40019950796 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (387284454433721 / 800000000000) 1 (IntervalRat.scale (895 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (32075386655 / 1000000000000) (32075386656 / 1000000000000), orderedInterval (16884686145 / 1000000000000) (16884686146 / 1000000000000)))) (orderedInterval (-995386341 / 1000000000000) (-995386239 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (163758904576827 / 800000000000) 1 (IntervalRat.scale (895 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-53424576979 / 1000000000000) (-53424576978 / 1000000000000), orderedInterval (-15864540910 / 1000000000000) (-15864540909 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (665670855482267 / 800000000000) 1 (IntervalRat.scale (895 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-9530442364 / 1000000000000) (-9530442363 / 1000000000000), orderedInterval (-25960738540 / 1000000000000) (-25960738539 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (444637281569653 / 800000000000) 1 (IntervalRat.scale (895 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-16812769051 / 1000000000000) (-16812769050 / 1000000000000), orderedInterval (-29357475301 / 1000000000000) (-29357475300 / 1000000000000)))) (orderedInterval (10726919216 / 1000000000000) (10726919390 / 1000000000000))) = true
  rfl'

theorem compactCertificate576_chunkChecks1 :
    compactCertificate576.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate576.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate576_chunkChecks1_0
    compactCertificate576_chunkChecks1_1 compactCertificate576_chunkChecks1_2

theorem compactCertificate576_chunkChecks2_0 :
    compactCertificate576.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (895 / 2) 2 (IntervalRat.scale (895 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (30954653854 / 1000000000000) (30954728108 / 1000000000000), orderedInterval (-21585045849 / 1000000000000) (-21584971594 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (263701179674279 / 800000000000) 2 (IntervalRat.scale (895 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-22755264578 / 1000000000000) (-22755264577 / 1000000000000), orderedInterval (-37562502644 / 1000000000000) (-37562502643 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (85275543424007 / 160000000000) 2 (IntervalRat.scale (895 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-10656361827 / 1000000000000) (-10656361798 / 1000000000000), orderedInterval (32887244203 / 1000000000000) (32887244232 / 1000000000000)))) (orderedInterval (-11252753878 / 1000000000000) (-11252724337 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (76947346548853 / 800000000000) 2 (IntervalRat.scale (895 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (33254412832 / 1000000000000) (33254414943 / 1000000000000), orderedInterval (-74422180354 / 1000000000000) (-74422178242 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (206691396369841 / 800000000000) 2 (IntervalRat.scale (895 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (49613262343 / 1000000000000) (49613262409 / 1000000000000), orderedInterval (1503782360 / 1000000000000) (1503782426 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (561207348346797 / 800000000000) 2 (IntervalRat.scale (895 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29793430999 / 1000000000000) (-29793422271 / 1000000000000), orderedInterval (4476763105 / 1000000000000) (4476771832 / 1000000000000)))) (orderedInterval (-5791339778 / 1000000000000) (-5791338164 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (413382792739861 / 800000000000) 2 (IntervalRat.scale (895 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (26350114929 / 1000000000000) (26350134443 / 1000000000000), orderedInterval (-23213665652 / 1000000000000) (-23213646137 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (708338461243753 / 800000000000) 2 (IntervalRat.scale (895 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (7389768121 / 1000000000000) (7389768122 / 1000000000000), orderedInterval (25771631139 / 1000000000000) (25771631140 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (521758904576827 / 800000000000) 2 (IntervalRat.scale (895 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-14077936637 / 1000000000000) (-14077936525 / 1000000000000), orderedInterval (27902102988 / 1000000000000) (27902103100 / 1000000000000)))) (orderedInterval (1616324217 / 1000000000000) (1616324301 / 1000000000000))) = true
  rfl'

theorem compactCertificate576_chunkChecks2_1 :
    compactCertificate576.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (800512335944821 / 800000000000) 2 (IntervalRat.scale (895 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (17051704176 / 1000000000000) (17051704591 / 1000000000000), orderedInterval (-18594851964 / 1000000000000) (-18594851549 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (462176012647309 / 800000000000) 2 (IntervalRat.scale (895 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (14503179338 / 1000000000000) (14503179339 / 1000000000000), orderedInterval (29847289235 / 1000000000000) (29847289236 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (820139444856881 / 800000000000) 2 (IntervalRat.scale (895 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (24265719252 / 1000000000000) (24265803122 / 1000000000000), orderedInterval (-5682818215 / 1000000000000) (-5682734344 / 1000000000000)))) (orderedInterval (-4764052507 / 1000000000000) (-4763988717 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (766280655075989 / 800000000000) 2 (IntervalRat.scale (895 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-11221216867 / 1000000000000) (-11221216866 / 1000000000000), orderedInterval (-23204439353 / 1000000000000) (-23204439352 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (546854032931237 / 800000000000) 2 (IntervalRat.scale (895 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-15016122045 / 1000000000000) (-15016121873 / 1000000000000), orderedInterval (26578552080 / 1000000000000) (26578552251 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (620074189109523 / 800000000000) 2 (IntervalRat.scale (895 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (2730283636 / 1000000000000) (2730283637 / 1000000000000), orderedInterval (-28530559071 / 1000000000000) (-28530559070 / 1000000000000)))) (orderedInterval (2415452681 / 1000000000000) (2415452863 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (516953212895587 / 800000000000) 2 (IntervalRat.scale (895 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-5969936890 / 1000000000000) (-5969936888 / 1000000000000), orderedInterval (30819349203 / 1000000000000) (30819349205 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (456743841211327 / 800000000000) 2 (IntervalRat.scale (895 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-1831733225 / 1000000000000) (-1831733224 / 1000000000000), orderedInterval (33343815480 / 1000000000000) (33343815481 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (132382167629373 / 160000000000) 2 (IntervalRat.scale (895 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-25919982395 / 1000000000000) (-25919870651 / 1000000000000), orderedInterval (9894366888 / 1000000000000) (9894478632 / 1000000000000)))) (orderedInterval (2245045912 / 1000000000000) (2245055797 / 1000000000000))) = true
  rfl'

theorem compactCertificate576_chunkChecks2_2 :
    compactCertificate576.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (366176042554631 / 800000000000) 2 (IntervalRat.scale (895 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-6212043363 / 1000000000000) (-6212043358 / 1000000000000), orderedInterval (36779886659 / 1000000000000) (36779886665 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (310411486562191 / 800000000000) 2 (IntervalRat.scale (895 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-27848079634 / 1000000000000) (-27848064398 / 1000000000000), orderedInterval (29450106033 / 1000000000000) (29450121268 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (194241095423173 / 800000000000) 2 (IntervalRat.scale (895 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-50879651755 / 1000000000000) (-50879651331 / 1000000000000), orderedInterval (5869610881 / 1000000000000) (5869611305 / 1000000000000)))) (orderedInterval (-1720092243 / 1000000000000) (-1720091489 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (104463507135291 / 800000000000) 2 (IntervalRat.scale (895 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-38443838374 / 1000000000000) (-38443828585 / 1000000000000), orderedInterval (58434695779 / 1000000000000) (58434705568 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (283638742918873 / 800000000000) 2 (IntervalRat.scale (895 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-13871480601 / 1000000000000) (-13871480600 / 1000000000000), orderedInterval (-40019950797 / 1000000000000) (-40019950796 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (387284454433721 / 800000000000) 2 (IntervalRat.scale (895 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (32075386655 / 1000000000000) (32075386656 / 1000000000000), orderedInterval (16884686145 / 1000000000000) (16884686146 / 1000000000000)))) (orderedInterval (2621074335 / 1000000000000) (2621074399 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (163758904576827 / 800000000000) 2 (IntervalRat.scale (895 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-53424576979 / 1000000000000) (-53424576978 / 1000000000000), orderedInterval (-15864540910 / 1000000000000) (-15864540909 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (665670855482267 / 800000000000) 2 (IntervalRat.scale (895 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-9530442364 / 1000000000000) (-9530442363 / 1000000000000), orderedInterval (-25960738540 / 1000000000000) (-25960738539 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (444637281569653 / 800000000000) 2 (IntervalRat.scale (895 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-16812769051 / 1000000000000) (-16812769050 / 1000000000000), orderedInterval (-29357475301 / 1000000000000) (-29357475300 / 1000000000000)))) (orderedInterval (-7504916794 / 1000000000000) (-7504916537 / 1000000000000))) = true
  rfl'

theorem compactCertificate576_chunkChecks2 :
    compactCertificate576.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate576.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate576_chunkChecks2_0
    compactCertificate576_chunkChecks2_1 compactCertificate576_chunkChecks2_2

theorem compactCertificate576_chunkChecks3_0 :
    compactCertificate576.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (895 / 2) 3 (IntervalRat.scale (895 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (30954653854 / 1000000000000) (30954728108 / 1000000000000), orderedInterval (-21585045849 / 1000000000000) (-21584971594 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (263701179674279 / 800000000000) 3 (IntervalRat.scale (895 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-22755264578 / 1000000000000) (-22755264577 / 1000000000000), orderedInterval (-37562502644 / 1000000000000) (-37562502643 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (85275543424007 / 160000000000) 3 (IntervalRat.scale (895 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-10656361827 / 1000000000000) (-10656361798 / 1000000000000), orderedInterval (32887244203 / 1000000000000) (32887244232 / 1000000000000)))) (orderedInterval (5460202392 / 1000000000000) (5460231940 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (76947346548853 / 800000000000) 3 (IntervalRat.scale (895 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (33254412832 / 1000000000000) (33254414943 / 1000000000000), orderedInterval (-74422180354 / 1000000000000) (-74422178242 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (206691396369841 / 800000000000) 3 (IntervalRat.scale (895 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (49613262343 / 1000000000000) (49613262409 / 1000000000000), orderedInterval (1503782360 / 1000000000000) (1503782426 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (561207348346797 / 800000000000) 3 (IntervalRat.scale (895 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29793430999 / 1000000000000) (-29793422271 / 1000000000000), orderedInterval (4476763105 / 1000000000000) (4476771832 / 1000000000000)))) (orderedInterval (1220358588 / 1000000000000) (1220361109 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (413382792739861 / 800000000000) 3 (IntervalRat.scale (895 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (26350114929 / 1000000000000) (26350134443 / 1000000000000), orderedInterval (-23213665652 / 1000000000000) (-23213646137 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (708338461243753 / 800000000000) 3 (IntervalRat.scale (895 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (7389768121 / 1000000000000) (7389768122 / 1000000000000), orderedInterval (25771631139 / 1000000000000) (25771631140 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (521758904576827 / 800000000000) 3 (IntervalRat.scale (895 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-14077936637 / 1000000000000) (-14077936525 / 1000000000000), orderedInterval (27902102988 / 1000000000000) (27902103100 / 1000000000000)))) (orderedInterval (4066065461 / 1000000000000) (4066065611 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate576_chunkChecks3_1 :
    compactCertificate576.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (800512335944821 / 800000000000) 3 (IntervalRat.scale (895 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (17051704176 / 1000000000000) (17051704591 / 1000000000000), orderedInterval (-18594851964 / 1000000000000) (-18594851549 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (462176012647309 / 800000000000) 3 (IntervalRat.scale (895 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (14503179338 / 1000000000000) (14503179339 / 1000000000000), orderedInterval (29847289235 / 1000000000000) (29847289236 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (820139444856881 / 800000000000) 3 (IntervalRat.scale (895 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (24265719252 / 1000000000000) (24265803122 / 1000000000000), orderedInterval (-5682818215 / 1000000000000) (-5682734344 / 1000000000000)))) (orderedInterval (-31975699821 / 1000000000000) (-31975553783 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (766280655075989 / 800000000000) 3 (IntervalRat.scale (895 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-11221216867 / 1000000000000) (-11221216866 / 1000000000000), orderedInterval (-23204439353 / 1000000000000) (-23204439352 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (546854032931237 / 800000000000) 3 (IntervalRat.scale (895 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-15016122045 / 1000000000000) (-15016121873 / 1000000000000), orderedInterval (26578552080 / 1000000000000) (26578552251 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (620074189109523 / 800000000000) 3 (IntervalRat.scale (895 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (2730283636 / 1000000000000) (2730283637 / 1000000000000), orderedInterval (-28530559071 / 1000000000000) (-28530559070 / 1000000000000)))) (orderedInterval (-13821786479 / 1000000000000) (-13821786179 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (516953212895587 / 800000000000) 3 (IntervalRat.scale (895 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-5969936890 / 1000000000000) (-5969936888 / 1000000000000), orderedInterval (30819349203 / 1000000000000) (30819349205 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (456743841211327 / 800000000000) 3 (IntervalRat.scale (895 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-1831733225 / 1000000000000) (-1831733224 / 1000000000000), orderedInterval (33343815480 / 1000000000000) (33343815481 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (132382167629373 / 160000000000) 3 (IntervalRat.scale (895 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-25919982395 / 1000000000000) (-25919870651 / 1000000000000), orderedInterval (9894366888 / 1000000000000) (9894478632 / 1000000000000)))) (orderedInterval (1284811203 / 1000000000000) (1284829451 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate576_chunkChecks3_2 :
    compactCertificate576.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (366176042554631 / 800000000000) 3 (IntervalRat.scale (895 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-6212043363 / 1000000000000) (-6212043358 / 1000000000000), orderedInterval (36779886659 / 1000000000000) (36779886665 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (310411486562191 / 800000000000) 3 (IntervalRat.scale (895 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-27848079634 / 1000000000000) (-27848064398 / 1000000000000), orderedInterval (29450106033 / 1000000000000) (29450121268 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (194241095423173 / 800000000000) 3 (IntervalRat.scale (895 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-50879651755 / 1000000000000) (-50879651331 / 1000000000000), orderedInterval (5869610881 / 1000000000000) (5869611305 / 1000000000000)))) (orderedInterval (7352898073 / 1000000000000) (7352898736 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (104463507135291 / 800000000000) 3 (IntervalRat.scale (895 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-38443838374 / 1000000000000) (-38443828585 / 1000000000000), orderedInterval (58434695779 / 1000000000000) (58434705568 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (283638742918873 / 800000000000) 3 (IntervalRat.scale (895 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-13871480601 / 1000000000000) (-13871480600 / 1000000000000), orderedInterval (-40019950797 / 1000000000000) (-40019950796 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (387284454433721 / 800000000000) 3 (IntervalRat.scale (895 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (32075386655 / 1000000000000) (32075386656 / 1000000000000), orderedInterval (16884686145 / 1000000000000) (16884686146 / 1000000000000)))) (orderedInterval (1207665034 / 1000000000000) (1207665088 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (163758904576827 / 800000000000) 3 (IntervalRat.scale (895 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-53424576979 / 1000000000000) (-53424576978 / 1000000000000), orderedInterval (-15864540910 / 1000000000000) (-15864540909 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (665670855482267 / 800000000000) 3 (IntervalRat.scale (895 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-9530442364 / 1000000000000) (-9530442363 / 1000000000000), orderedInterval (-25960738540 / 1000000000000) (-25960738539 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (444637281569653 / 800000000000) 3 (IntervalRat.scale (895 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-16812769051 / 1000000000000) (-16812769050 / 1000000000000), orderedInterval (-29357475301 / 1000000000000) (-29357475300 / 1000000000000)))) (orderedInterval (-24112808890 / 1000000000000) (-24112808493 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate576_chunkChecks3 :
    compactCertificate576.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate576.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate576_chunkChecks3_0
    compactCertificate576_chunkChecks3_1 compactCertificate576_chunkChecks3_2

theorem compactCertificate576_chunkChecks4_0 :
    compactCertificate576.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (895 / 2) 4 (IntervalRat.scale (895 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (30954653854 / 1000000000000) (30954728108 / 1000000000000), orderedInterval (-21585045849 / 1000000000000) (-21584971594 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (263701179674279 / 800000000000) 4 (IntervalRat.scale (895 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-22755264578 / 1000000000000) (-22755264577 / 1000000000000), orderedInterval (-37562502644 / 1000000000000) (-37562502643 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (85275543424007 / 160000000000) 4 (IntervalRat.scale (895 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-10656361827 / 1000000000000) (-10656361798 / 1000000000000), orderedInterval (32887244203 / 1000000000000) (32887244232 / 1000000000000)))) (orderedInterval (10924251011 / 1000000000000) (10924280632 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (76947346548853 / 800000000000) 4 (IntervalRat.scale (895 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (33254412832 / 1000000000000) (33254414943 / 1000000000000), orderedInterval (-74422180354 / 1000000000000) (-74422178242 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (206691396369841 / 800000000000) 4 (IntervalRat.scale (895 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (49613262343 / 1000000000000) (49613262409 / 1000000000000), orderedInterval (1503782360 / 1000000000000) (1503782426 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (561207348346797 / 800000000000) 4 (IntervalRat.scale (895 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29793430999 / 1000000000000) (-29793422271 / 1000000000000), orderedInterval (4476763105 / 1000000000000) (4476771832 / 1000000000000)))) (orderedInterval (12985535094 / 1000000000000) (12985539047 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (413382792739861 / 800000000000) 4 (IntervalRat.scale (895 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (26350114929 / 1000000000000) (26350134443 / 1000000000000), orderedInterval (-23213665652 / 1000000000000) (-23213646137 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (708338461243753 / 800000000000) 4 (IntervalRat.scale (895 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (7389768121 / 1000000000000) (7389768122 / 1000000000000), orderedInterval (25771631139 / 1000000000000) (25771631140 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (521758904576827 / 800000000000) 4 (IntervalRat.scale (895 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-14077936637 / 1000000000000) (-14077936525 / 1000000000000), orderedInterval (27902102988 / 1000000000000) (27902103100 / 1000000000000)))) (orderedInterval (-5046506715 / 1000000000000) (-5046506441 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate576_chunkChecks4_1 :
    compactCertificate576.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (800512335944821 / 800000000000) 4 (IntervalRat.scale (895 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (17051704176 / 1000000000000) (17051704591 / 1000000000000), orderedInterval (-18594851964 / 1000000000000) (-18594851549 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (462176012647309 / 800000000000) 4 (IntervalRat.scale (895 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (14503179338 / 1000000000000) (14503179339 / 1000000000000), orderedInterval (29847289235 / 1000000000000) (29847289236 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (820139444856881 / 800000000000) 4 (IntervalRat.scale (895 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (24265719252 / 1000000000000) (24265803122 / 1000000000000), orderedInterval (-5682818215 / 1000000000000) (-5682734344 / 1000000000000)))) (orderedInterval (22392358098 / 1000000000000) (22392692808 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (766280655075989 / 800000000000) 4 (IntervalRat.scale (895 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-11221216867 / 1000000000000) (-11221216866 / 1000000000000), orderedInterval (-23204439353 / 1000000000000) (-23204439352 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (546854032931237 / 800000000000) 4 (IntervalRat.scale (895 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-15016122045 / 1000000000000) (-15016121873 / 1000000000000), orderedInterval (26578552080 / 1000000000000) (26578552251 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (620074189109523 / 800000000000) 4 (IntervalRat.scale (895 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (2730283636 / 1000000000000) (2730283637 / 1000000000000), orderedInterval (-28530559071 / 1000000000000) (-28530559070 / 1000000000000)))) (orderedInterval (-3541329238 / 1000000000000) (-3541328727 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (516953212895587 / 800000000000) 4 (IntervalRat.scale (895 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-5969936890 / 1000000000000) (-5969936888 / 1000000000000), orderedInterval (30819349203 / 1000000000000) (30819349205 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (456743841211327 / 800000000000) 4 (IntervalRat.scale (895 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-1831733225 / 1000000000000) (-1831733224 / 1000000000000), orderedInterval (33343815480 / 1000000000000) (33343815481 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (132382167629373 / 160000000000) 4 (IntervalRat.scale (895 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-25919982395 / 1000000000000) (-25919870651 / 1000000000000), orderedInterval (9894366888 / 1000000000000) (9894478632 / 1000000000000)))) (orderedInterval (-7783197451 / 1000000000000) (-7783163710 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate576_chunkChecks4_2 :
    compactCertificate576.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (366176042554631 / 800000000000) 4 (IntervalRat.scale (895 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-6212043363 / 1000000000000) (-6212043358 / 1000000000000), orderedInterval (36779886659 / 1000000000000) (36779886665 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (310411486562191 / 800000000000) 4 (IntervalRat.scale (895 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-27848079634 / 1000000000000) (-27848064398 / 1000000000000), orderedInterval (29450106033 / 1000000000000) (29450121268 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (194241095423173 / 800000000000) 4 (IntervalRat.scale (895 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-50879651755 / 1000000000000) (-50879651331 / 1000000000000), orderedInterval (5869610881 / 1000000000000) (5869611305 / 1000000000000)))) (orderedInterval (1801634884 / 1000000000000) (1801635471 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (104463507135291 / 800000000000) 4 (IntervalRat.scale (895 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-38443838374 / 1000000000000) (-38443828585 / 1000000000000), orderedInterval (58434695779 / 1000000000000) (58434705568 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (283638742918873 / 800000000000) 4 (IntervalRat.scale (895 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-13871480601 / 1000000000000) (-13871480600 / 1000000000000), orderedInterval (-40019950797 / 1000000000000) (-40019950796 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (387284454433721 / 800000000000) 4 (IntervalRat.scale (895 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (32075386655 / 1000000000000) (32075386656 / 1000000000000), orderedInterval (16884686145 / 1000000000000) (16884686146 / 1000000000000)))) (orderedInterval (-3242972919 / 1000000000000) (-3242972865 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (163758904576827 / 800000000000) 4 (IntervalRat.scale (895 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-53424576979 / 1000000000000) (-53424576978 / 1000000000000), orderedInterval (-15864540910 / 1000000000000) (-15864540909 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (665670855482267 / 800000000000) 4 (IntervalRat.scale (895 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-9530442364 / 1000000000000) (-9530442363 / 1000000000000), orderedInterval (-25960738540 / 1000000000000) (-25960738539 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (444637281569653 / 800000000000) 4 (IntervalRat.scale (895 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-16812769051 / 1000000000000) (-16812769050 / 1000000000000), orderedInterval (-29357475301 / 1000000000000) (-29357475300 / 1000000000000)))) (orderedInterval (16873609953 / 1000000000000) (16873610591 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate576_chunkChecks4 :
    compactCertificate576.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate576.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate576_chunkChecks4_0
    compactCertificate576_chunkChecks4_1 compactCertificate576_chunkChecks4_2

theorem compactCertificate576_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate576.chunkCheck r b = true :=
  compactCertificate576.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate576_chunkChecks0
    · exact compactCertificate576_chunkChecks1
    · exact compactCertificate576_chunkChecks2
    · exact compactCertificate576_chunkChecks3
    · exact compactCertificate576_chunkChecks4)

theorem compactCertificate576_coefficient0 :
    compactCertificate576.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate576_coefficient1 :
    compactCertificate576.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate576_coefficient2 :
    compactCertificate576.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate576_coefficient3 :
    compactCertificate576.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate576_coefficient4 :
    compactCertificate576.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate576_coefficients : ∀ r : Fin 5,
    compactCertificate576.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate576_coefficient0
  · exact compactCertificate576_coefficient1
  · exact compactCertificate576_coefficient2
  · exact compactCertificate576_coefficient3
  · exact compactCertificate576_coefficient4

theorem compactCertificate576_lower : (1 : ℚ) ≤ compactCertificate576.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate576, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate576_proves {t : ℝ} (ht : t ∈ compactCertificate576.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate576.proves compactCertificate576_states compactCertificate576_chunks
    compactCertificate576_coefficients compactCertificate576_lower ht

end Erdos232
