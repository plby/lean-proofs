/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate589 : CompactCertificate where
  left := 460
  right := 461
  center := 921 / 2
  grid := fun i =>
    match i.val with
    | 0 => 147
    | 1 => 108
    | 2 => 175
    | 3 => 32
    | 4 => 85
    | 5 => 230
    | 6 => 169
    | 7 => 290
    | 8 => 214
    | 9 => 328
    | 10 => 189
    | 11 => 336
    | 12 => 314
    | 13 => 224
    | 14 => 254
    | 15 => 212
    | 16 => 187
    | 17 => 271
    | 18 => 150
    | 19 => 127
    | 20 => 80
    | 21 => 43
    | 22 => 116
    | 23 => 159
    | 24 => 67
    | 25 => 273
    | _ => 182
  point := fun i =>
    match i.val with
    | 0 => 921 / 2
    | 1 => 1356808863016821 / 4000000000000
    | 2 => 438764108902293 / 800000000000
    | 3 => 395913442298847 / 4000000000000
    | 4 => 1063479195847059 / 4000000000000
    | 5 => 2887552892890503 / 4000000000000
    | 6 => 2126958391695039 / 4000000000000
    | 7 => 3644579457013947 / 4000000000000
    | 8 => 2684580732487473 / 4000000000000
    | 9 => 4118837214554079 / 4000000000000
    | 10 => 2378011774570791 / 4000000000000
    | 11 => 4219823624096019 / 4000000000000
    | 12 => 3942706610754111 / 4000000000000
    | 13 => 2813701476702063 / 4000000000000
    | 14 => 3190437587541177 / 4000000000000
    | 15 => 2659854240652713 / 4000000000000
    | 16 => 2350061886902973 / 4000000000000
    | 17 => 681139532886327 / 800000000000
    | 18 => 1884067794373269 / 4000000000000
    | 19 => 1597145134769709 / 4000000000000
    | 20 => 999419267512527 / 4000000000000
    | 21 => 537491005986609 / 4000000000000
    | 22 => 1459392638146827 / 4000000000000
    | 23 => 1992675880075179 / 4000000000000
    | 24 => 842580732487473 / 4000000000000
    | 25 => 3425043898878033 / 4000000000000
    | _ => 2287770593998047 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (18764107062 / 1000000000000) (18764107937 / 1000000000000), orderedInterval (-32119626812 / 1000000000000) (-32119625938 / 1000000000000))
    | 1 => (orderedInterval (27750850606 / 1000000000000) (27750850607 / 1000000000000), orderedInterval (33226278395 / 1000000000000) (33226278396 / 1000000000000))
    | 2 => (orderedInterval (17469959845 / 1000000000000) (17469960414 / 1000000000000), orderedInterval (-29265740187 / 1000000000000) (-29265739618 / 1000000000000))
    | 3 => (orderedInterval (-55740936915 / 1000000000000) (-55740873512 / 1000000000000), orderedInterval (57943163101 / 1000000000000) (57943226504 / 1000000000000))
    | 4 => (orderedInterval (18179859784 / 1000000000000) (18179860258 / 1000000000000), orderedInterval (-45465183489 / 1000000000000) (-45465183015 / 1000000000000))
    | 5 => (orderedInterval (3175535798 / 1000000000000) (3175535799 / 1000000000000), orderedInterval (29524018462 / 1000000000000) (29524018463 / 1000000000000))
    | 6 => (orderedInterval (-34590499573 / 1000000000000) (-34590498703 / 1000000000000), orderedInterval (890761502 / 1000000000000) (890762373 / 1000000000000))
    | 7 => (orderedInterval (20173738119 / 1000000000000) (20173738120 / 1000000000000), orderedInterval (17068841845 / 1000000000000) (17068841846 / 1000000000000))
    | 8 => (orderedInterval (-11149696705 / 1000000000000) (-11149696682 / 1000000000000), orderedInterval (28717920195 / 1000000000000) (28717920219 / 1000000000000))
    | 9 => (orderedInterval (1297098925 / 1000000000000) (1297098926 / 1000000000000), orderedInterval (24830188608 / 1000000000000) (24830188609 / 1000000000000))
    | 10 => (orderedInterval (-32692536511 / 1000000000000) (-32692535956 / 1000000000000), orderedInterval (-1401303068 / 1000000000000) (-1401302513 / 1000000000000))
    | 11 => (orderedInterval (4060455546 / 1000000000000) (4060455547 / 1000000000000), orderedInterval (24225519688 / 1000000000000) (24225519689 / 1000000000000))
    | 12 => (orderedInterval (46528113 / 1000000000000) (46528114 / 1000000000000), orderedInterval (25413923797 / 1000000000000) (25413923798 / 1000000000000))
    | 13 => (orderedInterval (14259857049 / 1000000000000) (14259857050 / 1000000000000), orderedInterval (26479197122 / 1000000000000) (26479197123 / 1000000000000))
    | 14 => (orderedInterval (11779995861 / 1000000000000) (11779995862 / 1000000000000), orderedInterval (25671237275 / 1000000000000) (25671237276 / 1000000000000))
    | 15 => (orderedInterval (-8219428928 / 1000000000000) (-8219428922 / 1000000000000), orderedInterval (29835974983 / 1000000000000) (29835974989 / 1000000000000))
    | 16 => (orderedInterval (-24131163692 / 1000000000000) (-24131163691 / 1000000000000), orderedInterval (-22368444989 / 1000000000000) (-22368444988 / 1000000000000))
    | 17 => (orderedInterval (-20326276269 / 1000000000000) (-20326276268 / 1000000000000), orderedInterval (-18278878419 / 1000000000000) (-18278878418 / 1000000000000))
    | 18 => (orderedInterval (19627537291 / 1000000000000) (19627537292 / 1000000000000), orderedInterval (31065267874 / 1000000000000) (31065267875 / 1000000000000))
    | 19 => (orderedInterval (-35386279610 / 1000000000000) (-35386279609 / 1000000000000), orderedInterval (-18454466382 / 1000000000000) (-18454466381 / 1000000000000))
    | 20 => (orderedInterval (-32040938387 / 1000000000000) (-32040923219 / 1000000000000), orderedInterval (39068450490 / 1000000000000) (39068465659 / 1000000000000))
    | 21 => (orderedInterval (-4727385026 / 1000000000000) (-4727385024 / 1000000000000), orderedInterval (-68651173387 / 1000000000000) (-68651173385 / 1000000000000))
    | 22 => (orderedInterval (39059769523 / 1000000000000) (39059769524 / 1000000000000), orderedInterval (14752646166 / 1000000000000) (14752646167 / 1000000000000))
    | 23 => (orderedInterval (18962015438 / 1000000000000) (18962016436 / 1000000000000), orderedInterval (-30323513609 / 1000000000000) (-30323512612 / 1000000000000))
    | 24 => (orderedInterval (-44501460480 / 1000000000000) (-44501460479 / 1000000000000), orderedInterval (-32172146065 / 1000000000000) (-32172146064 / 1000000000000))
    | 25 => (orderedInterval (15588331487 / 1000000000000) (15588331675 / 1000000000000), orderedInterval (-22380780665 / 1000000000000) (-22380780478 / 1000000000000))
    | _ => (orderedInterval (27291610995 / 1000000000000) (27291610996 / 1000000000000), orderedInterval (19166009965 / 1000000000000) (19166009966 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (8721176399 / 1000000000000) (8721176811 / 1000000000000)
      | 1 => orderedInterval (1042779652 / 1000000000000) (1042780413 / 1000000000000)
      | 2 => orderedInterval (-891704983 / 1000000000000) (-891704956 / 1000000000000)
      | 3 => orderedInterval (-2075509158 / 1000000000000) (-2075508934 / 1000000000000)
      | 4 => orderedInterval (1287999383 / 1000000000000) (1287999439 / 1000000000000)
      | 5 => orderedInterval (765598074 / 1000000000000) (765598118 / 1000000000000)
      | 6 => orderedInterval (-2178534489 / 1000000000000) (-2178533880 / 1000000000000)
      | 7 => orderedInterval (-2252079424 / 1000000000000) (-2252079292 / 1000000000000)
      | _ => orderedInterval (-6657817550 / 1000000000000) (-6657817407 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-14548401350 / 1000000000000) (-14548400928 / 1000000000000)
      | 1 => orderedInterval (-4383726155 / 1000000000000) (-4383725934 / 1000000000000)
      | 2 => orderedInterval (-30140530 / 1000000000000) (-30140484 / 1000000000000)
      | 3 => orderedInterval (-2110249162 / 1000000000000) (-2110248731 / 1000000000000)
      | 4 => orderedInterval (2617794640 / 1000000000000) (2617794729 / 1000000000000)
      | 5 => orderedInterval (1265340783 / 1000000000000) (1265340847 / 1000000000000)
      | 6 => orderedInterval (-3484776096 / 1000000000000) (-3484775721 / 1000000000000)
      | 7 => orderedInterval (2618786132 / 1000000000000) (2618786264 / 1000000000000)
      | _ => orderedInterval (-1167475422 / 1000000000000) (-1167475215 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-9000307702 / 1000000000000) (-9000307265 / 1000000000000)
      | 1 => orderedInterval (315080385 / 1000000000000) (315080511 / 1000000000000)
      | 2 => orderedInterval (3008411011 / 1000000000000) (3008411092 / 1000000000000)
      | 3 => orderedInterval (2164709371 / 1000000000000) (2164710251 / 1000000000000)
      | 4 => orderedInterval (-2969385912 / 1000000000000) (-2969385764 / 1000000000000)
      | 5 => orderedInterval (-273538553 / 1000000000000) (-273538457 / 1000000000000)
      | 6 => orderedInterval (2092141630 / 1000000000000) (2092141878 / 1000000000000)
      | 7 => orderedInterval (2243829326 / 1000000000000) (2243829465 / 1000000000000)
      | _ => orderedInterval (12344804079 / 1000000000000) (12344804397 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (15528134671 / 1000000000000) (15528135123 / 1000000000000)
      | 1 => orderedInterval (8410430108 / 1000000000000) (8410430249 / 1000000000000)
      | 2 => orderedInterval (1922879875 / 1000000000000) (1922880022 / 1000000000000)
      | 3 => orderedInterval (8141696553 / 1000000000000) (8141698422 / 1000000000000)
      | 4 => orderedInterval (-3743914450 / 1000000000000) (-3743914200 / 1000000000000)
      | 5 => orderedInterval (-737026659 / 1000000000000) (-737026512 / 1000000000000)
      | 6 => orderedInterval (4426640762 / 1000000000000) (4426640941 / 1000000000000)
      | 7 => orderedInterval (-2812085701 / 1000000000000) (-2812085553 / 1000000000000)
      | _ => orderedInterval (-4830847676 / 1000000000000) (-4830847170 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (9508777184 / 1000000000000) (9508777656 / 1000000000000)
      | 1 => orderedInterval (-1324760737 / 1000000000000) (-1324760533 / 1000000000000)
      | 2 => orderedInterval (-10760591584 / 1000000000000) (-10760591312 / 1000000000000)
      | 3 => orderedInterval (3372790415 / 1000000000000) (3372794482 / 1000000000000)
      | 4 => orderedInterval (6803669691 / 1000000000000) (6803670125 / 1000000000000)
      | 5 => orderedInterval (-2832482228 / 1000000000000) (-2832481996 / 1000000000000)
      | 6 => orderedInterval (-2412509352 / 1000000000000) (-2412509211 / 1000000000000)
      | 7 => orderedInterval (-2326626018 / 1000000000000) (-2326625859 / 1000000000000)
      | _ => orderedInterval (-27343798880 / 1000000000000) (-27343798041 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-2238092096 / 1000000000000) (-2238089688 / 1000000000000)
    | 1 => orderedInterval (-19222847160 / 1000000000000) (-19222845173 / 1000000000000)
    | 2 => orderedInterval (9925743635 / 1000000000000) (9925746108 / 1000000000000)
    | 3 => orderedInterval (26305907483 / 1000000000000) (26305911322 / 1000000000000)
    | _ => orderedInterval (-27315531509 / 1000000000000) (-27315524689 / 1000000000000)

theorem compactCertificate589_stateChecks0 :
    compactCertificate589.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 147 12 (921 / 2)) (orderedInterval (18764107062 / 1000000000000) (18764107937 / 1000000000000), orderedInterval (-32119626812 / 1000000000000) (-32119625938 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 108 12 (1356808863016821 / 4000000000000)) (orderedInterval (27750850606 / 1000000000000) (27750850607 / 1000000000000), orderedInterval (33226278395 / 1000000000000) (33226278396 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 175 12 (438764108902293 / 800000000000)) (orderedInterval (17469959845 / 1000000000000) (17469960414 / 1000000000000), orderedInterval (-29265740187 / 1000000000000) (-29265739618 / 1000000000000))) = true
  rfl'

theorem compactCertificate589_stateChecks1 :
    compactCertificate589.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (395913442298847 / 4000000000000)) (orderedInterval (-55740936915 / 1000000000000) (-55740873512 / 1000000000000), orderedInterval (57943163101 / 1000000000000) (57943226504 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (1063479195847059 / 4000000000000)) (orderedInterval (18179859784 / 1000000000000) (18179860258 / 1000000000000), orderedInterval (-45465183489 / 1000000000000) (-45465183015 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 230 12 (2887552892890503 / 4000000000000)) (orderedInterval (3175535798 / 1000000000000) (3175535799 / 1000000000000), orderedInterval (29524018462 / 1000000000000) (29524018463 / 1000000000000))) = true
  rfl'

theorem compactCertificate589_stateChecks2 :
    compactCertificate589.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 169 12 (2126958391695039 / 4000000000000)) (orderedInterval (-34590499573 / 1000000000000) (-34590498703 / 1000000000000), orderedInterval (890761502 / 1000000000000) (890762373 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 290 12 (3644579457013947 / 4000000000000)) (orderedInterval (20173738119 / 1000000000000) (20173738120 / 1000000000000), orderedInterval (17068841845 / 1000000000000) (17068841846 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 214 12 (2684580732487473 / 4000000000000)) (orderedInterval (-11149696705 / 1000000000000) (-11149696682 / 1000000000000), orderedInterval (28717920195 / 1000000000000) (28717920219 / 1000000000000))) = true
  rfl'

theorem compactCertificate589_stateChecks3 :
    compactCertificate589.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 328 12 (4118837214554079 / 4000000000000)) (orderedInterval (1297098925 / 1000000000000) (1297098926 / 1000000000000), orderedInterval (24830188608 / 1000000000000) (24830188609 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 189 12 (2378011774570791 / 4000000000000)) (orderedInterval (-32692536511 / 1000000000000) (-32692535956 / 1000000000000), orderedInterval (-1401303068 / 1000000000000) (-1401302513 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 336 12 (4219823624096019 / 4000000000000)) (orderedInterval (4060455546 / 1000000000000) (4060455547 / 1000000000000), orderedInterval (24225519688 / 1000000000000) (24225519689 / 1000000000000))) = true
  rfl'

theorem compactCertificate589_stateChecks4 :
    compactCertificate589.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 314 12 (3942706610754111 / 4000000000000)) (orderedInterval (46528113 / 1000000000000) (46528114 / 1000000000000), orderedInterval (25413923797 / 1000000000000) (25413923798 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 224 12 (2813701476702063 / 4000000000000)) (orderedInterval (14259857049 / 1000000000000) (14259857050 / 1000000000000), orderedInterval (26479197122 / 1000000000000) (26479197123 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 254 12 (3190437587541177 / 4000000000000)) (orderedInterval (11779995861 / 1000000000000) (11779995862 / 1000000000000), orderedInterval (25671237275 / 1000000000000) (25671237276 / 1000000000000))) = true
  rfl'

theorem compactCertificate589_stateChecks5 :
    compactCertificate589.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 212 12 (2659854240652713 / 4000000000000)) (orderedInterval (-8219428928 / 1000000000000) (-8219428922 / 1000000000000), orderedInterval (29835974983 / 1000000000000) (29835974989 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 187 12 (2350061886902973 / 4000000000000)) (orderedInterval (-24131163692 / 1000000000000) (-24131163691 / 1000000000000), orderedInterval (-22368444989 / 1000000000000) (-22368444988 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 271 12 (681139532886327 / 800000000000)) (orderedInterval (-20326276269 / 1000000000000) (-20326276268 / 1000000000000), orderedInterval (-18278878419 / 1000000000000) (-18278878418 / 1000000000000))) = true
  rfl'

theorem compactCertificate589_stateChecks6 :
    compactCertificate589.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 150 12 (1884067794373269 / 4000000000000)) (orderedInterval (19627537291 / 1000000000000) (19627537292 / 1000000000000), orderedInterval (31065267874 / 1000000000000) (31065267875 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 127 12 (1597145134769709 / 4000000000000)) (orderedInterval (-35386279610 / 1000000000000) (-35386279609 / 1000000000000), orderedInterval (-18454466382 / 1000000000000) (-18454466381 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (999419267512527 / 4000000000000)) (orderedInterval (-32040938387 / 1000000000000) (-32040923219 / 1000000000000), orderedInterval (39068450490 / 1000000000000) (39068465659 / 1000000000000))) = true
  rfl'

theorem compactCertificate589_stateChecks7 :
    compactCertificate589.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (537491005986609 / 4000000000000)) (orderedInterval (-4727385026 / 1000000000000) (-4727385024 / 1000000000000), orderedInterval (-68651173387 / 1000000000000) (-68651173385 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 116 12 (1459392638146827 / 4000000000000)) (orderedInterval (39059769523 / 1000000000000) (39059769524 / 1000000000000), orderedInterval (14752646166 / 1000000000000) (14752646167 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 159 12 (1992675880075179 / 4000000000000)) (orderedInterval (18962015438 / 1000000000000) (18962016436 / 1000000000000), orderedInterval (-30323513609 / 1000000000000) (-30323512612 / 1000000000000))) = true
  rfl'

theorem compactCertificate589_stateChecks8 :
    compactCertificate589.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (842580732487473 / 4000000000000)) (orderedInterval (-44501460480 / 1000000000000) (-44501460479 / 1000000000000), orderedInterval (-32172146065 / 1000000000000) (-32172146064 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 273 12 (3425043898878033 / 4000000000000)) (orderedInterval (15588331487 / 1000000000000) (15588331675 / 1000000000000), orderedInterval (-22380780665 / 1000000000000) (-22380780478 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 182 12 (2287770593998047 / 4000000000000)) (orderedInterval (27291610995 / 1000000000000) (27291610996 / 1000000000000), orderedInterval (19166009965 / 1000000000000) (19166009966 / 1000000000000))) = true
  rfl'

theorem compactCertificate589_states : ∀ j,
    BesselStateValid (compactCertificate589.point j) (compactCertificate589.state j) :=
  compactCertificate589.statesValid_of_checks3 compactCertificate589_stateChecks0
    compactCertificate589_stateChecks1 compactCertificate589_stateChecks2
    compactCertificate589_stateChecks3 compactCertificate589_stateChecks4
    compactCertificate589_stateChecks5 compactCertificate589_stateChecks6
    compactCertificate589_stateChecks7 compactCertificate589_stateChecks8

theorem compactCertificate589_chunkChecks0_0 :
    compactCertificate589.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (921 / 2) 0 (IntervalRat.scale (921 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (18764107062 / 1000000000000) (18764107937 / 1000000000000), orderedInterval (-32119626812 / 1000000000000) (-32119625938 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1356808863016821 / 4000000000000) 0 (IntervalRat.scale (921 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (27750850606 / 1000000000000) (27750850607 / 1000000000000), orderedInterval (33226278395 / 1000000000000) (33226278396 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (438764108902293 / 800000000000) 0 (IntervalRat.scale (921 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (17469959845 / 1000000000000) (17469960414 / 1000000000000), orderedInterval (-29265740187 / 1000000000000) (-29265739618 / 1000000000000)))) (orderedInterval (8721176399 / 1000000000000) (8721176811 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (395913442298847 / 4000000000000) 0 (IntervalRat.scale (921 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-55740936915 / 1000000000000) (-55740873512 / 1000000000000), orderedInterval (57943163101 / 1000000000000) (57943226504 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (1063479195847059 / 4000000000000) 0 (IntervalRat.scale (921 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (18179859784 / 1000000000000) (18179860258 / 1000000000000), orderedInterval (-45465183489 / 1000000000000) (-45465183015 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2887552892890503 / 4000000000000) 0 (IntervalRat.scale (921 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (3175535798 / 1000000000000) (3175535799 / 1000000000000), orderedInterval (29524018462 / 1000000000000) (29524018463 / 1000000000000)))) (orderedInterval (1042779652 / 1000000000000) (1042780413 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (2126958391695039 / 4000000000000) 0 (IntervalRat.scale (921 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-34590499573 / 1000000000000) (-34590498703 / 1000000000000), orderedInterval (890761502 / 1000000000000) (890762373 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3644579457013947 / 4000000000000) 0 (IntervalRat.scale (921 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (20173738119 / 1000000000000) (20173738120 / 1000000000000), orderedInterval (17068841845 / 1000000000000) (17068841846 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2684580732487473 / 4000000000000) 0 (IntervalRat.scale (921 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-11149696705 / 1000000000000) (-11149696682 / 1000000000000), orderedInterval (28717920195 / 1000000000000) (28717920219 / 1000000000000)))) (orderedInterval (-891704983 / 1000000000000) (-891704956 / 1000000000000))) = true
  rfl'

theorem compactCertificate589_chunkChecks0_1 :
    compactCertificate589.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (4118837214554079 / 4000000000000) 0 (IntervalRat.scale (921 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (1297098925 / 1000000000000) (1297098926 / 1000000000000), orderedInterval (24830188608 / 1000000000000) (24830188609 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2378011774570791 / 4000000000000) 0 (IntervalRat.scale (921 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-32692536511 / 1000000000000) (-32692535956 / 1000000000000), orderedInterval (-1401303068 / 1000000000000) (-1401302513 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (4219823624096019 / 4000000000000) 0 (IntervalRat.scale (921 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (4060455546 / 1000000000000) (4060455547 / 1000000000000), orderedInterval (24225519688 / 1000000000000) (24225519689 / 1000000000000)))) (orderedInterval (-2075509158 / 1000000000000) (-2075508934 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3942706610754111 / 4000000000000) 0 (IntervalRat.scale (921 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (46528113 / 1000000000000) (46528114 / 1000000000000), orderedInterval (25413923797 / 1000000000000) (25413923798 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2813701476702063 / 4000000000000) 0 (IntervalRat.scale (921 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (14259857049 / 1000000000000) (14259857050 / 1000000000000), orderedInterval (26479197122 / 1000000000000) (26479197123 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (3190437587541177 / 4000000000000) 0 (IntervalRat.scale (921 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (11779995861 / 1000000000000) (11779995862 / 1000000000000), orderedInterval (25671237275 / 1000000000000) (25671237276 / 1000000000000)))) (orderedInterval (1287999383 / 1000000000000) (1287999439 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2659854240652713 / 4000000000000) 0 (IntervalRat.scale (921 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-8219428928 / 1000000000000) (-8219428922 / 1000000000000), orderedInterval (29835974983 / 1000000000000) (29835974989 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2350061886902973 / 4000000000000) 0 (IntervalRat.scale (921 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-24131163692 / 1000000000000) (-24131163691 / 1000000000000), orderedInterval (-22368444989 / 1000000000000) (-22368444988 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (681139532886327 / 800000000000) 0 (IntervalRat.scale (921 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-20326276269 / 1000000000000) (-20326276268 / 1000000000000), orderedInterval (-18278878419 / 1000000000000) (-18278878418 / 1000000000000)))) (orderedInterval (765598074 / 1000000000000) (765598118 / 1000000000000))) = true
  rfl'

theorem compactCertificate589_chunkChecks0_2 :
    compactCertificate589.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1884067794373269 / 4000000000000) 0 (IntervalRat.scale (921 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (19627537291 / 1000000000000) (19627537292 / 1000000000000), orderedInterval (31065267874 / 1000000000000) (31065267875 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1597145134769709 / 4000000000000) 0 (IntervalRat.scale (921 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-35386279610 / 1000000000000) (-35386279609 / 1000000000000), orderedInterval (-18454466382 / 1000000000000) (-18454466381 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (999419267512527 / 4000000000000) 0 (IntervalRat.scale (921 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-32040938387 / 1000000000000) (-32040923219 / 1000000000000), orderedInterval (39068450490 / 1000000000000) (39068465659 / 1000000000000)))) (orderedInterval (-2178534489 / 1000000000000) (-2178533880 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (537491005986609 / 4000000000000) 0 (IntervalRat.scale (921 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-4727385026 / 1000000000000) (-4727385024 / 1000000000000), orderedInterval (-68651173387 / 1000000000000) (-68651173385 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1459392638146827 / 4000000000000) 0 (IntervalRat.scale (921 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (39059769523 / 1000000000000) (39059769524 / 1000000000000), orderedInterval (14752646166 / 1000000000000) (14752646167 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1992675880075179 / 4000000000000) 0 (IntervalRat.scale (921 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (18962015438 / 1000000000000) (18962016436 / 1000000000000), orderedInterval (-30323513609 / 1000000000000) (-30323512612 / 1000000000000)))) (orderedInterval (-2252079424 / 1000000000000) (-2252079292 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (842580732487473 / 4000000000000) 0 (IntervalRat.scale (921 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-44501460480 / 1000000000000) (-44501460479 / 1000000000000), orderedInterval (-32172146065 / 1000000000000) (-32172146064 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3425043898878033 / 4000000000000) 0 (IntervalRat.scale (921 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (15588331487 / 1000000000000) (15588331675 / 1000000000000), orderedInterval (-22380780665 / 1000000000000) (-22380780478 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2287770593998047 / 4000000000000) 0 (IntervalRat.scale (921 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (27291610995 / 1000000000000) (27291610996 / 1000000000000), orderedInterval (19166009965 / 1000000000000) (19166009966 / 1000000000000)))) (orderedInterval (-6657817550 / 1000000000000) (-6657817407 / 1000000000000))) = true
  rfl'

theorem compactCertificate589_chunkChecks0 :
    compactCertificate589.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate589.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate589_chunkChecks0_0
    compactCertificate589_chunkChecks0_1 compactCertificate589_chunkChecks0_2

theorem compactCertificate589_chunkChecks1_0 :
    compactCertificate589.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (921 / 2) 1 (IntervalRat.scale (921 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (18764107062 / 1000000000000) (18764107937 / 1000000000000), orderedInterval (-32119626812 / 1000000000000) (-32119625938 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1356808863016821 / 4000000000000) 1 (IntervalRat.scale (921 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (27750850606 / 1000000000000) (27750850607 / 1000000000000), orderedInterval (33226278395 / 1000000000000) (33226278396 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (438764108902293 / 800000000000) 1 (IntervalRat.scale (921 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (17469959845 / 1000000000000) (17469960414 / 1000000000000), orderedInterval (-29265740187 / 1000000000000) (-29265739618 / 1000000000000)))) (orderedInterval (-14548401350 / 1000000000000) (-14548400928 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (395913442298847 / 4000000000000) 1 (IntervalRat.scale (921 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-55740936915 / 1000000000000) (-55740873512 / 1000000000000), orderedInterval (57943163101 / 1000000000000) (57943226504 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (1063479195847059 / 4000000000000) 1 (IntervalRat.scale (921 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (18179859784 / 1000000000000) (18179860258 / 1000000000000), orderedInterval (-45465183489 / 1000000000000) (-45465183015 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2887552892890503 / 4000000000000) 1 (IntervalRat.scale (921 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (3175535798 / 1000000000000) (3175535799 / 1000000000000), orderedInterval (29524018462 / 1000000000000) (29524018463 / 1000000000000)))) (orderedInterval (-4383726155 / 1000000000000) (-4383725934 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (2126958391695039 / 4000000000000) 1 (IntervalRat.scale (921 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-34590499573 / 1000000000000) (-34590498703 / 1000000000000), orderedInterval (890761502 / 1000000000000) (890762373 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3644579457013947 / 4000000000000) 1 (IntervalRat.scale (921 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (20173738119 / 1000000000000) (20173738120 / 1000000000000), orderedInterval (17068841845 / 1000000000000) (17068841846 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2684580732487473 / 4000000000000) 1 (IntervalRat.scale (921 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-11149696705 / 1000000000000) (-11149696682 / 1000000000000), orderedInterval (28717920195 / 1000000000000) (28717920219 / 1000000000000)))) (orderedInterval (-30140530 / 1000000000000) (-30140484 / 1000000000000))) = true
  rfl'

theorem compactCertificate589_chunkChecks1_1 :
    compactCertificate589.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (4118837214554079 / 4000000000000) 1 (IntervalRat.scale (921 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (1297098925 / 1000000000000) (1297098926 / 1000000000000), orderedInterval (24830188608 / 1000000000000) (24830188609 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2378011774570791 / 4000000000000) 1 (IntervalRat.scale (921 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-32692536511 / 1000000000000) (-32692535956 / 1000000000000), orderedInterval (-1401303068 / 1000000000000) (-1401302513 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (4219823624096019 / 4000000000000) 1 (IntervalRat.scale (921 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (4060455546 / 1000000000000) (4060455547 / 1000000000000), orderedInterval (24225519688 / 1000000000000) (24225519689 / 1000000000000)))) (orderedInterval (-2110249162 / 1000000000000) (-2110248731 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3942706610754111 / 4000000000000) 1 (IntervalRat.scale (921 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (46528113 / 1000000000000) (46528114 / 1000000000000), orderedInterval (25413923797 / 1000000000000) (25413923798 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2813701476702063 / 4000000000000) 1 (IntervalRat.scale (921 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (14259857049 / 1000000000000) (14259857050 / 1000000000000), orderedInterval (26479197122 / 1000000000000) (26479197123 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (3190437587541177 / 4000000000000) 1 (IntervalRat.scale (921 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (11779995861 / 1000000000000) (11779995862 / 1000000000000), orderedInterval (25671237275 / 1000000000000) (25671237276 / 1000000000000)))) (orderedInterval (2617794640 / 1000000000000) (2617794729 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2659854240652713 / 4000000000000) 1 (IntervalRat.scale (921 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-8219428928 / 1000000000000) (-8219428922 / 1000000000000), orderedInterval (29835974983 / 1000000000000) (29835974989 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2350061886902973 / 4000000000000) 1 (IntervalRat.scale (921 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-24131163692 / 1000000000000) (-24131163691 / 1000000000000), orderedInterval (-22368444989 / 1000000000000) (-22368444988 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (681139532886327 / 800000000000) 1 (IntervalRat.scale (921 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-20326276269 / 1000000000000) (-20326276268 / 1000000000000), orderedInterval (-18278878419 / 1000000000000) (-18278878418 / 1000000000000)))) (orderedInterval (1265340783 / 1000000000000) (1265340847 / 1000000000000))) = true
  rfl'

theorem compactCertificate589_chunkChecks1_2 :
    compactCertificate589.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1884067794373269 / 4000000000000) 1 (IntervalRat.scale (921 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (19627537291 / 1000000000000) (19627537292 / 1000000000000), orderedInterval (31065267874 / 1000000000000) (31065267875 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1597145134769709 / 4000000000000) 1 (IntervalRat.scale (921 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-35386279610 / 1000000000000) (-35386279609 / 1000000000000), orderedInterval (-18454466382 / 1000000000000) (-18454466381 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (999419267512527 / 4000000000000) 1 (IntervalRat.scale (921 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-32040938387 / 1000000000000) (-32040923219 / 1000000000000), orderedInterval (39068450490 / 1000000000000) (39068465659 / 1000000000000)))) (orderedInterval (-3484776096 / 1000000000000) (-3484775721 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (537491005986609 / 4000000000000) 1 (IntervalRat.scale (921 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-4727385026 / 1000000000000) (-4727385024 / 1000000000000), orderedInterval (-68651173387 / 1000000000000) (-68651173385 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1459392638146827 / 4000000000000) 1 (IntervalRat.scale (921 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (39059769523 / 1000000000000) (39059769524 / 1000000000000), orderedInterval (14752646166 / 1000000000000) (14752646167 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1992675880075179 / 4000000000000) 1 (IntervalRat.scale (921 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (18962015438 / 1000000000000) (18962016436 / 1000000000000), orderedInterval (-30323513609 / 1000000000000) (-30323512612 / 1000000000000)))) (orderedInterval (2618786132 / 1000000000000) (2618786264 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (842580732487473 / 4000000000000) 1 (IntervalRat.scale (921 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-44501460480 / 1000000000000) (-44501460479 / 1000000000000), orderedInterval (-32172146065 / 1000000000000) (-32172146064 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3425043898878033 / 4000000000000) 1 (IntervalRat.scale (921 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (15588331487 / 1000000000000) (15588331675 / 1000000000000), orderedInterval (-22380780665 / 1000000000000) (-22380780478 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2287770593998047 / 4000000000000) 1 (IntervalRat.scale (921 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (27291610995 / 1000000000000) (27291610996 / 1000000000000), orderedInterval (19166009965 / 1000000000000) (19166009966 / 1000000000000)))) (orderedInterval (-1167475422 / 1000000000000) (-1167475215 / 1000000000000))) = true
  rfl'

theorem compactCertificate589_chunkChecks1 :
    compactCertificate589.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate589.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate589_chunkChecks1_0
    compactCertificate589_chunkChecks1_1 compactCertificate589_chunkChecks1_2

theorem compactCertificate589_chunkChecks2_0 :
    compactCertificate589.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (921 / 2) 2 (IntervalRat.scale (921 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (18764107062 / 1000000000000) (18764107937 / 1000000000000), orderedInterval (-32119626812 / 1000000000000) (-32119625938 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1356808863016821 / 4000000000000) 2 (IntervalRat.scale (921 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (27750850606 / 1000000000000) (27750850607 / 1000000000000), orderedInterval (33226278395 / 1000000000000) (33226278396 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (438764108902293 / 800000000000) 2 (IntervalRat.scale (921 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (17469959845 / 1000000000000) (17469960414 / 1000000000000), orderedInterval (-29265740187 / 1000000000000) (-29265739618 / 1000000000000)))) (orderedInterval (-9000307702 / 1000000000000) (-9000307265 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (395913442298847 / 4000000000000) 2 (IntervalRat.scale (921 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-55740936915 / 1000000000000) (-55740873512 / 1000000000000), orderedInterval (57943163101 / 1000000000000) (57943226504 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (1063479195847059 / 4000000000000) 2 (IntervalRat.scale (921 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (18179859784 / 1000000000000) (18179860258 / 1000000000000), orderedInterval (-45465183489 / 1000000000000) (-45465183015 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2887552892890503 / 4000000000000) 2 (IntervalRat.scale (921 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (3175535798 / 1000000000000) (3175535799 / 1000000000000), orderedInterval (29524018462 / 1000000000000) (29524018463 / 1000000000000)))) (orderedInterval (315080385 / 1000000000000) (315080511 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (2126958391695039 / 4000000000000) 2 (IntervalRat.scale (921 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-34590499573 / 1000000000000) (-34590498703 / 1000000000000), orderedInterval (890761502 / 1000000000000) (890762373 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3644579457013947 / 4000000000000) 2 (IntervalRat.scale (921 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (20173738119 / 1000000000000) (20173738120 / 1000000000000), orderedInterval (17068841845 / 1000000000000) (17068841846 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2684580732487473 / 4000000000000) 2 (IntervalRat.scale (921 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-11149696705 / 1000000000000) (-11149696682 / 1000000000000), orderedInterval (28717920195 / 1000000000000) (28717920219 / 1000000000000)))) (orderedInterval (3008411011 / 1000000000000) (3008411092 / 1000000000000))) = true
  rfl'

theorem compactCertificate589_chunkChecks2_1 :
    compactCertificate589.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (4118837214554079 / 4000000000000) 2 (IntervalRat.scale (921 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (1297098925 / 1000000000000) (1297098926 / 1000000000000), orderedInterval (24830188608 / 1000000000000) (24830188609 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2378011774570791 / 4000000000000) 2 (IntervalRat.scale (921 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-32692536511 / 1000000000000) (-32692535956 / 1000000000000), orderedInterval (-1401303068 / 1000000000000) (-1401302513 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (4219823624096019 / 4000000000000) 2 (IntervalRat.scale (921 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (4060455546 / 1000000000000) (4060455547 / 1000000000000), orderedInterval (24225519688 / 1000000000000) (24225519689 / 1000000000000)))) (orderedInterval (2164709371 / 1000000000000) (2164710251 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3942706610754111 / 4000000000000) 2 (IntervalRat.scale (921 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (46528113 / 1000000000000) (46528114 / 1000000000000), orderedInterval (25413923797 / 1000000000000) (25413923798 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2813701476702063 / 4000000000000) 2 (IntervalRat.scale (921 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (14259857049 / 1000000000000) (14259857050 / 1000000000000), orderedInterval (26479197122 / 1000000000000) (26479197123 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (3190437587541177 / 4000000000000) 2 (IntervalRat.scale (921 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (11779995861 / 1000000000000) (11779995862 / 1000000000000), orderedInterval (25671237275 / 1000000000000) (25671237276 / 1000000000000)))) (orderedInterval (-2969385912 / 1000000000000) (-2969385764 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2659854240652713 / 4000000000000) 2 (IntervalRat.scale (921 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-8219428928 / 1000000000000) (-8219428922 / 1000000000000), orderedInterval (29835974983 / 1000000000000) (29835974989 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2350061886902973 / 4000000000000) 2 (IntervalRat.scale (921 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-24131163692 / 1000000000000) (-24131163691 / 1000000000000), orderedInterval (-22368444989 / 1000000000000) (-22368444988 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (681139532886327 / 800000000000) 2 (IntervalRat.scale (921 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-20326276269 / 1000000000000) (-20326276268 / 1000000000000), orderedInterval (-18278878419 / 1000000000000) (-18278878418 / 1000000000000)))) (orderedInterval (-273538553 / 1000000000000) (-273538457 / 1000000000000))) = true
  rfl'

theorem compactCertificate589_chunkChecks2_2 :
    compactCertificate589.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1884067794373269 / 4000000000000) 2 (IntervalRat.scale (921 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (19627537291 / 1000000000000) (19627537292 / 1000000000000), orderedInterval (31065267874 / 1000000000000) (31065267875 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1597145134769709 / 4000000000000) 2 (IntervalRat.scale (921 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-35386279610 / 1000000000000) (-35386279609 / 1000000000000), orderedInterval (-18454466382 / 1000000000000) (-18454466381 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (999419267512527 / 4000000000000) 2 (IntervalRat.scale (921 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-32040938387 / 1000000000000) (-32040923219 / 1000000000000), orderedInterval (39068450490 / 1000000000000) (39068465659 / 1000000000000)))) (orderedInterval (2092141630 / 1000000000000) (2092141878 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (537491005986609 / 4000000000000) 2 (IntervalRat.scale (921 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-4727385026 / 1000000000000) (-4727385024 / 1000000000000), orderedInterval (-68651173387 / 1000000000000) (-68651173385 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1459392638146827 / 4000000000000) 2 (IntervalRat.scale (921 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (39059769523 / 1000000000000) (39059769524 / 1000000000000), orderedInterval (14752646166 / 1000000000000) (14752646167 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1992675880075179 / 4000000000000) 2 (IntervalRat.scale (921 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (18962015438 / 1000000000000) (18962016436 / 1000000000000), orderedInterval (-30323513609 / 1000000000000) (-30323512612 / 1000000000000)))) (orderedInterval (2243829326 / 1000000000000) (2243829465 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (842580732487473 / 4000000000000) 2 (IntervalRat.scale (921 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-44501460480 / 1000000000000) (-44501460479 / 1000000000000), orderedInterval (-32172146065 / 1000000000000) (-32172146064 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3425043898878033 / 4000000000000) 2 (IntervalRat.scale (921 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (15588331487 / 1000000000000) (15588331675 / 1000000000000), orderedInterval (-22380780665 / 1000000000000) (-22380780478 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2287770593998047 / 4000000000000) 2 (IntervalRat.scale (921 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (27291610995 / 1000000000000) (27291610996 / 1000000000000), orderedInterval (19166009965 / 1000000000000) (19166009966 / 1000000000000)))) (orderedInterval (12344804079 / 1000000000000) (12344804397 / 1000000000000))) = true
  rfl'

theorem compactCertificate589_chunkChecks2 :
    compactCertificate589.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate589.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate589_chunkChecks2_0
    compactCertificate589_chunkChecks2_1 compactCertificate589_chunkChecks2_2

theorem compactCertificate589_chunkChecks3_0 :
    compactCertificate589.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (921 / 2) 3 (IntervalRat.scale (921 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (18764107062 / 1000000000000) (18764107937 / 1000000000000), orderedInterval (-32119626812 / 1000000000000) (-32119625938 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1356808863016821 / 4000000000000) 3 (IntervalRat.scale (921 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (27750850606 / 1000000000000) (27750850607 / 1000000000000), orderedInterval (33226278395 / 1000000000000) (33226278396 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (438764108902293 / 800000000000) 3 (IntervalRat.scale (921 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (17469959845 / 1000000000000) (17469960414 / 1000000000000), orderedInterval (-29265740187 / 1000000000000) (-29265739618 / 1000000000000)))) (orderedInterval (15528134671 / 1000000000000) (15528135123 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (395913442298847 / 4000000000000) 3 (IntervalRat.scale (921 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-55740936915 / 1000000000000) (-55740873512 / 1000000000000), orderedInterval (57943163101 / 1000000000000) (57943226504 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (1063479195847059 / 4000000000000) 3 (IntervalRat.scale (921 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (18179859784 / 1000000000000) (18179860258 / 1000000000000), orderedInterval (-45465183489 / 1000000000000) (-45465183015 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2887552892890503 / 4000000000000) 3 (IntervalRat.scale (921 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (3175535798 / 1000000000000) (3175535799 / 1000000000000), orderedInterval (29524018462 / 1000000000000) (29524018463 / 1000000000000)))) (orderedInterval (8410430108 / 1000000000000) (8410430249 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (2126958391695039 / 4000000000000) 3 (IntervalRat.scale (921 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-34590499573 / 1000000000000) (-34590498703 / 1000000000000), orderedInterval (890761502 / 1000000000000) (890762373 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3644579457013947 / 4000000000000) 3 (IntervalRat.scale (921 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (20173738119 / 1000000000000) (20173738120 / 1000000000000), orderedInterval (17068841845 / 1000000000000) (17068841846 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2684580732487473 / 4000000000000) 3 (IntervalRat.scale (921 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-11149696705 / 1000000000000) (-11149696682 / 1000000000000), orderedInterval (28717920195 / 1000000000000) (28717920219 / 1000000000000)))) (orderedInterval (1922879875 / 1000000000000) (1922880022 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate589_chunkChecks3_1 :
    compactCertificate589.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (4118837214554079 / 4000000000000) 3 (IntervalRat.scale (921 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (1297098925 / 1000000000000) (1297098926 / 1000000000000), orderedInterval (24830188608 / 1000000000000) (24830188609 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2378011774570791 / 4000000000000) 3 (IntervalRat.scale (921 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-32692536511 / 1000000000000) (-32692535956 / 1000000000000), orderedInterval (-1401303068 / 1000000000000) (-1401302513 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (4219823624096019 / 4000000000000) 3 (IntervalRat.scale (921 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (4060455546 / 1000000000000) (4060455547 / 1000000000000), orderedInterval (24225519688 / 1000000000000) (24225519689 / 1000000000000)))) (orderedInterval (8141696553 / 1000000000000) (8141698422 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3942706610754111 / 4000000000000) 3 (IntervalRat.scale (921 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (46528113 / 1000000000000) (46528114 / 1000000000000), orderedInterval (25413923797 / 1000000000000) (25413923798 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2813701476702063 / 4000000000000) 3 (IntervalRat.scale (921 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (14259857049 / 1000000000000) (14259857050 / 1000000000000), orderedInterval (26479197122 / 1000000000000) (26479197123 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (3190437587541177 / 4000000000000) 3 (IntervalRat.scale (921 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (11779995861 / 1000000000000) (11779995862 / 1000000000000), orderedInterval (25671237275 / 1000000000000) (25671237276 / 1000000000000)))) (orderedInterval (-3743914450 / 1000000000000) (-3743914200 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2659854240652713 / 4000000000000) 3 (IntervalRat.scale (921 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-8219428928 / 1000000000000) (-8219428922 / 1000000000000), orderedInterval (29835974983 / 1000000000000) (29835974989 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2350061886902973 / 4000000000000) 3 (IntervalRat.scale (921 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-24131163692 / 1000000000000) (-24131163691 / 1000000000000), orderedInterval (-22368444989 / 1000000000000) (-22368444988 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (681139532886327 / 800000000000) 3 (IntervalRat.scale (921 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-20326276269 / 1000000000000) (-20326276268 / 1000000000000), orderedInterval (-18278878419 / 1000000000000) (-18278878418 / 1000000000000)))) (orderedInterval (-737026659 / 1000000000000) (-737026512 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate589_chunkChecks3_2 :
    compactCertificate589.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1884067794373269 / 4000000000000) 3 (IntervalRat.scale (921 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (19627537291 / 1000000000000) (19627537292 / 1000000000000), orderedInterval (31065267874 / 1000000000000) (31065267875 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1597145134769709 / 4000000000000) 3 (IntervalRat.scale (921 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-35386279610 / 1000000000000) (-35386279609 / 1000000000000), orderedInterval (-18454466382 / 1000000000000) (-18454466381 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (999419267512527 / 4000000000000) 3 (IntervalRat.scale (921 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-32040938387 / 1000000000000) (-32040923219 / 1000000000000), orderedInterval (39068450490 / 1000000000000) (39068465659 / 1000000000000)))) (orderedInterval (4426640762 / 1000000000000) (4426640941 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (537491005986609 / 4000000000000) 3 (IntervalRat.scale (921 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-4727385026 / 1000000000000) (-4727385024 / 1000000000000), orderedInterval (-68651173387 / 1000000000000) (-68651173385 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1459392638146827 / 4000000000000) 3 (IntervalRat.scale (921 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (39059769523 / 1000000000000) (39059769524 / 1000000000000), orderedInterval (14752646166 / 1000000000000) (14752646167 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1992675880075179 / 4000000000000) 3 (IntervalRat.scale (921 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (18962015438 / 1000000000000) (18962016436 / 1000000000000), orderedInterval (-30323513609 / 1000000000000) (-30323512612 / 1000000000000)))) (orderedInterval (-2812085701 / 1000000000000) (-2812085553 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (842580732487473 / 4000000000000) 3 (IntervalRat.scale (921 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-44501460480 / 1000000000000) (-44501460479 / 1000000000000), orderedInterval (-32172146065 / 1000000000000) (-32172146064 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3425043898878033 / 4000000000000) 3 (IntervalRat.scale (921 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (15588331487 / 1000000000000) (15588331675 / 1000000000000), orderedInterval (-22380780665 / 1000000000000) (-22380780478 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2287770593998047 / 4000000000000) 3 (IntervalRat.scale (921 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (27291610995 / 1000000000000) (27291610996 / 1000000000000), orderedInterval (19166009965 / 1000000000000) (19166009966 / 1000000000000)))) (orderedInterval (-4830847676 / 1000000000000) (-4830847170 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate589_chunkChecks3 :
    compactCertificate589.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate589.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate589_chunkChecks3_0
    compactCertificate589_chunkChecks3_1 compactCertificate589_chunkChecks3_2

theorem compactCertificate589_chunkChecks4_0 :
    compactCertificate589.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (921 / 2) 4 (IntervalRat.scale (921 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (18764107062 / 1000000000000) (18764107937 / 1000000000000), orderedInterval (-32119626812 / 1000000000000) (-32119625938 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1356808863016821 / 4000000000000) 4 (IntervalRat.scale (921 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (27750850606 / 1000000000000) (27750850607 / 1000000000000), orderedInterval (33226278395 / 1000000000000) (33226278396 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (438764108902293 / 800000000000) 4 (IntervalRat.scale (921 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (17469959845 / 1000000000000) (17469960414 / 1000000000000), orderedInterval (-29265740187 / 1000000000000) (-29265739618 / 1000000000000)))) (orderedInterval (9508777184 / 1000000000000) (9508777656 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (395913442298847 / 4000000000000) 4 (IntervalRat.scale (921 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-55740936915 / 1000000000000) (-55740873512 / 1000000000000), orderedInterval (57943163101 / 1000000000000) (57943226504 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (1063479195847059 / 4000000000000) 4 (IntervalRat.scale (921 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (18179859784 / 1000000000000) (18179860258 / 1000000000000), orderedInterval (-45465183489 / 1000000000000) (-45465183015 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2887552892890503 / 4000000000000) 4 (IntervalRat.scale (921 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (3175535798 / 1000000000000) (3175535799 / 1000000000000), orderedInterval (29524018462 / 1000000000000) (29524018463 / 1000000000000)))) (orderedInterval (-1324760737 / 1000000000000) (-1324760533 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (2126958391695039 / 4000000000000) 4 (IntervalRat.scale (921 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-34590499573 / 1000000000000) (-34590498703 / 1000000000000), orderedInterval (890761502 / 1000000000000) (890762373 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3644579457013947 / 4000000000000) 4 (IntervalRat.scale (921 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (20173738119 / 1000000000000) (20173738120 / 1000000000000), orderedInterval (17068841845 / 1000000000000) (17068841846 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2684580732487473 / 4000000000000) 4 (IntervalRat.scale (921 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-11149696705 / 1000000000000) (-11149696682 / 1000000000000), orderedInterval (28717920195 / 1000000000000) (28717920219 / 1000000000000)))) (orderedInterval (-10760591584 / 1000000000000) (-10760591312 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate589_chunkChecks4_1 :
    compactCertificate589.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (4118837214554079 / 4000000000000) 4 (IntervalRat.scale (921 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (1297098925 / 1000000000000) (1297098926 / 1000000000000), orderedInterval (24830188608 / 1000000000000) (24830188609 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2378011774570791 / 4000000000000) 4 (IntervalRat.scale (921 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-32692536511 / 1000000000000) (-32692535956 / 1000000000000), orderedInterval (-1401303068 / 1000000000000) (-1401302513 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (4219823624096019 / 4000000000000) 4 (IntervalRat.scale (921 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (4060455546 / 1000000000000) (4060455547 / 1000000000000), orderedInterval (24225519688 / 1000000000000) (24225519689 / 1000000000000)))) (orderedInterval (3372790415 / 1000000000000) (3372794482 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3942706610754111 / 4000000000000) 4 (IntervalRat.scale (921 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (46528113 / 1000000000000) (46528114 / 1000000000000), orderedInterval (25413923797 / 1000000000000) (25413923798 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2813701476702063 / 4000000000000) 4 (IntervalRat.scale (921 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (14259857049 / 1000000000000) (14259857050 / 1000000000000), orderedInterval (26479197122 / 1000000000000) (26479197123 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (3190437587541177 / 4000000000000) 4 (IntervalRat.scale (921 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (11779995861 / 1000000000000) (11779995862 / 1000000000000), orderedInterval (25671237275 / 1000000000000) (25671237276 / 1000000000000)))) (orderedInterval (6803669691 / 1000000000000) (6803670125 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2659854240652713 / 4000000000000) 4 (IntervalRat.scale (921 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-8219428928 / 1000000000000) (-8219428922 / 1000000000000), orderedInterval (29835974983 / 1000000000000) (29835974989 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2350061886902973 / 4000000000000) 4 (IntervalRat.scale (921 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-24131163692 / 1000000000000) (-24131163691 / 1000000000000), orderedInterval (-22368444989 / 1000000000000) (-22368444988 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (681139532886327 / 800000000000) 4 (IntervalRat.scale (921 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-20326276269 / 1000000000000) (-20326276268 / 1000000000000), orderedInterval (-18278878419 / 1000000000000) (-18278878418 / 1000000000000)))) (orderedInterval (-2832482228 / 1000000000000) (-2832481996 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate589_chunkChecks4_2 :
    compactCertificate589.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1884067794373269 / 4000000000000) 4 (IntervalRat.scale (921 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (19627537291 / 1000000000000) (19627537292 / 1000000000000), orderedInterval (31065267874 / 1000000000000) (31065267875 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1597145134769709 / 4000000000000) 4 (IntervalRat.scale (921 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-35386279610 / 1000000000000) (-35386279609 / 1000000000000), orderedInterval (-18454466382 / 1000000000000) (-18454466381 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (999419267512527 / 4000000000000) 4 (IntervalRat.scale (921 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-32040938387 / 1000000000000) (-32040923219 / 1000000000000), orderedInterval (39068450490 / 1000000000000) (39068465659 / 1000000000000)))) (orderedInterval (-2412509352 / 1000000000000) (-2412509211 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (537491005986609 / 4000000000000) 4 (IntervalRat.scale (921 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-4727385026 / 1000000000000) (-4727385024 / 1000000000000), orderedInterval (-68651173387 / 1000000000000) (-68651173385 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1459392638146827 / 4000000000000) 4 (IntervalRat.scale (921 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (39059769523 / 1000000000000) (39059769524 / 1000000000000), orderedInterval (14752646166 / 1000000000000) (14752646167 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1992675880075179 / 4000000000000) 4 (IntervalRat.scale (921 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (18962015438 / 1000000000000) (18962016436 / 1000000000000), orderedInterval (-30323513609 / 1000000000000) (-30323512612 / 1000000000000)))) (orderedInterval (-2326626018 / 1000000000000) (-2326625859 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (842580732487473 / 4000000000000) 4 (IntervalRat.scale (921 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-44501460480 / 1000000000000) (-44501460479 / 1000000000000), orderedInterval (-32172146065 / 1000000000000) (-32172146064 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3425043898878033 / 4000000000000) 4 (IntervalRat.scale (921 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (15588331487 / 1000000000000) (15588331675 / 1000000000000), orderedInterval (-22380780665 / 1000000000000) (-22380780478 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2287770593998047 / 4000000000000) 4 (IntervalRat.scale (921 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (27291610995 / 1000000000000) (27291610996 / 1000000000000), orderedInterval (19166009965 / 1000000000000) (19166009966 / 1000000000000)))) (orderedInterval (-27343798880 / 1000000000000) (-27343798041 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate589_chunkChecks4 :
    compactCertificate589.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate589.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate589_chunkChecks4_0
    compactCertificate589_chunkChecks4_1 compactCertificate589_chunkChecks4_2

theorem compactCertificate589_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate589.chunkCheck r b = true :=
  compactCertificate589.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate589_chunkChecks0
    · exact compactCertificate589_chunkChecks1
    · exact compactCertificate589_chunkChecks2
    · exact compactCertificate589_chunkChecks3
    · exact compactCertificate589_chunkChecks4)

theorem compactCertificate589_coefficient0 :
    compactCertificate589.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate589_coefficient1 :
    compactCertificate589.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate589_coefficient2 :
    compactCertificate589.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate589_coefficient3 :
    compactCertificate589.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate589_coefficient4 :
    compactCertificate589.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate589_coefficients : ∀ r : Fin 5,
    compactCertificate589.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate589_coefficient0
  · exact compactCertificate589_coefficient1
  · exact compactCertificate589_coefficient2
  · exact compactCertificate589_coefficient3
  · exact compactCertificate589_coefficient4

theorem compactCertificate589_lower : (1 : ℚ) ≤ compactCertificate589.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate589, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate589_proves {t : ℝ} (ht : t ∈ compactCertificate589.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate589.proves compactCertificate589_states compactCertificate589_chunks
    compactCertificate589_coefficients compactCertificate589_lower ht

end Erdos232
