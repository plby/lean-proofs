/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate432 : CompactCertificate where
  left := 303
  right := 304
  center := 607 / 2
  grid := fun i =>
    match i.val with
    | 0 => 97
    | 1 => 71
    | 2 => 115
    | 3 => 21
    | 4 => 56
    | 5 => 152
    | 6 => 112
    | 7 => 191
    | 8 => 141
    | 9 => 216
    | 10 => 125
    | 11 => 221
    | 12 => 207
    | 13 => 148
    | 14 => 167
    | 15 => 140
    | 16 => 123
    | 17 => 179
    | 18 => 99
    | 19 => 84
    | 20 => 52
    | 21 => 28
    | 22 => 77
    | 23 => 105
    | 24 => 44
    | 25 => 180
    | _ => 120
  point := fun i =>
    match i.val with
    | 0 => 607 / 2
    | 1 => 894226905375907 / 4000000000000
    | 2 => 289174608147331 / 800000000000
    | 3 => 260933180755049 / 4000000000000
    | 4 => 700903226796053 / 4000000000000
    | 5 => 1903088605846401 / 4000000000000
    | 6 => 1401806453592713 / 4000000000000
    | 7 => 2402019251256749 / 4000000000000
    | 8 => 1769316508816391 / 4000000000000
    | 9 => 2714586524684393 / 4000000000000
    | 10 => 1567267260764897 / 4000000000000
    | 11 => 2781143257140373 / 4000000000000
    | 12 => 2598504791235337 / 4000000000000
    | 13 => 1854415631224921 / 4000000000000
    | 14 => 2102709680388159 / 4000000000000
    | 15 => 1753020113003471 / 4000000000000
    | 16 => 1548846433604891 / 4000000000000
    | 17 => 448916065648209 / 800000000000
    | 18 => 1241725462741123 / 4000000000000
    | 19 => 1052624426498603 / 4000000000000
    | 20 => 658683491183609 / 4000000000000
    | 21 => 354242172240903 / 4000000000000
    | 22 => 961836407551709 / 4000000000000
    | 23 => 1313305384588093 / 4000000000000
    | 24 => 555316508816391 / 4000000000000
    | 25 => 2257330778087911 / 4000000000000
    | _ => 1507792345881449 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (19900611598 / 1000000000000) (19900612472 / 1000000000000), orderedInterval (-41282772072 / 1000000000000) (-41282771198 / 1000000000000))
    | 1 => (orderedInterval (-51251246610 / 1000000000000) (-51251246608 / 1000000000000), orderedInterval (-14751158165 / 1000000000000) (-14751158163 / 1000000000000))
    | 2 => (orderedInterval (-34621460283 / 1000000000000) (-34621460282 / 1000000000000), orderedInterval (-23670437557 / 1000000000000) (-23670437556 / 1000000000000))
    | 3 => (orderedInterval (-4279257842 / 1000000000000) (-4279257838 / 1000000000000), orderedInterval (-98664196981 / 1000000000000) (-98664196977 / 1000000000000))
    | 4 => (orderedInterval (4895168653 / 1000000000000) (4895168655 / 1000000000000), orderedInterval (60062576970 / 1000000000000) (60062576972 / 1000000000000))
    | 5 => (orderedInterval (-30066115039 / 1000000000000) (-30066048142 / 1000000000000), orderedInterval (20866807573 / 1000000000000) (20866874470 / 1000000000000))
    | 6 => (orderedInterval (-24824133726 / 1000000000000) (-24824129068 / 1000000000000), orderedInterval (34681233725 / 1000000000000) (34681238383 / 1000000000000))
    | 7 => (orderedInterval (-30855419341 / 1000000000000) (-30855419330 / 1000000000000), orderedInterval (-10370644895 / 1000000000000) (-10370644884 / 1000000000000))
    | 8 => (orderedInterval (-5657233048 / 1000000000000) (-5657233047 / 1000000000000), orderedInterval (-37506817696 / 1000000000000) (-37506817695 / 1000000000000))
    | 9 => (orderedInterval (22966312078 / 1000000000000) (22966312079 / 1000000000000), orderedInterval (20246865328 / 1000000000000) (20246865329 / 1000000000000))
    | 10 => (orderedInterval (3911328410 / 1000000000000) (3911328413 / 1000000000000), orderedInterval (-40123467270 / 1000000000000) (-40123467267 / 1000000000000))
    | 11 => (orderedInterval (-29605431884 / 1000000000000) (-29605416623 / 1000000000000), orderedInterval (6277619531 / 1000000000000) (6277634792 / 1000000000000))
    | 12 => (orderedInterval (-3178948677 / 1000000000000) (-3178948676 / 1000000000000), orderedInterval (-31140340061 / 1000000000000) (-31140340060 / 1000000000000))
    | 13 => (orderedInterval (-19893166986 / 1000000000000) (-19893165646 / 1000000000000), orderedInterval (31285808814 / 1000000000000) (31285810155 / 1000000000000))
    | 14 => (orderedInterval (-33754009051 / 1000000000000) (-33753999571 / 1000000000000), orderedInterval (8500462025 / 1000000000000) (8500471506 / 1000000000000))
    | 15 => (orderedInterval (-26880881934 / 1000000000000) (-26880866796 / 1000000000000), orderedInterval (27049960564 / 1000000000000) (27049975701 / 1000000000000))
    | 16 => (orderedInterval (-40545627063 / 1000000000000) (-40545626775 / 1000000000000), orderedInterval (457461918 / 1000000000000) (457462207 / 1000000000000))
    | 17 => (orderedInterval (13575068250 / 1000000000000) (13575068352 / 1000000000000), orderedInterval (-30837718861 / 1000000000000) (-30837718759 / 1000000000000))
    | 18 => (orderedInterval (-8938578348 / 1000000000000) (-8938578347 / 1000000000000), orderedInterval (-44380003600 / 1000000000000) (-44380003599 / 1000000000000))
    | 19 => (orderedInterval (2322975085 / 1000000000000) (2322975087 / 1000000000000), orderedInterval (49125818437 / 1000000000000) (49125818439 / 1000000000000))
    | 20 => (orderedInterval (53899771389 / 1000000000000) (53899794805 / 1000000000000), orderedInterval (-31160726623 / 1000000000000) (-31160703208 / 1000000000000))
    | 21 => (orderedInterval (83244924733 / 1000000000000) (83244924735 / 1000000000000), orderedInterval (15614250550 / 1000000000000) (15614250552 / 1000000000000))
    | 22 => (orderedInterval (31492559957 / 1000000000000) (31492571926 / 1000000000000), orderedInterval (-40756245394 / 1000000000000) (-40756233424 / 1000000000000))
    | 23 => (orderedInterval (30203636996 / 1000000000000) (30203656911 / 1000000000000), orderedInterval (-32088548869 / 1000000000000) (-32088528955 / 1000000000000))
    | 24 => (orderedInterval (66533422230 / 1000000000000) (66533422233 / 1000000000000), orderedInterval (12366391602 / 1000000000000) (12366391605 / 1000000000000))
    | 25 => (orderedInterval (-12108226554 / 1000000000000) (-12108226502 / 1000000000000), orderedInterval (31339376044 / 1000000000000) (31339376096 / 1000000000000))
    | _ => (orderedInterval (27772195657 / 1000000000000) (27772195658 / 1000000000000), orderedInterval (30254818276 / 1000000000000) (30254818277 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (5378716817 / 1000000000000) (5378717185 / 1000000000000)
      | 1 => orderedInterval (2362542618 / 1000000000000) (2362547411 / 1000000000000)
      | 2 => orderedInterval (814980415 / 1000000000000) (814980433 / 1000000000000)
      | 3 => orderedInterval (-7999625750 / 1000000000000) (-7999623460 / 1000000000000)
      | 4 => orderedInterval (-1652950388 / 1000000000000) (-1652950177 / 1000000000000)
      | 5 => orderedInterval (2357455287 / 1000000000000) (2357455511 / 1000000000000)
      | 6 => orderedInterval (3052452458 / 1000000000000) (3052453297 / 1000000000000)
      | 7 => orderedInterval (-4566369062 / 1000000000000) (-4566367228 / 1000000000000)
      | _ => orderedInterval (-3824084215 / 1000000000000) (-3824084126 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-18118600067 / 1000000000000) (-18118599696 / 1000000000000)
      | 1 => orderedInterval (-829234935 / 1000000000000) (-829227438 / 1000000000000)
      | 2 => orderedInterval (-688209024 / 1000000000000) (-688208993 / 1000000000000)
      | 3 => orderedInterval (-9838029672 / 1000000000000) (-9838024452 / 1000000000000)
      | 4 => orderedInterval (5647954052 / 1000000000000) (5647954388 / 1000000000000)
      | 5 => orderedInterval (-1042186504 / 1000000000000) (-1042186183 / 1000000000000)
      | 6 => orderedInterval (4296768039 / 1000000000000) (4296768524 / 1000000000000)
      | 7 => orderedInterval (3308836249 / 1000000000000) (3308838148 / 1000000000000)
      | _ => orderedInterval (-11759785180 / 1000000000000) (-11759785054 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-4687274861 / 1000000000000) (-4687274485 / 1000000000000)
      | 1 => orderedInterval (-5311468151 / 1000000000000) (-5311456382 / 1000000000000)
      | 2 => orderedInterval (-3433102219 / 1000000000000) (-3433102164 / 1000000000000)
      | 3 => orderedInterval (42041041649 / 1000000000000) (42041053587 / 1000000000000)
      | 4 => orderedInterval (3595374740 / 1000000000000) (3595375278 / 1000000000000)
      | 5 => orderedInterval (-4314274126 / 1000000000000) (-4314273662 / 1000000000000)
      | 6 => orderedInterval (-1927110994 / 1000000000000) (-1927110701 / 1000000000000)
      | 7 => orderedInterval (3277420999 / 1000000000000) (3277422995 / 1000000000000)
      | _ => orderedInterval (4585116133 / 1000000000000) (4585116323 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (18779827339 / 1000000000000) (18779827719 / 1000000000000)
      | 1 => orderedInterval (5299388197 / 1000000000000) (5299406642 / 1000000000000)
      | 2 => orderedInterval (339754528 / 1000000000000) (339754627 / 1000000000000)
      | 3 => orderedInterval (35751125433 / 1000000000000) (35751152727 / 1000000000000)
      | 4 => orderedInterval (-15845952999 / 1000000000000) (-15845952131 / 1000000000000)
      | 5 => orderedInterval (4118491145 / 1000000000000) (4118491821 / 1000000000000)
      | 6 => orderedInterval (-5612414893 / 1000000000000) (-5612414705 / 1000000000000)
      | 7 => orderedInterval (-3576887907 / 1000000000000) (-3576885799 / 1000000000000)
      | _ => orderedInterval (27253707414 / 1000000000000) (27253707711 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (3535711490 / 1000000000000) (3535711876 / 1000000000000)
      | 1 => orderedInterval (12892532694 / 1000000000000) (12892561667 / 1000000000000)
      | 2 => orderedInterval (13966759150 / 1000000000000) (13966759333 / 1000000000000)
      | 3 => orderedInterval (-217370142508 / 1000000000000) (-217370079977 / 1000000000000)
      | 4 => orderedInterval (-7395419260 / 1000000000000) (-7395417847 / 1000000000000)
      | 5 => orderedInterval (8832499399 / 1000000000000) (8832500390 / 1000000000000)
      | 6 => orderedInterval (1679031126 / 1000000000000) (1679031257 / 1000000000000)
      | 7 => orderedInterval (-3439333540 / 1000000000000) (-3439331293 / 1000000000000)
      | _ => orderedInterval (-779208537 / 1000000000000) (-779208054 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-4076881820 / 1000000000000) (-4076871154 / 1000000000000)
    | 1 => orderedInterval (-29022487042 / 1000000000000) (-29022470756 / 1000000000000)
    | 2 => orderedInterval (33825723170 / 1000000000000) (33825750789 / 1000000000000)
    | 3 => orderedInterval (66507038257 / 1000000000000) (66507088612 / 1000000000000)
    | _ => orderedInterval (-188077569986 / 1000000000000) (-188077472648 / 1000000000000)

theorem compactCertificate432_stateChecks0 :
    compactCertificate432.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 97 12 (607 / 2)) (orderedInterval (19900611598 / 1000000000000) (19900612472 / 1000000000000), orderedInterval (-41282772072 / 1000000000000) (-41282771198 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (894226905375907 / 4000000000000)) (orderedInterval (-51251246610 / 1000000000000) (-51251246608 / 1000000000000), orderedInterval (-14751158165 / 1000000000000) (-14751158163 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 115 12 (289174608147331 / 800000000000)) (orderedInterval (-34621460283 / 1000000000000) (-34621460282 / 1000000000000), orderedInterval (-23670437557 / 1000000000000) (-23670437556 / 1000000000000))) = true
  rfl'

theorem compactCertificate432_stateChecks1 :
    compactCertificate432.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 21 12 (260933180755049 / 4000000000000)) (orderedInterval (-4279257842 / 1000000000000) (-4279257838 / 1000000000000), orderedInterval (-98664196981 / 1000000000000) (-98664196977 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (700903226796053 / 4000000000000)) (orderedInterval (4895168653 / 1000000000000) (4895168655 / 1000000000000), orderedInterval (60062576970 / 1000000000000) (60062576972 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 152 12 (1903088605846401 / 4000000000000)) (orderedInterval (-30066115039 / 1000000000000) (-30066048142 / 1000000000000), orderedInterval (20866807573 / 1000000000000) (20866874470 / 1000000000000))) = true
  rfl'

theorem compactCertificate432_stateChecks2 :
    compactCertificate432.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 112 12 (1401806453592713 / 4000000000000)) (orderedInterval (-24824133726 / 1000000000000) (-24824129068 / 1000000000000), orderedInterval (34681233725 / 1000000000000) (34681238383 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 191 12 (2402019251256749 / 4000000000000)) (orderedInterval (-30855419341 / 1000000000000) (-30855419330 / 1000000000000), orderedInterval (-10370644895 / 1000000000000) (-10370644884 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 141 12 (1769316508816391 / 4000000000000)) (orderedInterval (-5657233048 / 1000000000000) (-5657233047 / 1000000000000), orderedInterval (-37506817696 / 1000000000000) (-37506817695 / 1000000000000))) = true
  rfl'

theorem compactCertificate432_stateChecks3 :
    compactCertificate432.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 216 12 (2714586524684393 / 4000000000000)) (orderedInterval (22966312078 / 1000000000000) (22966312079 / 1000000000000), orderedInterval (20246865328 / 1000000000000) (20246865329 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 125 12 (1567267260764897 / 4000000000000)) (orderedInterval (3911328410 / 1000000000000) (3911328413 / 1000000000000), orderedInterval (-40123467270 / 1000000000000) (-40123467267 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 221 12 (2781143257140373 / 4000000000000)) (orderedInterval (-29605431884 / 1000000000000) (-29605416623 / 1000000000000), orderedInterval (6277619531 / 1000000000000) (6277634792 / 1000000000000))) = true
  rfl'

theorem compactCertificate432_stateChecks4 :
    compactCertificate432.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 207 12 (2598504791235337 / 4000000000000)) (orderedInterval (-3178948677 / 1000000000000) (-3178948676 / 1000000000000), orderedInterval (-31140340061 / 1000000000000) (-31140340060 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 148 12 (1854415631224921 / 4000000000000)) (orderedInterval (-19893166986 / 1000000000000) (-19893165646 / 1000000000000), orderedInterval (31285808814 / 1000000000000) (31285810155 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 167 12 (2102709680388159 / 4000000000000)) (orderedInterval (-33754009051 / 1000000000000) (-33753999571 / 1000000000000), orderedInterval (8500462025 / 1000000000000) (8500471506 / 1000000000000))) = true
  rfl'

theorem compactCertificate432_stateChecks5 :
    compactCertificate432.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 140 12 (1753020113003471 / 4000000000000)) (orderedInterval (-26880881934 / 1000000000000) (-26880866796 / 1000000000000), orderedInterval (27049960564 / 1000000000000) (27049975701 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 123 12 (1548846433604891 / 4000000000000)) (orderedInterval (-40545627063 / 1000000000000) (-40545626775 / 1000000000000), orderedInterval (457461918 / 1000000000000) (457462207 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 179 12 (448916065648209 / 800000000000)) (orderedInterval (13575068250 / 1000000000000) (13575068352 / 1000000000000), orderedInterval (-30837718861 / 1000000000000) (-30837718759 / 1000000000000))) = true
  rfl'

theorem compactCertificate432_stateChecks6 :
    compactCertificate432.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 99 12 (1241725462741123 / 4000000000000)) (orderedInterval (-8938578348 / 1000000000000) (-8938578347 / 1000000000000), orderedInterval (-44380003600 / 1000000000000) (-44380003599 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (1052624426498603 / 4000000000000)) (orderedInterval (2322975085 / 1000000000000) (2322975087 / 1000000000000), orderedInterval (49125818437 / 1000000000000) (49125818439 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (658683491183609 / 4000000000000)) (orderedInterval (53899771389 / 1000000000000) (53899794805 / 1000000000000), orderedInterval (-31160726623 / 1000000000000) (-31160703208 / 1000000000000))) = true
  rfl'

theorem compactCertificate432_stateChecks7 :
    compactCertificate432.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 28 12 (354242172240903 / 4000000000000)) (orderedInterval (83244924733 / 1000000000000) (83244924735 / 1000000000000), orderedInterval (15614250550 / 1000000000000) (15614250552 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (961836407551709 / 4000000000000)) (orderedInterval (31492559957 / 1000000000000) (31492571926 / 1000000000000), orderedInterval (-40756245394 / 1000000000000) (-40756233424 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 105 12 (1313305384588093 / 4000000000000)) (orderedInterval (30203636996 / 1000000000000) (30203656911 / 1000000000000), orderedInterval (-32088548869 / 1000000000000) (-32088528955 / 1000000000000))) = true
  rfl'

theorem compactCertificate432_stateChecks8 :
    compactCertificate432.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (555316508816391 / 4000000000000)) (orderedInterval (66533422230 / 1000000000000) (66533422233 / 1000000000000), orderedInterval (12366391602 / 1000000000000) (12366391605 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 180 12 (2257330778087911 / 4000000000000)) (orderedInterval (-12108226554 / 1000000000000) (-12108226502 / 1000000000000), orderedInterval (31339376044 / 1000000000000) (31339376096 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 120 12 (1507792345881449 / 4000000000000)) (orderedInterval (27772195657 / 1000000000000) (27772195658 / 1000000000000), orderedInterval (30254818276 / 1000000000000) (30254818277 / 1000000000000))) = true
  rfl'

theorem compactCertificate432_states : ∀ j,
    BesselStateValid (compactCertificate432.point j) (compactCertificate432.state j) :=
  compactCertificate432.statesValid_of_checks3 compactCertificate432_stateChecks0
    compactCertificate432_stateChecks1 compactCertificate432_stateChecks2
    compactCertificate432_stateChecks3 compactCertificate432_stateChecks4
    compactCertificate432_stateChecks5 compactCertificate432_stateChecks6
    compactCertificate432_stateChecks7 compactCertificate432_stateChecks8

theorem compactCertificate432_chunkChecks0_0 :
    compactCertificate432.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (607 / 2) 0 (IntervalRat.scale (607 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (19900611598 / 1000000000000) (19900612472 / 1000000000000), orderedInterval (-41282772072 / 1000000000000) (-41282771198 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (894226905375907 / 4000000000000) 0 (IntervalRat.scale (607 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-51251246610 / 1000000000000) (-51251246608 / 1000000000000), orderedInterval (-14751158165 / 1000000000000) (-14751158163 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (289174608147331 / 800000000000) 0 (IntervalRat.scale (607 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34621460283 / 1000000000000) (-34621460282 / 1000000000000), orderedInterval (-23670437557 / 1000000000000) (-23670437556 / 1000000000000)))) (orderedInterval (5378716817 / 1000000000000) (5378717185 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (260933180755049 / 4000000000000) 0 (IntervalRat.scale (607 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-4279257842 / 1000000000000) (-4279257838 / 1000000000000), orderedInterval (-98664196981 / 1000000000000) (-98664196977 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (700903226796053 / 4000000000000) 0 (IntervalRat.scale (607 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (4895168653 / 1000000000000) (4895168655 / 1000000000000), orderedInterval (60062576970 / 1000000000000) (60062576972 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1903088605846401 / 4000000000000) 0 (IntervalRat.scale (607 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30066115039 / 1000000000000) (-30066048142 / 1000000000000), orderedInterval (20866807573 / 1000000000000) (20866874470 / 1000000000000)))) (orderedInterval (2362542618 / 1000000000000) (2362547411 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1401806453592713 / 4000000000000) 0 (IntervalRat.scale (607 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-24824133726 / 1000000000000) (-24824129068 / 1000000000000), orderedInterval (34681233725 / 1000000000000) (34681238383 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2402019251256749 / 4000000000000) 0 (IntervalRat.scale (607 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-30855419341 / 1000000000000) (-30855419330 / 1000000000000), orderedInterval (-10370644895 / 1000000000000) (-10370644884 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1769316508816391 / 4000000000000) 0 (IntervalRat.scale (607 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-5657233048 / 1000000000000) (-5657233047 / 1000000000000), orderedInterval (-37506817696 / 1000000000000) (-37506817695 / 1000000000000)))) (orderedInterval (814980415 / 1000000000000) (814980433 / 1000000000000))) = true
  rfl'

theorem compactCertificate432_chunkChecks0_1 :
    compactCertificate432.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2714586524684393 / 4000000000000) 0 (IntervalRat.scale (607 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (22966312078 / 1000000000000) (22966312079 / 1000000000000), orderedInterval (20246865328 / 1000000000000) (20246865329 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1567267260764897 / 4000000000000) 0 (IntervalRat.scale (607 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (3911328410 / 1000000000000) (3911328413 / 1000000000000), orderedInterval (-40123467270 / 1000000000000) (-40123467267 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2781143257140373 / 4000000000000) 0 (IntervalRat.scale (607 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-29605431884 / 1000000000000) (-29605416623 / 1000000000000), orderedInterval (6277619531 / 1000000000000) (6277634792 / 1000000000000)))) (orderedInterval (-7999625750 / 1000000000000) (-7999623460 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2598504791235337 / 4000000000000) 0 (IntervalRat.scale (607 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-3178948677 / 1000000000000) (-3178948676 / 1000000000000), orderedInterval (-31140340061 / 1000000000000) (-31140340060 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1854415631224921 / 4000000000000) 0 (IntervalRat.scale (607 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-19893166986 / 1000000000000) (-19893165646 / 1000000000000), orderedInterval (31285808814 / 1000000000000) (31285810155 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2102709680388159 / 4000000000000) 0 (IntervalRat.scale (607 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-33754009051 / 1000000000000) (-33753999571 / 1000000000000), orderedInterval (8500462025 / 1000000000000) (8500471506 / 1000000000000)))) (orderedInterval (-1652950388 / 1000000000000) (-1652950177 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1753020113003471 / 4000000000000) 0 (IntervalRat.scale (607 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-26880881934 / 1000000000000) (-26880866796 / 1000000000000), orderedInterval (27049960564 / 1000000000000) (27049975701 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1548846433604891 / 4000000000000) 0 (IntervalRat.scale (607 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-40545627063 / 1000000000000) (-40545626775 / 1000000000000), orderedInterval (457461918 / 1000000000000) (457462207 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (448916065648209 / 800000000000) 0 (IntervalRat.scale (607 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (13575068250 / 1000000000000) (13575068352 / 1000000000000), orderedInterval (-30837718861 / 1000000000000) (-30837718759 / 1000000000000)))) (orderedInterval (2357455287 / 1000000000000) (2357455511 / 1000000000000))) = true
  rfl'

theorem compactCertificate432_chunkChecks0_2 :
    compactCertificate432.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1241725462741123 / 4000000000000) 0 (IntervalRat.scale (607 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-8938578348 / 1000000000000) (-8938578347 / 1000000000000), orderedInterval (-44380003600 / 1000000000000) (-44380003599 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1052624426498603 / 4000000000000) 0 (IntervalRat.scale (607 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (2322975085 / 1000000000000) (2322975087 / 1000000000000), orderedInterval (49125818437 / 1000000000000) (49125818439 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (658683491183609 / 4000000000000) 0 (IntervalRat.scale (607 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (53899771389 / 1000000000000) (53899794805 / 1000000000000), orderedInterval (-31160726623 / 1000000000000) (-31160703208 / 1000000000000)))) (orderedInterval (3052452458 / 1000000000000) (3052453297 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (354242172240903 / 4000000000000) 0 (IntervalRat.scale (607 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (83244924733 / 1000000000000) (83244924735 / 1000000000000), orderedInterval (15614250550 / 1000000000000) (15614250552 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (961836407551709 / 4000000000000) 0 (IntervalRat.scale (607 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (31492559957 / 1000000000000) (31492571926 / 1000000000000), orderedInterval (-40756245394 / 1000000000000) (-40756233424 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1313305384588093 / 4000000000000) 0 (IntervalRat.scale (607 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (30203636996 / 1000000000000) (30203656911 / 1000000000000), orderedInterval (-32088548869 / 1000000000000) (-32088528955 / 1000000000000)))) (orderedInterval (-4566369062 / 1000000000000) (-4566367228 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (555316508816391 / 4000000000000) 0 (IntervalRat.scale (607 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (66533422230 / 1000000000000) (66533422233 / 1000000000000), orderedInterval (12366391602 / 1000000000000) (12366391605 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2257330778087911 / 4000000000000) 0 (IntervalRat.scale (607 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-12108226554 / 1000000000000) (-12108226502 / 1000000000000), orderedInterval (31339376044 / 1000000000000) (31339376096 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1507792345881449 / 4000000000000) 0 (IntervalRat.scale (607 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (27772195657 / 1000000000000) (27772195658 / 1000000000000), orderedInterval (30254818276 / 1000000000000) (30254818277 / 1000000000000)))) (orderedInterval (-3824084215 / 1000000000000) (-3824084126 / 1000000000000))) = true
  rfl'

theorem compactCertificate432_chunkChecks0 :
    compactCertificate432.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate432.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate432_chunkChecks0_0
    compactCertificate432_chunkChecks0_1 compactCertificate432_chunkChecks0_2

theorem compactCertificate432_chunkChecks1_0 :
    compactCertificate432.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (607 / 2) 1 (IntervalRat.scale (607 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (19900611598 / 1000000000000) (19900612472 / 1000000000000), orderedInterval (-41282772072 / 1000000000000) (-41282771198 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (894226905375907 / 4000000000000) 1 (IntervalRat.scale (607 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-51251246610 / 1000000000000) (-51251246608 / 1000000000000), orderedInterval (-14751158165 / 1000000000000) (-14751158163 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (289174608147331 / 800000000000) 1 (IntervalRat.scale (607 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34621460283 / 1000000000000) (-34621460282 / 1000000000000), orderedInterval (-23670437557 / 1000000000000) (-23670437556 / 1000000000000)))) (orderedInterval (-18118600067 / 1000000000000) (-18118599696 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (260933180755049 / 4000000000000) 1 (IntervalRat.scale (607 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-4279257842 / 1000000000000) (-4279257838 / 1000000000000), orderedInterval (-98664196981 / 1000000000000) (-98664196977 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (700903226796053 / 4000000000000) 1 (IntervalRat.scale (607 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (4895168653 / 1000000000000) (4895168655 / 1000000000000), orderedInterval (60062576970 / 1000000000000) (60062576972 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1903088605846401 / 4000000000000) 1 (IntervalRat.scale (607 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30066115039 / 1000000000000) (-30066048142 / 1000000000000), orderedInterval (20866807573 / 1000000000000) (20866874470 / 1000000000000)))) (orderedInterval (-829234935 / 1000000000000) (-829227438 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1401806453592713 / 4000000000000) 1 (IntervalRat.scale (607 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-24824133726 / 1000000000000) (-24824129068 / 1000000000000), orderedInterval (34681233725 / 1000000000000) (34681238383 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2402019251256749 / 4000000000000) 1 (IntervalRat.scale (607 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-30855419341 / 1000000000000) (-30855419330 / 1000000000000), orderedInterval (-10370644895 / 1000000000000) (-10370644884 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1769316508816391 / 4000000000000) 1 (IntervalRat.scale (607 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-5657233048 / 1000000000000) (-5657233047 / 1000000000000), orderedInterval (-37506817696 / 1000000000000) (-37506817695 / 1000000000000)))) (orderedInterval (-688209024 / 1000000000000) (-688208993 / 1000000000000))) = true
  rfl'

theorem compactCertificate432_chunkChecks1_1 :
    compactCertificate432.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2714586524684393 / 4000000000000) 1 (IntervalRat.scale (607 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (22966312078 / 1000000000000) (22966312079 / 1000000000000), orderedInterval (20246865328 / 1000000000000) (20246865329 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1567267260764897 / 4000000000000) 1 (IntervalRat.scale (607 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (3911328410 / 1000000000000) (3911328413 / 1000000000000), orderedInterval (-40123467270 / 1000000000000) (-40123467267 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2781143257140373 / 4000000000000) 1 (IntervalRat.scale (607 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-29605431884 / 1000000000000) (-29605416623 / 1000000000000), orderedInterval (6277619531 / 1000000000000) (6277634792 / 1000000000000)))) (orderedInterval (-9838029672 / 1000000000000) (-9838024452 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2598504791235337 / 4000000000000) 1 (IntervalRat.scale (607 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-3178948677 / 1000000000000) (-3178948676 / 1000000000000), orderedInterval (-31140340061 / 1000000000000) (-31140340060 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1854415631224921 / 4000000000000) 1 (IntervalRat.scale (607 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-19893166986 / 1000000000000) (-19893165646 / 1000000000000), orderedInterval (31285808814 / 1000000000000) (31285810155 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2102709680388159 / 4000000000000) 1 (IntervalRat.scale (607 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-33754009051 / 1000000000000) (-33753999571 / 1000000000000), orderedInterval (8500462025 / 1000000000000) (8500471506 / 1000000000000)))) (orderedInterval (5647954052 / 1000000000000) (5647954388 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1753020113003471 / 4000000000000) 1 (IntervalRat.scale (607 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-26880881934 / 1000000000000) (-26880866796 / 1000000000000), orderedInterval (27049960564 / 1000000000000) (27049975701 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1548846433604891 / 4000000000000) 1 (IntervalRat.scale (607 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-40545627063 / 1000000000000) (-40545626775 / 1000000000000), orderedInterval (457461918 / 1000000000000) (457462207 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (448916065648209 / 800000000000) 1 (IntervalRat.scale (607 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (13575068250 / 1000000000000) (13575068352 / 1000000000000), orderedInterval (-30837718861 / 1000000000000) (-30837718759 / 1000000000000)))) (orderedInterval (-1042186504 / 1000000000000) (-1042186183 / 1000000000000))) = true
  rfl'

theorem compactCertificate432_chunkChecks1_2 :
    compactCertificate432.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1241725462741123 / 4000000000000) 1 (IntervalRat.scale (607 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-8938578348 / 1000000000000) (-8938578347 / 1000000000000), orderedInterval (-44380003600 / 1000000000000) (-44380003599 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1052624426498603 / 4000000000000) 1 (IntervalRat.scale (607 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (2322975085 / 1000000000000) (2322975087 / 1000000000000), orderedInterval (49125818437 / 1000000000000) (49125818439 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (658683491183609 / 4000000000000) 1 (IntervalRat.scale (607 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (53899771389 / 1000000000000) (53899794805 / 1000000000000), orderedInterval (-31160726623 / 1000000000000) (-31160703208 / 1000000000000)))) (orderedInterval (4296768039 / 1000000000000) (4296768524 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (354242172240903 / 4000000000000) 1 (IntervalRat.scale (607 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (83244924733 / 1000000000000) (83244924735 / 1000000000000), orderedInterval (15614250550 / 1000000000000) (15614250552 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (961836407551709 / 4000000000000) 1 (IntervalRat.scale (607 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (31492559957 / 1000000000000) (31492571926 / 1000000000000), orderedInterval (-40756245394 / 1000000000000) (-40756233424 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1313305384588093 / 4000000000000) 1 (IntervalRat.scale (607 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (30203636996 / 1000000000000) (30203656911 / 1000000000000), orderedInterval (-32088548869 / 1000000000000) (-32088528955 / 1000000000000)))) (orderedInterval (3308836249 / 1000000000000) (3308838148 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (555316508816391 / 4000000000000) 1 (IntervalRat.scale (607 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (66533422230 / 1000000000000) (66533422233 / 1000000000000), orderedInterval (12366391602 / 1000000000000) (12366391605 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2257330778087911 / 4000000000000) 1 (IntervalRat.scale (607 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-12108226554 / 1000000000000) (-12108226502 / 1000000000000), orderedInterval (31339376044 / 1000000000000) (31339376096 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1507792345881449 / 4000000000000) 1 (IntervalRat.scale (607 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (27772195657 / 1000000000000) (27772195658 / 1000000000000), orderedInterval (30254818276 / 1000000000000) (30254818277 / 1000000000000)))) (orderedInterval (-11759785180 / 1000000000000) (-11759785054 / 1000000000000))) = true
  rfl'

theorem compactCertificate432_chunkChecks1 :
    compactCertificate432.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate432.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate432_chunkChecks1_0
    compactCertificate432_chunkChecks1_1 compactCertificate432_chunkChecks1_2

theorem compactCertificate432_chunkChecks2_0 :
    compactCertificate432.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (607 / 2) 2 (IntervalRat.scale (607 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (19900611598 / 1000000000000) (19900612472 / 1000000000000), orderedInterval (-41282772072 / 1000000000000) (-41282771198 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (894226905375907 / 4000000000000) 2 (IntervalRat.scale (607 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-51251246610 / 1000000000000) (-51251246608 / 1000000000000), orderedInterval (-14751158165 / 1000000000000) (-14751158163 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (289174608147331 / 800000000000) 2 (IntervalRat.scale (607 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34621460283 / 1000000000000) (-34621460282 / 1000000000000), orderedInterval (-23670437557 / 1000000000000) (-23670437556 / 1000000000000)))) (orderedInterval (-4687274861 / 1000000000000) (-4687274485 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (260933180755049 / 4000000000000) 2 (IntervalRat.scale (607 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-4279257842 / 1000000000000) (-4279257838 / 1000000000000), orderedInterval (-98664196981 / 1000000000000) (-98664196977 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (700903226796053 / 4000000000000) 2 (IntervalRat.scale (607 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (4895168653 / 1000000000000) (4895168655 / 1000000000000), orderedInterval (60062576970 / 1000000000000) (60062576972 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1903088605846401 / 4000000000000) 2 (IntervalRat.scale (607 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30066115039 / 1000000000000) (-30066048142 / 1000000000000), orderedInterval (20866807573 / 1000000000000) (20866874470 / 1000000000000)))) (orderedInterval (-5311468151 / 1000000000000) (-5311456382 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1401806453592713 / 4000000000000) 2 (IntervalRat.scale (607 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-24824133726 / 1000000000000) (-24824129068 / 1000000000000), orderedInterval (34681233725 / 1000000000000) (34681238383 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2402019251256749 / 4000000000000) 2 (IntervalRat.scale (607 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-30855419341 / 1000000000000) (-30855419330 / 1000000000000), orderedInterval (-10370644895 / 1000000000000) (-10370644884 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1769316508816391 / 4000000000000) 2 (IntervalRat.scale (607 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-5657233048 / 1000000000000) (-5657233047 / 1000000000000), orderedInterval (-37506817696 / 1000000000000) (-37506817695 / 1000000000000)))) (orderedInterval (-3433102219 / 1000000000000) (-3433102164 / 1000000000000))) = true
  rfl'

theorem compactCertificate432_chunkChecks2_1 :
    compactCertificate432.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2714586524684393 / 4000000000000) 2 (IntervalRat.scale (607 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (22966312078 / 1000000000000) (22966312079 / 1000000000000), orderedInterval (20246865328 / 1000000000000) (20246865329 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1567267260764897 / 4000000000000) 2 (IntervalRat.scale (607 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (3911328410 / 1000000000000) (3911328413 / 1000000000000), orderedInterval (-40123467270 / 1000000000000) (-40123467267 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2781143257140373 / 4000000000000) 2 (IntervalRat.scale (607 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-29605431884 / 1000000000000) (-29605416623 / 1000000000000), orderedInterval (6277619531 / 1000000000000) (6277634792 / 1000000000000)))) (orderedInterval (42041041649 / 1000000000000) (42041053587 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2598504791235337 / 4000000000000) 2 (IntervalRat.scale (607 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-3178948677 / 1000000000000) (-3178948676 / 1000000000000), orderedInterval (-31140340061 / 1000000000000) (-31140340060 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1854415631224921 / 4000000000000) 2 (IntervalRat.scale (607 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-19893166986 / 1000000000000) (-19893165646 / 1000000000000), orderedInterval (31285808814 / 1000000000000) (31285810155 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2102709680388159 / 4000000000000) 2 (IntervalRat.scale (607 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-33754009051 / 1000000000000) (-33753999571 / 1000000000000), orderedInterval (8500462025 / 1000000000000) (8500471506 / 1000000000000)))) (orderedInterval (3595374740 / 1000000000000) (3595375278 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1753020113003471 / 4000000000000) 2 (IntervalRat.scale (607 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-26880881934 / 1000000000000) (-26880866796 / 1000000000000), orderedInterval (27049960564 / 1000000000000) (27049975701 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1548846433604891 / 4000000000000) 2 (IntervalRat.scale (607 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-40545627063 / 1000000000000) (-40545626775 / 1000000000000), orderedInterval (457461918 / 1000000000000) (457462207 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (448916065648209 / 800000000000) 2 (IntervalRat.scale (607 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (13575068250 / 1000000000000) (13575068352 / 1000000000000), orderedInterval (-30837718861 / 1000000000000) (-30837718759 / 1000000000000)))) (orderedInterval (-4314274126 / 1000000000000) (-4314273662 / 1000000000000))) = true
  rfl'

theorem compactCertificate432_chunkChecks2_2 :
    compactCertificate432.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1241725462741123 / 4000000000000) 2 (IntervalRat.scale (607 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-8938578348 / 1000000000000) (-8938578347 / 1000000000000), orderedInterval (-44380003600 / 1000000000000) (-44380003599 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1052624426498603 / 4000000000000) 2 (IntervalRat.scale (607 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (2322975085 / 1000000000000) (2322975087 / 1000000000000), orderedInterval (49125818437 / 1000000000000) (49125818439 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (658683491183609 / 4000000000000) 2 (IntervalRat.scale (607 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (53899771389 / 1000000000000) (53899794805 / 1000000000000), orderedInterval (-31160726623 / 1000000000000) (-31160703208 / 1000000000000)))) (orderedInterval (-1927110994 / 1000000000000) (-1927110701 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (354242172240903 / 4000000000000) 2 (IntervalRat.scale (607 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (83244924733 / 1000000000000) (83244924735 / 1000000000000), orderedInterval (15614250550 / 1000000000000) (15614250552 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (961836407551709 / 4000000000000) 2 (IntervalRat.scale (607 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (31492559957 / 1000000000000) (31492571926 / 1000000000000), orderedInterval (-40756245394 / 1000000000000) (-40756233424 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1313305384588093 / 4000000000000) 2 (IntervalRat.scale (607 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (30203636996 / 1000000000000) (30203656911 / 1000000000000), orderedInterval (-32088548869 / 1000000000000) (-32088528955 / 1000000000000)))) (orderedInterval (3277420999 / 1000000000000) (3277422995 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (555316508816391 / 4000000000000) 2 (IntervalRat.scale (607 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (66533422230 / 1000000000000) (66533422233 / 1000000000000), orderedInterval (12366391602 / 1000000000000) (12366391605 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2257330778087911 / 4000000000000) 2 (IntervalRat.scale (607 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-12108226554 / 1000000000000) (-12108226502 / 1000000000000), orderedInterval (31339376044 / 1000000000000) (31339376096 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1507792345881449 / 4000000000000) 2 (IntervalRat.scale (607 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (27772195657 / 1000000000000) (27772195658 / 1000000000000), orderedInterval (30254818276 / 1000000000000) (30254818277 / 1000000000000)))) (orderedInterval (4585116133 / 1000000000000) (4585116323 / 1000000000000))) = true
  rfl'

theorem compactCertificate432_chunkChecks2 :
    compactCertificate432.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate432.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate432_chunkChecks2_0
    compactCertificate432_chunkChecks2_1 compactCertificate432_chunkChecks2_2

theorem compactCertificate432_chunkChecks3_0 :
    compactCertificate432.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (607 / 2) 3 (IntervalRat.scale (607 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (19900611598 / 1000000000000) (19900612472 / 1000000000000), orderedInterval (-41282772072 / 1000000000000) (-41282771198 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (894226905375907 / 4000000000000) 3 (IntervalRat.scale (607 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-51251246610 / 1000000000000) (-51251246608 / 1000000000000), orderedInterval (-14751158165 / 1000000000000) (-14751158163 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (289174608147331 / 800000000000) 3 (IntervalRat.scale (607 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34621460283 / 1000000000000) (-34621460282 / 1000000000000), orderedInterval (-23670437557 / 1000000000000) (-23670437556 / 1000000000000)))) (orderedInterval (18779827339 / 1000000000000) (18779827719 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (260933180755049 / 4000000000000) 3 (IntervalRat.scale (607 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-4279257842 / 1000000000000) (-4279257838 / 1000000000000), orderedInterval (-98664196981 / 1000000000000) (-98664196977 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (700903226796053 / 4000000000000) 3 (IntervalRat.scale (607 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (4895168653 / 1000000000000) (4895168655 / 1000000000000), orderedInterval (60062576970 / 1000000000000) (60062576972 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1903088605846401 / 4000000000000) 3 (IntervalRat.scale (607 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30066115039 / 1000000000000) (-30066048142 / 1000000000000), orderedInterval (20866807573 / 1000000000000) (20866874470 / 1000000000000)))) (orderedInterval (5299388197 / 1000000000000) (5299406642 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1401806453592713 / 4000000000000) 3 (IntervalRat.scale (607 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-24824133726 / 1000000000000) (-24824129068 / 1000000000000), orderedInterval (34681233725 / 1000000000000) (34681238383 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2402019251256749 / 4000000000000) 3 (IntervalRat.scale (607 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-30855419341 / 1000000000000) (-30855419330 / 1000000000000), orderedInterval (-10370644895 / 1000000000000) (-10370644884 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1769316508816391 / 4000000000000) 3 (IntervalRat.scale (607 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-5657233048 / 1000000000000) (-5657233047 / 1000000000000), orderedInterval (-37506817696 / 1000000000000) (-37506817695 / 1000000000000)))) (orderedInterval (339754528 / 1000000000000) (339754627 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate432_chunkChecks3_1 :
    compactCertificate432.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2714586524684393 / 4000000000000) 3 (IntervalRat.scale (607 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (22966312078 / 1000000000000) (22966312079 / 1000000000000), orderedInterval (20246865328 / 1000000000000) (20246865329 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1567267260764897 / 4000000000000) 3 (IntervalRat.scale (607 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (3911328410 / 1000000000000) (3911328413 / 1000000000000), orderedInterval (-40123467270 / 1000000000000) (-40123467267 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2781143257140373 / 4000000000000) 3 (IntervalRat.scale (607 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-29605431884 / 1000000000000) (-29605416623 / 1000000000000), orderedInterval (6277619531 / 1000000000000) (6277634792 / 1000000000000)))) (orderedInterval (35751125433 / 1000000000000) (35751152727 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2598504791235337 / 4000000000000) 3 (IntervalRat.scale (607 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-3178948677 / 1000000000000) (-3178948676 / 1000000000000), orderedInterval (-31140340061 / 1000000000000) (-31140340060 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1854415631224921 / 4000000000000) 3 (IntervalRat.scale (607 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-19893166986 / 1000000000000) (-19893165646 / 1000000000000), orderedInterval (31285808814 / 1000000000000) (31285810155 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2102709680388159 / 4000000000000) 3 (IntervalRat.scale (607 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-33754009051 / 1000000000000) (-33753999571 / 1000000000000), orderedInterval (8500462025 / 1000000000000) (8500471506 / 1000000000000)))) (orderedInterval (-15845952999 / 1000000000000) (-15845952131 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1753020113003471 / 4000000000000) 3 (IntervalRat.scale (607 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-26880881934 / 1000000000000) (-26880866796 / 1000000000000), orderedInterval (27049960564 / 1000000000000) (27049975701 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1548846433604891 / 4000000000000) 3 (IntervalRat.scale (607 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-40545627063 / 1000000000000) (-40545626775 / 1000000000000), orderedInterval (457461918 / 1000000000000) (457462207 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (448916065648209 / 800000000000) 3 (IntervalRat.scale (607 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (13575068250 / 1000000000000) (13575068352 / 1000000000000), orderedInterval (-30837718861 / 1000000000000) (-30837718759 / 1000000000000)))) (orderedInterval (4118491145 / 1000000000000) (4118491821 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate432_chunkChecks3_2 :
    compactCertificate432.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1241725462741123 / 4000000000000) 3 (IntervalRat.scale (607 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-8938578348 / 1000000000000) (-8938578347 / 1000000000000), orderedInterval (-44380003600 / 1000000000000) (-44380003599 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1052624426498603 / 4000000000000) 3 (IntervalRat.scale (607 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (2322975085 / 1000000000000) (2322975087 / 1000000000000), orderedInterval (49125818437 / 1000000000000) (49125818439 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (658683491183609 / 4000000000000) 3 (IntervalRat.scale (607 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (53899771389 / 1000000000000) (53899794805 / 1000000000000), orderedInterval (-31160726623 / 1000000000000) (-31160703208 / 1000000000000)))) (orderedInterval (-5612414893 / 1000000000000) (-5612414705 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (354242172240903 / 4000000000000) 3 (IntervalRat.scale (607 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (83244924733 / 1000000000000) (83244924735 / 1000000000000), orderedInterval (15614250550 / 1000000000000) (15614250552 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (961836407551709 / 4000000000000) 3 (IntervalRat.scale (607 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (31492559957 / 1000000000000) (31492571926 / 1000000000000), orderedInterval (-40756245394 / 1000000000000) (-40756233424 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1313305384588093 / 4000000000000) 3 (IntervalRat.scale (607 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (30203636996 / 1000000000000) (30203656911 / 1000000000000), orderedInterval (-32088548869 / 1000000000000) (-32088528955 / 1000000000000)))) (orderedInterval (-3576887907 / 1000000000000) (-3576885799 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (555316508816391 / 4000000000000) 3 (IntervalRat.scale (607 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (66533422230 / 1000000000000) (66533422233 / 1000000000000), orderedInterval (12366391602 / 1000000000000) (12366391605 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2257330778087911 / 4000000000000) 3 (IntervalRat.scale (607 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-12108226554 / 1000000000000) (-12108226502 / 1000000000000), orderedInterval (31339376044 / 1000000000000) (31339376096 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1507792345881449 / 4000000000000) 3 (IntervalRat.scale (607 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (27772195657 / 1000000000000) (27772195658 / 1000000000000), orderedInterval (30254818276 / 1000000000000) (30254818277 / 1000000000000)))) (orderedInterval (27253707414 / 1000000000000) (27253707711 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate432_chunkChecks3 :
    compactCertificate432.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate432.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate432_chunkChecks3_0
    compactCertificate432_chunkChecks3_1 compactCertificate432_chunkChecks3_2

theorem compactCertificate432_chunkChecks4_0 :
    compactCertificate432.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (607 / 2) 4 (IntervalRat.scale (607 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (19900611598 / 1000000000000) (19900612472 / 1000000000000), orderedInterval (-41282772072 / 1000000000000) (-41282771198 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (894226905375907 / 4000000000000) 4 (IntervalRat.scale (607 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-51251246610 / 1000000000000) (-51251246608 / 1000000000000), orderedInterval (-14751158165 / 1000000000000) (-14751158163 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (289174608147331 / 800000000000) 4 (IntervalRat.scale (607 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34621460283 / 1000000000000) (-34621460282 / 1000000000000), orderedInterval (-23670437557 / 1000000000000) (-23670437556 / 1000000000000)))) (orderedInterval (3535711490 / 1000000000000) (3535711876 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (260933180755049 / 4000000000000) 4 (IntervalRat.scale (607 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-4279257842 / 1000000000000) (-4279257838 / 1000000000000), orderedInterval (-98664196981 / 1000000000000) (-98664196977 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (700903226796053 / 4000000000000) 4 (IntervalRat.scale (607 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (4895168653 / 1000000000000) (4895168655 / 1000000000000), orderedInterval (60062576970 / 1000000000000) (60062576972 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1903088605846401 / 4000000000000) 4 (IntervalRat.scale (607 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30066115039 / 1000000000000) (-30066048142 / 1000000000000), orderedInterval (20866807573 / 1000000000000) (20866874470 / 1000000000000)))) (orderedInterval (12892532694 / 1000000000000) (12892561667 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1401806453592713 / 4000000000000) 4 (IntervalRat.scale (607 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-24824133726 / 1000000000000) (-24824129068 / 1000000000000), orderedInterval (34681233725 / 1000000000000) (34681238383 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2402019251256749 / 4000000000000) 4 (IntervalRat.scale (607 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-30855419341 / 1000000000000) (-30855419330 / 1000000000000), orderedInterval (-10370644895 / 1000000000000) (-10370644884 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1769316508816391 / 4000000000000) 4 (IntervalRat.scale (607 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-5657233048 / 1000000000000) (-5657233047 / 1000000000000), orderedInterval (-37506817696 / 1000000000000) (-37506817695 / 1000000000000)))) (orderedInterval (13966759150 / 1000000000000) (13966759333 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate432_chunkChecks4_1 :
    compactCertificate432.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2714586524684393 / 4000000000000) 4 (IntervalRat.scale (607 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (22966312078 / 1000000000000) (22966312079 / 1000000000000), orderedInterval (20246865328 / 1000000000000) (20246865329 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1567267260764897 / 4000000000000) 4 (IntervalRat.scale (607 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (3911328410 / 1000000000000) (3911328413 / 1000000000000), orderedInterval (-40123467270 / 1000000000000) (-40123467267 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2781143257140373 / 4000000000000) 4 (IntervalRat.scale (607 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-29605431884 / 1000000000000) (-29605416623 / 1000000000000), orderedInterval (6277619531 / 1000000000000) (6277634792 / 1000000000000)))) (orderedInterval (-217370142508 / 1000000000000) (-217370079977 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2598504791235337 / 4000000000000) 4 (IntervalRat.scale (607 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-3178948677 / 1000000000000) (-3178948676 / 1000000000000), orderedInterval (-31140340061 / 1000000000000) (-31140340060 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1854415631224921 / 4000000000000) 4 (IntervalRat.scale (607 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-19893166986 / 1000000000000) (-19893165646 / 1000000000000), orderedInterval (31285808814 / 1000000000000) (31285810155 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2102709680388159 / 4000000000000) 4 (IntervalRat.scale (607 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-33754009051 / 1000000000000) (-33753999571 / 1000000000000), orderedInterval (8500462025 / 1000000000000) (8500471506 / 1000000000000)))) (orderedInterval (-7395419260 / 1000000000000) (-7395417847 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1753020113003471 / 4000000000000) 4 (IntervalRat.scale (607 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-26880881934 / 1000000000000) (-26880866796 / 1000000000000), orderedInterval (27049960564 / 1000000000000) (27049975701 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1548846433604891 / 4000000000000) 4 (IntervalRat.scale (607 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-40545627063 / 1000000000000) (-40545626775 / 1000000000000), orderedInterval (457461918 / 1000000000000) (457462207 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (448916065648209 / 800000000000) 4 (IntervalRat.scale (607 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (13575068250 / 1000000000000) (13575068352 / 1000000000000), orderedInterval (-30837718861 / 1000000000000) (-30837718759 / 1000000000000)))) (orderedInterval (8832499399 / 1000000000000) (8832500390 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate432_chunkChecks4_2 :
    compactCertificate432.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1241725462741123 / 4000000000000) 4 (IntervalRat.scale (607 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-8938578348 / 1000000000000) (-8938578347 / 1000000000000), orderedInterval (-44380003600 / 1000000000000) (-44380003599 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1052624426498603 / 4000000000000) 4 (IntervalRat.scale (607 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (2322975085 / 1000000000000) (2322975087 / 1000000000000), orderedInterval (49125818437 / 1000000000000) (49125818439 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (658683491183609 / 4000000000000) 4 (IntervalRat.scale (607 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (53899771389 / 1000000000000) (53899794805 / 1000000000000), orderedInterval (-31160726623 / 1000000000000) (-31160703208 / 1000000000000)))) (orderedInterval (1679031126 / 1000000000000) (1679031257 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (354242172240903 / 4000000000000) 4 (IntervalRat.scale (607 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (83244924733 / 1000000000000) (83244924735 / 1000000000000), orderedInterval (15614250550 / 1000000000000) (15614250552 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (961836407551709 / 4000000000000) 4 (IntervalRat.scale (607 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (31492559957 / 1000000000000) (31492571926 / 1000000000000), orderedInterval (-40756245394 / 1000000000000) (-40756233424 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1313305384588093 / 4000000000000) 4 (IntervalRat.scale (607 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (30203636996 / 1000000000000) (30203656911 / 1000000000000), orderedInterval (-32088548869 / 1000000000000) (-32088528955 / 1000000000000)))) (orderedInterval (-3439333540 / 1000000000000) (-3439331293 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (555316508816391 / 4000000000000) 4 (IntervalRat.scale (607 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (66533422230 / 1000000000000) (66533422233 / 1000000000000), orderedInterval (12366391602 / 1000000000000) (12366391605 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2257330778087911 / 4000000000000) 4 (IntervalRat.scale (607 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-12108226554 / 1000000000000) (-12108226502 / 1000000000000), orderedInterval (31339376044 / 1000000000000) (31339376096 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1507792345881449 / 4000000000000) 4 (IntervalRat.scale (607 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (27772195657 / 1000000000000) (27772195658 / 1000000000000), orderedInterval (30254818276 / 1000000000000) (30254818277 / 1000000000000)))) (orderedInterval (-779208537 / 1000000000000) (-779208054 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate432_chunkChecks4 :
    compactCertificate432.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate432.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate432_chunkChecks4_0
    compactCertificate432_chunkChecks4_1 compactCertificate432_chunkChecks4_2

theorem compactCertificate432_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate432.chunkCheck r b = true :=
  compactCertificate432.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate432_chunkChecks0
    · exact compactCertificate432_chunkChecks1
    · exact compactCertificate432_chunkChecks2
    · exact compactCertificate432_chunkChecks3
    · exact compactCertificate432_chunkChecks4)

theorem compactCertificate432_coefficient0 :
    compactCertificate432.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate432_coefficient1 :
    compactCertificate432.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate432_coefficient2 :
    compactCertificate432.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate432_coefficient3 :
    compactCertificate432.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate432_coefficient4 :
    compactCertificate432.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate432_coefficients : ∀ r : Fin 5,
    compactCertificate432.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate432_coefficient0
  · exact compactCertificate432_coefficient1
  · exact compactCertificate432_coefficient2
  · exact compactCertificate432_coefficient3
  · exact compactCertificate432_coefficient4

theorem compactCertificate432_lower : (1 : ℚ) ≤ compactCertificate432.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate432, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate432_proves {t : ℝ} (ht : t ∈ compactCertificate432.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate432.proves compactCertificate432_states compactCertificate432_chunks
    compactCertificate432_coefficients compactCertificate432_lower ht

end Erdos232
