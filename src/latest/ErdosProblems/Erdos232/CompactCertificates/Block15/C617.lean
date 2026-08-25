/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate617 : CompactCertificate where
  left := 488
  right := 489
  center := 977 / 2
  grid := fun i =>
    match i.val with
    | 0 => 156
    | 1 => 115
    | 2 => 185
    | 3 => 33
    | 4 => 90
    | 5 => 244
    | 6 => 180
    | 7 => 308
    | 8 => 227
    | 9 => 348
    | 10 => 201
    | 11 => 356
    | 12 => 333
    | 13 => 238
    | 14 => 269
    | 15 => 225
    | 16 => 198
    | 17 => 288
    | 18 => 159
    | 19 => 135
    | 20 => 84
    | 21 => 45
    | 22 => 123
    | 23 => 168
    | 24 => 71
    | 25 => 289
    | _ => 193
  point := fun i =>
    match i.val with
    | 0 => 977 / 2
    | 1 => 1439307556099277 / 4000000000000
    | 2 => 465442491202541 / 800000000000
    | 3 => 419986355185639 / 4000000000000
    | 4 => 1128142425996283 / 4000000000000
    | 5 => 3063126141535311 / 4000000000000
    | 6 => 2256284851993543 / 4000000000000
    | 7 => 3866182551034339 / 4000000000000
    | 8 => 2847812568556201 / 4000000000000
    | 9 => 4369276828034023 / 4000000000000
    | 10 => 2522603152829167 / 4000000000000
    | 11 => 4476403562151803 / 4000000000000
    | 12 => 4182436871560007 / 4000000000000
    | 13 => 2984784302647031 / 4000000000000
    | 14 => 3384427277988849 / 4000000000000
    | 15 => 2821582620106081 / 4000000000000
    | 16 => 2492953814879701 / 4000000000000
    | 17 => 722555183094399 / 800000000000
    | 18 => 1998625662435053 / 4000000000000
    | 19 => 1694257108219333 / 4000000000000
    | 20 => 1060187431443799 / 4000000000000
    | 21 => 570172326654633 / 4000000000000
    | 22 => 1548128781182899 / 4000000000000
    | 23 => 2113837497104723 / 4000000000000
    | 24 => 893812568556201 / 4000000000000
    | 25 => 3633298468190921 / 4000000000000
    | _ => 2426874994936039 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-25979739799 / 1000000000000) (-25979725373 / 1000000000000), orderedInterval (25091837067 / 1000000000000) (25091851493 / 1000000000000))
    | 1 => (orderedInterval (26160147144 / 1000000000000) (26160154559 / 1000000000000), orderedInterval (-32973960850 / 1000000000000) (-32973953436 / 1000000000000))
    | 2 => (orderedInterval (-32561339290 / 1000000000000) (-32561339203 / 1000000000000), orderedInterval (-5801028780 / 1000000000000) (-5801028694 / 1000000000000))
    | 3 => (orderedInterval (-66888846903 / 1000000000000) (-66888826428 / 1000000000000), orderedInterval (40181942237 / 1000000000000) (40181962712 / 1000000000000))
    | 4 => (orderedInterval (3665225038 / 1000000000000) (3665225039 / 1000000000000), orderedInterval (47362284614 / 1000000000000) (47362284615 / 1000000000000))
    | 5 => (orderedInterval (523657631 / 1000000000000) (523657632 / 1000000000000), orderedInterval (28827758376 / 1000000000000) (28827758377 / 1000000000000))
    | 6 => (orderedInterval (-19800063747 / 1000000000000) (-19800062194 / 1000000000000), orderedInterval (27157439667 / 1000000000000) (27157441220 / 1000000000000))
    | 7 => (orderedInterval (-7083355970 / 1000000000000) (-7083355969 / 1000000000000), orderedInterval (24671067577 / 1000000000000) (24671067578 / 1000000000000))
    | 8 => (orderedInterval (11731950286 / 1000000000000) (11731950315 / 1000000000000), orderedInterval (-27513679406 / 1000000000000) (-27513679378 / 1000000000000))
    | 9 => (orderedInterval (-4078441143 / 1000000000000) (-4078441142 / 1000000000000), orderedInterval (23796428224 / 1000000000000) (23796428225 / 1000000000000))
    | 10 => (orderedInterval (766751110 / 1000000000000) (766751111 / 1000000000000), orderedInterval (-31763435401 / 1000000000000) (-31763435400 / 1000000000000))
    | 11 => (orderedInterval (23750932086 / 1000000000000) (23750938626 / 1000000000000), orderedInterval (2171172139 / 1000000000000) (2171178680 / 1000000000000))
    | 12 => (orderedInterval (-5964531713 / 1000000000000) (-5964531712 / 1000000000000), orderedInterval (-23940309617 / 1000000000000) (-23940309616 / 1000000000000))
    | 13 => (orderedInterval (-19210265796 / 1000000000000) (-19210264328 / 1000000000000), orderedInterval (22015580598 / 1000000000000) (22015582066 / 1000000000000))
    | 14 => (orderedInterval (-26689858413 / 1000000000000) (-26689819316 / 1000000000000), orderedInterval (6345286071 / 1000000000000) (6345325168 / 1000000000000))
    | 15 => (orderedInterval (18830837204 / 1000000000000) (18830838372 / 1000000000000), orderedInterval (-23420609354 / 1000000000000) (-23420608185 / 1000000000000))
    | 16 => (orderedInterval (29215059960 / 1000000000000) (29215133238 / 1000000000000), orderedInterval (-12982967840 / 1000000000000) (-12982894562 / 1000000000000))
    | 17 => (orderedInterval (-19034888903 / 1000000000000) (-19034887400 / 1000000000000), orderedInterval (18518019063 / 1000000000000) (18518020567 / 1000000000000))
    | 18 => (orderedInterval (-28577974126 / 1000000000000) (-28577974125 / 1000000000000), orderedInterval (-21358648413 / 1000000000000) (-21358648412 / 1000000000000))
    | 19 => (orderedInterval (-9003315071 / 1000000000000) (-9003315070 / 1000000000000), orderedInterval (-37698091676 / 1000000000000) (-37698091675 / 1000000000000))
    | 20 => (orderedInterval (45742042551 / 1000000000000) (45742051076 / 1000000000000), orderedInterval (-17681066810 / 1000000000000) (-17681058285 / 1000000000000))
    | 21 => (orderedInterval (-61933669996 / 1000000000000) (-61933664559 / 1000000000000), orderedInterval (25324172356 / 1000000000000) (25324177793 / 1000000000000))
    | 22 => (orderedInterval (-39976366148 / 1000000000000) (-39976366126 / 1000000000000), orderedInterval (-6786801594 / 1000000000000) (-6786801572 / 1000000000000))
    | 23 => (orderedInterval (34483760107 / 1000000000000) (34483760250 / 1000000000000), orderedInterval (3909571626 / 1000000000000) (3909571769 / 1000000000000))
    | 24 => (orderedInterval (-49450885548 / 1000000000000) (-49450885547 / 1000000000000), orderedInterval (-19979464213 / 1000000000000) (-19979464211 / 1000000000000))
    | 25 => (orderedInterval (-24573704917 / 1000000000000) (-24573704867 / 1000000000000), orderedInterval (-9835609144 / 1000000000000) (-9835609094 / 1000000000000))
    | _ => (orderedInterval (-29907785601 / 1000000000000) (-29907785597 / 1000000000000), orderedInterval (-12417510231 / 1000000000000) (-12417510227 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-11964434089 / 1000000000000) (-11964428263 / 1000000000000)
      | 1 => orderedInterval (822293446 / 1000000000000) (822293727 / 1000000000000)
      | 2 => orderedInterval (502017116 / 1000000000000) (502017145 / 1000000000000)
      | 3 => orderedInterval (4157834535 / 1000000000000) (4157835659 / 1000000000000)
      | 4 => orderedInterval (-1573833757 / 1000000000000) (-1573833361 / 1000000000000)
      | 5 => orderedInterval (-1941801067 / 1000000000000) (-1941796774 / 1000000000000)
      | 6 => orderedInterval (6568133837 / 1000000000000) (6568134237 / 1000000000000)
      | 7 => orderedInterval (-592245784 / 1000000000000) (-592245614 / 1000000000000)
      | _ => orderedInterval (7313730960 / 1000000000000) (7313731100 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (9313775170 / 1000000000000) (9313780983 / 1000000000000)
      | 1 => orderedInterval (-2307907067 / 1000000000000) (-2307906952 / 1000000000000)
      | 2 => orderedInterval (-2474741863 / 1000000000000) (-2474741814 / 1000000000000)
      | 3 => orderedInterval (-11786017286 / 1000000000000) (-11786014754 / 1000000000000)
      | 4 => orderedInterval (4049564639 / 1000000000000) (4049565288 / 1000000000000)
      | 5 => orderedInterval (1433991447 / 1000000000000) (1433996956 / 1000000000000)
      | 6 => orderedInterval (5030847841 / 1000000000000) (5030848105 / 1000000000000)
      | 7 => orderedInterval (-338593741 / 1000000000000) (-338593647 / 1000000000000)
      | _ => orderedInterval (4327308858 / 1000000000000) (4327309056 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (12856468799 / 1000000000000) (12856474618 / 1000000000000)
      | 1 => orderedInterval (18072665 / 1000000000000) (18072768 / 1000000000000)
      | 2 => orderedInterval (-1452509122 / 1000000000000) (-1452509035 / 1000000000000)
      | 3 => orderedInterval (-21413649320 / 1000000000000) (-21413643576 / 1000000000000)
      | 4 => orderedInterval (3331863202 / 1000000000000) (3331864277 / 1000000000000)
      | 5 => orderedInterval (3931054654 / 1000000000000) (3931061752 / 1000000000000)
      | 6 => orderedInterval (-5612293439 / 1000000000000) (-5612293248 / 1000000000000)
      | 7 => orderedInterval (2426859567 / 1000000000000) (2426859641 / 1000000000000)
      | _ => orderedInterval (-15518662310 / 1000000000000) (-15518662014 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-9273922104 / 1000000000000) (-9273916287 / 1000000000000)
      | 1 => orderedInterval (7566227985 / 1000000000000) (7566228126 / 1000000000000)
      | 2 => orderedInterval (7955758090 / 1000000000000) (7955758246 / 1000000000000)
      | 3 => orderedInterval (48670912256 / 1000000000000) (48670925332 / 1000000000000)
      | 4 => orderedInterval (-11498496664 / 1000000000000) (-11498494874 / 1000000000000)
      | 5 => orderedInterval (-3733383591 / 1000000000000) (-3733374429 / 1000000000000)
      | 6 => orderedInterval (-4941915708 / 1000000000000) (-4941915558 / 1000000000000)
      | 7 => orderedInterval (309405475 / 1000000000000) (309405546 / 1000000000000)
      | _ => orderedInterval (-9567534823 / 1000000000000) (-9567534363 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-14032237222 / 1000000000000) (-14032231390 / 1000000000000)
      | 1 => orderedInterval (-239368989 / 1000000000000) (-239368776 / 1000000000000)
      | 2 => orderedInterval (4595109484 / 1000000000000) (4595109773 / 1000000000000)
      | 3 => orderedInterval (111071679182 / 1000000000000) (111071709024 / 1000000000000)
      | 4 => orderedInterval (-6367372262 / 1000000000000) (-6367369259 / 1000000000000)
      | 5 => orderedInterval (-9164244513 / 1000000000000) (-9164232611 / 1000000000000)
      | 6 => orderedInterval (5438639492 / 1000000000000) (5438639620 / 1000000000000)
      | 7 => orderedInterval (-3255131426 / 1000000000000) (-3255131354 / 1000000000000)
      | _ => orderedInterval (37290486200 / 1000000000000) (37290486945 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (3291695197 / 1000000000000) (3291707856 / 1000000000000)
    | 1 => orderedInterval (7248227998 / 1000000000000) (7248243221 / 1000000000000)
    | 2 => orderedInterval (-21432795304 / 1000000000000) (-21432774817 / 1000000000000)
    | 3 => orderedInterval (25487050916 / 1000000000000) (25487081739 / 1000000000000)
    | _ => orderedInterval (125337559946 / 1000000000000) (125337611972 / 1000000000000)

theorem compactCertificate617_stateChecks0 :
    compactCertificate617.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 156 12 (977 / 2)) (orderedInterval (-25979739799 / 1000000000000) (-25979725373 / 1000000000000), orderedInterval (25091837067 / 1000000000000) (25091851493 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 115 12 (1439307556099277 / 4000000000000)) (orderedInterval (26160147144 / 1000000000000) (26160154559 / 1000000000000), orderedInterval (-32973960850 / 1000000000000) (-32973953436 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 185 12 (465442491202541 / 800000000000)) (orderedInterval (-32561339290 / 1000000000000) (-32561339203 / 1000000000000), orderedInterval (-5801028780 / 1000000000000) (-5801028694 / 1000000000000))) = true
  rfl'

theorem compactCertificate617_stateChecks1 :
    compactCertificate617.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (419986355185639 / 4000000000000)) (orderedInterval (-66888846903 / 1000000000000) (-66888826428 / 1000000000000), orderedInterval (40181942237 / 1000000000000) (40181962712 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (1128142425996283 / 4000000000000)) (orderedInterval (3665225038 / 1000000000000) (3665225039 / 1000000000000), orderedInterval (47362284614 / 1000000000000) (47362284615 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 244 12 (3063126141535311 / 4000000000000)) (orderedInterval (523657631 / 1000000000000) (523657632 / 1000000000000), orderedInterval (28827758376 / 1000000000000) (28827758377 / 1000000000000))) = true
  rfl'

theorem compactCertificate617_stateChecks2 :
    compactCertificate617.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 180 12 (2256284851993543 / 4000000000000)) (orderedInterval (-19800063747 / 1000000000000) (-19800062194 / 1000000000000), orderedInterval (27157439667 / 1000000000000) (27157441220 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 308 12 (3866182551034339 / 4000000000000)) (orderedInterval (-7083355970 / 1000000000000) (-7083355969 / 1000000000000), orderedInterval (24671067577 / 1000000000000) (24671067578 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 227 12 (2847812568556201 / 4000000000000)) (orderedInterval (11731950286 / 1000000000000) (11731950315 / 1000000000000), orderedInterval (-27513679406 / 1000000000000) (-27513679378 / 1000000000000))) = true
  rfl'

theorem compactCertificate617_stateChecks3 :
    compactCertificate617.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 348 12 (4369276828034023 / 4000000000000)) (orderedInterval (-4078441143 / 1000000000000) (-4078441142 / 1000000000000), orderedInterval (23796428224 / 1000000000000) (23796428225 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 201 12 (2522603152829167 / 4000000000000)) (orderedInterval (766751110 / 1000000000000) (766751111 / 1000000000000), orderedInterval (-31763435401 / 1000000000000) (-31763435400 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 356 12 (4476403562151803 / 4000000000000)) (orderedInterval (23750932086 / 1000000000000) (23750938626 / 1000000000000), orderedInterval (2171172139 / 1000000000000) (2171178680 / 1000000000000))) = true
  rfl'

theorem compactCertificate617_stateChecks4 :
    compactCertificate617.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 333 12 (4182436871560007 / 4000000000000)) (orderedInterval (-5964531713 / 1000000000000) (-5964531712 / 1000000000000), orderedInterval (-23940309617 / 1000000000000) (-23940309616 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 238 12 (2984784302647031 / 4000000000000)) (orderedInterval (-19210265796 / 1000000000000) (-19210264328 / 1000000000000), orderedInterval (22015580598 / 1000000000000) (22015582066 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 269 12 (3384427277988849 / 4000000000000)) (orderedInterval (-26689858413 / 1000000000000) (-26689819316 / 1000000000000), orderedInterval (6345286071 / 1000000000000) (6345325168 / 1000000000000))) = true
  rfl'

theorem compactCertificate617_stateChecks5 :
    compactCertificate617.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 225 12 (2821582620106081 / 4000000000000)) (orderedInterval (18830837204 / 1000000000000) (18830838372 / 1000000000000), orderedInterval (-23420609354 / 1000000000000) (-23420608185 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 198 12 (2492953814879701 / 4000000000000)) (orderedInterval (29215059960 / 1000000000000) (29215133238 / 1000000000000), orderedInterval (-12982967840 / 1000000000000) (-12982894562 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 288 12 (722555183094399 / 800000000000)) (orderedInterval (-19034888903 / 1000000000000) (-19034887400 / 1000000000000), orderedInterval (18518019063 / 1000000000000) (18518020567 / 1000000000000))) = true
  rfl'

theorem compactCertificate617_stateChecks6 :
    compactCertificate617.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 159 12 (1998625662435053 / 4000000000000)) (orderedInterval (-28577974126 / 1000000000000) (-28577974125 / 1000000000000), orderedInterval (-21358648413 / 1000000000000) (-21358648412 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 135 12 (1694257108219333 / 4000000000000)) (orderedInterval (-9003315071 / 1000000000000) (-9003315070 / 1000000000000), orderedInterval (-37698091676 / 1000000000000) (-37698091675 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (1060187431443799 / 4000000000000)) (orderedInterval (45742042551 / 1000000000000) (45742051076 / 1000000000000), orderedInterval (-17681066810 / 1000000000000) (-17681058285 / 1000000000000))) = true
  rfl'

theorem compactCertificate617_stateChecks7 :
    compactCertificate617.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (570172326654633 / 4000000000000)) (orderedInterval (-61933669996 / 1000000000000) (-61933664559 / 1000000000000), orderedInterval (25324172356 / 1000000000000) (25324177793 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 123 12 (1548128781182899 / 4000000000000)) (orderedInterval (-39976366148 / 1000000000000) (-39976366126 / 1000000000000), orderedInterval (-6786801594 / 1000000000000) (-6786801572 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 168 12 (2113837497104723 / 4000000000000)) (orderedInterval (34483760107 / 1000000000000) (34483760250 / 1000000000000), orderedInterval (3909571626 / 1000000000000) (3909571769 / 1000000000000))) = true
  rfl'

theorem compactCertificate617_stateChecks8 :
    compactCertificate617.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (893812568556201 / 4000000000000)) (orderedInterval (-49450885548 / 1000000000000) (-49450885547 / 1000000000000), orderedInterval (-19979464213 / 1000000000000) (-19979464211 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 289 12 (3633298468190921 / 4000000000000)) (orderedInterval (-24573704917 / 1000000000000) (-24573704867 / 1000000000000), orderedInterval (-9835609144 / 1000000000000) (-9835609094 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 193 12 (2426874994936039 / 4000000000000)) (orderedInterval (-29907785601 / 1000000000000) (-29907785597 / 1000000000000), orderedInterval (-12417510231 / 1000000000000) (-12417510227 / 1000000000000))) = true
  rfl'

theorem compactCertificate617_states : ∀ j,
    BesselStateValid (compactCertificate617.point j) (compactCertificate617.state j) :=
  compactCertificate617.statesValid_of_checks3 compactCertificate617_stateChecks0
    compactCertificate617_stateChecks1 compactCertificate617_stateChecks2
    compactCertificate617_stateChecks3 compactCertificate617_stateChecks4
    compactCertificate617_stateChecks5 compactCertificate617_stateChecks6
    compactCertificate617_stateChecks7 compactCertificate617_stateChecks8

theorem compactCertificate617_chunkChecks0_0 :
    compactCertificate617.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (977 / 2) 0 (IntervalRat.scale (977 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-25979739799 / 1000000000000) (-25979725373 / 1000000000000), orderedInterval (25091837067 / 1000000000000) (25091851493 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1439307556099277 / 4000000000000) 0 (IntervalRat.scale (977 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (26160147144 / 1000000000000) (26160154559 / 1000000000000), orderedInterval (-32973960850 / 1000000000000) (-32973953436 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (465442491202541 / 800000000000) 0 (IntervalRat.scale (977 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-32561339290 / 1000000000000) (-32561339203 / 1000000000000), orderedInterval (-5801028780 / 1000000000000) (-5801028694 / 1000000000000)))) (orderedInterval (-11964434089 / 1000000000000) (-11964428263 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (419986355185639 / 4000000000000) 0 (IntervalRat.scale (977 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-66888846903 / 1000000000000) (-66888826428 / 1000000000000), orderedInterval (40181942237 / 1000000000000) (40181962712 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (1128142425996283 / 4000000000000) 0 (IntervalRat.scale (977 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (3665225038 / 1000000000000) (3665225039 / 1000000000000), orderedInterval (47362284614 / 1000000000000) (47362284615 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (3063126141535311 / 4000000000000) 0 (IntervalRat.scale (977 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (523657631 / 1000000000000) (523657632 / 1000000000000), orderedInterval (28827758376 / 1000000000000) (28827758377 / 1000000000000)))) (orderedInterval (822293446 / 1000000000000) (822293727 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (2256284851993543 / 4000000000000) 0 (IntervalRat.scale (977 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-19800063747 / 1000000000000) (-19800062194 / 1000000000000), orderedInterval (27157439667 / 1000000000000) (27157441220 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3866182551034339 / 4000000000000) 0 (IntervalRat.scale (977 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-7083355970 / 1000000000000) (-7083355969 / 1000000000000), orderedInterval (24671067577 / 1000000000000) (24671067578 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2847812568556201 / 4000000000000) 0 (IntervalRat.scale (977 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (11731950286 / 1000000000000) (11731950315 / 1000000000000), orderedInterval (-27513679406 / 1000000000000) (-27513679378 / 1000000000000)))) (orderedInterval (502017116 / 1000000000000) (502017145 / 1000000000000))) = true
  rfl'

theorem compactCertificate617_chunkChecks0_1 :
    compactCertificate617.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (4369276828034023 / 4000000000000) 0 (IntervalRat.scale (977 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-4078441143 / 1000000000000) (-4078441142 / 1000000000000), orderedInterval (23796428224 / 1000000000000) (23796428225 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2522603152829167 / 4000000000000) 0 (IntervalRat.scale (977 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (766751110 / 1000000000000) (766751111 / 1000000000000), orderedInterval (-31763435401 / 1000000000000) (-31763435400 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (4476403562151803 / 4000000000000) 0 (IntervalRat.scale (977 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23750932086 / 1000000000000) (23750938626 / 1000000000000), orderedInterval (2171172139 / 1000000000000) (2171178680 / 1000000000000)))) (orderedInterval (4157834535 / 1000000000000) (4157835659 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (4182436871560007 / 4000000000000) 0 (IntervalRat.scale (977 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-5964531713 / 1000000000000) (-5964531712 / 1000000000000), orderedInterval (-23940309617 / 1000000000000) (-23940309616 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2984784302647031 / 4000000000000) 0 (IntervalRat.scale (977 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-19210265796 / 1000000000000) (-19210264328 / 1000000000000), orderedInterval (22015580598 / 1000000000000) (22015582066 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (3384427277988849 / 4000000000000) 0 (IntervalRat.scale (977 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-26689858413 / 1000000000000) (-26689819316 / 1000000000000), orderedInterval (6345286071 / 1000000000000) (6345325168 / 1000000000000)))) (orderedInterval (-1573833757 / 1000000000000) (-1573833361 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2821582620106081 / 4000000000000) 0 (IntervalRat.scale (977 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (18830837204 / 1000000000000) (18830838372 / 1000000000000), orderedInterval (-23420609354 / 1000000000000) (-23420608185 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2492953814879701 / 4000000000000) 0 (IntervalRat.scale (977 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (29215059960 / 1000000000000) (29215133238 / 1000000000000), orderedInterval (-12982967840 / 1000000000000) (-12982894562 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (722555183094399 / 800000000000) 0 (IntervalRat.scale (977 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-19034888903 / 1000000000000) (-19034887400 / 1000000000000), orderedInterval (18518019063 / 1000000000000) (18518020567 / 1000000000000)))) (orderedInterval (-1941801067 / 1000000000000) (-1941796774 / 1000000000000))) = true
  rfl'

theorem compactCertificate617_chunkChecks0_2 :
    compactCertificate617.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1998625662435053 / 4000000000000) 0 (IntervalRat.scale (977 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-28577974126 / 1000000000000) (-28577974125 / 1000000000000), orderedInterval (-21358648413 / 1000000000000) (-21358648412 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1694257108219333 / 4000000000000) 0 (IntervalRat.scale (977 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-9003315071 / 1000000000000) (-9003315070 / 1000000000000), orderedInterval (-37698091676 / 1000000000000) (-37698091675 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (1060187431443799 / 4000000000000) 0 (IntervalRat.scale (977 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (45742042551 / 1000000000000) (45742051076 / 1000000000000), orderedInterval (-17681066810 / 1000000000000) (-17681058285 / 1000000000000)))) (orderedInterval (6568133837 / 1000000000000) (6568134237 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (570172326654633 / 4000000000000) 0 (IntervalRat.scale (977 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-61933669996 / 1000000000000) (-61933664559 / 1000000000000), orderedInterval (25324172356 / 1000000000000) (25324177793 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1548128781182899 / 4000000000000) 0 (IntervalRat.scale (977 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-39976366148 / 1000000000000) (-39976366126 / 1000000000000), orderedInterval (-6786801594 / 1000000000000) (-6786801572 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (2113837497104723 / 4000000000000) 0 (IntervalRat.scale (977 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (34483760107 / 1000000000000) (34483760250 / 1000000000000), orderedInterval (3909571626 / 1000000000000) (3909571769 / 1000000000000)))) (orderedInterval (-592245784 / 1000000000000) (-592245614 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (893812568556201 / 4000000000000) 0 (IntervalRat.scale (977 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-49450885548 / 1000000000000) (-49450885547 / 1000000000000), orderedInterval (-19979464213 / 1000000000000) (-19979464211 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3633298468190921 / 4000000000000) 0 (IntervalRat.scale (977 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-24573704917 / 1000000000000) (-24573704867 / 1000000000000), orderedInterval (-9835609144 / 1000000000000) (-9835609094 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2426874994936039 / 4000000000000) 0 (IntervalRat.scale (977 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-29907785601 / 1000000000000) (-29907785597 / 1000000000000), orderedInterval (-12417510231 / 1000000000000) (-12417510227 / 1000000000000)))) (orderedInterval (7313730960 / 1000000000000) (7313731100 / 1000000000000))) = true
  rfl'

theorem compactCertificate617_chunkChecks0 :
    compactCertificate617.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate617.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate617_chunkChecks0_0
    compactCertificate617_chunkChecks0_1 compactCertificate617_chunkChecks0_2

theorem compactCertificate617_chunkChecks1_0 :
    compactCertificate617.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (977 / 2) 1 (IntervalRat.scale (977 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-25979739799 / 1000000000000) (-25979725373 / 1000000000000), orderedInterval (25091837067 / 1000000000000) (25091851493 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1439307556099277 / 4000000000000) 1 (IntervalRat.scale (977 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (26160147144 / 1000000000000) (26160154559 / 1000000000000), orderedInterval (-32973960850 / 1000000000000) (-32973953436 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (465442491202541 / 800000000000) 1 (IntervalRat.scale (977 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-32561339290 / 1000000000000) (-32561339203 / 1000000000000), orderedInterval (-5801028780 / 1000000000000) (-5801028694 / 1000000000000)))) (orderedInterval (9313775170 / 1000000000000) (9313780983 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (419986355185639 / 4000000000000) 1 (IntervalRat.scale (977 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-66888846903 / 1000000000000) (-66888826428 / 1000000000000), orderedInterval (40181942237 / 1000000000000) (40181962712 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (1128142425996283 / 4000000000000) 1 (IntervalRat.scale (977 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (3665225038 / 1000000000000) (3665225039 / 1000000000000), orderedInterval (47362284614 / 1000000000000) (47362284615 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (3063126141535311 / 4000000000000) 1 (IntervalRat.scale (977 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (523657631 / 1000000000000) (523657632 / 1000000000000), orderedInterval (28827758376 / 1000000000000) (28827758377 / 1000000000000)))) (orderedInterval (-2307907067 / 1000000000000) (-2307906952 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (2256284851993543 / 4000000000000) 1 (IntervalRat.scale (977 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-19800063747 / 1000000000000) (-19800062194 / 1000000000000), orderedInterval (27157439667 / 1000000000000) (27157441220 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3866182551034339 / 4000000000000) 1 (IntervalRat.scale (977 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-7083355970 / 1000000000000) (-7083355969 / 1000000000000), orderedInterval (24671067577 / 1000000000000) (24671067578 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2847812568556201 / 4000000000000) 1 (IntervalRat.scale (977 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (11731950286 / 1000000000000) (11731950315 / 1000000000000), orderedInterval (-27513679406 / 1000000000000) (-27513679378 / 1000000000000)))) (orderedInterval (-2474741863 / 1000000000000) (-2474741814 / 1000000000000))) = true
  rfl'

theorem compactCertificate617_chunkChecks1_1 :
    compactCertificate617.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (4369276828034023 / 4000000000000) 1 (IntervalRat.scale (977 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-4078441143 / 1000000000000) (-4078441142 / 1000000000000), orderedInterval (23796428224 / 1000000000000) (23796428225 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2522603152829167 / 4000000000000) 1 (IntervalRat.scale (977 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (766751110 / 1000000000000) (766751111 / 1000000000000), orderedInterval (-31763435401 / 1000000000000) (-31763435400 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (4476403562151803 / 4000000000000) 1 (IntervalRat.scale (977 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23750932086 / 1000000000000) (23750938626 / 1000000000000), orderedInterval (2171172139 / 1000000000000) (2171178680 / 1000000000000)))) (orderedInterval (-11786017286 / 1000000000000) (-11786014754 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (4182436871560007 / 4000000000000) 1 (IntervalRat.scale (977 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-5964531713 / 1000000000000) (-5964531712 / 1000000000000), orderedInterval (-23940309617 / 1000000000000) (-23940309616 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2984784302647031 / 4000000000000) 1 (IntervalRat.scale (977 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-19210265796 / 1000000000000) (-19210264328 / 1000000000000), orderedInterval (22015580598 / 1000000000000) (22015582066 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (3384427277988849 / 4000000000000) 1 (IntervalRat.scale (977 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-26689858413 / 1000000000000) (-26689819316 / 1000000000000), orderedInterval (6345286071 / 1000000000000) (6345325168 / 1000000000000)))) (orderedInterval (4049564639 / 1000000000000) (4049565288 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2821582620106081 / 4000000000000) 1 (IntervalRat.scale (977 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (18830837204 / 1000000000000) (18830838372 / 1000000000000), orderedInterval (-23420609354 / 1000000000000) (-23420608185 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2492953814879701 / 4000000000000) 1 (IntervalRat.scale (977 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (29215059960 / 1000000000000) (29215133238 / 1000000000000), orderedInterval (-12982967840 / 1000000000000) (-12982894562 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (722555183094399 / 800000000000) 1 (IntervalRat.scale (977 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-19034888903 / 1000000000000) (-19034887400 / 1000000000000), orderedInterval (18518019063 / 1000000000000) (18518020567 / 1000000000000)))) (orderedInterval (1433991447 / 1000000000000) (1433996956 / 1000000000000))) = true
  rfl'

theorem compactCertificate617_chunkChecks1_2 :
    compactCertificate617.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1998625662435053 / 4000000000000) 1 (IntervalRat.scale (977 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-28577974126 / 1000000000000) (-28577974125 / 1000000000000), orderedInterval (-21358648413 / 1000000000000) (-21358648412 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1694257108219333 / 4000000000000) 1 (IntervalRat.scale (977 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-9003315071 / 1000000000000) (-9003315070 / 1000000000000), orderedInterval (-37698091676 / 1000000000000) (-37698091675 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (1060187431443799 / 4000000000000) 1 (IntervalRat.scale (977 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (45742042551 / 1000000000000) (45742051076 / 1000000000000), orderedInterval (-17681066810 / 1000000000000) (-17681058285 / 1000000000000)))) (orderedInterval (5030847841 / 1000000000000) (5030848105 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (570172326654633 / 4000000000000) 1 (IntervalRat.scale (977 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-61933669996 / 1000000000000) (-61933664559 / 1000000000000), orderedInterval (25324172356 / 1000000000000) (25324177793 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1548128781182899 / 4000000000000) 1 (IntervalRat.scale (977 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-39976366148 / 1000000000000) (-39976366126 / 1000000000000), orderedInterval (-6786801594 / 1000000000000) (-6786801572 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (2113837497104723 / 4000000000000) 1 (IntervalRat.scale (977 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (34483760107 / 1000000000000) (34483760250 / 1000000000000), orderedInterval (3909571626 / 1000000000000) (3909571769 / 1000000000000)))) (orderedInterval (-338593741 / 1000000000000) (-338593647 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (893812568556201 / 4000000000000) 1 (IntervalRat.scale (977 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-49450885548 / 1000000000000) (-49450885547 / 1000000000000), orderedInterval (-19979464213 / 1000000000000) (-19979464211 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3633298468190921 / 4000000000000) 1 (IntervalRat.scale (977 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-24573704917 / 1000000000000) (-24573704867 / 1000000000000), orderedInterval (-9835609144 / 1000000000000) (-9835609094 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2426874994936039 / 4000000000000) 1 (IntervalRat.scale (977 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-29907785601 / 1000000000000) (-29907785597 / 1000000000000), orderedInterval (-12417510231 / 1000000000000) (-12417510227 / 1000000000000)))) (orderedInterval (4327308858 / 1000000000000) (4327309056 / 1000000000000))) = true
  rfl'

theorem compactCertificate617_chunkChecks1 :
    compactCertificate617.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate617.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate617_chunkChecks1_0
    compactCertificate617_chunkChecks1_1 compactCertificate617_chunkChecks1_2

theorem compactCertificate617_chunkChecks2_0 :
    compactCertificate617.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (977 / 2) 2 (IntervalRat.scale (977 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-25979739799 / 1000000000000) (-25979725373 / 1000000000000), orderedInterval (25091837067 / 1000000000000) (25091851493 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1439307556099277 / 4000000000000) 2 (IntervalRat.scale (977 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (26160147144 / 1000000000000) (26160154559 / 1000000000000), orderedInterval (-32973960850 / 1000000000000) (-32973953436 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (465442491202541 / 800000000000) 2 (IntervalRat.scale (977 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-32561339290 / 1000000000000) (-32561339203 / 1000000000000), orderedInterval (-5801028780 / 1000000000000) (-5801028694 / 1000000000000)))) (orderedInterval (12856468799 / 1000000000000) (12856474618 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (419986355185639 / 4000000000000) 2 (IntervalRat.scale (977 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-66888846903 / 1000000000000) (-66888826428 / 1000000000000), orderedInterval (40181942237 / 1000000000000) (40181962712 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (1128142425996283 / 4000000000000) 2 (IntervalRat.scale (977 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (3665225038 / 1000000000000) (3665225039 / 1000000000000), orderedInterval (47362284614 / 1000000000000) (47362284615 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (3063126141535311 / 4000000000000) 2 (IntervalRat.scale (977 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (523657631 / 1000000000000) (523657632 / 1000000000000), orderedInterval (28827758376 / 1000000000000) (28827758377 / 1000000000000)))) (orderedInterval (18072665 / 1000000000000) (18072768 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (2256284851993543 / 4000000000000) 2 (IntervalRat.scale (977 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-19800063747 / 1000000000000) (-19800062194 / 1000000000000), orderedInterval (27157439667 / 1000000000000) (27157441220 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3866182551034339 / 4000000000000) 2 (IntervalRat.scale (977 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-7083355970 / 1000000000000) (-7083355969 / 1000000000000), orderedInterval (24671067577 / 1000000000000) (24671067578 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2847812568556201 / 4000000000000) 2 (IntervalRat.scale (977 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (11731950286 / 1000000000000) (11731950315 / 1000000000000), orderedInterval (-27513679406 / 1000000000000) (-27513679378 / 1000000000000)))) (orderedInterval (-1452509122 / 1000000000000) (-1452509035 / 1000000000000))) = true
  rfl'

theorem compactCertificate617_chunkChecks2_1 :
    compactCertificate617.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (4369276828034023 / 4000000000000) 2 (IntervalRat.scale (977 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-4078441143 / 1000000000000) (-4078441142 / 1000000000000), orderedInterval (23796428224 / 1000000000000) (23796428225 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2522603152829167 / 4000000000000) 2 (IntervalRat.scale (977 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (766751110 / 1000000000000) (766751111 / 1000000000000), orderedInterval (-31763435401 / 1000000000000) (-31763435400 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (4476403562151803 / 4000000000000) 2 (IntervalRat.scale (977 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23750932086 / 1000000000000) (23750938626 / 1000000000000), orderedInterval (2171172139 / 1000000000000) (2171178680 / 1000000000000)))) (orderedInterval (-21413649320 / 1000000000000) (-21413643576 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (4182436871560007 / 4000000000000) 2 (IntervalRat.scale (977 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-5964531713 / 1000000000000) (-5964531712 / 1000000000000), orderedInterval (-23940309617 / 1000000000000) (-23940309616 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2984784302647031 / 4000000000000) 2 (IntervalRat.scale (977 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-19210265796 / 1000000000000) (-19210264328 / 1000000000000), orderedInterval (22015580598 / 1000000000000) (22015582066 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (3384427277988849 / 4000000000000) 2 (IntervalRat.scale (977 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-26689858413 / 1000000000000) (-26689819316 / 1000000000000), orderedInterval (6345286071 / 1000000000000) (6345325168 / 1000000000000)))) (orderedInterval (3331863202 / 1000000000000) (3331864277 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2821582620106081 / 4000000000000) 2 (IntervalRat.scale (977 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (18830837204 / 1000000000000) (18830838372 / 1000000000000), orderedInterval (-23420609354 / 1000000000000) (-23420608185 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2492953814879701 / 4000000000000) 2 (IntervalRat.scale (977 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (29215059960 / 1000000000000) (29215133238 / 1000000000000), orderedInterval (-12982967840 / 1000000000000) (-12982894562 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (722555183094399 / 800000000000) 2 (IntervalRat.scale (977 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-19034888903 / 1000000000000) (-19034887400 / 1000000000000), orderedInterval (18518019063 / 1000000000000) (18518020567 / 1000000000000)))) (orderedInterval (3931054654 / 1000000000000) (3931061752 / 1000000000000))) = true
  rfl'

theorem compactCertificate617_chunkChecks2_2 :
    compactCertificate617.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1998625662435053 / 4000000000000) 2 (IntervalRat.scale (977 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-28577974126 / 1000000000000) (-28577974125 / 1000000000000), orderedInterval (-21358648413 / 1000000000000) (-21358648412 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1694257108219333 / 4000000000000) 2 (IntervalRat.scale (977 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-9003315071 / 1000000000000) (-9003315070 / 1000000000000), orderedInterval (-37698091676 / 1000000000000) (-37698091675 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (1060187431443799 / 4000000000000) 2 (IntervalRat.scale (977 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (45742042551 / 1000000000000) (45742051076 / 1000000000000), orderedInterval (-17681066810 / 1000000000000) (-17681058285 / 1000000000000)))) (orderedInterval (-5612293439 / 1000000000000) (-5612293248 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (570172326654633 / 4000000000000) 2 (IntervalRat.scale (977 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-61933669996 / 1000000000000) (-61933664559 / 1000000000000), orderedInterval (25324172356 / 1000000000000) (25324177793 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1548128781182899 / 4000000000000) 2 (IntervalRat.scale (977 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-39976366148 / 1000000000000) (-39976366126 / 1000000000000), orderedInterval (-6786801594 / 1000000000000) (-6786801572 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (2113837497104723 / 4000000000000) 2 (IntervalRat.scale (977 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (34483760107 / 1000000000000) (34483760250 / 1000000000000), orderedInterval (3909571626 / 1000000000000) (3909571769 / 1000000000000)))) (orderedInterval (2426859567 / 1000000000000) (2426859641 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (893812568556201 / 4000000000000) 2 (IntervalRat.scale (977 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-49450885548 / 1000000000000) (-49450885547 / 1000000000000), orderedInterval (-19979464213 / 1000000000000) (-19979464211 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3633298468190921 / 4000000000000) 2 (IntervalRat.scale (977 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-24573704917 / 1000000000000) (-24573704867 / 1000000000000), orderedInterval (-9835609144 / 1000000000000) (-9835609094 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2426874994936039 / 4000000000000) 2 (IntervalRat.scale (977 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-29907785601 / 1000000000000) (-29907785597 / 1000000000000), orderedInterval (-12417510231 / 1000000000000) (-12417510227 / 1000000000000)))) (orderedInterval (-15518662310 / 1000000000000) (-15518662014 / 1000000000000))) = true
  rfl'

theorem compactCertificate617_chunkChecks2 :
    compactCertificate617.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate617.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate617_chunkChecks2_0
    compactCertificate617_chunkChecks2_1 compactCertificate617_chunkChecks2_2

theorem compactCertificate617_chunkChecks3_0 :
    compactCertificate617.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (977 / 2) 3 (IntervalRat.scale (977 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-25979739799 / 1000000000000) (-25979725373 / 1000000000000), orderedInterval (25091837067 / 1000000000000) (25091851493 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1439307556099277 / 4000000000000) 3 (IntervalRat.scale (977 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (26160147144 / 1000000000000) (26160154559 / 1000000000000), orderedInterval (-32973960850 / 1000000000000) (-32973953436 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (465442491202541 / 800000000000) 3 (IntervalRat.scale (977 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-32561339290 / 1000000000000) (-32561339203 / 1000000000000), orderedInterval (-5801028780 / 1000000000000) (-5801028694 / 1000000000000)))) (orderedInterval (-9273922104 / 1000000000000) (-9273916287 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (419986355185639 / 4000000000000) 3 (IntervalRat.scale (977 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-66888846903 / 1000000000000) (-66888826428 / 1000000000000), orderedInterval (40181942237 / 1000000000000) (40181962712 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (1128142425996283 / 4000000000000) 3 (IntervalRat.scale (977 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (3665225038 / 1000000000000) (3665225039 / 1000000000000), orderedInterval (47362284614 / 1000000000000) (47362284615 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (3063126141535311 / 4000000000000) 3 (IntervalRat.scale (977 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (523657631 / 1000000000000) (523657632 / 1000000000000), orderedInterval (28827758376 / 1000000000000) (28827758377 / 1000000000000)))) (orderedInterval (7566227985 / 1000000000000) (7566228126 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (2256284851993543 / 4000000000000) 3 (IntervalRat.scale (977 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-19800063747 / 1000000000000) (-19800062194 / 1000000000000), orderedInterval (27157439667 / 1000000000000) (27157441220 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3866182551034339 / 4000000000000) 3 (IntervalRat.scale (977 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-7083355970 / 1000000000000) (-7083355969 / 1000000000000), orderedInterval (24671067577 / 1000000000000) (24671067578 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2847812568556201 / 4000000000000) 3 (IntervalRat.scale (977 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (11731950286 / 1000000000000) (11731950315 / 1000000000000), orderedInterval (-27513679406 / 1000000000000) (-27513679378 / 1000000000000)))) (orderedInterval (7955758090 / 1000000000000) (7955758246 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate617_chunkChecks3_1 :
    compactCertificate617.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (4369276828034023 / 4000000000000) 3 (IntervalRat.scale (977 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-4078441143 / 1000000000000) (-4078441142 / 1000000000000), orderedInterval (23796428224 / 1000000000000) (23796428225 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2522603152829167 / 4000000000000) 3 (IntervalRat.scale (977 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (766751110 / 1000000000000) (766751111 / 1000000000000), orderedInterval (-31763435401 / 1000000000000) (-31763435400 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (4476403562151803 / 4000000000000) 3 (IntervalRat.scale (977 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23750932086 / 1000000000000) (23750938626 / 1000000000000), orderedInterval (2171172139 / 1000000000000) (2171178680 / 1000000000000)))) (orderedInterval (48670912256 / 1000000000000) (48670925332 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (4182436871560007 / 4000000000000) 3 (IntervalRat.scale (977 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-5964531713 / 1000000000000) (-5964531712 / 1000000000000), orderedInterval (-23940309617 / 1000000000000) (-23940309616 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2984784302647031 / 4000000000000) 3 (IntervalRat.scale (977 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-19210265796 / 1000000000000) (-19210264328 / 1000000000000), orderedInterval (22015580598 / 1000000000000) (22015582066 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (3384427277988849 / 4000000000000) 3 (IntervalRat.scale (977 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-26689858413 / 1000000000000) (-26689819316 / 1000000000000), orderedInterval (6345286071 / 1000000000000) (6345325168 / 1000000000000)))) (orderedInterval (-11498496664 / 1000000000000) (-11498494874 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2821582620106081 / 4000000000000) 3 (IntervalRat.scale (977 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (18830837204 / 1000000000000) (18830838372 / 1000000000000), orderedInterval (-23420609354 / 1000000000000) (-23420608185 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2492953814879701 / 4000000000000) 3 (IntervalRat.scale (977 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (29215059960 / 1000000000000) (29215133238 / 1000000000000), orderedInterval (-12982967840 / 1000000000000) (-12982894562 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (722555183094399 / 800000000000) 3 (IntervalRat.scale (977 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-19034888903 / 1000000000000) (-19034887400 / 1000000000000), orderedInterval (18518019063 / 1000000000000) (18518020567 / 1000000000000)))) (orderedInterval (-3733383591 / 1000000000000) (-3733374429 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate617_chunkChecks3_2 :
    compactCertificate617.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1998625662435053 / 4000000000000) 3 (IntervalRat.scale (977 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-28577974126 / 1000000000000) (-28577974125 / 1000000000000), orderedInterval (-21358648413 / 1000000000000) (-21358648412 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1694257108219333 / 4000000000000) 3 (IntervalRat.scale (977 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-9003315071 / 1000000000000) (-9003315070 / 1000000000000), orderedInterval (-37698091676 / 1000000000000) (-37698091675 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (1060187431443799 / 4000000000000) 3 (IntervalRat.scale (977 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (45742042551 / 1000000000000) (45742051076 / 1000000000000), orderedInterval (-17681066810 / 1000000000000) (-17681058285 / 1000000000000)))) (orderedInterval (-4941915708 / 1000000000000) (-4941915558 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (570172326654633 / 4000000000000) 3 (IntervalRat.scale (977 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-61933669996 / 1000000000000) (-61933664559 / 1000000000000), orderedInterval (25324172356 / 1000000000000) (25324177793 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1548128781182899 / 4000000000000) 3 (IntervalRat.scale (977 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-39976366148 / 1000000000000) (-39976366126 / 1000000000000), orderedInterval (-6786801594 / 1000000000000) (-6786801572 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (2113837497104723 / 4000000000000) 3 (IntervalRat.scale (977 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (34483760107 / 1000000000000) (34483760250 / 1000000000000), orderedInterval (3909571626 / 1000000000000) (3909571769 / 1000000000000)))) (orderedInterval (309405475 / 1000000000000) (309405546 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (893812568556201 / 4000000000000) 3 (IntervalRat.scale (977 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-49450885548 / 1000000000000) (-49450885547 / 1000000000000), orderedInterval (-19979464213 / 1000000000000) (-19979464211 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3633298468190921 / 4000000000000) 3 (IntervalRat.scale (977 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-24573704917 / 1000000000000) (-24573704867 / 1000000000000), orderedInterval (-9835609144 / 1000000000000) (-9835609094 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2426874994936039 / 4000000000000) 3 (IntervalRat.scale (977 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-29907785601 / 1000000000000) (-29907785597 / 1000000000000), orderedInterval (-12417510231 / 1000000000000) (-12417510227 / 1000000000000)))) (orderedInterval (-9567534823 / 1000000000000) (-9567534363 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate617_chunkChecks3 :
    compactCertificate617.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate617.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate617_chunkChecks3_0
    compactCertificate617_chunkChecks3_1 compactCertificate617_chunkChecks3_2

theorem compactCertificate617_chunkChecks4_0 :
    compactCertificate617.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (977 / 2) 4 (IntervalRat.scale (977 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-25979739799 / 1000000000000) (-25979725373 / 1000000000000), orderedInterval (25091837067 / 1000000000000) (25091851493 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1439307556099277 / 4000000000000) 4 (IntervalRat.scale (977 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (26160147144 / 1000000000000) (26160154559 / 1000000000000), orderedInterval (-32973960850 / 1000000000000) (-32973953436 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (465442491202541 / 800000000000) 4 (IntervalRat.scale (977 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-32561339290 / 1000000000000) (-32561339203 / 1000000000000), orderedInterval (-5801028780 / 1000000000000) (-5801028694 / 1000000000000)))) (orderedInterval (-14032237222 / 1000000000000) (-14032231390 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (419986355185639 / 4000000000000) 4 (IntervalRat.scale (977 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-66888846903 / 1000000000000) (-66888826428 / 1000000000000), orderedInterval (40181942237 / 1000000000000) (40181962712 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (1128142425996283 / 4000000000000) 4 (IntervalRat.scale (977 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (3665225038 / 1000000000000) (3665225039 / 1000000000000), orderedInterval (47362284614 / 1000000000000) (47362284615 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (3063126141535311 / 4000000000000) 4 (IntervalRat.scale (977 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (523657631 / 1000000000000) (523657632 / 1000000000000), orderedInterval (28827758376 / 1000000000000) (28827758377 / 1000000000000)))) (orderedInterval (-239368989 / 1000000000000) (-239368776 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (2256284851993543 / 4000000000000) 4 (IntervalRat.scale (977 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-19800063747 / 1000000000000) (-19800062194 / 1000000000000), orderedInterval (27157439667 / 1000000000000) (27157441220 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3866182551034339 / 4000000000000) 4 (IntervalRat.scale (977 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-7083355970 / 1000000000000) (-7083355969 / 1000000000000), orderedInterval (24671067577 / 1000000000000) (24671067578 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2847812568556201 / 4000000000000) 4 (IntervalRat.scale (977 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (11731950286 / 1000000000000) (11731950315 / 1000000000000), orderedInterval (-27513679406 / 1000000000000) (-27513679378 / 1000000000000)))) (orderedInterval (4595109484 / 1000000000000) (4595109773 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate617_chunkChecks4_1 :
    compactCertificate617.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (4369276828034023 / 4000000000000) 4 (IntervalRat.scale (977 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-4078441143 / 1000000000000) (-4078441142 / 1000000000000), orderedInterval (23796428224 / 1000000000000) (23796428225 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2522603152829167 / 4000000000000) 4 (IntervalRat.scale (977 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (766751110 / 1000000000000) (766751111 / 1000000000000), orderedInterval (-31763435401 / 1000000000000) (-31763435400 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (4476403562151803 / 4000000000000) 4 (IntervalRat.scale (977 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23750932086 / 1000000000000) (23750938626 / 1000000000000), orderedInterval (2171172139 / 1000000000000) (2171178680 / 1000000000000)))) (orderedInterval (111071679182 / 1000000000000) (111071709024 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (4182436871560007 / 4000000000000) 4 (IntervalRat.scale (977 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-5964531713 / 1000000000000) (-5964531712 / 1000000000000), orderedInterval (-23940309617 / 1000000000000) (-23940309616 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2984784302647031 / 4000000000000) 4 (IntervalRat.scale (977 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-19210265796 / 1000000000000) (-19210264328 / 1000000000000), orderedInterval (22015580598 / 1000000000000) (22015582066 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (3384427277988849 / 4000000000000) 4 (IntervalRat.scale (977 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-26689858413 / 1000000000000) (-26689819316 / 1000000000000), orderedInterval (6345286071 / 1000000000000) (6345325168 / 1000000000000)))) (orderedInterval (-6367372262 / 1000000000000) (-6367369259 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2821582620106081 / 4000000000000) 4 (IntervalRat.scale (977 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (18830837204 / 1000000000000) (18830838372 / 1000000000000), orderedInterval (-23420609354 / 1000000000000) (-23420608185 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2492953814879701 / 4000000000000) 4 (IntervalRat.scale (977 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (29215059960 / 1000000000000) (29215133238 / 1000000000000), orderedInterval (-12982967840 / 1000000000000) (-12982894562 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (722555183094399 / 800000000000) 4 (IntervalRat.scale (977 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-19034888903 / 1000000000000) (-19034887400 / 1000000000000), orderedInterval (18518019063 / 1000000000000) (18518020567 / 1000000000000)))) (orderedInterval (-9164244513 / 1000000000000) (-9164232611 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate617_chunkChecks4_2 :
    compactCertificate617.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1998625662435053 / 4000000000000) 4 (IntervalRat.scale (977 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-28577974126 / 1000000000000) (-28577974125 / 1000000000000), orderedInterval (-21358648413 / 1000000000000) (-21358648412 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1694257108219333 / 4000000000000) 4 (IntervalRat.scale (977 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-9003315071 / 1000000000000) (-9003315070 / 1000000000000), orderedInterval (-37698091676 / 1000000000000) (-37698091675 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (1060187431443799 / 4000000000000) 4 (IntervalRat.scale (977 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (45742042551 / 1000000000000) (45742051076 / 1000000000000), orderedInterval (-17681066810 / 1000000000000) (-17681058285 / 1000000000000)))) (orderedInterval (5438639492 / 1000000000000) (5438639620 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (570172326654633 / 4000000000000) 4 (IntervalRat.scale (977 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-61933669996 / 1000000000000) (-61933664559 / 1000000000000), orderedInterval (25324172356 / 1000000000000) (25324177793 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1548128781182899 / 4000000000000) 4 (IntervalRat.scale (977 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-39976366148 / 1000000000000) (-39976366126 / 1000000000000), orderedInterval (-6786801594 / 1000000000000) (-6786801572 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (2113837497104723 / 4000000000000) 4 (IntervalRat.scale (977 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (34483760107 / 1000000000000) (34483760250 / 1000000000000), orderedInterval (3909571626 / 1000000000000) (3909571769 / 1000000000000)))) (orderedInterval (-3255131426 / 1000000000000) (-3255131354 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (893812568556201 / 4000000000000) 4 (IntervalRat.scale (977 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-49450885548 / 1000000000000) (-49450885547 / 1000000000000), orderedInterval (-19979464213 / 1000000000000) (-19979464211 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3633298468190921 / 4000000000000) 4 (IntervalRat.scale (977 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-24573704917 / 1000000000000) (-24573704867 / 1000000000000), orderedInterval (-9835609144 / 1000000000000) (-9835609094 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2426874994936039 / 4000000000000) 4 (IntervalRat.scale (977 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-29907785601 / 1000000000000) (-29907785597 / 1000000000000), orderedInterval (-12417510231 / 1000000000000) (-12417510227 / 1000000000000)))) (orderedInterval (37290486200 / 1000000000000) (37290486945 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate617_chunkChecks4 :
    compactCertificate617.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate617.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate617_chunkChecks4_0
    compactCertificate617_chunkChecks4_1 compactCertificate617_chunkChecks4_2

theorem compactCertificate617_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate617.chunkCheck r b = true :=
  compactCertificate617.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate617_chunkChecks0
    · exact compactCertificate617_chunkChecks1
    · exact compactCertificate617_chunkChecks2
    · exact compactCertificate617_chunkChecks3
    · exact compactCertificate617_chunkChecks4)

theorem compactCertificate617_coefficient0 :
    compactCertificate617.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate617_coefficient1 :
    compactCertificate617.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate617_coefficient2 :
    compactCertificate617.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate617_coefficient3 :
    compactCertificate617.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate617_coefficient4 :
    compactCertificate617.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate617_coefficients : ∀ r : Fin 5,
    compactCertificate617.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate617_coefficient0
  · exact compactCertificate617_coefficient1
  · exact compactCertificate617_coefficient2
  · exact compactCertificate617_coefficient3
  · exact compactCertificate617_coefficient4

theorem compactCertificate617_lower : (1 : ℚ) ≤ compactCertificate617.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate617, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate617_proves {t : ℝ} (ht : t ∈ compactCertificate617.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate617.proves compactCertificate617_states compactCertificate617_chunks
    compactCertificate617_coefficients compactCertificate617_lower ht

end Erdos232
