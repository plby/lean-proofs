/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate385 : CompactCertificate where
  left := 256
  right := 257
  center := 513 / 2
  grid := fun i =>
    match i.val with
    | 0 => 82
    | 1 => 60
    | 2 => 97
    | 3 => 18
    | 4 => 47
    | 5 => 128
    | 6 => 94
    | 7 => 162
    | 8 => 119
    | 9 => 183
    | 10 => 105
    | 11 => 187
    | 12 => 175
    | 13 => 125
    | 14 => 141
    | 15 => 118
    | 16 => 104
    | 17 => 151
    | 18 => 84
    | 19 => 71
    | 20 => 44
    | 21 => 24
    | 22 => 65
    | 23 => 88
    | 24 => 37
    | 25 => 152
    | _ => 101
  point := fun i =>
    match i.val with
    | 0 => 513 / 2
    | 1 => 755746956273213 / 4000000000000
    | 2 => 244393037857629 / 800000000000
    | 3 => 220525076980791 / 4000000000000
    | 4 => 592361376188427 / 4000000000000
    | 5 => 1608376367049759 / 4000000000000
    | 6 => 1184722752377367 / 4000000000000
    | 7 => 2030042629151091 / 4000000000000
    | 8 => 1495320212558169 / 4000000000000
    | 9 => 2294205744914487 / 4000000000000
    | 10 => 1324560304402623 / 4000000000000
    | 11 => 2350455503975307 / 4000000000000
    | 12 => 2196100424882583 / 4000000000000
    | 13 => 1567240887674439 / 4000000000000
    | 14 => 1777084128565281 / 4000000000000
    | 15 => 1481547476063889 / 4000000000000
    | 16 => 1308992125929669 / 4000000000000
    | 17 => 379396938513231 / 800000000000
    | 18 => 1049431898494557 / 4000000000000
    | 19 => 889615042493877 / 4000000000000
    | 20 => 556679787441831 / 4000000000000
    | 21 => 299384241119577 / 4000000000000
    | 22 => 812886453169731 / 4000000000000
    | 23 => 1109926956002787 / 4000000000000
    | 24 => 469320212558169 / 4000000000000
    | 25 => 1907760608169849 / 4000000000000
    | _ => 1274295672878391 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-15940098414 / 1000000000000) (-15940098166 / 1000000000000), orderedInterval (47231341631 / 1000000000000) (47231341879 / 1000000000000))
    | 1 => (orderedInterval (54629129459 / 1000000000000) (54629129460 / 1000000000000), orderedInterval (19480300828 / 1000000000000) (19480300829 / 1000000000000))
    | 2 => (orderedInterval (-45630763534 / 1000000000000) (-45630763437 / 1000000000000), orderedInterval (-1248862934 / 1000000000000) (-1248862837 / 1000000000000))
    | 3 => (orderedInterval (-63677304941 / 1000000000000) (-63677281990 / 1000000000000), orderedInterval (87137761980 / 1000000000000) (87137784931 / 1000000000000))
    | 4 => (orderedInterval (-61573508066 / 1000000000000) (-61573508065 / 1000000000000), orderedInterval (-22320873886 / 1000000000000) (-22320873884 / 1000000000000))
    | 5 => (orderedInterval (27277022568 / 1000000000000) (27277022569 / 1000000000000), orderedInterval (28935458477 / 1000000000000) (28935458478 / 1000000000000))
    | 6 => (orderedInterval (46193910699 / 1000000000000) (46193911119 / 1000000000000), orderedInterval (-4021327326 / 1000000000000) (-4021326905 / 1000000000000))
    | 7 => (orderedInterval (-21213612428 / 1000000000000) (-21213609973 / 1000000000000), orderedInterval (28382487307 / 1000000000000) (28382489763 / 1000000000000))
    | 8 => (orderedInterval (-28596508434 / 1000000000000) (-28596508433 / 1000000000000), orderedInterval (-29714155391 / 1000000000000) (-29714155390 / 1000000000000))
    | 9 => (orderedInterval (18113941464 / 1000000000000) (18113942225 / 1000000000000), orderedInterval (-27977307170 / 1000000000000) (-27977306408 / 1000000000000))
    | 10 => (orderedInterval (-38747394898 / 1000000000000) (-38747358105 / 1000000000000), orderedInterval (20580390471 / 1000000000000) (20580427265 / 1000000000000))
    | 11 => (orderedInterval (-26211844324 / 1000000000000) (-26211844323 / 1000000000000), orderedInterval (-19885916761 / 1000000000000) (-19885916760 / 1000000000000))
    | 12 => (orderedInterval (-1074585105 / 1000000000000) (-1074585104 / 1000000000000), orderedInterval (-34034173443 / 1000000000000) (-34034173442 / 1000000000000))
    | 13 => (orderedInterval (4175788662 / 1000000000000) (4175788665 / 1000000000000), orderedInterval (-40097481857 / 1000000000000) (-40097481854 / 1000000000000))
    | 14 => (orderedInterval (-32835940097 / 1000000000000) (-32835858523 / 1000000000000), orderedInterval (18871901038 / 1000000000000) (18871982612 / 1000000000000))
    | 15 => (orderedInterval (18553679232 / 1000000000000) (18553679233 / 1000000000000), orderedInterval (37049995771 / 1000000000000) (37049995772 / 1000000000000))
    | 16 => (orderedInterval (42585329054 / 1000000000000) (42585329058 / 1000000000000), orderedInterval (11418037788 / 1000000000000) (11418037792 / 1000000000000))
    | 17 => (orderedInterval (-22196962791 / 1000000000000) (-22196962790 / 1000000000000), orderedInterval (-29125826811 / 1000000000000) (-29125826810 / 1000000000000))
    | 18 => (orderedInterval (-33609333708 / 1000000000000) (-33609307731 / 1000000000000), orderedInterval (36077159807 / 1000000000000) (36077185785 / 1000000000000))
    | 19 => (orderedInterval (-7228304036 / 1000000000000) (-7228304035 / 1000000000000), orderedInterval (-52995155661 / 1000000000000) (-52995155660 / 1000000000000))
    | 20 => (orderedInterval (66838127142 / 1000000000000) (66838127508 / 1000000000000), orderedInterval (-10586244125 / 1000000000000) (-10586243759 / 1000000000000))
    | 21 => (orderedInterval (21165817706 / 1000000000000) (21165817707 / 1000000000000), orderedInterval (89624415887 / 1000000000000) (89624415888 / 1000000000000))
    | 22 => (orderedInterval (10961810055 / 1000000000000) (10961810116 / 1000000000000), orderedInterval (-54913084705 / 1000000000000) (-54913084644 / 1000000000000))
    | 23 => (orderedInterval (46573809953 / 1000000000000) (46573812209 / 1000000000000), orderedInterval (-11271106907 / 1000000000000) (-11271104651 / 1000000000000))
    | 24 => (orderedInterval (-70268133563 / 1000000000000) (-70268131585 / 1000000000000), orderedInterval (22395537464 / 1000000000000) (22395539442 / 1000000000000))
    | 25 => (orderedInterval (7373080108 / 1000000000000) (7373080109 / 1000000000000), orderedInterval (35775485556 / 1000000000000) (35775485557 / 1000000000000))
    | _ => (orderedInterval (-39500056780 / 1000000000000) (-39500021980 / 1000000000000), orderedInterval (20992525850 / 1000000000000) (20992560650 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-8486724723 / 1000000000000) (-8486724600 / 1000000000000)
      | 1 => orderedInterval (-3496416682 / 1000000000000) (-3496416402 / 1000000000000)
      | 2 => orderedInterval (-36808588 / 1000000000000) (-36808497 / 1000000000000)
      | 3 => orderedInterval (-9815660097 / 1000000000000) (-9815657134 / 1000000000000)
      | 4 => orderedInterval (580442463 / 1000000000000) (580442907 / 1000000000000)
      | 5 => orderedInterval (-2791095044 / 1000000000000) (-2791095018 / 1000000000000)
      | 6 => orderedInterval (7958929287 / 1000000000000) (7958933518 / 1000000000000)
      | 7 => orderedInterval (-4208882729 / 1000000000000) (-4208882523 / 1000000000000)
      | _ => orderedInterval (6387470725 / 1000000000000) (6387477338 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (18767274152 / 1000000000000) (18767274278 / 1000000000000)
      | 1 => orderedInterval (-3898331711 / 1000000000000) (-3898331621 / 1000000000000)
      | 2 => orderedInterval (-2778749864 / 1000000000000) (-2778749689 / 1000000000000)
      | 3 => orderedInterval (6608439956 / 1000000000000) (6608443990 / 1000000000000)
      | 4 => orderedInterval (-4642245273 / 1000000000000) (-4642244507 / 1000000000000)
      | 5 => orderedInterval (-1594639506 / 1000000000000) (-1594639469 / 1000000000000)
      | 6 => orderedInterval (-3486401155 / 1000000000000) (-3486396840 / 1000000000000)
      | 7 => orderedInterval (1438596535 / 1000000000000) (1438596751 / 1000000000000)
      | _ => orderedInterval (-10245168016 / 1000000000000) (-10245159801 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (9766952369 / 1000000000000) (9766952499 / 1000000000000)
      | 1 => orderedInterval (5497898340 / 1000000000000) (5497898401 / 1000000000000)
      | 2 => orderedInterval (-1082699243 / 1000000000000) (-1082698901 / 1000000000000)
      | 3 => orderedInterval (40407775702 / 1000000000000) (40407781389 / 1000000000000)
      | 4 => orderedInterval (-1490661438 / 1000000000000) (-1490660113 / 1000000000000)
      | 5 => orderedInterval (5469072585 / 1000000000000) (5469072639 / 1000000000000)
      | 6 => orderedInterval (-6556693279 / 1000000000000) (-6556688857 / 1000000000000)
      | 7 => orderedInterval (4360972455 / 1000000000000) (4360972687 / 1000000000000)
      | _ => orderedInterval (-9228745700 / 1000000000000) (-9228735445 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-18707380466 / 1000000000000) (-18707380330 / 1000000000000)
      | 1 => orderedInterval (8068976171 / 1000000000000) (8068976247 / 1000000000000)
      | 2 => orderedInterval (9008322700 / 1000000000000) (9008323369 / 1000000000000)
      | 3 => orderedInterval (-25030493449 / 1000000000000) (-25030485058 / 1000000000000)
      | 4 => orderedInterval (7991243812 / 1000000000000) (7991246102 / 1000000000000)
      | 5 => orderedInterval (4760780872 / 1000000000000) (4760780955 / 1000000000000)
      | 6 => orderedInterval (4298025001 / 1000000000000) (4298029520 / 1000000000000)
      | 7 => orderedInterval (-1689039135 / 1000000000000) (-1689038886 / 1000000000000)
      | _ => orderedInterval (26290946416 / 1000000000000) (26290959193 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-11409914675 / 1000000000000) (-11409914532 / 1000000000000)
      | 1 => orderedInterval (-12021359987 / 1000000000000) (-12021359874 / 1000000000000)
      | 2 => orderedInterval (6839610110 / 1000000000000) (6839611426 / 1000000000000)
      | 3 => orderedInterval (-190876167300 / 1000000000000) (-190876154088 / 1000000000000)
      | 4 => orderedInterval (3990258919 / 1000000000000) (3990262895 / 1000000000000)
      | 5 => orderedInterval (-12203808709 / 1000000000000) (-12203808578 / 1000000000000)
      | 6 => orderedInterval (6268070195 / 1000000000000) (6268074832 / 1000000000000)
      | 7 => orderedInterval (-4976126920 / 1000000000000) (-4976126651 / 1000000000000)
      | _ => orderedInterval (10237166629 / 1000000000000) (10237182629 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-13908745388 / 1000000000000) (-13908730411 / 1000000000000)
    | 1 => orderedInterval (168775118 / 1000000000000) (168793092 / 1000000000000)
    | 2 => orderedInterval (47143871791 / 1000000000000) (47143894299 / 1000000000000)
    | 3 => orderedInterval (14991381922 / 1000000000000) (14991411112 / 1000000000000)
    | _ => orderedInterval (-204152271738 / 1000000000000) (-204152231941 / 1000000000000)

theorem compactCertificate385_stateChecks0 :
    compactCertificate385.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (513 / 2)) (orderedInterval (-15940098414 / 1000000000000) (-15940098166 / 1000000000000), orderedInterval (47231341631 / 1000000000000) (47231341879 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (755746956273213 / 4000000000000)) (orderedInterval (54629129459 / 1000000000000) (54629129460 / 1000000000000), orderedInterval (19480300828 / 1000000000000) (19480300829 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 97 12 (244393037857629 / 800000000000)) (orderedInterval (-45630763534 / 1000000000000) (-45630763437 / 1000000000000), orderedInterval (-1248862934 / 1000000000000) (-1248862837 / 1000000000000))) = true
  rfl'

theorem compactCertificate385_stateChecks1 :
    compactCertificate385.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 18 12 (220525076980791 / 4000000000000)) (orderedInterval (-63677304941 / 1000000000000) (-63677281990 / 1000000000000), orderedInterval (87137761980 / 1000000000000) (87137784931 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (592361376188427 / 4000000000000)) (orderedInterval (-61573508066 / 1000000000000) (-61573508065 / 1000000000000), orderedInterval (-22320873886 / 1000000000000) (-22320873884 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 128 12 (1608376367049759 / 4000000000000)) (orderedInterval (27277022568 / 1000000000000) (27277022569 / 1000000000000), orderedInterval (28935458477 / 1000000000000) (28935458478 / 1000000000000))) = true
  rfl'

theorem compactCertificate385_stateChecks2 :
    compactCertificate385.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 94 12 (1184722752377367 / 4000000000000)) (orderedInterval (46193910699 / 1000000000000) (46193911119 / 1000000000000), orderedInterval (-4021327326 / 1000000000000) (-4021326905 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 162 12 (2030042629151091 / 4000000000000)) (orderedInterval (-21213612428 / 1000000000000) (-21213609973 / 1000000000000), orderedInterval (28382487307 / 1000000000000) (28382489763 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 119 12 (1495320212558169 / 4000000000000)) (orderedInterval (-28596508434 / 1000000000000) (-28596508433 / 1000000000000), orderedInterval (-29714155391 / 1000000000000) (-29714155390 / 1000000000000))) = true
  rfl'

theorem compactCertificate385_stateChecks3 :
    compactCertificate385.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 183 12 (2294205744914487 / 4000000000000)) (orderedInterval (18113941464 / 1000000000000) (18113942225 / 1000000000000), orderedInterval (-27977307170 / 1000000000000) (-27977306408 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 105 12 (1324560304402623 / 4000000000000)) (orderedInterval (-38747394898 / 1000000000000) (-38747358105 / 1000000000000), orderedInterval (20580390471 / 1000000000000) (20580427265 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 187 12 (2350455503975307 / 4000000000000)) (orderedInterval (-26211844324 / 1000000000000) (-26211844323 / 1000000000000), orderedInterval (-19885916761 / 1000000000000) (-19885916760 / 1000000000000))) = true
  rfl'

theorem compactCertificate385_stateChecks4 :
    compactCertificate385.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 175 12 (2196100424882583 / 4000000000000)) (orderedInterval (-1074585105 / 1000000000000) (-1074585104 / 1000000000000), orderedInterval (-34034173443 / 1000000000000) (-34034173442 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 125 12 (1567240887674439 / 4000000000000)) (orderedInterval (4175788662 / 1000000000000) (4175788665 / 1000000000000), orderedInterval (-40097481857 / 1000000000000) (-40097481854 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 141 12 (1777084128565281 / 4000000000000)) (orderedInterval (-32835940097 / 1000000000000) (-32835858523 / 1000000000000), orderedInterval (18871901038 / 1000000000000) (18871982612 / 1000000000000))) = true
  rfl'

theorem compactCertificate385_stateChecks5 :
    compactCertificate385.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 118 12 (1481547476063889 / 4000000000000)) (orderedInterval (18553679232 / 1000000000000) (18553679233 / 1000000000000), orderedInterval (37049995771 / 1000000000000) (37049995772 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 104 12 (1308992125929669 / 4000000000000)) (orderedInterval (42585329054 / 1000000000000) (42585329058 / 1000000000000), orderedInterval (11418037788 / 1000000000000) (11418037792 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 151 12 (379396938513231 / 800000000000)) (orderedInterval (-22196962791 / 1000000000000) (-22196962790 / 1000000000000), orderedInterval (-29125826811 / 1000000000000) (-29125826810 / 1000000000000))) = true
  rfl'

theorem compactCertificate385_stateChecks6 :
    compactCertificate385.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (1049431898494557 / 4000000000000)) (orderedInterval (-33609333708 / 1000000000000) (-33609307731 / 1000000000000), orderedInterval (36077159807 / 1000000000000) (36077185785 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (889615042493877 / 4000000000000)) (orderedInterval (-7228304036 / 1000000000000) (-7228304035 / 1000000000000), orderedInterval (-52995155661 / 1000000000000) (-52995155660 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (556679787441831 / 4000000000000)) (orderedInterval (66838127142 / 1000000000000) (66838127508 / 1000000000000), orderedInterval (-10586244125 / 1000000000000) (-10586243759 / 1000000000000))) = true
  rfl'

theorem compactCertificate385_stateChecks7 :
    compactCertificate385.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 24 12 (299384241119577 / 4000000000000)) (orderedInterval (21165817706 / 1000000000000) (21165817707 / 1000000000000), orderedInterval (89624415887 / 1000000000000) (89624415888 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (812886453169731 / 4000000000000)) (orderedInterval (10961810055 / 1000000000000) (10961810116 / 1000000000000), orderedInterval (-54913084705 / 1000000000000) (-54913084644 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 88 12 (1109926956002787 / 4000000000000)) (orderedInterval (46573809953 / 1000000000000) (46573812209 / 1000000000000), orderedInterval (-11271106907 / 1000000000000) (-11271104651 / 1000000000000))) = true
  rfl'

theorem compactCertificate385_stateChecks8 :
    compactCertificate385.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (469320212558169 / 4000000000000)) (orderedInterval (-70268133563 / 1000000000000) (-70268131585 / 1000000000000), orderedInterval (22395537464 / 1000000000000) (22395539442 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 152 12 (1907760608169849 / 4000000000000)) (orderedInterval (7373080108 / 1000000000000) (7373080109 / 1000000000000), orderedInterval (35775485556 / 1000000000000) (35775485557 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 101 12 (1274295672878391 / 4000000000000)) (orderedInterval (-39500056780 / 1000000000000) (-39500021980 / 1000000000000), orderedInterval (20992525850 / 1000000000000) (20992560650 / 1000000000000))) = true
  rfl'

theorem compactCertificate385_states : ∀ j,
    BesselStateValid (compactCertificate385.point j) (compactCertificate385.state j) :=
  compactCertificate385.statesValid_of_checks3 compactCertificate385_stateChecks0
    compactCertificate385_stateChecks1 compactCertificate385_stateChecks2
    compactCertificate385_stateChecks3 compactCertificate385_stateChecks4
    compactCertificate385_stateChecks5 compactCertificate385_stateChecks6
    compactCertificate385_stateChecks7 compactCertificate385_stateChecks8

theorem compactCertificate385_chunkChecks0_0 :
    compactCertificate385.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (513 / 2) 0 (IntervalRat.scale (513 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-15940098414 / 1000000000000) (-15940098166 / 1000000000000), orderedInterval (47231341631 / 1000000000000) (47231341879 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (755746956273213 / 4000000000000) 0 (IntervalRat.scale (513 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (54629129459 / 1000000000000) (54629129460 / 1000000000000), orderedInterval (19480300828 / 1000000000000) (19480300829 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (244393037857629 / 800000000000) 0 (IntervalRat.scale (513 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-45630763534 / 1000000000000) (-45630763437 / 1000000000000), orderedInterval (-1248862934 / 1000000000000) (-1248862837 / 1000000000000)))) (orderedInterval (-8486724723 / 1000000000000) (-8486724600 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (220525076980791 / 4000000000000) 0 (IntervalRat.scale (513 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-63677304941 / 1000000000000) (-63677281990 / 1000000000000), orderedInterval (87137761980 / 1000000000000) (87137784931 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (592361376188427 / 4000000000000) 0 (IntervalRat.scale (513 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-61573508066 / 1000000000000) (-61573508065 / 1000000000000), orderedInterval (-22320873886 / 1000000000000) (-22320873884 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1608376367049759 / 4000000000000) 0 (IntervalRat.scale (513 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (27277022568 / 1000000000000) (27277022569 / 1000000000000), orderedInterval (28935458477 / 1000000000000) (28935458478 / 1000000000000)))) (orderedInterval (-3496416682 / 1000000000000) (-3496416402 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1184722752377367 / 4000000000000) 0 (IntervalRat.scale (513 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (46193910699 / 1000000000000) (46193911119 / 1000000000000), orderedInterval (-4021327326 / 1000000000000) (-4021326905 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2030042629151091 / 4000000000000) 0 (IntervalRat.scale (513 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-21213612428 / 1000000000000) (-21213609973 / 1000000000000), orderedInterval (28382487307 / 1000000000000) (28382489763 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1495320212558169 / 4000000000000) 0 (IntervalRat.scale (513 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-28596508434 / 1000000000000) (-28596508433 / 1000000000000), orderedInterval (-29714155391 / 1000000000000) (-29714155390 / 1000000000000)))) (orderedInterval (-36808588 / 1000000000000) (-36808497 / 1000000000000))) = true
  rfl'

theorem compactCertificate385_chunkChecks0_1 :
    compactCertificate385.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2294205744914487 / 4000000000000) 0 (IntervalRat.scale (513 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (18113941464 / 1000000000000) (18113942225 / 1000000000000), orderedInterval (-27977307170 / 1000000000000) (-27977306408 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1324560304402623 / 4000000000000) 0 (IntervalRat.scale (513 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-38747394898 / 1000000000000) (-38747358105 / 1000000000000), orderedInterval (20580390471 / 1000000000000) (20580427265 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2350455503975307 / 4000000000000) 0 (IntervalRat.scale (513 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-26211844324 / 1000000000000) (-26211844323 / 1000000000000), orderedInterval (-19885916761 / 1000000000000) (-19885916760 / 1000000000000)))) (orderedInterval (-9815660097 / 1000000000000) (-9815657134 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2196100424882583 / 4000000000000) 0 (IntervalRat.scale (513 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-1074585105 / 1000000000000) (-1074585104 / 1000000000000), orderedInterval (-34034173443 / 1000000000000) (-34034173442 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1567240887674439 / 4000000000000) 0 (IntervalRat.scale (513 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (4175788662 / 1000000000000) (4175788665 / 1000000000000), orderedInterval (-40097481857 / 1000000000000) (-40097481854 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1777084128565281 / 4000000000000) 0 (IntervalRat.scale (513 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-32835940097 / 1000000000000) (-32835858523 / 1000000000000), orderedInterval (18871901038 / 1000000000000) (18871982612 / 1000000000000)))) (orderedInterval (580442463 / 1000000000000) (580442907 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1481547476063889 / 4000000000000) 0 (IntervalRat.scale (513 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (18553679232 / 1000000000000) (18553679233 / 1000000000000), orderedInterval (37049995771 / 1000000000000) (37049995772 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1308992125929669 / 4000000000000) 0 (IntervalRat.scale (513 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (42585329054 / 1000000000000) (42585329058 / 1000000000000), orderedInterval (11418037788 / 1000000000000) (11418037792 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (379396938513231 / 800000000000) 0 (IntervalRat.scale (513 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-22196962791 / 1000000000000) (-22196962790 / 1000000000000), orderedInterval (-29125826811 / 1000000000000) (-29125826810 / 1000000000000)))) (orderedInterval (-2791095044 / 1000000000000) (-2791095018 / 1000000000000))) = true
  rfl'

theorem compactCertificate385_chunkChecks0_2 :
    compactCertificate385.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1049431898494557 / 4000000000000) 0 (IntervalRat.scale (513 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-33609333708 / 1000000000000) (-33609307731 / 1000000000000), orderedInterval (36077159807 / 1000000000000) (36077185785 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (889615042493877 / 4000000000000) 0 (IntervalRat.scale (513 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-7228304036 / 1000000000000) (-7228304035 / 1000000000000), orderedInterval (-52995155661 / 1000000000000) (-52995155660 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (556679787441831 / 4000000000000) 0 (IntervalRat.scale (513 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (66838127142 / 1000000000000) (66838127508 / 1000000000000), orderedInterval (-10586244125 / 1000000000000) (-10586243759 / 1000000000000)))) (orderedInterval (7958929287 / 1000000000000) (7958933518 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (299384241119577 / 4000000000000) 0 (IntervalRat.scale (513 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (21165817706 / 1000000000000) (21165817707 / 1000000000000), orderedInterval (89624415887 / 1000000000000) (89624415888 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (812886453169731 / 4000000000000) 0 (IntervalRat.scale (513 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (10961810055 / 1000000000000) (10961810116 / 1000000000000), orderedInterval (-54913084705 / 1000000000000) (-54913084644 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1109926956002787 / 4000000000000) 0 (IntervalRat.scale (513 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (46573809953 / 1000000000000) (46573812209 / 1000000000000), orderedInterval (-11271106907 / 1000000000000) (-11271104651 / 1000000000000)))) (orderedInterval (-4208882729 / 1000000000000) (-4208882523 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (469320212558169 / 4000000000000) 0 (IntervalRat.scale (513 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-70268133563 / 1000000000000) (-70268131585 / 1000000000000), orderedInterval (22395537464 / 1000000000000) (22395539442 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1907760608169849 / 4000000000000) 0 (IntervalRat.scale (513 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (7373080108 / 1000000000000) (7373080109 / 1000000000000), orderedInterval (35775485556 / 1000000000000) (35775485557 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1274295672878391 / 4000000000000) 0 (IntervalRat.scale (513 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-39500056780 / 1000000000000) (-39500021980 / 1000000000000), orderedInterval (20992525850 / 1000000000000) (20992560650 / 1000000000000)))) (orderedInterval (6387470725 / 1000000000000) (6387477338 / 1000000000000))) = true
  rfl'

theorem compactCertificate385_chunkChecks0 :
    compactCertificate385.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate385.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate385_chunkChecks0_0
    compactCertificate385_chunkChecks0_1 compactCertificate385_chunkChecks0_2

theorem compactCertificate385_chunkChecks1_0 :
    compactCertificate385.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (513 / 2) 1 (IntervalRat.scale (513 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-15940098414 / 1000000000000) (-15940098166 / 1000000000000), orderedInterval (47231341631 / 1000000000000) (47231341879 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (755746956273213 / 4000000000000) 1 (IntervalRat.scale (513 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (54629129459 / 1000000000000) (54629129460 / 1000000000000), orderedInterval (19480300828 / 1000000000000) (19480300829 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (244393037857629 / 800000000000) 1 (IntervalRat.scale (513 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-45630763534 / 1000000000000) (-45630763437 / 1000000000000), orderedInterval (-1248862934 / 1000000000000) (-1248862837 / 1000000000000)))) (orderedInterval (18767274152 / 1000000000000) (18767274278 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (220525076980791 / 4000000000000) 1 (IntervalRat.scale (513 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-63677304941 / 1000000000000) (-63677281990 / 1000000000000), orderedInterval (87137761980 / 1000000000000) (87137784931 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (592361376188427 / 4000000000000) 1 (IntervalRat.scale (513 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-61573508066 / 1000000000000) (-61573508065 / 1000000000000), orderedInterval (-22320873886 / 1000000000000) (-22320873884 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1608376367049759 / 4000000000000) 1 (IntervalRat.scale (513 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (27277022568 / 1000000000000) (27277022569 / 1000000000000), orderedInterval (28935458477 / 1000000000000) (28935458478 / 1000000000000)))) (orderedInterval (-3898331711 / 1000000000000) (-3898331621 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1184722752377367 / 4000000000000) 1 (IntervalRat.scale (513 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (46193910699 / 1000000000000) (46193911119 / 1000000000000), orderedInterval (-4021327326 / 1000000000000) (-4021326905 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2030042629151091 / 4000000000000) 1 (IntervalRat.scale (513 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-21213612428 / 1000000000000) (-21213609973 / 1000000000000), orderedInterval (28382487307 / 1000000000000) (28382489763 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1495320212558169 / 4000000000000) 1 (IntervalRat.scale (513 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-28596508434 / 1000000000000) (-28596508433 / 1000000000000), orderedInterval (-29714155391 / 1000000000000) (-29714155390 / 1000000000000)))) (orderedInterval (-2778749864 / 1000000000000) (-2778749689 / 1000000000000))) = true
  rfl'

theorem compactCertificate385_chunkChecks1_1 :
    compactCertificate385.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2294205744914487 / 4000000000000) 1 (IntervalRat.scale (513 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (18113941464 / 1000000000000) (18113942225 / 1000000000000), orderedInterval (-27977307170 / 1000000000000) (-27977306408 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1324560304402623 / 4000000000000) 1 (IntervalRat.scale (513 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-38747394898 / 1000000000000) (-38747358105 / 1000000000000), orderedInterval (20580390471 / 1000000000000) (20580427265 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2350455503975307 / 4000000000000) 1 (IntervalRat.scale (513 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-26211844324 / 1000000000000) (-26211844323 / 1000000000000), orderedInterval (-19885916761 / 1000000000000) (-19885916760 / 1000000000000)))) (orderedInterval (6608439956 / 1000000000000) (6608443990 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2196100424882583 / 4000000000000) 1 (IntervalRat.scale (513 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-1074585105 / 1000000000000) (-1074585104 / 1000000000000), orderedInterval (-34034173443 / 1000000000000) (-34034173442 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1567240887674439 / 4000000000000) 1 (IntervalRat.scale (513 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (4175788662 / 1000000000000) (4175788665 / 1000000000000), orderedInterval (-40097481857 / 1000000000000) (-40097481854 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1777084128565281 / 4000000000000) 1 (IntervalRat.scale (513 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-32835940097 / 1000000000000) (-32835858523 / 1000000000000), orderedInterval (18871901038 / 1000000000000) (18871982612 / 1000000000000)))) (orderedInterval (-4642245273 / 1000000000000) (-4642244507 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1481547476063889 / 4000000000000) 1 (IntervalRat.scale (513 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (18553679232 / 1000000000000) (18553679233 / 1000000000000), orderedInterval (37049995771 / 1000000000000) (37049995772 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1308992125929669 / 4000000000000) 1 (IntervalRat.scale (513 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (42585329054 / 1000000000000) (42585329058 / 1000000000000), orderedInterval (11418037788 / 1000000000000) (11418037792 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (379396938513231 / 800000000000) 1 (IntervalRat.scale (513 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-22196962791 / 1000000000000) (-22196962790 / 1000000000000), orderedInterval (-29125826811 / 1000000000000) (-29125826810 / 1000000000000)))) (orderedInterval (-1594639506 / 1000000000000) (-1594639469 / 1000000000000))) = true
  rfl'

theorem compactCertificate385_chunkChecks1_2 :
    compactCertificate385.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1049431898494557 / 4000000000000) 1 (IntervalRat.scale (513 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-33609333708 / 1000000000000) (-33609307731 / 1000000000000), orderedInterval (36077159807 / 1000000000000) (36077185785 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (889615042493877 / 4000000000000) 1 (IntervalRat.scale (513 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-7228304036 / 1000000000000) (-7228304035 / 1000000000000), orderedInterval (-52995155661 / 1000000000000) (-52995155660 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (556679787441831 / 4000000000000) 1 (IntervalRat.scale (513 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (66838127142 / 1000000000000) (66838127508 / 1000000000000), orderedInterval (-10586244125 / 1000000000000) (-10586243759 / 1000000000000)))) (orderedInterval (-3486401155 / 1000000000000) (-3486396840 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (299384241119577 / 4000000000000) 1 (IntervalRat.scale (513 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (21165817706 / 1000000000000) (21165817707 / 1000000000000), orderedInterval (89624415887 / 1000000000000) (89624415888 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (812886453169731 / 4000000000000) 1 (IntervalRat.scale (513 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (10961810055 / 1000000000000) (10961810116 / 1000000000000), orderedInterval (-54913084705 / 1000000000000) (-54913084644 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1109926956002787 / 4000000000000) 1 (IntervalRat.scale (513 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (46573809953 / 1000000000000) (46573812209 / 1000000000000), orderedInterval (-11271106907 / 1000000000000) (-11271104651 / 1000000000000)))) (orderedInterval (1438596535 / 1000000000000) (1438596751 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (469320212558169 / 4000000000000) 1 (IntervalRat.scale (513 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-70268133563 / 1000000000000) (-70268131585 / 1000000000000), orderedInterval (22395537464 / 1000000000000) (22395539442 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1907760608169849 / 4000000000000) 1 (IntervalRat.scale (513 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (7373080108 / 1000000000000) (7373080109 / 1000000000000), orderedInterval (35775485556 / 1000000000000) (35775485557 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1274295672878391 / 4000000000000) 1 (IntervalRat.scale (513 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-39500056780 / 1000000000000) (-39500021980 / 1000000000000), orderedInterval (20992525850 / 1000000000000) (20992560650 / 1000000000000)))) (orderedInterval (-10245168016 / 1000000000000) (-10245159801 / 1000000000000))) = true
  rfl'

theorem compactCertificate385_chunkChecks1 :
    compactCertificate385.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate385.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate385_chunkChecks1_0
    compactCertificate385_chunkChecks1_1 compactCertificate385_chunkChecks1_2

theorem compactCertificate385_chunkChecks2_0 :
    compactCertificate385.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (513 / 2) 2 (IntervalRat.scale (513 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-15940098414 / 1000000000000) (-15940098166 / 1000000000000), orderedInterval (47231341631 / 1000000000000) (47231341879 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (755746956273213 / 4000000000000) 2 (IntervalRat.scale (513 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (54629129459 / 1000000000000) (54629129460 / 1000000000000), orderedInterval (19480300828 / 1000000000000) (19480300829 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (244393037857629 / 800000000000) 2 (IntervalRat.scale (513 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-45630763534 / 1000000000000) (-45630763437 / 1000000000000), orderedInterval (-1248862934 / 1000000000000) (-1248862837 / 1000000000000)))) (orderedInterval (9766952369 / 1000000000000) (9766952499 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (220525076980791 / 4000000000000) 2 (IntervalRat.scale (513 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-63677304941 / 1000000000000) (-63677281990 / 1000000000000), orderedInterval (87137761980 / 1000000000000) (87137784931 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (592361376188427 / 4000000000000) 2 (IntervalRat.scale (513 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-61573508066 / 1000000000000) (-61573508065 / 1000000000000), orderedInterval (-22320873886 / 1000000000000) (-22320873884 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1608376367049759 / 4000000000000) 2 (IntervalRat.scale (513 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (27277022568 / 1000000000000) (27277022569 / 1000000000000), orderedInterval (28935458477 / 1000000000000) (28935458478 / 1000000000000)))) (orderedInterval (5497898340 / 1000000000000) (5497898401 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1184722752377367 / 4000000000000) 2 (IntervalRat.scale (513 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (46193910699 / 1000000000000) (46193911119 / 1000000000000), orderedInterval (-4021327326 / 1000000000000) (-4021326905 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2030042629151091 / 4000000000000) 2 (IntervalRat.scale (513 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-21213612428 / 1000000000000) (-21213609973 / 1000000000000), orderedInterval (28382487307 / 1000000000000) (28382489763 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1495320212558169 / 4000000000000) 2 (IntervalRat.scale (513 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-28596508434 / 1000000000000) (-28596508433 / 1000000000000), orderedInterval (-29714155391 / 1000000000000) (-29714155390 / 1000000000000)))) (orderedInterval (-1082699243 / 1000000000000) (-1082698901 / 1000000000000))) = true
  rfl'

theorem compactCertificate385_chunkChecks2_1 :
    compactCertificate385.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2294205744914487 / 4000000000000) 2 (IntervalRat.scale (513 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (18113941464 / 1000000000000) (18113942225 / 1000000000000), orderedInterval (-27977307170 / 1000000000000) (-27977306408 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1324560304402623 / 4000000000000) 2 (IntervalRat.scale (513 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-38747394898 / 1000000000000) (-38747358105 / 1000000000000), orderedInterval (20580390471 / 1000000000000) (20580427265 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2350455503975307 / 4000000000000) 2 (IntervalRat.scale (513 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-26211844324 / 1000000000000) (-26211844323 / 1000000000000), orderedInterval (-19885916761 / 1000000000000) (-19885916760 / 1000000000000)))) (orderedInterval (40407775702 / 1000000000000) (40407781389 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2196100424882583 / 4000000000000) 2 (IntervalRat.scale (513 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-1074585105 / 1000000000000) (-1074585104 / 1000000000000), orderedInterval (-34034173443 / 1000000000000) (-34034173442 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1567240887674439 / 4000000000000) 2 (IntervalRat.scale (513 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (4175788662 / 1000000000000) (4175788665 / 1000000000000), orderedInterval (-40097481857 / 1000000000000) (-40097481854 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1777084128565281 / 4000000000000) 2 (IntervalRat.scale (513 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-32835940097 / 1000000000000) (-32835858523 / 1000000000000), orderedInterval (18871901038 / 1000000000000) (18871982612 / 1000000000000)))) (orderedInterval (-1490661438 / 1000000000000) (-1490660113 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1481547476063889 / 4000000000000) 2 (IntervalRat.scale (513 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (18553679232 / 1000000000000) (18553679233 / 1000000000000), orderedInterval (37049995771 / 1000000000000) (37049995772 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1308992125929669 / 4000000000000) 2 (IntervalRat.scale (513 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (42585329054 / 1000000000000) (42585329058 / 1000000000000), orderedInterval (11418037788 / 1000000000000) (11418037792 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (379396938513231 / 800000000000) 2 (IntervalRat.scale (513 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-22196962791 / 1000000000000) (-22196962790 / 1000000000000), orderedInterval (-29125826811 / 1000000000000) (-29125826810 / 1000000000000)))) (orderedInterval (5469072585 / 1000000000000) (5469072639 / 1000000000000))) = true
  rfl'

theorem compactCertificate385_chunkChecks2_2 :
    compactCertificate385.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1049431898494557 / 4000000000000) 2 (IntervalRat.scale (513 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-33609333708 / 1000000000000) (-33609307731 / 1000000000000), orderedInterval (36077159807 / 1000000000000) (36077185785 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (889615042493877 / 4000000000000) 2 (IntervalRat.scale (513 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-7228304036 / 1000000000000) (-7228304035 / 1000000000000), orderedInterval (-52995155661 / 1000000000000) (-52995155660 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (556679787441831 / 4000000000000) 2 (IntervalRat.scale (513 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (66838127142 / 1000000000000) (66838127508 / 1000000000000), orderedInterval (-10586244125 / 1000000000000) (-10586243759 / 1000000000000)))) (orderedInterval (-6556693279 / 1000000000000) (-6556688857 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (299384241119577 / 4000000000000) 2 (IntervalRat.scale (513 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (21165817706 / 1000000000000) (21165817707 / 1000000000000), orderedInterval (89624415887 / 1000000000000) (89624415888 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (812886453169731 / 4000000000000) 2 (IntervalRat.scale (513 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (10961810055 / 1000000000000) (10961810116 / 1000000000000), orderedInterval (-54913084705 / 1000000000000) (-54913084644 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1109926956002787 / 4000000000000) 2 (IntervalRat.scale (513 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (46573809953 / 1000000000000) (46573812209 / 1000000000000), orderedInterval (-11271106907 / 1000000000000) (-11271104651 / 1000000000000)))) (orderedInterval (4360972455 / 1000000000000) (4360972687 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (469320212558169 / 4000000000000) 2 (IntervalRat.scale (513 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-70268133563 / 1000000000000) (-70268131585 / 1000000000000), orderedInterval (22395537464 / 1000000000000) (22395539442 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1907760608169849 / 4000000000000) 2 (IntervalRat.scale (513 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (7373080108 / 1000000000000) (7373080109 / 1000000000000), orderedInterval (35775485556 / 1000000000000) (35775485557 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1274295672878391 / 4000000000000) 2 (IntervalRat.scale (513 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-39500056780 / 1000000000000) (-39500021980 / 1000000000000), orderedInterval (20992525850 / 1000000000000) (20992560650 / 1000000000000)))) (orderedInterval (-9228745700 / 1000000000000) (-9228735445 / 1000000000000))) = true
  rfl'

theorem compactCertificate385_chunkChecks2 :
    compactCertificate385.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate385.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate385_chunkChecks2_0
    compactCertificate385_chunkChecks2_1 compactCertificate385_chunkChecks2_2

theorem compactCertificate385_chunkChecks3_0 :
    compactCertificate385.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (513 / 2) 3 (IntervalRat.scale (513 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-15940098414 / 1000000000000) (-15940098166 / 1000000000000), orderedInterval (47231341631 / 1000000000000) (47231341879 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (755746956273213 / 4000000000000) 3 (IntervalRat.scale (513 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (54629129459 / 1000000000000) (54629129460 / 1000000000000), orderedInterval (19480300828 / 1000000000000) (19480300829 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (244393037857629 / 800000000000) 3 (IntervalRat.scale (513 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-45630763534 / 1000000000000) (-45630763437 / 1000000000000), orderedInterval (-1248862934 / 1000000000000) (-1248862837 / 1000000000000)))) (orderedInterval (-18707380466 / 1000000000000) (-18707380330 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (220525076980791 / 4000000000000) 3 (IntervalRat.scale (513 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-63677304941 / 1000000000000) (-63677281990 / 1000000000000), orderedInterval (87137761980 / 1000000000000) (87137784931 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (592361376188427 / 4000000000000) 3 (IntervalRat.scale (513 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-61573508066 / 1000000000000) (-61573508065 / 1000000000000), orderedInterval (-22320873886 / 1000000000000) (-22320873884 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1608376367049759 / 4000000000000) 3 (IntervalRat.scale (513 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (27277022568 / 1000000000000) (27277022569 / 1000000000000), orderedInterval (28935458477 / 1000000000000) (28935458478 / 1000000000000)))) (orderedInterval (8068976171 / 1000000000000) (8068976247 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1184722752377367 / 4000000000000) 3 (IntervalRat.scale (513 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (46193910699 / 1000000000000) (46193911119 / 1000000000000), orderedInterval (-4021327326 / 1000000000000) (-4021326905 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2030042629151091 / 4000000000000) 3 (IntervalRat.scale (513 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-21213612428 / 1000000000000) (-21213609973 / 1000000000000), orderedInterval (28382487307 / 1000000000000) (28382489763 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1495320212558169 / 4000000000000) 3 (IntervalRat.scale (513 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-28596508434 / 1000000000000) (-28596508433 / 1000000000000), orderedInterval (-29714155391 / 1000000000000) (-29714155390 / 1000000000000)))) (orderedInterval (9008322700 / 1000000000000) (9008323369 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate385_chunkChecks3_1 :
    compactCertificate385.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2294205744914487 / 4000000000000) 3 (IntervalRat.scale (513 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (18113941464 / 1000000000000) (18113942225 / 1000000000000), orderedInterval (-27977307170 / 1000000000000) (-27977306408 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1324560304402623 / 4000000000000) 3 (IntervalRat.scale (513 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-38747394898 / 1000000000000) (-38747358105 / 1000000000000), orderedInterval (20580390471 / 1000000000000) (20580427265 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2350455503975307 / 4000000000000) 3 (IntervalRat.scale (513 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-26211844324 / 1000000000000) (-26211844323 / 1000000000000), orderedInterval (-19885916761 / 1000000000000) (-19885916760 / 1000000000000)))) (orderedInterval (-25030493449 / 1000000000000) (-25030485058 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2196100424882583 / 4000000000000) 3 (IntervalRat.scale (513 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-1074585105 / 1000000000000) (-1074585104 / 1000000000000), orderedInterval (-34034173443 / 1000000000000) (-34034173442 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1567240887674439 / 4000000000000) 3 (IntervalRat.scale (513 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (4175788662 / 1000000000000) (4175788665 / 1000000000000), orderedInterval (-40097481857 / 1000000000000) (-40097481854 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1777084128565281 / 4000000000000) 3 (IntervalRat.scale (513 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-32835940097 / 1000000000000) (-32835858523 / 1000000000000), orderedInterval (18871901038 / 1000000000000) (18871982612 / 1000000000000)))) (orderedInterval (7991243812 / 1000000000000) (7991246102 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1481547476063889 / 4000000000000) 3 (IntervalRat.scale (513 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (18553679232 / 1000000000000) (18553679233 / 1000000000000), orderedInterval (37049995771 / 1000000000000) (37049995772 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1308992125929669 / 4000000000000) 3 (IntervalRat.scale (513 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (42585329054 / 1000000000000) (42585329058 / 1000000000000), orderedInterval (11418037788 / 1000000000000) (11418037792 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (379396938513231 / 800000000000) 3 (IntervalRat.scale (513 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-22196962791 / 1000000000000) (-22196962790 / 1000000000000), orderedInterval (-29125826811 / 1000000000000) (-29125826810 / 1000000000000)))) (orderedInterval (4760780872 / 1000000000000) (4760780955 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate385_chunkChecks3_2 :
    compactCertificate385.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1049431898494557 / 4000000000000) 3 (IntervalRat.scale (513 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-33609333708 / 1000000000000) (-33609307731 / 1000000000000), orderedInterval (36077159807 / 1000000000000) (36077185785 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (889615042493877 / 4000000000000) 3 (IntervalRat.scale (513 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-7228304036 / 1000000000000) (-7228304035 / 1000000000000), orderedInterval (-52995155661 / 1000000000000) (-52995155660 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (556679787441831 / 4000000000000) 3 (IntervalRat.scale (513 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (66838127142 / 1000000000000) (66838127508 / 1000000000000), orderedInterval (-10586244125 / 1000000000000) (-10586243759 / 1000000000000)))) (orderedInterval (4298025001 / 1000000000000) (4298029520 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (299384241119577 / 4000000000000) 3 (IntervalRat.scale (513 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (21165817706 / 1000000000000) (21165817707 / 1000000000000), orderedInterval (89624415887 / 1000000000000) (89624415888 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (812886453169731 / 4000000000000) 3 (IntervalRat.scale (513 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (10961810055 / 1000000000000) (10961810116 / 1000000000000), orderedInterval (-54913084705 / 1000000000000) (-54913084644 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1109926956002787 / 4000000000000) 3 (IntervalRat.scale (513 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (46573809953 / 1000000000000) (46573812209 / 1000000000000), orderedInterval (-11271106907 / 1000000000000) (-11271104651 / 1000000000000)))) (orderedInterval (-1689039135 / 1000000000000) (-1689038886 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (469320212558169 / 4000000000000) 3 (IntervalRat.scale (513 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-70268133563 / 1000000000000) (-70268131585 / 1000000000000), orderedInterval (22395537464 / 1000000000000) (22395539442 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1907760608169849 / 4000000000000) 3 (IntervalRat.scale (513 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (7373080108 / 1000000000000) (7373080109 / 1000000000000), orderedInterval (35775485556 / 1000000000000) (35775485557 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1274295672878391 / 4000000000000) 3 (IntervalRat.scale (513 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-39500056780 / 1000000000000) (-39500021980 / 1000000000000), orderedInterval (20992525850 / 1000000000000) (20992560650 / 1000000000000)))) (orderedInterval (26290946416 / 1000000000000) (26290959193 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate385_chunkChecks3 :
    compactCertificate385.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate385.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate385_chunkChecks3_0
    compactCertificate385_chunkChecks3_1 compactCertificate385_chunkChecks3_2

theorem compactCertificate385_chunkChecks4_0 :
    compactCertificate385.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (513 / 2) 4 (IntervalRat.scale (513 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-15940098414 / 1000000000000) (-15940098166 / 1000000000000), orderedInterval (47231341631 / 1000000000000) (47231341879 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (755746956273213 / 4000000000000) 4 (IntervalRat.scale (513 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (54629129459 / 1000000000000) (54629129460 / 1000000000000), orderedInterval (19480300828 / 1000000000000) (19480300829 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (244393037857629 / 800000000000) 4 (IntervalRat.scale (513 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-45630763534 / 1000000000000) (-45630763437 / 1000000000000), orderedInterval (-1248862934 / 1000000000000) (-1248862837 / 1000000000000)))) (orderedInterval (-11409914675 / 1000000000000) (-11409914532 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (220525076980791 / 4000000000000) 4 (IntervalRat.scale (513 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-63677304941 / 1000000000000) (-63677281990 / 1000000000000), orderedInterval (87137761980 / 1000000000000) (87137784931 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (592361376188427 / 4000000000000) 4 (IntervalRat.scale (513 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-61573508066 / 1000000000000) (-61573508065 / 1000000000000), orderedInterval (-22320873886 / 1000000000000) (-22320873884 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1608376367049759 / 4000000000000) 4 (IntervalRat.scale (513 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (27277022568 / 1000000000000) (27277022569 / 1000000000000), orderedInterval (28935458477 / 1000000000000) (28935458478 / 1000000000000)))) (orderedInterval (-12021359987 / 1000000000000) (-12021359874 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1184722752377367 / 4000000000000) 4 (IntervalRat.scale (513 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (46193910699 / 1000000000000) (46193911119 / 1000000000000), orderedInterval (-4021327326 / 1000000000000) (-4021326905 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2030042629151091 / 4000000000000) 4 (IntervalRat.scale (513 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-21213612428 / 1000000000000) (-21213609973 / 1000000000000), orderedInterval (28382487307 / 1000000000000) (28382489763 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1495320212558169 / 4000000000000) 4 (IntervalRat.scale (513 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-28596508434 / 1000000000000) (-28596508433 / 1000000000000), orderedInterval (-29714155391 / 1000000000000) (-29714155390 / 1000000000000)))) (orderedInterval (6839610110 / 1000000000000) (6839611426 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate385_chunkChecks4_1 :
    compactCertificate385.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2294205744914487 / 4000000000000) 4 (IntervalRat.scale (513 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (18113941464 / 1000000000000) (18113942225 / 1000000000000), orderedInterval (-27977307170 / 1000000000000) (-27977306408 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1324560304402623 / 4000000000000) 4 (IntervalRat.scale (513 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-38747394898 / 1000000000000) (-38747358105 / 1000000000000), orderedInterval (20580390471 / 1000000000000) (20580427265 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2350455503975307 / 4000000000000) 4 (IntervalRat.scale (513 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-26211844324 / 1000000000000) (-26211844323 / 1000000000000), orderedInterval (-19885916761 / 1000000000000) (-19885916760 / 1000000000000)))) (orderedInterval (-190876167300 / 1000000000000) (-190876154088 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2196100424882583 / 4000000000000) 4 (IntervalRat.scale (513 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-1074585105 / 1000000000000) (-1074585104 / 1000000000000), orderedInterval (-34034173443 / 1000000000000) (-34034173442 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1567240887674439 / 4000000000000) 4 (IntervalRat.scale (513 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (4175788662 / 1000000000000) (4175788665 / 1000000000000), orderedInterval (-40097481857 / 1000000000000) (-40097481854 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1777084128565281 / 4000000000000) 4 (IntervalRat.scale (513 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-32835940097 / 1000000000000) (-32835858523 / 1000000000000), orderedInterval (18871901038 / 1000000000000) (18871982612 / 1000000000000)))) (orderedInterval (3990258919 / 1000000000000) (3990262895 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1481547476063889 / 4000000000000) 4 (IntervalRat.scale (513 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (18553679232 / 1000000000000) (18553679233 / 1000000000000), orderedInterval (37049995771 / 1000000000000) (37049995772 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1308992125929669 / 4000000000000) 4 (IntervalRat.scale (513 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (42585329054 / 1000000000000) (42585329058 / 1000000000000), orderedInterval (11418037788 / 1000000000000) (11418037792 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (379396938513231 / 800000000000) 4 (IntervalRat.scale (513 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-22196962791 / 1000000000000) (-22196962790 / 1000000000000), orderedInterval (-29125826811 / 1000000000000) (-29125826810 / 1000000000000)))) (orderedInterval (-12203808709 / 1000000000000) (-12203808578 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate385_chunkChecks4_2 :
    compactCertificate385.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1049431898494557 / 4000000000000) 4 (IntervalRat.scale (513 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-33609333708 / 1000000000000) (-33609307731 / 1000000000000), orderedInterval (36077159807 / 1000000000000) (36077185785 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (889615042493877 / 4000000000000) 4 (IntervalRat.scale (513 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-7228304036 / 1000000000000) (-7228304035 / 1000000000000), orderedInterval (-52995155661 / 1000000000000) (-52995155660 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (556679787441831 / 4000000000000) 4 (IntervalRat.scale (513 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (66838127142 / 1000000000000) (66838127508 / 1000000000000), orderedInterval (-10586244125 / 1000000000000) (-10586243759 / 1000000000000)))) (orderedInterval (6268070195 / 1000000000000) (6268074832 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (299384241119577 / 4000000000000) 4 (IntervalRat.scale (513 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (21165817706 / 1000000000000) (21165817707 / 1000000000000), orderedInterval (89624415887 / 1000000000000) (89624415888 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (812886453169731 / 4000000000000) 4 (IntervalRat.scale (513 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (10961810055 / 1000000000000) (10961810116 / 1000000000000), orderedInterval (-54913084705 / 1000000000000) (-54913084644 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1109926956002787 / 4000000000000) 4 (IntervalRat.scale (513 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (46573809953 / 1000000000000) (46573812209 / 1000000000000), orderedInterval (-11271106907 / 1000000000000) (-11271104651 / 1000000000000)))) (orderedInterval (-4976126920 / 1000000000000) (-4976126651 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (469320212558169 / 4000000000000) 4 (IntervalRat.scale (513 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-70268133563 / 1000000000000) (-70268131585 / 1000000000000), orderedInterval (22395537464 / 1000000000000) (22395539442 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1907760608169849 / 4000000000000) 4 (IntervalRat.scale (513 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (7373080108 / 1000000000000) (7373080109 / 1000000000000), orderedInterval (35775485556 / 1000000000000) (35775485557 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1274295672878391 / 4000000000000) 4 (IntervalRat.scale (513 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-39500056780 / 1000000000000) (-39500021980 / 1000000000000), orderedInterval (20992525850 / 1000000000000) (20992560650 / 1000000000000)))) (orderedInterval (10237166629 / 1000000000000) (10237182629 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate385_chunkChecks4 :
    compactCertificate385.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate385.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate385_chunkChecks4_0
    compactCertificate385_chunkChecks4_1 compactCertificate385_chunkChecks4_2

theorem compactCertificate385_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate385.chunkCheck r b = true :=
  compactCertificate385.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate385_chunkChecks0
    · exact compactCertificate385_chunkChecks1
    · exact compactCertificate385_chunkChecks2
    · exact compactCertificate385_chunkChecks3
    · exact compactCertificate385_chunkChecks4)

theorem compactCertificate385_coefficient0 :
    compactCertificate385.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate385_coefficient1 :
    compactCertificate385.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate385_coefficient2 :
    compactCertificate385.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate385_coefficient3 :
    compactCertificate385.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate385_coefficient4 :
    compactCertificate385.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate385_coefficients : ∀ r : Fin 5,
    compactCertificate385.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate385_coefficient0
  · exact compactCertificate385_coefficient1
  · exact compactCertificate385_coefficient2
  · exact compactCertificate385_coefficient3
  · exact compactCertificate385_coefficient4

theorem compactCertificate385_lower : (1 : ℚ) ≤ compactCertificate385.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate385, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate385_proves {t : ℝ} (ht : t ∈ compactCertificate385.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate385.proves compactCertificate385_states compactCertificate385_chunks
    compactCertificate385_coefficients compactCertificate385_lower ht

end Erdos232
