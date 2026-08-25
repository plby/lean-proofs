/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate391 : CompactCertificate where
  left := 262
  right := 263
  center := 525 / 2
  grid := fun i =>
    match i.val with
    | 0 => 84
    | 1 => 62
    | 2 => 100
    | 3 => 18
    | 4 => 48
    | 5 => 131
    | 6 => 97
    | 7 => 165
    | 8 => 122
    | 9 => 187
    | 10 => 108
    | 11 => 192
    | 12 => 179
    | 13 => 128
    | 14 => 145
    | 15 => 121
    | 16 => 107
    | 17 => 155
    | 18 => 86
    | 19 => 72
    | 20 => 45
    | 21 => 24
    | 22 => 66
    | 23 => 90
    | 24 => 38
    | 25 => 155
    | _ => 104
  point := fun i =>
    match i.val with
    | 0 => 525 / 2
    | 1 => 30937009905921 / 160000000000
    | 2 => 10004393362593 / 32000000000
    | 3 => 9027342332547 / 160000000000
    | 4 => 24248711305959 / 160000000000
    | 5 => 65839968241803 / 160000000000
    | 6 => 48497422611939 / 160000000000
    | 7 => 83101160257647 / 160000000000
    | 8 => 61211938525773 / 160000000000
    | 9 => 93914855054979 / 160000000000
    | 10 => 54221766846891 / 160000000000
    | 11 => 96217476770919 / 160000000000
    | 12 => 89898847802211 / 160000000000
    | 13 => 64156059729363 / 160000000000
    | 14 => 72746133917877 / 160000000000
    | 15 => 60648142295013 / 160000000000
    | 16 => 53584472991273 / 160000000000
    | 17 => 15530868828027 / 32000000000
    | 18 => 42959200523169 / 160000000000
    | 19 => 36416990043609 / 160000000000
    | 20 => 22788061474227 / 160000000000
    | 21 => 12255495250509 / 160000000000
    | 22 => 33276053638527 / 160000000000
    | 23 => 45435606386079 / 160000000000
    | 24 => 19211938525773 / 160000000000
    | 25 => 78095463492333 / 160000000000
    | _ => 52164150351747 / 160000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-28165700543 / 1000000000000) (-28165694062 / 1000000000000), orderedInterval (40450590727 / 1000000000000) (40450597207 / 1000000000000))
    | 1 => (orderedInterval (-34160223689 / 1000000000000) (-34160211386 / 1000000000000), orderedInterval (46192040261 / 1000000000000) (46192052564 / 1000000000000))
    | 2 => (orderedInterval (-30326441606 / 1000000000000) (-30326423659 / 1000000000000), orderedInterval (33464002609 / 1000000000000) (33464020557 / 1000000000000))
    | 3 => (orderedInterval (64739779592 / 1000000000000) (64739779593 / 1000000000000), orderedInterval (83642000138 / 1000000000000) (83642000139 / 1000000000000))
    | 4 => (orderedInterval (64786054267 / 1000000000000) (64786054298 / 1000000000000), orderedInterval (1615322549 / 1000000000000) (1615322581 / 1000000000000))
    | 5 => (orderedInterval (-26412777803 / 1000000000000) (-26412777802 / 1000000000000), orderedInterval (-29113012040 / 1000000000000) (-29113012039 / 1000000000000))
    | 6 => (orderedInterval (34144890264 / 1000000000000) (34144938809 / 1000000000000), orderedInterval (-30624713819 / 1000000000000) (-30624665274 / 1000000000000))
    | 7 => (orderedInterval (-34057623499 / 1000000000000) (-34057615363 / 1000000000000), orderedInterval (8144685506 / 1000000000000) (8144693643 / 1000000000000))
    | 8 => (orderedInterval (3478786905 / 1000000000000) (3478786906 / 1000000000000), orderedInterval (40639521282 / 1000000000000) (40639521283 / 1000000000000))
    | 9 => (orderedInterval (-8949323336 / 1000000000000) (-8949323335 / 1000000000000), orderedInterval (-31686232362 / 1000000000000) (-31686232361 / 1000000000000))
    | 10 => (orderedInterval (16038963830 / 1000000000000) (16038963831 / 1000000000000), orderedInterval (40241942082 / 1000000000000) (40241942083 / 1000000000000))
    | 11 => (orderedInterval (-28082319297 / 1000000000000) (-28082244552 / 1000000000000), orderedInterval (16455594651 / 1000000000000) (16455669396 / 1000000000000))
    | 12 => (orderedInterval (-10200802972 / 1000000000000) (-10200802971 / 1000000000000), orderedInterval (-32068732669 / 1000000000000) (-32068732668 / 1000000000000))
    | 13 => (orderedInterval (-14163306709 / 1000000000000) (-14163306555 / 1000000000000), orderedInterval (37261179213 / 1000000000000) (37261179367 / 1000000000000))
    | 14 => (orderedInterval (3082637435 / 1000000000000) (3082637437 / 1000000000000), orderedInterval (-37295460905 / 1000000000000) (-37295460903 / 1000000000000))
    | 15 => (orderedInterval (11983777614 / 1000000000000) (11983777685 / 1000000000000), orderedInterval (-39206371779 / 1000000000000) (-39206371709 / 1000000000000))
    | 16 => (orderedInterval (19450848730 / 1000000000000) (19450849574 / 1000000000000), orderedInterval (-39049213277 / 1000000000000) (-39049212433 / 1000000000000))
    | 17 => (orderedInterval (26531263965 / 1000000000000) (26531281513 / 1000000000000), orderedInterval (-24680758711 / 1000000000000) (-24680741163 / 1000000000000))
    | 18 => (orderedInterval (-38053030167 / 1000000000000) (-38052938373 / 1000000000000), orderedInterval (30452337209 / 1000000000000) (30452429002 / 1000000000000))
    | 19 => (orderedInterval (42871599724 / 1000000000000) (42871678005 / 1000000000000), orderedInterval (-31062643617 / 1000000000000) (-31062565335 / 1000000000000))
    | 20 => (orderedInterval (-64480013612 / 1000000000000) (-64480012119 / 1000000000000), orderedInterval (17894182092 / 1000000000000) (17894183585 / 1000000000000))
    | 21 => (orderedInterval (83551727996 / 1000000000000) (83551733089 / 1000000000000), orderedInterval (-37018564757 / 1000000000000) (-37018559664 / 1000000000000))
    | 22 => (orderedInterval (54656589255 / 1000000000000) (54656589262 / 1000000000000), orderedInterval (8452525545 / 1000000000000) (8452525552 / 1000000000000))
    | 23 => (orderedInterval (42770103132 / 1000000000000) (42770122838 / 1000000000000), orderedInterval (-20386664905 / 1000000000000) (-20386645199 / 1000000000000))
    | 24 => (orderedInterval (72503375484 / 1000000000000) (72503375493 / 1000000000000), orderedInterval (6412515967 / 1000000000000) (6412515976 / 1000000000000))
    | 25 => (orderedInterval (-33747032657 / 1000000000000) (-33747007946 / 1000000000000), orderedInterval (12896458054 / 1000000000000) (12896482765 / 1000000000000))
    | _ => (orderedInterval (3765562391 / 1000000000000) (3765562392 / 1000000000000), orderedInterval (44022498004 / 1000000000000) (44022498005 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-13261794888 / 1000000000000) (-13261791132 / 1000000000000)
      | 1 => orderedInterval (3540746125 / 1000000000000) (3540746159 / 1000000000000)
      | 2 => orderedInterval (1134548530 / 1000000000000) (1134548797 / 1000000000000)
      | 3 => orderedInterval (-1213525264 / 1000000000000) (-1213514534 / 1000000000000)
      | 4 => orderedInterval (-1170766838 / 1000000000000) (-1170766792 / 1000000000000)
      | 5 => orderedInterval (-295417634 / 1000000000000) (-295417109 / 1000000000000)
      | 6 => orderedInterval (1558677803 / 1000000000000) (1558697025 / 1000000000000)
      | 7 => orderedInterval (-6060632925 / 1000000000000) (-6060631289 / 1000000000000)
      | _ => orderedInterval (2477621113 / 1000000000000) (2477623198 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (18689015755 / 1000000000000) (18689019684 / 1000000000000)
      | 1 => orderedInterval (3083400832 / 1000000000000) (3083400869 / 1000000000000)
      | 2 => orderedInterval (934397800 / 1000000000000) (934398323 / 1000000000000)
      | 3 => orderedInterval (21797863009 / 1000000000000) (21797887567 / 1000000000000)
      | 4 => orderedInterval (6948363387 / 1000000000000) (6948363460 / 1000000000000)
      | 5 => orderedInterval (1028885916 / 1000000000000) (1028886846 / 1000000000000)
      | 6 => orderedInterval (-3139806393 / 1000000000000) (-3139787451 / 1000000000000)
      | 7 => orderedInterval (1737743578 / 1000000000000) (1737745269 / 1000000000000)
      | _ => orderedInterval (-12193012589 / 1000000000000) (-12193008746 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (13789713541 / 1000000000000) (13789717705 / 1000000000000)
      | 1 => orderedInterval (-5382031039 / 1000000000000) (-5382030989 / 1000000000000)
      | 2 => orderedInterval (-4294593817 / 1000000000000) (-4294592786 / 1000000000000)
      | 3 => orderedInterval (10936495967 / 1000000000000) (10936552288 / 1000000000000)
      | 4 => orderedInterval (2301702000 / 1000000000000) (2301702119 / 1000000000000)
      | 5 => orderedInterval (-802838152 / 1000000000000) (-802836478 / 1000000000000)
      | 6 => orderedInterval (-3911257185 / 1000000000000) (-3911238354 / 1000000000000)
      | 7 => orderedInterval (4739147957 / 1000000000000) (4739149767 / 1000000000000)
      | _ => orderedInterval (-8452934897 / 1000000000000) (-8452927777 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-19574983246 / 1000000000000) (-19574978809 / 1000000000000)
      | 1 => orderedInterval (-7954657324 / 1000000000000) (-7954657248 / 1000000000000)
      | 2 => orderedInterval (-1078272654 / 1000000000000) (-1078270623 / 1000000000000)
      | 3 => orderedInterval (-97530076135 / 1000000000000) (-97529947158 / 1000000000000)
      | 4 => orderedInterval (-19225382496 / 1000000000000) (-19225382301 / 1000000000000)
      | 5 => orderedInterval (719659897 / 1000000000000) (719662929 / 1000000000000)
      | 6 => orderedInterval (3986094536 / 1000000000000) (3986113265 / 1000000000000)
      | 7 => orderedInterval (-1917688519 / 1000000000000) (-1917686568 / 1000000000000)
      | _ => orderedInterval (22602010636 / 1000000000000) (22602023827 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-14688943982 / 1000000000000) (-14688939194 / 1000000000000)
      | 1 => orderedInterval (11661038540 / 1000000000000) (11661038656 / 1000000000000)
      | 2 => orderedInterval (16487121065 / 1000000000000) (16487125080 / 1000000000000)
      | 3 => orderedInterval (-66156495900 / 1000000000000) (-66156200013 / 1000000000000)
      | 4 => orderedInterval (-3420260960 / 1000000000000) (-3420260632 / 1000000000000)
      | 5 => orderedInterval (5585395611 / 1000000000000) (5585401148 / 1000000000000)
      | 6 => orderedInterval (5075655123 / 1000000000000) (5075673893 / 1000000000000)
      | 7 => orderedInterval (-4974388974 / 1000000000000) (-4974386859 / 1000000000000)
      | _ => orderedInterval (31003511229 / 1000000000000) (31003535747 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-13290543978 / 1000000000000) (-13290505677 / 1000000000000)
    | 1 => orderedInterval (38886851295 / 1000000000000) (38886905821 / 1000000000000)
    | 2 => orderedInterval (8923404375 / 1000000000000) (8923495495 / 1000000000000)
    | 3 => orderedInterval (-119973295305 / 1000000000000) (-119973122686 / 1000000000000)
    | _ => orderedInterval (-19427368248 / 1000000000000) (-19427012174 / 1000000000000)

theorem compactCertificate391_stateChecks0 :
    compactCertificate391.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (525 / 2)) (orderedInterval (-28165700543 / 1000000000000) (-28165694062 / 1000000000000), orderedInterval (40450590727 / 1000000000000) (40450597207 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (30937009905921 / 160000000000)) (orderedInterval (-34160223689 / 1000000000000) (-34160211386 / 1000000000000), orderedInterval (46192040261 / 1000000000000) (46192052564 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 100 12 (10004393362593 / 32000000000)) (orderedInterval (-30326441606 / 1000000000000) (-30326423659 / 1000000000000), orderedInterval (33464002609 / 1000000000000) (33464020557 / 1000000000000))) = true
  rfl'

theorem compactCertificate391_stateChecks1 :
    compactCertificate391.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 18 12 (9027342332547 / 160000000000)) (orderedInterval (64739779592 / 1000000000000) (64739779593 / 1000000000000), orderedInterval (83642000138 / 1000000000000) (83642000139 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (24248711305959 / 160000000000)) (orderedInterval (64786054267 / 1000000000000) (64786054298 / 1000000000000), orderedInterval (1615322549 / 1000000000000) (1615322581 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 131 12 (65839968241803 / 160000000000)) (orderedInterval (-26412777803 / 1000000000000) (-26412777802 / 1000000000000), orderedInterval (-29113012040 / 1000000000000) (-29113012039 / 1000000000000))) = true
  rfl'

theorem compactCertificate391_stateChecks2 :
    compactCertificate391.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 97 12 (48497422611939 / 160000000000)) (orderedInterval (34144890264 / 1000000000000) (34144938809 / 1000000000000), orderedInterval (-30624713819 / 1000000000000) (-30624665274 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 165 12 (83101160257647 / 160000000000)) (orderedInterval (-34057623499 / 1000000000000) (-34057615363 / 1000000000000), orderedInterval (8144685506 / 1000000000000) (8144693643 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 122 12 (61211938525773 / 160000000000)) (orderedInterval (3478786905 / 1000000000000) (3478786906 / 1000000000000), orderedInterval (40639521282 / 1000000000000) (40639521283 / 1000000000000))) = true
  rfl'

theorem compactCertificate391_stateChecks3 :
    compactCertificate391.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 187 12 (93914855054979 / 160000000000)) (orderedInterval (-8949323336 / 1000000000000) (-8949323335 / 1000000000000), orderedInterval (-31686232362 / 1000000000000) (-31686232361 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 108 12 (54221766846891 / 160000000000)) (orderedInterval (16038963830 / 1000000000000) (16038963831 / 1000000000000), orderedInterval (40241942082 / 1000000000000) (40241942083 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 192 12 (96217476770919 / 160000000000)) (orderedInterval (-28082319297 / 1000000000000) (-28082244552 / 1000000000000), orderedInterval (16455594651 / 1000000000000) (16455669396 / 1000000000000))) = true
  rfl'

theorem compactCertificate391_stateChecks4 :
    compactCertificate391.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 179 12 (89898847802211 / 160000000000)) (orderedInterval (-10200802972 / 1000000000000) (-10200802971 / 1000000000000), orderedInterval (-32068732669 / 1000000000000) (-32068732668 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 128 12 (64156059729363 / 160000000000)) (orderedInterval (-14163306709 / 1000000000000) (-14163306555 / 1000000000000), orderedInterval (37261179213 / 1000000000000) (37261179367 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 145 12 (72746133917877 / 160000000000)) (orderedInterval (3082637435 / 1000000000000) (3082637437 / 1000000000000), orderedInterval (-37295460905 / 1000000000000) (-37295460903 / 1000000000000))) = true
  rfl'

theorem compactCertificate391_stateChecks5 :
    compactCertificate391.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 121 12 (60648142295013 / 160000000000)) (orderedInterval (11983777614 / 1000000000000) (11983777685 / 1000000000000), orderedInterval (-39206371779 / 1000000000000) (-39206371709 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 107 12 (53584472991273 / 160000000000)) (orderedInterval (19450848730 / 1000000000000) (19450849574 / 1000000000000), orderedInterval (-39049213277 / 1000000000000) (-39049212433 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 155 12 (15530868828027 / 32000000000)) (orderedInterval (26531263965 / 1000000000000) (26531281513 / 1000000000000), orderedInterval (-24680758711 / 1000000000000) (-24680741163 / 1000000000000))) = true
  rfl'

theorem compactCertificate391_stateChecks6 :
    compactCertificate391.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (42959200523169 / 160000000000)) (orderedInterval (-38053030167 / 1000000000000) (-38052938373 / 1000000000000), orderedInterval (30452337209 / 1000000000000) (30452429002 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (36416990043609 / 160000000000)) (orderedInterval (42871599724 / 1000000000000) (42871678005 / 1000000000000), orderedInterval (-31062643617 / 1000000000000) (-31062565335 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (22788061474227 / 160000000000)) (orderedInterval (-64480013612 / 1000000000000) (-64480012119 / 1000000000000), orderedInterval (17894182092 / 1000000000000) (17894183585 / 1000000000000))) = true
  rfl'

theorem compactCertificate391_stateChecks7 :
    compactCertificate391.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 24 12 (12255495250509 / 160000000000)) (orderedInterval (83551727996 / 1000000000000) (83551733089 / 1000000000000), orderedInterval (-37018564757 / 1000000000000) (-37018559664 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (33276053638527 / 160000000000)) (orderedInterval (54656589255 / 1000000000000) (54656589262 / 1000000000000), orderedInterval (8452525545 / 1000000000000) (8452525552 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (45435606386079 / 160000000000)) (orderedInterval (42770103132 / 1000000000000) (42770122838 / 1000000000000), orderedInterval (-20386664905 / 1000000000000) (-20386645199 / 1000000000000))) = true
  rfl'

theorem compactCertificate391_stateChecks8 :
    compactCertificate391.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (19211938525773 / 160000000000)) (orderedInterval (72503375484 / 1000000000000) (72503375493 / 1000000000000), orderedInterval (6412515967 / 1000000000000) (6412515976 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 155 12 (78095463492333 / 160000000000)) (orderedInterval (-33747032657 / 1000000000000) (-33747007946 / 1000000000000), orderedInterval (12896458054 / 1000000000000) (12896482765 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 104 12 (52164150351747 / 160000000000)) (orderedInterval (3765562391 / 1000000000000) (3765562392 / 1000000000000), orderedInterval (44022498004 / 1000000000000) (44022498005 / 1000000000000))) = true
  rfl'

theorem compactCertificate391_states : ∀ j,
    BesselStateValid (compactCertificate391.point j) (compactCertificate391.state j) :=
  compactCertificate391.statesValid_of_checks3 compactCertificate391_stateChecks0
    compactCertificate391_stateChecks1 compactCertificate391_stateChecks2
    compactCertificate391_stateChecks3 compactCertificate391_stateChecks4
    compactCertificate391_stateChecks5 compactCertificate391_stateChecks6
    compactCertificate391_stateChecks7 compactCertificate391_stateChecks8

theorem compactCertificate391_chunkChecks0_0 :
    compactCertificate391.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (525 / 2) 0 (IntervalRat.scale (525 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-28165700543 / 1000000000000) (-28165694062 / 1000000000000), orderedInterval (40450590727 / 1000000000000) (40450597207 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (30937009905921 / 160000000000) 0 (IntervalRat.scale (525 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-34160223689 / 1000000000000) (-34160211386 / 1000000000000), orderedInterval (46192040261 / 1000000000000) (46192052564 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (10004393362593 / 32000000000) 0 (IntervalRat.scale (525 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-30326441606 / 1000000000000) (-30326423659 / 1000000000000), orderedInterval (33464002609 / 1000000000000) (33464020557 / 1000000000000)))) (orderedInterval (-13261794888 / 1000000000000) (-13261791132 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (9027342332547 / 160000000000) 0 (IntervalRat.scale (525 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (64739779592 / 1000000000000) (64739779593 / 1000000000000), orderedInterval (83642000138 / 1000000000000) (83642000139 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (24248711305959 / 160000000000) 0 (IntervalRat.scale (525 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (64786054267 / 1000000000000) (64786054298 / 1000000000000), orderedInterval (1615322549 / 1000000000000) (1615322581 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (65839968241803 / 160000000000) 0 (IntervalRat.scale (525 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-26412777803 / 1000000000000) (-26412777802 / 1000000000000), orderedInterval (-29113012040 / 1000000000000) (-29113012039 / 1000000000000)))) (orderedInterval (3540746125 / 1000000000000) (3540746159 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (48497422611939 / 160000000000) 0 (IntervalRat.scale (525 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (34144890264 / 1000000000000) (34144938809 / 1000000000000), orderedInterval (-30624713819 / 1000000000000) (-30624665274 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (83101160257647 / 160000000000) 0 (IntervalRat.scale (525 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-34057623499 / 1000000000000) (-34057615363 / 1000000000000), orderedInterval (8144685506 / 1000000000000) (8144693643 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (61211938525773 / 160000000000) 0 (IntervalRat.scale (525 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (3478786905 / 1000000000000) (3478786906 / 1000000000000), orderedInterval (40639521282 / 1000000000000) (40639521283 / 1000000000000)))) (orderedInterval (1134548530 / 1000000000000) (1134548797 / 1000000000000))) = true
  rfl'

theorem compactCertificate391_chunkChecks0_1 :
    compactCertificate391.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (93914855054979 / 160000000000) 0 (IntervalRat.scale (525 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-8949323336 / 1000000000000) (-8949323335 / 1000000000000), orderedInterval (-31686232362 / 1000000000000) (-31686232361 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (54221766846891 / 160000000000) 0 (IntervalRat.scale (525 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (16038963830 / 1000000000000) (16038963831 / 1000000000000), orderedInterval (40241942082 / 1000000000000) (40241942083 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (96217476770919 / 160000000000) 0 (IntervalRat.scale (525 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-28082319297 / 1000000000000) (-28082244552 / 1000000000000), orderedInterval (16455594651 / 1000000000000) (16455669396 / 1000000000000)))) (orderedInterval (-1213525264 / 1000000000000) (-1213514534 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (89898847802211 / 160000000000) 0 (IntervalRat.scale (525 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-10200802972 / 1000000000000) (-10200802971 / 1000000000000), orderedInterval (-32068732669 / 1000000000000) (-32068732668 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (64156059729363 / 160000000000) 0 (IntervalRat.scale (525 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14163306709 / 1000000000000) (-14163306555 / 1000000000000), orderedInterval (37261179213 / 1000000000000) (37261179367 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (72746133917877 / 160000000000) 0 (IntervalRat.scale (525 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (3082637435 / 1000000000000) (3082637437 / 1000000000000), orderedInterval (-37295460905 / 1000000000000) (-37295460903 / 1000000000000)))) (orderedInterval (-1170766838 / 1000000000000) (-1170766792 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (60648142295013 / 160000000000) 0 (IntervalRat.scale (525 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (11983777614 / 1000000000000) (11983777685 / 1000000000000), orderedInterval (-39206371779 / 1000000000000) (-39206371709 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (53584472991273 / 160000000000) 0 (IntervalRat.scale (525 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (19450848730 / 1000000000000) (19450849574 / 1000000000000), orderedInterval (-39049213277 / 1000000000000) (-39049212433 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (15530868828027 / 32000000000) 0 (IntervalRat.scale (525 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (26531263965 / 1000000000000) (26531281513 / 1000000000000), orderedInterval (-24680758711 / 1000000000000) (-24680741163 / 1000000000000)))) (orderedInterval (-295417634 / 1000000000000) (-295417109 / 1000000000000))) = true
  rfl'

theorem compactCertificate391_chunkChecks0_2 :
    compactCertificate391.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (42959200523169 / 160000000000) 0 (IntervalRat.scale (525 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-38053030167 / 1000000000000) (-38052938373 / 1000000000000), orderedInterval (30452337209 / 1000000000000) (30452429002 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (36416990043609 / 160000000000) 0 (IntervalRat.scale (525 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (42871599724 / 1000000000000) (42871678005 / 1000000000000), orderedInterval (-31062643617 / 1000000000000) (-31062565335 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (22788061474227 / 160000000000) 0 (IntervalRat.scale (525 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-64480013612 / 1000000000000) (-64480012119 / 1000000000000), orderedInterval (17894182092 / 1000000000000) (17894183585 / 1000000000000)))) (orderedInterval (1558677803 / 1000000000000) (1558697025 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (12255495250509 / 160000000000) 0 (IntervalRat.scale (525 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (83551727996 / 1000000000000) (83551733089 / 1000000000000), orderedInterval (-37018564757 / 1000000000000) (-37018559664 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (33276053638527 / 160000000000) 0 (IntervalRat.scale (525 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (54656589255 / 1000000000000) (54656589262 / 1000000000000), orderedInterval (8452525545 / 1000000000000) (8452525552 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (45435606386079 / 160000000000) 0 (IntervalRat.scale (525 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (42770103132 / 1000000000000) (42770122838 / 1000000000000), orderedInterval (-20386664905 / 1000000000000) (-20386645199 / 1000000000000)))) (orderedInterval (-6060632925 / 1000000000000) (-6060631289 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (19211938525773 / 160000000000) 0 (IntervalRat.scale (525 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (72503375484 / 1000000000000) (72503375493 / 1000000000000), orderedInterval (6412515967 / 1000000000000) (6412515976 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (78095463492333 / 160000000000) 0 (IntervalRat.scale (525 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-33747032657 / 1000000000000) (-33747007946 / 1000000000000), orderedInterval (12896458054 / 1000000000000) (12896482765 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (52164150351747 / 160000000000) 0 (IntervalRat.scale (525 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (3765562391 / 1000000000000) (3765562392 / 1000000000000), orderedInterval (44022498004 / 1000000000000) (44022498005 / 1000000000000)))) (orderedInterval (2477621113 / 1000000000000) (2477623198 / 1000000000000))) = true
  rfl'

theorem compactCertificate391_chunkChecks0 :
    compactCertificate391.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate391.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate391_chunkChecks0_0
    compactCertificate391_chunkChecks0_1 compactCertificate391_chunkChecks0_2

theorem compactCertificate391_chunkChecks1_0 :
    compactCertificate391.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (525 / 2) 1 (IntervalRat.scale (525 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-28165700543 / 1000000000000) (-28165694062 / 1000000000000), orderedInterval (40450590727 / 1000000000000) (40450597207 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (30937009905921 / 160000000000) 1 (IntervalRat.scale (525 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-34160223689 / 1000000000000) (-34160211386 / 1000000000000), orderedInterval (46192040261 / 1000000000000) (46192052564 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (10004393362593 / 32000000000) 1 (IntervalRat.scale (525 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-30326441606 / 1000000000000) (-30326423659 / 1000000000000), orderedInterval (33464002609 / 1000000000000) (33464020557 / 1000000000000)))) (orderedInterval (18689015755 / 1000000000000) (18689019684 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (9027342332547 / 160000000000) 1 (IntervalRat.scale (525 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (64739779592 / 1000000000000) (64739779593 / 1000000000000), orderedInterval (83642000138 / 1000000000000) (83642000139 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (24248711305959 / 160000000000) 1 (IntervalRat.scale (525 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (64786054267 / 1000000000000) (64786054298 / 1000000000000), orderedInterval (1615322549 / 1000000000000) (1615322581 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (65839968241803 / 160000000000) 1 (IntervalRat.scale (525 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-26412777803 / 1000000000000) (-26412777802 / 1000000000000), orderedInterval (-29113012040 / 1000000000000) (-29113012039 / 1000000000000)))) (orderedInterval (3083400832 / 1000000000000) (3083400869 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (48497422611939 / 160000000000) 1 (IntervalRat.scale (525 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (34144890264 / 1000000000000) (34144938809 / 1000000000000), orderedInterval (-30624713819 / 1000000000000) (-30624665274 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (83101160257647 / 160000000000) 1 (IntervalRat.scale (525 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-34057623499 / 1000000000000) (-34057615363 / 1000000000000), orderedInterval (8144685506 / 1000000000000) (8144693643 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (61211938525773 / 160000000000) 1 (IntervalRat.scale (525 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (3478786905 / 1000000000000) (3478786906 / 1000000000000), orderedInterval (40639521282 / 1000000000000) (40639521283 / 1000000000000)))) (orderedInterval (934397800 / 1000000000000) (934398323 / 1000000000000))) = true
  rfl'

theorem compactCertificate391_chunkChecks1_1 :
    compactCertificate391.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (93914855054979 / 160000000000) 1 (IntervalRat.scale (525 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-8949323336 / 1000000000000) (-8949323335 / 1000000000000), orderedInterval (-31686232362 / 1000000000000) (-31686232361 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (54221766846891 / 160000000000) 1 (IntervalRat.scale (525 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (16038963830 / 1000000000000) (16038963831 / 1000000000000), orderedInterval (40241942082 / 1000000000000) (40241942083 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (96217476770919 / 160000000000) 1 (IntervalRat.scale (525 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-28082319297 / 1000000000000) (-28082244552 / 1000000000000), orderedInterval (16455594651 / 1000000000000) (16455669396 / 1000000000000)))) (orderedInterval (21797863009 / 1000000000000) (21797887567 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (89898847802211 / 160000000000) 1 (IntervalRat.scale (525 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-10200802972 / 1000000000000) (-10200802971 / 1000000000000), orderedInterval (-32068732669 / 1000000000000) (-32068732668 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (64156059729363 / 160000000000) 1 (IntervalRat.scale (525 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14163306709 / 1000000000000) (-14163306555 / 1000000000000), orderedInterval (37261179213 / 1000000000000) (37261179367 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (72746133917877 / 160000000000) 1 (IntervalRat.scale (525 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (3082637435 / 1000000000000) (3082637437 / 1000000000000), orderedInterval (-37295460905 / 1000000000000) (-37295460903 / 1000000000000)))) (orderedInterval (6948363387 / 1000000000000) (6948363460 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (60648142295013 / 160000000000) 1 (IntervalRat.scale (525 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (11983777614 / 1000000000000) (11983777685 / 1000000000000), orderedInterval (-39206371779 / 1000000000000) (-39206371709 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (53584472991273 / 160000000000) 1 (IntervalRat.scale (525 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (19450848730 / 1000000000000) (19450849574 / 1000000000000), orderedInterval (-39049213277 / 1000000000000) (-39049212433 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (15530868828027 / 32000000000) 1 (IntervalRat.scale (525 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (26531263965 / 1000000000000) (26531281513 / 1000000000000), orderedInterval (-24680758711 / 1000000000000) (-24680741163 / 1000000000000)))) (orderedInterval (1028885916 / 1000000000000) (1028886846 / 1000000000000))) = true
  rfl'

theorem compactCertificate391_chunkChecks1_2 :
    compactCertificate391.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (42959200523169 / 160000000000) 1 (IntervalRat.scale (525 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-38053030167 / 1000000000000) (-38052938373 / 1000000000000), orderedInterval (30452337209 / 1000000000000) (30452429002 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (36416990043609 / 160000000000) 1 (IntervalRat.scale (525 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (42871599724 / 1000000000000) (42871678005 / 1000000000000), orderedInterval (-31062643617 / 1000000000000) (-31062565335 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (22788061474227 / 160000000000) 1 (IntervalRat.scale (525 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-64480013612 / 1000000000000) (-64480012119 / 1000000000000), orderedInterval (17894182092 / 1000000000000) (17894183585 / 1000000000000)))) (orderedInterval (-3139806393 / 1000000000000) (-3139787451 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (12255495250509 / 160000000000) 1 (IntervalRat.scale (525 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (83551727996 / 1000000000000) (83551733089 / 1000000000000), orderedInterval (-37018564757 / 1000000000000) (-37018559664 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (33276053638527 / 160000000000) 1 (IntervalRat.scale (525 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (54656589255 / 1000000000000) (54656589262 / 1000000000000), orderedInterval (8452525545 / 1000000000000) (8452525552 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (45435606386079 / 160000000000) 1 (IntervalRat.scale (525 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (42770103132 / 1000000000000) (42770122838 / 1000000000000), orderedInterval (-20386664905 / 1000000000000) (-20386645199 / 1000000000000)))) (orderedInterval (1737743578 / 1000000000000) (1737745269 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (19211938525773 / 160000000000) 1 (IntervalRat.scale (525 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (72503375484 / 1000000000000) (72503375493 / 1000000000000), orderedInterval (6412515967 / 1000000000000) (6412515976 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (78095463492333 / 160000000000) 1 (IntervalRat.scale (525 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-33747032657 / 1000000000000) (-33747007946 / 1000000000000), orderedInterval (12896458054 / 1000000000000) (12896482765 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (52164150351747 / 160000000000) 1 (IntervalRat.scale (525 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (3765562391 / 1000000000000) (3765562392 / 1000000000000), orderedInterval (44022498004 / 1000000000000) (44022498005 / 1000000000000)))) (orderedInterval (-12193012589 / 1000000000000) (-12193008746 / 1000000000000))) = true
  rfl'

theorem compactCertificate391_chunkChecks1 :
    compactCertificate391.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate391.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate391_chunkChecks1_0
    compactCertificate391_chunkChecks1_1 compactCertificate391_chunkChecks1_2

theorem compactCertificate391_chunkChecks2_0 :
    compactCertificate391.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (525 / 2) 2 (IntervalRat.scale (525 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-28165700543 / 1000000000000) (-28165694062 / 1000000000000), orderedInterval (40450590727 / 1000000000000) (40450597207 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (30937009905921 / 160000000000) 2 (IntervalRat.scale (525 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-34160223689 / 1000000000000) (-34160211386 / 1000000000000), orderedInterval (46192040261 / 1000000000000) (46192052564 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (10004393362593 / 32000000000) 2 (IntervalRat.scale (525 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-30326441606 / 1000000000000) (-30326423659 / 1000000000000), orderedInterval (33464002609 / 1000000000000) (33464020557 / 1000000000000)))) (orderedInterval (13789713541 / 1000000000000) (13789717705 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (9027342332547 / 160000000000) 2 (IntervalRat.scale (525 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (64739779592 / 1000000000000) (64739779593 / 1000000000000), orderedInterval (83642000138 / 1000000000000) (83642000139 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (24248711305959 / 160000000000) 2 (IntervalRat.scale (525 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (64786054267 / 1000000000000) (64786054298 / 1000000000000), orderedInterval (1615322549 / 1000000000000) (1615322581 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (65839968241803 / 160000000000) 2 (IntervalRat.scale (525 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-26412777803 / 1000000000000) (-26412777802 / 1000000000000), orderedInterval (-29113012040 / 1000000000000) (-29113012039 / 1000000000000)))) (orderedInterval (-5382031039 / 1000000000000) (-5382030989 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (48497422611939 / 160000000000) 2 (IntervalRat.scale (525 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (34144890264 / 1000000000000) (34144938809 / 1000000000000), orderedInterval (-30624713819 / 1000000000000) (-30624665274 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (83101160257647 / 160000000000) 2 (IntervalRat.scale (525 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-34057623499 / 1000000000000) (-34057615363 / 1000000000000), orderedInterval (8144685506 / 1000000000000) (8144693643 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (61211938525773 / 160000000000) 2 (IntervalRat.scale (525 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (3478786905 / 1000000000000) (3478786906 / 1000000000000), orderedInterval (40639521282 / 1000000000000) (40639521283 / 1000000000000)))) (orderedInterval (-4294593817 / 1000000000000) (-4294592786 / 1000000000000))) = true
  rfl'

theorem compactCertificate391_chunkChecks2_1 :
    compactCertificate391.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (93914855054979 / 160000000000) 2 (IntervalRat.scale (525 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-8949323336 / 1000000000000) (-8949323335 / 1000000000000), orderedInterval (-31686232362 / 1000000000000) (-31686232361 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (54221766846891 / 160000000000) 2 (IntervalRat.scale (525 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (16038963830 / 1000000000000) (16038963831 / 1000000000000), orderedInterval (40241942082 / 1000000000000) (40241942083 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (96217476770919 / 160000000000) 2 (IntervalRat.scale (525 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-28082319297 / 1000000000000) (-28082244552 / 1000000000000), orderedInterval (16455594651 / 1000000000000) (16455669396 / 1000000000000)))) (orderedInterval (10936495967 / 1000000000000) (10936552288 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (89898847802211 / 160000000000) 2 (IntervalRat.scale (525 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-10200802972 / 1000000000000) (-10200802971 / 1000000000000), orderedInterval (-32068732669 / 1000000000000) (-32068732668 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (64156059729363 / 160000000000) 2 (IntervalRat.scale (525 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14163306709 / 1000000000000) (-14163306555 / 1000000000000), orderedInterval (37261179213 / 1000000000000) (37261179367 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (72746133917877 / 160000000000) 2 (IntervalRat.scale (525 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (3082637435 / 1000000000000) (3082637437 / 1000000000000), orderedInterval (-37295460905 / 1000000000000) (-37295460903 / 1000000000000)))) (orderedInterval (2301702000 / 1000000000000) (2301702119 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (60648142295013 / 160000000000) 2 (IntervalRat.scale (525 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (11983777614 / 1000000000000) (11983777685 / 1000000000000), orderedInterval (-39206371779 / 1000000000000) (-39206371709 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (53584472991273 / 160000000000) 2 (IntervalRat.scale (525 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (19450848730 / 1000000000000) (19450849574 / 1000000000000), orderedInterval (-39049213277 / 1000000000000) (-39049212433 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (15530868828027 / 32000000000) 2 (IntervalRat.scale (525 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (26531263965 / 1000000000000) (26531281513 / 1000000000000), orderedInterval (-24680758711 / 1000000000000) (-24680741163 / 1000000000000)))) (orderedInterval (-802838152 / 1000000000000) (-802836478 / 1000000000000))) = true
  rfl'

theorem compactCertificate391_chunkChecks2_2 :
    compactCertificate391.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (42959200523169 / 160000000000) 2 (IntervalRat.scale (525 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-38053030167 / 1000000000000) (-38052938373 / 1000000000000), orderedInterval (30452337209 / 1000000000000) (30452429002 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (36416990043609 / 160000000000) 2 (IntervalRat.scale (525 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (42871599724 / 1000000000000) (42871678005 / 1000000000000), orderedInterval (-31062643617 / 1000000000000) (-31062565335 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (22788061474227 / 160000000000) 2 (IntervalRat.scale (525 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-64480013612 / 1000000000000) (-64480012119 / 1000000000000), orderedInterval (17894182092 / 1000000000000) (17894183585 / 1000000000000)))) (orderedInterval (-3911257185 / 1000000000000) (-3911238354 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (12255495250509 / 160000000000) 2 (IntervalRat.scale (525 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (83551727996 / 1000000000000) (83551733089 / 1000000000000), orderedInterval (-37018564757 / 1000000000000) (-37018559664 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (33276053638527 / 160000000000) 2 (IntervalRat.scale (525 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (54656589255 / 1000000000000) (54656589262 / 1000000000000), orderedInterval (8452525545 / 1000000000000) (8452525552 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (45435606386079 / 160000000000) 2 (IntervalRat.scale (525 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (42770103132 / 1000000000000) (42770122838 / 1000000000000), orderedInterval (-20386664905 / 1000000000000) (-20386645199 / 1000000000000)))) (orderedInterval (4739147957 / 1000000000000) (4739149767 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (19211938525773 / 160000000000) 2 (IntervalRat.scale (525 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (72503375484 / 1000000000000) (72503375493 / 1000000000000), orderedInterval (6412515967 / 1000000000000) (6412515976 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (78095463492333 / 160000000000) 2 (IntervalRat.scale (525 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-33747032657 / 1000000000000) (-33747007946 / 1000000000000), orderedInterval (12896458054 / 1000000000000) (12896482765 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (52164150351747 / 160000000000) 2 (IntervalRat.scale (525 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (3765562391 / 1000000000000) (3765562392 / 1000000000000), orderedInterval (44022498004 / 1000000000000) (44022498005 / 1000000000000)))) (orderedInterval (-8452934897 / 1000000000000) (-8452927777 / 1000000000000))) = true
  rfl'

theorem compactCertificate391_chunkChecks2 :
    compactCertificate391.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate391.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate391_chunkChecks2_0
    compactCertificate391_chunkChecks2_1 compactCertificate391_chunkChecks2_2

theorem compactCertificate391_chunkChecks3_0 :
    compactCertificate391.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (525 / 2) 3 (IntervalRat.scale (525 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-28165700543 / 1000000000000) (-28165694062 / 1000000000000), orderedInterval (40450590727 / 1000000000000) (40450597207 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (30937009905921 / 160000000000) 3 (IntervalRat.scale (525 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-34160223689 / 1000000000000) (-34160211386 / 1000000000000), orderedInterval (46192040261 / 1000000000000) (46192052564 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (10004393362593 / 32000000000) 3 (IntervalRat.scale (525 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-30326441606 / 1000000000000) (-30326423659 / 1000000000000), orderedInterval (33464002609 / 1000000000000) (33464020557 / 1000000000000)))) (orderedInterval (-19574983246 / 1000000000000) (-19574978809 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (9027342332547 / 160000000000) 3 (IntervalRat.scale (525 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (64739779592 / 1000000000000) (64739779593 / 1000000000000), orderedInterval (83642000138 / 1000000000000) (83642000139 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (24248711305959 / 160000000000) 3 (IntervalRat.scale (525 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (64786054267 / 1000000000000) (64786054298 / 1000000000000), orderedInterval (1615322549 / 1000000000000) (1615322581 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (65839968241803 / 160000000000) 3 (IntervalRat.scale (525 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-26412777803 / 1000000000000) (-26412777802 / 1000000000000), orderedInterval (-29113012040 / 1000000000000) (-29113012039 / 1000000000000)))) (orderedInterval (-7954657324 / 1000000000000) (-7954657248 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (48497422611939 / 160000000000) 3 (IntervalRat.scale (525 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (34144890264 / 1000000000000) (34144938809 / 1000000000000), orderedInterval (-30624713819 / 1000000000000) (-30624665274 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (83101160257647 / 160000000000) 3 (IntervalRat.scale (525 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-34057623499 / 1000000000000) (-34057615363 / 1000000000000), orderedInterval (8144685506 / 1000000000000) (8144693643 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (61211938525773 / 160000000000) 3 (IntervalRat.scale (525 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (3478786905 / 1000000000000) (3478786906 / 1000000000000), orderedInterval (40639521282 / 1000000000000) (40639521283 / 1000000000000)))) (orderedInterval (-1078272654 / 1000000000000) (-1078270623 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate391_chunkChecks3_1 :
    compactCertificate391.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (93914855054979 / 160000000000) 3 (IntervalRat.scale (525 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-8949323336 / 1000000000000) (-8949323335 / 1000000000000), orderedInterval (-31686232362 / 1000000000000) (-31686232361 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (54221766846891 / 160000000000) 3 (IntervalRat.scale (525 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (16038963830 / 1000000000000) (16038963831 / 1000000000000), orderedInterval (40241942082 / 1000000000000) (40241942083 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (96217476770919 / 160000000000) 3 (IntervalRat.scale (525 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-28082319297 / 1000000000000) (-28082244552 / 1000000000000), orderedInterval (16455594651 / 1000000000000) (16455669396 / 1000000000000)))) (orderedInterval (-97530076135 / 1000000000000) (-97529947158 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (89898847802211 / 160000000000) 3 (IntervalRat.scale (525 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-10200802972 / 1000000000000) (-10200802971 / 1000000000000), orderedInterval (-32068732669 / 1000000000000) (-32068732668 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (64156059729363 / 160000000000) 3 (IntervalRat.scale (525 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14163306709 / 1000000000000) (-14163306555 / 1000000000000), orderedInterval (37261179213 / 1000000000000) (37261179367 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (72746133917877 / 160000000000) 3 (IntervalRat.scale (525 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (3082637435 / 1000000000000) (3082637437 / 1000000000000), orderedInterval (-37295460905 / 1000000000000) (-37295460903 / 1000000000000)))) (orderedInterval (-19225382496 / 1000000000000) (-19225382301 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (60648142295013 / 160000000000) 3 (IntervalRat.scale (525 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (11983777614 / 1000000000000) (11983777685 / 1000000000000), orderedInterval (-39206371779 / 1000000000000) (-39206371709 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (53584472991273 / 160000000000) 3 (IntervalRat.scale (525 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (19450848730 / 1000000000000) (19450849574 / 1000000000000), orderedInterval (-39049213277 / 1000000000000) (-39049212433 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (15530868828027 / 32000000000) 3 (IntervalRat.scale (525 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (26531263965 / 1000000000000) (26531281513 / 1000000000000), orderedInterval (-24680758711 / 1000000000000) (-24680741163 / 1000000000000)))) (orderedInterval (719659897 / 1000000000000) (719662929 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate391_chunkChecks3_2 :
    compactCertificate391.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (42959200523169 / 160000000000) 3 (IntervalRat.scale (525 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-38053030167 / 1000000000000) (-38052938373 / 1000000000000), orderedInterval (30452337209 / 1000000000000) (30452429002 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (36416990043609 / 160000000000) 3 (IntervalRat.scale (525 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (42871599724 / 1000000000000) (42871678005 / 1000000000000), orderedInterval (-31062643617 / 1000000000000) (-31062565335 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (22788061474227 / 160000000000) 3 (IntervalRat.scale (525 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-64480013612 / 1000000000000) (-64480012119 / 1000000000000), orderedInterval (17894182092 / 1000000000000) (17894183585 / 1000000000000)))) (orderedInterval (3986094536 / 1000000000000) (3986113265 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (12255495250509 / 160000000000) 3 (IntervalRat.scale (525 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (83551727996 / 1000000000000) (83551733089 / 1000000000000), orderedInterval (-37018564757 / 1000000000000) (-37018559664 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (33276053638527 / 160000000000) 3 (IntervalRat.scale (525 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (54656589255 / 1000000000000) (54656589262 / 1000000000000), orderedInterval (8452525545 / 1000000000000) (8452525552 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (45435606386079 / 160000000000) 3 (IntervalRat.scale (525 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (42770103132 / 1000000000000) (42770122838 / 1000000000000), orderedInterval (-20386664905 / 1000000000000) (-20386645199 / 1000000000000)))) (orderedInterval (-1917688519 / 1000000000000) (-1917686568 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (19211938525773 / 160000000000) 3 (IntervalRat.scale (525 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (72503375484 / 1000000000000) (72503375493 / 1000000000000), orderedInterval (6412515967 / 1000000000000) (6412515976 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (78095463492333 / 160000000000) 3 (IntervalRat.scale (525 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-33747032657 / 1000000000000) (-33747007946 / 1000000000000), orderedInterval (12896458054 / 1000000000000) (12896482765 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (52164150351747 / 160000000000) 3 (IntervalRat.scale (525 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (3765562391 / 1000000000000) (3765562392 / 1000000000000), orderedInterval (44022498004 / 1000000000000) (44022498005 / 1000000000000)))) (orderedInterval (22602010636 / 1000000000000) (22602023827 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate391_chunkChecks3 :
    compactCertificate391.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate391.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate391_chunkChecks3_0
    compactCertificate391_chunkChecks3_1 compactCertificate391_chunkChecks3_2

theorem compactCertificate391_chunkChecks4_0 :
    compactCertificate391.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (525 / 2) 4 (IntervalRat.scale (525 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-28165700543 / 1000000000000) (-28165694062 / 1000000000000), orderedInterval (40450590727 / 1000000000000) (40450597207 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (30937009905921 / 160000000000) 4 (IntervalRat.scale (525 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-34160223689 / 1000000000000) (-34160211386 / 1000000000000), orderedInterval (46192040261 / 1000000000000) (46192052564 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (10004393362593 / 32000000000) 4 (IntervalRat.scale (525 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-30326441606 / 1000000000000) (-30326423659 / 1000000000000), orderedInterval (33464002609 / 1000000000000) (33464020557 / 1000000000000)))) (orderedInterval (-14688943982 / 1000000000000) (-14688939194 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (9027342332547 / 160000000000) 4 (IntervalRat.scale (525 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (64739779592 / 1000000000000) (64739779593 / 1000000000000), orderedInterval (83642000138 / 1000000000000) (83642000139 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (24248711305959 / 160000000000) 4 (IntervalRat.scale (525 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (64786054267 / 1000000000000) (64786054298 / 1000000000000), orderedInterval (1615322549 / 1000000000000) (1615322581 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (65839968241803 / 160000000000) 4 (IntervalRat.scale (525 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-26412777803 / 1000000000000) (-26412777802 / 1000000000000), orderedInterval (-29113012040 / 1000000000000) (-29113012039 / 1000000000000)))) (orderedInterval (11661038540 / 1000000000000) (11661038656 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (48497422611939 / 160000000000) 4 (IntervalRat.scale (525 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (34144890264 / 1000000000000) (34144938809 / 1000000000000), orderedInterval (-30624713819 / 1000000000000) (-30624665274 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (83101160257647 / 160000000000) 4 (IntervalRat.scale (525 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-34057623499 / 1000000000000) (-34057615363 / 1000000000000), orderedInterval (8144685506 / 1000000000000) (8144693643 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (61211938525773 / 160000000000) 4 (IntervalRat.scale (525 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (3478786905 / 1000000000000) (3478786906 / 1000000000000), orderedInterval (40639521282 / 1000000000000) (40639521283 / 1000000000000)))) (orderedInterval (16487121065 / 1000000000000) (16487125080 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate391_chunkChecks4_1 :
    compactCertificate391.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (93914855054979 / 160000000000) 4 (IntervalRat.scale (525 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-8949323336 / 1000000000000) (-8949323335 / 1000000000000), orderedInterval (-31686232362 / 1000000000000) (-31686232361 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (54221766846891 / 160000000000) 4 (IntervalRat.scale (525 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (16038963830 / 1000000000000) (16038963831 / 1000000000000), orderedInterval (40241942082 / 1000000000000) (40241942083 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (96217476770919 / 160000000000) 4 (IntervalRat.scale (525 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-28082319297 / 1000000000000) (-28082244552 / 1000000000000), orderedInterval (16455594651 / 1000000000000) (16455669396 / 1000000000000)))) (orderedInterval (-66156495900 / 1000000000000) (-66156200013 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (89898847802211 / 160000000000) 4 (IntervalRat.scale (525 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-10200802972 / 1000000000000) (-10200802971 / 1000000000000), orderedInterval (-32068732669 / 1000000000000) (-32068732668 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (64156059729363 / 160000000000) 4 (IntervalRat.scale (525 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14163306709 / 1000000000000) (-14163306555 / 1000000000000), orderedInterval (37261179213 / 1000000000000) (37261179367 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (72746133917877 / 160000000000) 4 (IntervalRat.scale (525 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (3082637435 / 1000000000000) (3082637437 / 1000000000000), orderedInterval (-37295460905 / 1000000000000) (-37295460903 / 1000000000000)))) (orderedInterval (-3420260960 / 1000000000000) (-3420260632 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (60648142295013 / 160000000000) 4 (IntervalRat.scale (525 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (11983777614 / 1000000000000) (11983777685 / 1000000000000), orderedInterval (-39206371779 / 1000000000000) (-39206371709 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (53584472991273 / 160000000000) 4 (IntervalRat.scale (525 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (19450848730 / 1000000000000) (19450849574 / 1000000000000), orderedInterval (-39049213277 / 1000000000000) (-39049212433 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (15530868828027 / 32000000000) 4 (IntervalRat.scale (525 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (26531263965 / 1000000000000) (26531281513 / 1000000000000), orderedInterval (-24680758711 / 1000000000000) (-24680741163 / 1000000000000)))) (orderedInterval (5585395611 / 1000000000000) (5585401148 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate391_chunkChecks4_2 :
    compactCertificate391.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (42959200523169 / 160000000000) 4 (IntervalRat.scale (525 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-38053030167 / 1000000000000) (-38052938373 / 1000000000000), orderedInterval (30452337209 / 1000000000000) (30452429002 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (36416990043609 / 160000000000) 4 (IntervalRat.scale (525 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (42871599724 / 1000000000000) (42871678005 / 1000000000000), orderedInterval (-31062643617 / 1000000000000) (-31062565335 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (22788061474227 / 160000000000) 4 (IntervalRat.scale (525 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-64480013612 / 1000000000000) (-64480012119 / 1000000000000), orderedInterval (17894182092 / 1000000000000) (17894183585 / 1000000000000)))) (orderedInterval (5075655123 / 1000000000000) (5075673893 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (12255495250509 / 160000000000) 4 (IntervalRat.scale (525 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (83551727996 / 1000000000000) (83551733089 / 1000000000000), orderedInterval (-37018564757 / 1000000000000) (-37018559664 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (33276053638527 / 160000000000) 4 (IntervalRat.scale (525 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (54656589255 / 1000000000000) (54656589262 / 1000000000000), orderedInterval (8452525545 / 1000000000000) (8452525552 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (45435606386079 / 160000000000) 4 (IntervalRat.scale (525 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (42770103132 / 1000000000000) (42770122838 / 1000000000000), orderedInterval (-20386664905 / 1000000000000) (-20386645199 / 1000000000000)))) (orderedInterval (-4974388974 / 1000000000000) (-4974386859 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (19211938525773 / 160000000000) 4 (IntervalRat.scale (525 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (72503375484 / 1000000000000) (72503375493 / 1000000000000), orderedInterval (6412515967 / 1000000000000) (6412515976 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (78095463492333 / 160000000000) 4 (IntervalRat.scale (525 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-33747032657 / 1000000000000) (-33747007946 / 1000000000000), orderedInterval (12896458054 / 1000000000000) (12896482765 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (52164150351747 / 160000000000) 4 (IntervalRat.scale (525 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (3765562391 / 1000000000000) (3765562392 / 1000000000000), orderedInterval (44022498004 / 1000000000000) (44022498005 / 1000000000000)))) (orderedInterval (31003511229 / 1000000000000) (31003535747 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate391_chunkChecks4 :
    compactCertificate391.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate391.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate391_chunkChecks4_0
    compactCertificate391_chunkChecks4_1 compactCertificate391_chunkChecks4_2

theorem compactCertificate391_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate391.chunkCheck r b = true :=
  compactCertificate391.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate391_chunkChecks0
    · exact compactCertificate391_chunkChecks1
    · exact compactCertificate391_chunkChecks2
    · exact compactCertificate391_chunkChecks3
    · exact compactCertificate391_chunkChecks4)

theorem compactCertificate391_coefficient0 :
    compactCertificate391.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate391_coefficient1 :
    compactCertificate391.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate391_coefficient2 :
    compactCertificate391.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate391_coefficient3 :
    compactCertificate391.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate391_coefficient4 :
    compactCertificate391.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate391_coefficients : ∀ r : Fin 5,
    compactCertificate391.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate391_coefficient0
  · exact compactCertificate391_coefficient1
  · exact compactCertificate391_coefficient2
  · exact compactCertificate391_coefficient3
  · exact compactCertificate391_coefficient4

theorem compactCertificate391_lower : (1 : ℚ) ≤ compactCertificate391.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate391, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate391_proves {t : ℝ} (ht : t ∈ compactCertificate391.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate391.proves compactCertificate391_states compactCertificate391_chunks
    compactCertificate391_coefficients compactCertificate391_lower ht

end Erdos232
