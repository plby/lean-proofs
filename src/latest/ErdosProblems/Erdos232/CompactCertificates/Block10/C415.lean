/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate415 : CompactCertificate where
  left := 286
  right := 287
  center := 573 / 2
  grid := fun i =>
    match i.val with
    | 0 => 91
    | 1 => 67
    | 2 => 109
    | 3 => 20
    | 4 => 53
    | 5 => 143
    | 6 => 105
    | 7 => 181
    | 8 => 133
    | 9 => 204
    | 10 => 118
    | 11 => 209
    | 12 => 195
    | 13 => 139
    | 14 => 158
    | 15 => 132
    | 16 => 116
    | 17 => 169
    | 18 => 93
    | 19 => 79
    | 20 => 50
    | 21 => 27
    | 22 => 72
    | 23 => 99
    | 24 => 42
    | 25 => 170
    | _ => 113
  point := fun i =>
    match i.val with
    | 0 => 573 / 2
    | 1 => 844138413147273 / 4000000000000
    | 2 => 272977018893609 / 800000000000
    | 3 => 246317483645211 / 4000000000000
    | 4 => 661643408491167 / 4000000000000
    | 5 => 1796490562026339 / 4000000000000
    | 6 => 1323286816982907 / 4000000000000
    | 7 => 2267474515601511 / 4000000000000
    | 8 => 1670211465488949 / 4000000000000
    | 9 => 2562533902214427 / 4000000000000
    | 10 => 1479479638250883 / 4000000000000
    | 11 => 2625362580463647 / 4000000000000
    | 12 => 2452954275746043 / 4000000000000
    | 13 => 1750543915472619 / 4000000000000
    | 14 => 1984930225473501 / 4000000000000
    | 15 => 1654827882621069 / 4000000000000
    | 16 => 1462090620190449 / 4000000000000
    | 17 => 423770849450451 / 800000000000
    | 18 => 1172172471417897 / 4000000000000
    | 19 => 993663585475617 / 4000000000000
    | 20 => 621788534511051 / 4000000000000
    | 21 => 334399941835317 / 4000000000000
    | 22 => 907960892136951 / 4000000000000
    | 23 => 1239742974248727 / 4000000000000
    | 24 => 524211465488949 / 4000000000000
    | 25 => 2130890503862229 / 4000000000000
    | _ => 1423336102454811 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-46453043008 / 1000000000000) (-46453042998 / 1000000000000), orderedInterval (-7929557666 / 1000000000000) (-7929557656 / 1000000000000))
    | 1 => (orderedInterval (-53374597465 / 1000000000000) (-53374597463 / 1000000000000), orderedInterval (-12827514419 / 1000000000000) (-12827514417 / 1000000000000))
    | 2 => (orderedInterval (17899932705 / 1000000000000) (17899933232 / 1000000000000), orderedInterval (-39336574316 / 1000000000000) (-39336573789 / 1000000000000))
    | 3 => (orderedInterval (-45966962953 / 1000000000000) (-45966958663 / 1000000000000), orderedInterval (91067410349 / 1000000000000) (91067414639 / 1000000000000))
    | 4 => (orderedInterval (18861143522 / 1000000000000) (18861143884 / 1000000000000), orderedInterval (-59158534500 / 1000000000000) (-59158534137 / 1000000000000))
    | 5 => (orderedInterval (-23083773158 / 1000000000000) (-23083773157 / 1000000000000), orderedInterval (-29716760373 / 1000000000000) (-29716760372 / 1000000000000))
    | 6 => (orderedInterval (-43244748048 / 1000000000000) (-43244746618 / 1000000000000), orderedInterval (7430743864 / 1000000000000) (7430745295 / 1000000000000))
    | 7 => (orderedInterval (27727730877 / 1000000000000) (27727779534 / 1000000000000), orderedInterval (-18845155414 / 1000000000000) (-18845106757 / 1000000000000))
    | 8 => (orderedInterval (-18930098069 / 1000000000000) (-18930098068 / 1000000000000), orderedInterval (-34128418271 / 1000000000000) (-34128418270 / 1000000000000))
    | 9 => (orderedInterval (16038830780 / 1000000000000) (16038830781 / 1000000000000), orderedInterval (27125846847 / 1000000000000) (27125846848 / 1000000000000))
    | 10 => (orderedInterval (-2196280335 / 1000000000000) (-2196280333 / 1000000000000), orderedInterval (41432150273 / 1000000000000) (41432150275 / 1000000000000))
    | 11 => (orderedInterval (-15824592370 / 1000000000000) (-15824592369 / 1000000000000), orderedInterval (-26812107623 / 1000000000000) (-26812107622 / 1000000000000))
    | 12 => (orderedInterval (-31820668352 / 1000000000000) (-31820668210 / 1000000000000), orderedInterval (-5030947670 / 1000000000000) (-5030947528 / 1000000000000))
    | 13 => (orderedInterval (-37597410968 / 1000000000000) (-37597408325 / 1000000000000), orderedInterval (6454869991 / 1000000000000) (6454872635 / 1000000000000))
    | 14 => (orderedInterval (21563950354 / 1000000000000) (21563950355 / 1000000000000), orderedInterval (28577263978 / 1000000000000) (28577263979 / 1000000000000))
    | 15 => (orderedInterval (-7722737393 / 1000000000000) (-7722737381 / 1000000000000), orderedInterval (38469422731 / 1000000000000) (38469422743 / 1000000000000))
    | 16 => (orderedInterval (39716333852 / 1000000000000) (39716342022 / 1000000000000), orderedInterval (-12871546084 / 1000000000000) (-12871537914 / 1000000000000))
    | 17 => (orderedInterval (14465454063 / 1000000000000) (14465454221 / 1000000000000), orderedInterval (-31518731302 / 1000000000000) (-31518731144 / 1000000000000))
    | 18 => (orderedInterval (-46424244423 / 1000000000000) (-46424243989 / 1000000000000), orderedInterval (4230170124 / 1000000000000) (4230170558 / 1000000000000))
    | 19 => (orderedInterval (-43002701585 / 1000000000000) (-43002701584 / 1000000000000), orderedInterval (-26624546933 / 1000000000000) (-26624546932 / 1000000000000))
    | 20 => (orderedInterval (-47989816811 / 1000000000000) (-47989718750 / 1000000000000), orderedInterval (42490928973 / 1000000000000) (42491027034 / 1000000000000))
    | 21 => (orderedInterval (37098970790 / 1000000000000) (37098973553 / 1000000000000), orderedInterval (-79208101171 / 1000000000000) (-79208098408 / 1000000000000))
    | 22 => (orderedInterval (52956092591 / 1000000000000) (52956092686 / 1000000000000), orderedInterval (-625209171 / 1000000000000) (-625209075 / 1000000000000))
    | 23 => (orderedInterval (13260609182 / 1000000000000) (13260609298 / 1000000000000), orderedInterval (-43359555665 / 1000000000000) (-43359555548 / 1000000000000))
    | 24 => (orderedInterval (-7622190139 / 1000000000000) (-7622190111 / 1000000000000), orderedInterval (69308725475 / 1000000000000) (69308725503 / 1000000000000))
    | 25 => (orderedInterval (-18449347257 / 1000000000000) (-18449346410 / 1000000000000), orderedInterval (29251752560 / 1000000000000) (29251753408 / 1000000000000))
    | _ => (orderedInterval (-42248296455 / 1000000000000) (-42248296069 / 1000000000000), orderedInterval (2101815047 / 1000000000000) (2101815433 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-17859319322 / 1000000000000) (-17859319266 / 1000000000000)
      | 1 => orderedInterval (2828379322 / 1000000000000) (2828379416 / 1000000000000)
      | 2 => orderedInterval (-1312738789 / 1000000000000) (-1312737272 / 1000000000000)
      | 3 => orderedInterval (-5262191977 / 1000000000000) (-5262191863 / 1000000000000)
      | 4 => orderedInterval (-3089983703 / 1000000000000) (-3089983415 / 1000000000000)
      | 5 => orderedInterval (-1991641151 / 1000000000000) (-1991640651 / 1000000000000)
      | 6 => orderedInterval (8294515229 / 1000000000000) (8294518563 / 1000000000000)
      | 7 => orderedInterval (-2902722584 / 1000000000000) (-2902722487 / 1000000000000)
      | _ => orderedInterval (9382761543 / 1000000000000) (9382761765 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-5980243902 / 1000000000000) (-5980243838 / 1000000000000)
      | 1 => orderedInterval (1852251056 / 1000000000000) (1852251113 / 1000000000000)
      | 2 => orderedInterval (-52032489 / 1000000000000) (-52029491 / 1000000000000)
      | 3 => orderedInterval (-15546366636 / 1000000000000) (-15546366399 / 1000000000000)
      | 4 => orderedInterval (876307315 / 1000000000000) (876307758 / 1000000000000)
      | 5 => orderedInterval (89156240 / 1000000000000) (89156885 / 1000000000000)
      | 6 => orderedInterval (1365355054 / 1000000000000) (1365356924 / 1000000000000)
      | 7 => orderedInterval (4032868473 / 1000000000000) (4032868531 / 1000000000000)
      | _ => orderedInterval (-4726209874 / 1000000000000) (-4726209544 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (17213126746 / 1000000000000) (17213126820 / 1000000000000)
      | 1 => orderedInterval (-4291735500 / 1000000000000) (-4291735439 / 1000000000000)
      | 2 => orderedInterval (4320078162 / 1000000000000) (4320084099 / 1000000000000)
      | 3 => orderedInterval (26381113954 / 1000000000000) (26381114460 / 1000000000000)
      | 4 => orderedInterval (5988156647 / 1000000000000) (5988157335 / 1000000000000)
      | 5 => orderedInterval (2619063763 / 1000000000000) (2619064600 / 1000000000000)
      | 6 => orderedInterval (-9140523509 / 1000000000000) (-9140522427 / 1000000000000)
      | 7 => orderedInterval (1987739316 / 1000000000000) (1987739363 / 1000000000000)
      | _ => orderedInterval (-17394109562 / 1000000000000) (-17394109047 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (7030300143 / 1000000000000) (7030300230 / 1000000000000)
      | 1 => orderedInterval (-7697705711 / 1000000000000) (-7697705627 / 1000000000000)
      | 2 => orderedInterval (-1964082571 / 1000000000000) (-1964070835 / 1000000000000)
      | 3 => orderedInterval (93016905367 / 1000000000000) (93016906477 / 1000000000000)
      | 4 => orderedInterval (-2335676251 / 1000000000000) (-2335675177 / 1000000000000)
      | 5 => orderedInterval (2224268276 / 1000000000000) (2224269367 / 1000000000000)
      | 6 => orderedInterval (-447590606 / 1000000000000) (-447589957 / 1000000000000)
      | 7 => orderedInterval (-4257305928 / 1000000000000) (-4257305882 / 1000000000000)
      | _ => orderedInterval (16084094239 / 1000000000000) (16084095076 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-16494170372 / 1000000000000) (-16494170270 / 1000000000000)
      | 1 => orderedInterval (10041282331 / 1000000000000) (10041282458 / 1000000000000)
      | 2 => orderedInterval (-15157800669 / 1000000000000) (-15157777419 / 1000000000000)
      | 3 => orderedInterval (-134309361537 / 1000000000000) (-134309359074 / 1000000000000)
      | 4 => orderedInterval (-8264359364 / 1000000000000) (-8264357673 / 1000000000000)
      | 5 => orderedInterval (-2096859437 / 1000000000000) (-2096857998 / 1000000000000)
      | 6 => orderedInterval (9367910445 / 1000000000000) (9367910863 / 1000000000000)
      | 7 => orderedInterval (-1840491023 / 1000000000000) (-1840490976 / 1000000000000)
      | _ => orderedInterval (36700139011 / 1000000000000) (36700140419 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-11912941432 / 1000000000000) (-11912935210 / 1000000000000)
    | 1 => orderedInterval (-18088914763 / 1000000000000) (-18088908061 / 1000000000000)
    | 2 => orderedInterval (27682910017 / 1000000000000) (27682919764 / 1000000000000)
    | 3 => orderedInterval (101653206958 / 1000000000000) (101653223672 / 1000000000000)
    | _ => orderedInterval (-122053710615 / 1000000000000) (-122053679670 / 1000000000000)

theorem compactCertificate415_stateChecks0 :
    compactCertificate415.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 91 12 (573 / 2)) (orderedInterval (-46453043008 / 1000000000000) (-46453042998 / 1000000000000), orderedInterval (-7929557666 / 1000000000000) (-7929557656 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (844138413147273 / 4000000000000)) (orderedInterval (-53374597465 / 1000000000000) (-53374597463 / 1000000000000), orderedInterval (-12827514419 / 1000000000000) (-12827514417 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 109 12 (272977018893609 / 800000000000)) (orderedInterval (17899932705 / 1000000000000) (17899933232 / 1000000000000), orderedInterval (-39336574316 / 1000000000000) (-39336573789 / 1000000000000))) = true
  rfl'

theorem compactCertificate415_stateChecks1 :
    compactCertificate415.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 20 12 (246317483645211 / 4000000000000)) (orderedInterval (-45966962953 / 1000000000000) (-45966958663 / 1000000000000), orderedInterval (91067410349 / 1000000000000) (91067414639 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (661643408491167 / 4000000000000)) (orderedInterval (18861143522 / 1000000000000) (18861143884 / 1000000000000), orderedInterval (-59158534500 / 1000000000000) (-59158534137 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 143 12 (1796490562026339 / 4000000000000)) (orderedInterval (-23083773158 / 1000000000000) (-23083773157 / 1000000000000), orderedInterval (-29716760373 / 1000000000000) (-29716760372 / 1000000000000))) = true
  rfl'

theorem compactCertificate415_stateChecks2 :
    compactCertificate415.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 105 12 (1323286816982907 / 4000000000000)) (orderedInterval (-43244748048 / 1000000000000) (-43244746618 / 1000000000000), orderedInterval (7430743864 / 1000000000000) (7430745295 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 181 12 (2267474515601511 / 4000000000000)) (orderedInterval (27727730877 / 1000000000000) (27727779534 / 1000000000000), orderedInterval (-18845155414 / 1000000000000) (-18845106757 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 133 12 (1670211465488949 / 4000000000000)) (orderedInterval (-18930098069 / 1000000000000) (-18930098068 / 1000000000000), orderedInterval (-34128418271 / 1000000000000) (-34128418270 / 1000000000000))) = true
  rfl'

theorem compactCertificate415_stateChecks3 :
    compactCertificate415.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 204 12 (2562533902214427 / 4000000000000)) (orderedInterval (16038830780 / 1000000000000) (16038830781 / 1000000000000), orderedInterval (27125846847 / 1000000000000) (27125846848 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 118 12 (1479479638250883 / 4000000000000)) (orderedInterval (-2196280335 / 1000000000000) (-2196280333 / 1000000000000), orderedInterval (41432150273 / 1000000000000) (41432150275 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 209 12 (2625362580463647 / 4000000000000)) (orderedInterval (-15824592370 / 1000000000000) (-15824592369 / 1000000000000), orderedInterval (-26812107623 / 1000000000000) (-26812107622 / 1000000000000))) = true
  rfl'

theorem compactCertificate415_stateChecks4 :
    compactCertificate415.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 195 12 (2452954275746043 / 4000000000000)) (orderedInterval (-31820668352 / 1000000000000) (-31820668210 / 1000000000000), orderedInterval (-5030947670 / 1000000000000) (-5030947528 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 139 12 (1750543915472619 / 4000000000000)) (orderedInterval (-37597410968 / 1000000000000) (-37597408325 / 1000000000000), orderedInterval (6454869991 / 1000000000000) (6454872635 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 158 12 (1984930225473501 / 4000000000000)) (orderedInterval (21563950354 / 1000000000000) (21563950355 / 1000000000000), orderedInterval (28577263978 / 1000000000000) (28577263979 / 1000000000000))) = true
  rfl'

theorem compactCertificate415_stateChecks5 :
    compactCertificate415.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 132 12 (1654827882621069 / 4000000000000)) (orderedInterval (-7722737393 / 1000000000000) (-7722737381 / 1000000000000), orderedInterval (38469422731 / 1000000000000) (38469422743 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 116 12 (1462090620190449 / 4000000000000)) (orderedInterval (39716333852 / 1000000000000) (39716342022 / 1000000000000), orderedInterval (-12871546084 / 1000000000000) (-12871537914 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 169 12 (423770849450451 / 800000000000)) (orderedInterval (14465454063 / 1000000000000) (14465454221 / 1000000000000), orderedInterval (-31518731302 / 1000000000000) (-31518731144 / 1000000000000))) = true
  rfl'

theorem compactCertificate415_stateChecks6 :
    compactCertificate415.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 93 12 (1172172471417897 / 4000000000000)) (orderedInterval (-46424244423 / 1000000000000) (-46424243989 / 1000000000000), orderedInterval (4230170124 / 1000000000000) (4230170558 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (993663585475617 / 4000000000000)) (orderedInterval (-43002701585 / 1000000000000) (-43002701584 / 1000000000000), orderedInterval (-26624546933 / 1000000000000) (-26624546932 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (621788534511051 / 4000000000000)) (orderedInterval (-47989816811 / 1000000000000) (-47989718750 / 1000000000000), orderedInterval (42490928973 / 1000000000000) (42491027034 / 1000000000000))) = true
  rfl'

theorem compactCertificate415_stateChecks7 :
    compactCertificate415.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (334399941835317 / 4000000000000)) (orderedInterval (37098970790 / 1000000000000) (37098973553 / 1000000000000), orderedInterval (-79208101171 / 1000000000000) (-79208098408 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (907960892136951 / 4000000000000)) (orderedInterval (52956092591 / 1000000000000) (52956092686 / 1000000000000), orderedInterval (-625209171 / 1000000000000) (-625209075 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 99 12 (1239742974248727 / 4000000000000)) (orderedInterval (13260609182 / 1000000000000) (13260609298 / 1000000000000), orderedInterval (-43359555665 / 1000000000000) (-43359555548 / 1000000000000))) = true
  rfl'

theorem compactCertificate415_stateChecks8 :
    compactCertificate415.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (524211465488949 / 4000000000000)) (orderedInterval (-7622190139 / 1000000000000) (-7622190111 / 1000000000000), orderedInterval (69308725475 / 1000000000000) (69308725503 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 170 12 (2130890503862229 / 4000000000000)) (orderedInterval (-18449347257 / 1000000000000) (-18449346410 / 1000000000000), orderedInterval (29251752560 / 1000000000000) (29251753408 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 113 12 (1423336102454811 / 4000000000000)) (orderedInterval (-42248296455 / 1000000000000) (-42248296069 / 1000000000000), orderedInterval (2101815047 / 1000000000000) (2101815433 / 1000000000000))) = true
  rfl'

theorem compactCertificate415_states : ∀ j,
    BesselStateValid (compactCertificate415.point j) (compactCertificate415.state j) :=
  compactCertificate415.statesValid_of_checks3 compactCertificate415_stateChecks0
    compactCertificate415_stateChecks1 compactCertificate415_stateChecks2
    compactCertificate415_stateChecks3 compactCertificate415_stateChecks4
    compactCertificate415_stateChecks5 compactCertificate415_stateChecks6
    compactCertificate415_stateChecks7 compactCertificate415_stateChecks8

theorem compactCertificate415_chunkChecks0_0 :
    compactCertificate415.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (573 / 2) 0 (IntervalRat.scale (573 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-46453043008 / 1000000000000) (-46453042998 / 1000000000000), orderedInterval (-7929557666 / 1000000000000) (-7929557656 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (844138413147273 / 4000000000000) 0 (IntervalRat.scale (573 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-53374597465 / 1000000000000) (-53374597463 / 1000000000000), orderedInterval (-12827514419 / 1000000000000) (-12827514417 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (272977018893609 / 800000000000) 0 (IntervalRat.scale (573 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (17899932705 / 1000000000000) (17899933232 / 1000000000000), orderedInterval (-39336574316 / 1000000000000) (-39336573789 / 1000000000000)))) (orderedInterval (-17859319322 / 1000000000000) (-17859319266 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (246317483645211 / 4000000000000) 0 (IntervalRat.scale (573 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-45966962953 / 1000000000000) (-45966958663 / 1000000000000), orderedInterval (91067410349 / 1000000000000) (91067414639 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (661643408491167 / 4000000000000) 0 (IntervalRat.scale (573 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (18861143522 / 1000000000000) (18861143884 / 1000000000000), orderedInterval (-59158534500 / 1000000000000) (-59158534137 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1796490562026339 / 4000000000000) 0 (IntervalRat.scale (573 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-23083773158 / 1000000000000) (-23083773157 / 1000000000000), orderedInterval (-29716760373 / 1000000000000) (-29716760372 / 1000000000000)))) (orderedInterval (2828379322 / 1000000000000) (2828379416 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1323286816982907 / 4000000000000) 0 (IntervalRat.scale (573 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-43244748048 / 1000000000000) (-43244746618 / 1000000000000), orderedInterval (7430743864 / 1000000000000) (7430745295 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2267474515601511 / 4000000000000) 0 (IntervalRat.scale (573 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (27727730877 / 1000000000000) (27727779534 / 1000000000000), orderedInterval (-18845155414 / 1000000000000) (-18845106757 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1670211465488949 / 4000000000000) 0 (IntervalRat.scale (573 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-18930098069 / 1000000000000) (-18930098068 / 1000000000000), orderedInterval (-34128418271 / 1000000000000) (-34128418270 / 1000000000000)))) (orderedInterval (-1312738789 / 1000000000000) (-1312737272 / 1000000000000))) = true
  rfl'

theorem compactCertificate415_chunkChecks0_1 :
    compactCertificate415.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2562533902214427 / 4000000000000) 0 (IntervalRat.scale (573 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (16038830780 / 1000000000000) (16038830781 / 1000000000000), orderedInterval (27125846847 / 1000000000000) (27125846848 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1479479638250883 / 4000000000000) 0 (IntervalRat.scale (573 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-2196280335 / 1000000000000) (-2196280333 / 1000000000000), orderedInterval (41432150273 / 1000000000000) (41432150275 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2625362580463647 / 4000000000000) 0 (IntervalRat.scale (573 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-15824592370 / 1000000000000) (-15824592369 / 1000000000000), orderedInterval (-26812107623 / 1000000000000) (-26812107622 / 1000000000000)))) (orderedInterval (-5262191977 / 1000000000000) (-5262191863 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2452954275746043 / 4000000000000) 0 (IntervalRat.scale (573 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-31820668352 / 1000000000000) (-31820668210 / 1000000000000), orderedInterval (-5030947670 / 1000000000000) (-5030947528 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1750543915472619 / 4000000000000) 0 (IntervalRat.scale (573 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-37597410968 / 1000000000000) (-37597408325 / 1000000000000), orderedInterval (6454869991 / 1000000000000) (6454872635 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1984930225473501 / 4000000000000) 0 (IntervalRat.scale (573 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (21563950354 / 1000000000000) (21563950355 / 1000000000000), orderedInterval (28577263978 / 1000000000000) (28577263979 / 1000000000000)))) (orderedInterval (-3089983703 / 1000000000000) (-3089983415 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1654827882621069 / 4000000000000) 0 (IntervalRat.scale (573 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-7722737393 / 1000000000000) (-7722737381 / 1000000000000), orderedInterval (38469422731 / 1000000000000) (38469422743 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1462090620190449 / 4000000000000) 0 (IntervalRat.scale (573 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (39716333852 / 1000000000000) (39716342022 / 1000000000000), orderedInterval (-12871546084 / 1000000000000) (-12871537914 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (423770849450451 / 800000000000) 0 (IntervalRat.scale (573 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (14465454063 / 1000000000000) (14465454221 / 1000000000000), orderedInterval (-31518731302 / 1000000000000) (-31518731144 / 1000000000000)))) (orderedInterval (-1991641151 / 1000000000000) (-1991640651 / 1000000000000))) = true
  rfl'

theorem compactCertificate415_chunkChecks0_2 :
    compactCertificate415.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1172172471417897 / 4000000000000) 0 (IntervalRat.scale (573 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-46424244423 / 1000000000000) (-46424243989 / 1000000000000), orderedInterval (4230170124 / 1000000000000) (4230170558 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (993663585475617 / 4000000000000) 0 (IntervalRat.scale (573 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-43002701585 / 1000000000000) (-43002701584 / 1000000000000), orderedInterval (-26624546933 / 1000000000000) (-26624546932 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (621788534511051 / 4000000000000) 0 (IntervalRat.scale (573 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-47989816811 / 1000000000000) (-47989718750 / 1000000000000), orderedInterval (42490928973 / 1000000000000) (42491027034 / 1000000000000)))) (orderedInterval (8294515229 / 1000000000000) (8294518563 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (334399941835317 / 4000000000000) 0 (IntervalRat.scale (573 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (37098970790 / 1000000000000) (37098973553 / 1000000000000), orderedInterval (-79208101171 / 1000000000000) (-79208098408 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (907960892136951 / 4000000000000) 0 (IntervalRat.scale (573 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (52956092591 / 1000000000000) (52956092686 / 1000000000000), orderedInterval (-625209171 / 1000000000000) (-625209075 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1239742974248727 / 4000000000000) 0 (IntervalRat.scale (573 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (13260609182 / 1000000000000) (13260609298 / 1000000000000), orderedInterval (-43359555665 / 1000000000000) (-43359555548 / 1000000000000)))) (orderedInterval (-2902722584 / 1000000000000) (-2902722487 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (524211465488949 / 4000000000000) 0 (IntervalRat.scale (573 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-7622190139 / 1000000000000) (-7622190111 / 1000000000000), orderedInterval (69308725475 / 1000000000000) (69308725503 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2130890503862229 / 4000000000000) 0 (IntervalRat.scale (573 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-18449347257 / 1000000000000) (-18449346410 / 1000000000000), orderedInterval (29251752560 / 1000000000000) (29251753408 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1423336102454811 / 4000000000000) 0 (IntervalRat.scale (573 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-42248296455 / 1000000000000) (-42248296069 / 1000000000000), orderedInterval (2101815047 / 1000000000000) (2101815433 / 1000000000000)))) (orderedInterval (9382761543 / 1000000000000) (9382761765 / 1000000000000))) = true
  rfl'

theorem compactCertificate415_chunkChecks0 :
    compactCertificate415.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate415.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate415_chunkChecks0_0
    compactCertificate415_chunkChecks0_1 compactCertificate415_chunkChecks0_2

theorem compactCertificate415_chunkChecks1_0 :
    compactCertificate415.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (573 / 2) 1 (IntervalRat.scale (573 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-46453043008 / 1000000000000) (-46453042998 / 1000000000000), orderedInterval (-7929557666 / 1000000000000) (-7929557656 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (844138413147273 / 4000000000000) 1 (IntervalRat.scale (573 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-53374597465 / 1000000000000) (-53374597463 / 1000000000000), orderedInterval (-12827514419 / 1000000000000) (-12827514417 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (272977018893609 / 800000000000) 1 (IntervalRat.scale (573 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (17899932705 / 1000000000000) (17899933232 / 1000000000000), orderedInterval (-39336574316 / 1000000000000) (-39336573789 / 1000000000000)))) (orderedInterval (-5980243902 / 1000000000000) (-5980243838 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (246317483645211 / 4000000000000) 1 (IntervalRat.scale (573 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-45966962953 / 1000000000000) (-45966958663 / 1000000000000), orderedInterval (91067410349 / 1000000000000) (91067414639 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (661643408491167 / 4000000000000) 1 (IntervalRat.scale (573 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (18861143522 / 1000000000000) (18861143884 / 1000000000000), orderedInterval (-59158534500 / 1000000000000) (-59158534137 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1796490562026339 / 4000000000000) 1 (IntervalRat.scale (573 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-23083773158 / 1000000000000) (-23083773157 / 1000000000000), orderedInterval (-29716760373 / 1000000000000) (-29716760372 / 1000000000000)))) (orderedInterval (1852251056 / 1000000000000) (1852251113 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1323286816982907 / 4000000000000) 1 (IntervalRat.scale (573 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-43244748048 / 1000000000000) (-43244746618 / 1000000000000), orderedInterval (7430743864 / 1000000000000) (7430745295 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2267474515601511 / 4000000000000) 1 (IntervalRat.scale (573 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (27727730877 / 1000000000000) (27727779534 / 1000000000000), orderedInterval (-18845155414 / 1000000000000) (-18845106757 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1670211465488949 / 4000000000000) 1 (IntervalRat.scale (573 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-18930098069 / 1000000000000) (-18930098068 / 1000000000000), orderedInterval (-34128418271 / 1000000000000) (-34128418270 / 1000000000000)))) (orderedInterval (-52032489 / 1000000000000) (-52029491 / 1000000000000))) = true
  rfl'

theorem compactCertificate415_chunkChecks1_1 :
    compactCertificate415.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2562533902214427 / 4000000000000) 1 (IntervalRat.scale (573 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (16038830780 / 1000000000000) (16038830781 / 1000000000000), orderedInterval (27125846847 / 1000000000000) (27125846848 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1479479638250883 / 4000000000000) 1 (IntervalRat.scale (573 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-2196280335 / 1000000000000) (-2196280333 / 1000000000000), orderedInterval (41432150273 / 1000000000000) (41432150275 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2625362580463647 / 4000000000000) 1 (IntervalRat.scale (573 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-15824592370 / 1000000000000) (-15824592369 / 1000000000000), orderedInterval (-26812107623 / 1000000000000) (-26812107622 / 1000000000000)))) (orderedInterval (-15546366636 / 1000000000000) (-15546366399 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2452954275746043 / 4000000000000) 1 (IntervalRat.scale (573 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-31820668352 / 1000000000000) (-31820668210 / 1000000000000), orderedInterval (-5030947670 / 1000000000000) (-5030947528 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1750543915472619 / 4000000000000) 1 (IntervalRat.scale (573 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-37597410968 / 1000000000000) (-37597408325 / 1000000000000), orderedInterval (6454869991 / 1000000000000) (6454872635 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1984930225473501 / 4000000000000) 1 (IntervalRat.scale (573 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (21563950354 / 1000000000000) (21563950355 / 1000000000000), orderedInterval (28577263978 / 1000000000000) (28577263979 / 1000000000000)))) (orderedInterval (876307315 / 1000000000000) (876307758 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1654827882621069 / 4000000000000) 1 (IntervalRat.scale (573 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-7722737393 / 1000000000000) (-7722737381 / 1000000000000), orderedInterval (38469422731 / 1000000000000) (38469422743 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1462090620190449 / 4000000000000) 1 (IntervalRat.scale (573 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (39716333852 / 1000000000000) (39716342022 / 1000000000000), orderedInterval (-12871546084 / 1000000000000) (-12871537914 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (423770849450451 / 800000000000) 1 (IntervalRat.scale (573 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (14465454063 / 1000000000000) (14465454221 / 1000000000000), orderedInterval (-31518731302 / 1000000000000) (-31518731144 / 1000000000000)))) (orderedInterval (89156240 / 1000000000000) (89156885 / 1000000000000))) = true
  rfl'

theorem compactCertificate415_chunkChecks1_2 :
    compactCertificate415.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1172172471417897 / 4000000000000) 1 (IntervalRat.scale (573 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-46424244423 / 1000000000000) (-46424243989 / 1000000000000), orderedInterval (4230170124 / 1000000000000) (4230170558 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (993663585475617 / 4000000000000) 1 (IntervalRat.scale (573 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-43002701585 / 1000000000000) (-43002701584 / 1000000000000), orderedInterval (-26624546933 / 1000000000000) (-26624546932 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (621788534511051 / 4000000000000) 1 (IntervalRat.scale (573 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-47989816811 / 1000000000000) (-47989718750 / 1000000000000), orderedInterval (42490928973 / 1000000000000) (42491027034 / 1000000000000)))) (orderedInterval (1365355054 / 1000000000000) (1365356924 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (334399941835317 / 4000000000000) 1 (IntervalRat.scale (573 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (37098970790 / 1000000000000) (37098973553 / 1000000000000), orderedInterval (-79208101171 / 1000000000000) (-79208098408 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (907960892136951 / 4000000000000) 1 (IntervalRat.scale (573 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (52956092591 / 1000000000000) (52956092686 / 1000000000000), orderedInterval (-625209171 / 1000000000000) (-625209075 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1239742974248727 / 4000000000000) 1 (IntervalRat.scale (573 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (13260609182 / 1000000000000) (13260609298 / 1000000000000), orderedInterval (-43359555665 / 1000000000000) (-43359555548 / 1000000000000)))) (orderedInterval (4032868473 / 1000000000000) (4032868531 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (524211465488949 / 4000000000000) 1 (IntervalRat.scale (573 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-7622190139 / 1000000000000) (-7622190111 / 1000000000000), orderedInterval (69308725475 / 1000000000000) (69308725503 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2130890503862229 / 4000000000000) 1 (IntervalRat.scale (573 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-18449347257 / 1000000000000) (-18449346410 / 1000000000000), orderedInterval (29251752560 / 1000000000000) (29251753408 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1423336102454811 / 4000000000000) 1 (IntervalRat.scale (573 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-42248296455 / 1000000000000) (-42248296069 / 1000000000000), orderedInterval (2101815047 / 1000000000000) (2101815433 / 1000000000000)))) (orderedInterval (-4726209874 / 1000000000000) (-4726209544 / 1000000000000))) = true
  rfl'

theorem compactCertificate415_chunkChecks1 :
    compactCertificate415.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate415.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate415_chunkChecks1_0
    compactCertificate415_chunkChecks1_1 compactCertificate415_chunkChecks1_2

theorem compactCertificate415_chunkChecks2_0 :
    compactCertificate415.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (573 / 2) 2 (IntervalRat.scale (573 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-46453043008 / 1000000000000) (-46453042998 / 1000000000000), orderedInterval (-7929557666 / 1000000000000) (-7929557656 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (844138413147273 / 4000000000000) 2 (IntervalRat.scale (573 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-53374597465 / 1000000000000) (-53374597463 / 1000000000000), orderedInterval (-12827514419 / 1000000000000) (-12827514417 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (272977018893609 / 800000000000) 2 (IntervalRat.scale (573 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (17899932705 / 1000000000000) (17899933232 / 1000000000000), orderedInterval (-39336574316 / 1000000000000) (-39336573789 / 1000000000000)))) (orderedInterval (17213126746 / 1000000000000) (17213126820 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (246317483645211 / 4000000000000) 2 (IntervalRat.scale (573 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-45966962953 / 1000000000000) (-45966958663 / 1000000000000), orderedInterval (91067410349 / 1000000000000) (91067414639 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (661643408491167 / 4000000000000) 2 (IntervalRat.scale (573 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (18861143522 / 1000000000000) (18861143884 / 1000000000000), orderedInterval (-59158534500 / 1000000000000) (-59158534137 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1796490562026339 / 4000000000000) 2 (IntervalRat.scale (573 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-23083773158 / 1000000000000) (-23083773157 / 1000000000000), orderedInterval (-29716760373 / 1000000000000) (-29716760372 / 1000000000000)))) (orderedInterval (-4291735500 / 1000000000000) (-4291735439 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1323286816982907 / 4000000000000) 2 (IntervalRat.scale (573 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-43244748048 / 1000000000000) (-43244746618 / 1000000000000), orderedInterval (7430743864 / 1000000000000) (7430745295 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2267474515601511 / 4000000000000) 2 (IntervalRat.scale (573 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (27727730877 / 1000000000000) (27727779534 / 1000000000000), orderedInterval (-18845155414 / 1000000000000) (-18845106757 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1670211465488949 / 4000000000000) 2 (IntervalRat.scale (573 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-18930098069 / 1000000000000) (-18930098068 / 1000000000000), orderedInterval (-34128418271 / 1000000000000) (-34128418270 / 1000000000000)))) (orderedInterval (4320078162 / 1000000000000) (4320084099 / 1000000000000))) = true
  rfl'

theorem compactCertificate415_chunkChecks2_1 :
    compactCertificate415.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2562533902214427 / 4000000000000) 2 (IntervalRat.scale (573 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (16038830780 / 1000000000000) (16038830781 / 1000000000000), orderedInterval (27125846847 / 1000000000000) (27125846848 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1479479638250883 / 4000000000000) 2 (IntervalRat.scale (573 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-2196280335 / 1000000000000) (-2196280333 / 1000000000000), orderedInterval (41432150273 / 1000000000000) (41432150275 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2625362580463647 / 4000000000000) 2 (IntervalRat.scale (573 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-15824592370 / 1000000000000) (-15824592369 / 1000000000000), orderedInterval (-26812107623 / 1000000000000) (-26812107622 / 1000000000000)))) (orderedInterval (26381113954 / 1000000000000) (26381114460 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2452954275746043 / 4000000000000) 2 (IntervalRat.scale (573 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-31820668352 / 1000000000000) (-31820668210 / 1000000000000), orderedInterval (-5030947670 / 1000000000000) (-5030947528 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1750543915472619 / 4000000000000) 2 (IntervalRat.scale (573 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-37597410968 / 1000000000000) (-37597408325 / 1000000000000), orderedInterval (6454869991 / 1000000000000) (6454872635 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1984930225473501 / 4000000000000) 2 (IntervalRat.scale (573 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (21563950354 / 1000000000000) (21563950355 / 1000000000000), orderedInterval (28577263978 / 1000000000000) (28577263979 / 1000000000000)))) (orderedInterval (5988156647 / 1000000000000) (5988157335 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1654827882621069 / 4000000000000) 2 (IntervalRat.scale (573 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-7722737393 / 1000000000000) (-7722737381 / 1000000000000), orderedInterval (38469422731 / 1000000000000) (38469422743 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1462090620190449 / 4000000000000) 2 (IntervalRat.scale (573 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (39716333852 / 1000000000000) (39716342022 / 1000000000000), orderedInterval (-12871546084 / 1000000000000) (-12871537914 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (423770849450451 / 800000000000) 2 (IntervalRat.scale (573 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (14465454063 / 1000000000000) (14465454221 / 1000000000000), orderedInterval (-31518731302 / 1000000000000) (-31518731144 / 1000000000000)))) (orderedInterval (2619063763 / 1000000000000) (2619064600 / 1000000000000))) = true
  rfl'

theorem compactCertificate415_chunkChecks2_2 :
    compactCertificate415.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1172172471417897 / 4000000000000) 2 (IntervalRat.scale (573 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-46424244423 / 1000000000000) (-46424243989 / 1000000000000), orderedInterval (4230170124 / 1000000000000) (4230170558 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (993663585475617 / 4000000000000) 2 (IntervalRat.scale (573 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-43002701585 / 1000000000000) (-43002701584 / 1000000000000), orderedInterval (-26624546933 / 1000000000000) (-26624546932 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (621788534511051 / 4000000000000) 2 (IntervalRat.scale (573 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-47989816811 / 1000000000000) (-47989718750 / 1000000000000), orderedInterval (42490928973 / 1000000000000) (42491027034 / 1000000000000)))) (orderedInterval (-9140523509 / 1000000000000) (-9140522427 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (334399941835317 / 4000000000000) 2 (IntervalRat.scale (573 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (37098970790 / 1000000000000) (37098973553 / 1000000000000), orderedInterval (-79208101171 / 1000000000000) (-79208098408 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (907960892136951 / 4000000000000) 2 (IntervalRat.scale (573 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (52956092591 / 1000000000000) (52956092686 / 1000000000000), orderedInterval (-625209171 / 1000000000000) (-625209075 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1239742974248727 / 4000000000000) 2 (IntervalRat.scale (573 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (13260609182 / 1000000000000) (13260609298 / 1000000000000), orderedInterval (-43359555665 / 1000000000000) (-43359555548 / 1000000000000)))) (orderedInterval (1987739316 / 1000000000000) (1987739363 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (524211465488949 / 4000000000000) 2 (IntervalRat.scale (573 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-7622190139 / 1000000000000) (-7622190111 / 1000000000000), orderedInterval (69308725475 / 1000000000000) (69308725503 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2130890503862229 / 4000000000000) 2 (IntervalRat.scale (573 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-18449347257 / 1000000000000) (-18449346410 / 1000000000000), orderedInterval (29251752560 / 1000000000000) (29251753408 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1423336102454811 / 4000000000000) 2 (IntervalRat.scale (573 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-42248296455 / 1000000000000) (-42248296069 / 1000000000000), orderedInterval (2101815047 / 1000000000000) (2101815433 / 1000000000000)))) (orderedInterval (-17394109562 / 1000000000000) (-17394109047 / 1000000000000))) = true
  rfl'

theorem compactCertificate415_chunkChecks2 :
    compactCertificate415.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate415.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate415_chunkChecks2_0
    compactCertificate415_chunkChecks2_1 compactCertificate415_chunkChecks2_2

theorem compactCertificate415_chunkChecks3_0 :
    compactCertificate415.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (573 / 2) 3 (IntervalRat.scale (573 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-46453043008 / 1000000000000) (-46453042998 / 1000000000000), orderedInterval (-7929557666 / 1000000000000) (-7929557656 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (844138413147273 / 4000000000000) 3 (IntervalRat.scale (573 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-53374597465 / 1000000000000) (-53374597463 / 1000000000000), orderedInterval (-12827514419 / 1000000000000) (-12827514417 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (272977018893609 / 800000000000) 3 (IntervalRat.scale (573 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (17899932705 / 1000000000000) (17899933232 / 1000000000000), orderedInterval (-39336574316 / 1000000000000) (-39336573789 / 1000000000000)))) (orderedInterval (7030300143 / 1000000000000) (7030300230 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (246317483645211 / 4000000000000) 3 (IntervalRat.scale (573 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-45966962953 / 1000000000000) (-45966958663 / 1000000000000), orderedInterval (91067410349 / 1000000000000) (91067414639 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (661643408491167 / 4000000000000) 3 (IntervalRat.scale (573 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (18861143522 / 1000000000000) (18861143884 / 1000000000000), orderedInterval (-59158534500 / 1000000000000) (-59158534137 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1796490562026339 / 4000000000000) 3 (IntervalRat.scale (573 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-23083773158 / 1000000000000) (-23083773157 / 1000000000000), orderedInterval (-29716760373 / 1000000000000) (-29716760372 / 1000000000000)))) (orderedInterval (-7697705711 / 1000000000000) (-7697705627 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1323286816982907 / 4000000000000) 3 (IntervalRat.scale (573 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-43244748048 / 1000000000000) (-43244746618 / 1000000000000), orderedInterval (7430743864 / 1000000000000) (7430745295 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2267474515601511 / 4000000000000) 3 (IntervalRat.scale (573 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (27727730877 / 1000000000000) (27727779534 / 1000000000000), orderedInterval (-18845155414 / 1000000000000) (-18845106757 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1670211465488949 / 4000000000000) 3 (IntervalRat.scale (573 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-18930098069 / 1000000000000) (-18930098068 / 1000000000000), orderedInterval (-34128418271 / 1000000000000) (-34128418270 / 1000000000000)))) (orderedInterval (-1964082571 / 1000000000000) (-1964070835 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate415_chunkChecks3_1 :
    compactCertificate415.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2562533902214427 / 4000000000000) 3 (IntervalRat.scale (573 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (16038830780 / 1000000000000) (16038830781 / 1000000000000), orderedInterval (27125846847 / 1000000000000) (27125846848 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1479479638250883 / 4000000000000) 3 (IntervalRat.scale (573 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-2196280335 / 1000000000000) (-2196280333 / 1000000000000), orderedInterval (41432150273 / 1000000000000) (41432150275 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2625362580463647 / 4000000000000) 3 (IntervalRat.scale (573 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-15824592370 / 1000000000000) (-15824592369 / 1000000000000), orderedInterval (-26812107623 / 1000000000000) (-26812107622 / 1000000000000)))) (orderedInterval (93016905367 / 1000000000000) (93016906477 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2452954275746043 / 4000000000000) 3 (IntervalRat.scale (573 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-31820668352 / 1000000000000) (-31820668210 / 1000000000000), orderedInterval (-5030947670 / 1000000000000) (-5030947528 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1750543915472619 / 4000000000000) 3 (IntervalRat.scale (573 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-37597410968 / 1000000000000) (-37597408325 / 1000000000000), orderedInterval (6454869991 / 1000000000000) (6454872635 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1984930225473501 / 4000000000000) 3 (IntervalRat.scale (573 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (21563950354 / 1000000000000) (21563950355 / 1000000000000), orderedInterval (28577263978 / 1000000000000) (28577263979 / 1000000000000)))) (orderedInterval (-2335676251 / 1000000000000) (-2335675177 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1654827882621069 / 4000000000000) 3 (IntervalRat.scale (573 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-7722737393 / 1000000000000) (-7722737381 / 1000000000000), orderedInterval (38469422731 / 1000000000000) (38469422743 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1462090620190449 / 4000000000000) 3 (IntervalRat.scale (573 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (39716333852 / 1000000000000) (39716342022 / 1000000000000), orderedInterval (-12871546084 / 1000000000000) (-12871537914 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (423770849450451 / 800000000000) 3 (IntervalRat.scale (573 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (14465454063 / 1000000000000) (14465454221 / 1000000000000), orderedInterval (-31518731302 / 1000000000000) (-31518731144 / 1000000000000)))) (orderedInterval (2224268276 / 1000000000000) (2224269367 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate415_chunkChecks3_2 :
    compactCertificate415.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1172172471417897 / 4000000000000) 3 (IntervalRat.scale (573 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-46424244423 / 1000000000000) (-46424243989 / 1000000000000), orderedInterval (4230170124 / 1000000000000) (4230170558 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (993663585475617 / 4000000000000) 3 (IntervalRat.scale (573 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-43002701585 / 1000000000000) (-43002701584 / 1000000000000), orderedInterval (-26624546933 / 1000000000000) (-26624546932 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (621788534511051 / 4000000000000) 3 (IntervalRat.scale (573 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-47989816811 / 1000000000000) (-47989718750 / 1000000000000), orderedInterval (42490928973 / 1000000000000) (42491027034 / 1000000000000)))) (orderedInterval (-447590606 / 1000000000000) (-447589957 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (334399941835317 / 4000000000000) 3 (IntervalRat.scale (573 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (37098970790 / 1000000000000) (37098973553 / 1000000000000), orderedInterval (-79208101171 / 1000000000000) (-79208098408 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (907960892136951 / 4000000000000) 3 (IntervalRat.scale (573 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (52956092591 / 1000000000000) (52956092686 / 1000000000000), orderedInterval (-625209171 / 1000000000000) (-625209075 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1239742974248727 / 4000000000000) 3 (IntervalRat.scale (573 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (13260609182 / 1000000000000) (13260609298 / 1000000000000), orderedInterval (-43359555665 / 1000000000000) (-43359555548 / 1000000000000)))) (orderedInterval (-4257305928 / 1000000000000) (-4257305882 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (524211465488949 / 4000000000000) 3 (IntervalRat.scale (573 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-7622190139 / 1000000000000) (-7622190111 / 1000000000000), orderedInterval (69308725475 / 1000000000000) (69308725503 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2130890503862229 / 4000000000000) 3 (IntervalRat.scale (573 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-18449347257 / 1000000000000) (-18449346410 / 1000000000000), orderedInterval (29251752560 / 1000000000000) (29251753408 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1423336102454811 / 4000000000000) 3 (IntervalRat.scale (573 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-42248296455 / 1000000000000) (-42248296069 / 1000000000000), orderedInterval (2101815047 / 1000000000000) (2101815433 / 1000000000000)))) (orderedInterval (16084094239 / 1000000000000) (16084095076 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate415_chunkChecks3 :
    compactCertificate415.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate415.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate415_chunkChecks3_0
    compactCertificate415_chunkChecks3_1 compactCertificate415_chunkChecks3_2

theorem compactCertificate415_chunkChecks4_0 :
    compactCertificate415.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (573 / 2) 4 (IntervalRat.scale (573 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-46453043008 / 1000000000000) (-46453042998 / 1000000000000), orderedInterval (-7929557666 / 1000000000000) (-7929557656 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (844138413147273 / 4000000000000) 4 (IntervalRat.scale (573 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-53374597465 / 1000000000000) (-53374597463 / 1000000000000), orderedInterval (-12827514419 / 1000000000000) (-12827514417 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (272977018893609 / 800000000000) 4 (IntervalRat.scale (573 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (17899932705 / 1000000000000) (17899933232 / 1000000000000), orderedInterval (-39336574316 / 1000000000000) (-39336573789 / 1000000000000)))) (orderedInterval (-16494170372 / 1000000000000) (-16494170270 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (246317483645211 / 4000000000000) 4 (IntervalRat.scale (573 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-45966962953 / 1000000000000) (-45966958663 / 1000000000000), orderedInterval (91067410349 / 1000000000000) (91067414639 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (661643408491167 / 4000000000000) 4 (IntervalRat.scale (573 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (18861143522 / 1000000000000) (18861143884 / 1000000000000), orderedInterval (-59158534500 / 1000000000000) (-59158534137 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1796490562026339 / 4000000000000) 4 (IntervalRat.scale (573 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-23083773158 / 1000000000000) (-23083773157 / 1000000000000), orderedInterval (-29716760373 / 1000000000000) (-29716760372 / 1000000000000)))) (orderedInterval (10041282331 / 1000000000000) (10041282458 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1323286816982907 / 4000000000000) 4 (IntervalRat.scale (573 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-43244748048 / 1000000000000) (-43244746618 / 1000000000000), orderedInterval (7430743864 / 1000000000000) (7430745295 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2267474515601511 / 4000000000000) 4 (IntervalRat.scale (573 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (27727730877 / 1000000000000) (27727779534 / 1000000000000), orderedInterval (-18845155414 / 1000000000000) (-18845106757 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1670211465488949 / 4000000000000) 4 (IntervalRat.scale (573 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-18930098069 / 1000000000000) (-18930098068 / 1000000000000), orderedInterval (-34128418271 / 1000000000000) (-34128418270 / 1000000000000)))) (orderedInterval (-15157800669 / 1000000000000) (-15157777419 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate415_chunkChecks4_1 :
    compactCertificate415.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2562533902214427 / 4000000000000) 4 (IntervalRat.scale (573 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (16038830780 / 1000000000000) (16038830781 / 1000000000000), orderedInterval (27125846847 / 1000000000000) (27125846848 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1479479638250883 / 4000000000000) 4 (IntervalRat.scale (573 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-2196280335 / 1000000000000) (-2196280333 / 1000000000000), orderedInterval (41432150273 / 1000000000000) (41432150275 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2625362580463647 / 4000000000000) 4 (IntervalRat.scale (573 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-15824592370 / 1000000000000) (-15824592369 / 1000000000000), orderedInterval (-26812107623 / 1000000000000) (-26812107622 / 1000000000000)))) (orderedInterval (-134309361537 / 1000000000000) (-134309359074 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2452954275746043 / 4000000000000) 4 (IntervalRat.scale (573 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-31820668352 / 1000000000000) (-31820668210 / 1000000000000), orderedInterval (-5030947670 / 1000000000000) (-5030947528 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1750543915472619 / 4000000000000) 4 (IntervalRat.scale (573 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-37597410968 / 1000000000000) (-37597408325 / 1000000000000), orderedInterval (6454869991 / 1000000000000) (6454872635 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1984930225473501 / 4000000000000) 4 (IntervalRat.scale (573 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (21563950354 / 1000000000000) (21563950355 / 1000000000000), orderedInterval (28577263978 / 1000000000000) (28577263979 / 1000000000000)))) (orderedInterval (-8264359364 / 1000000000000) (-8264357673 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1654827882621069 / 4000000000000) 4 (IntervalRat.scale (573 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-7722737393 / 1000000000000) (-7722737381 / 1000000000000), orderedInterval (38469422731 / 1000000000000) (38469422743 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1462090620190449 / 4000000000000) 4 (IntervalRat.scale (573 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (39716333852 / 1000000000000) (39716342022 / 1000000000000), orderedInterval (-12871546084 / 1000000000000) (-12871537914 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (423770849450451 / 800000000000) 4 (IntervalRat.scale (573 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (14465454063 / 1000000000000) (14465454221 / 1000000000000), orderedInterval (-31518731302 / 1000000000000) (-31518731144 / 1000000000000)))) (orderedInterval (-2096859437 / 1000000000000) (-2096857998 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate415_chunkChecks4_2 :
    compactCertificate415.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1172172471417897 / 4000000000000) 4 (IntervalRat.scale (573 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-46424244423 / 1000000000000) (-46424243989 / 1000000000000), orderedInterval (4230170124 / 1000000000000) (4230170558 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (993663585475617 / 4000000000000) 4 (IntervalRat.scale (573 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-43002701585 / 1000000000000) (-43002701584 / 1000000000000), orderedInterval (-26624546933 / 1000000000000) (-26624546932 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (621788534511051 / 4000000000000) 4 (IntervalRat.scale (573 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-47989816811 / 1000000000000) (-47989718750 / 1000000000000), orderedInterval (42490928973 / 1000000000000) (42491027034 / 1000000000000)))) (orderedInterval (9367910445 / 1000000000000) (9367910863 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (334399941835317 / 4000000000000) 4 (IntervalRat.scale (573 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (37098970790 / 1000000000000) (37098973553 / 1000000000000), orderedInterval (-79208101171 / 1000000000000) (-79208098408 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (907960892136951 / 4000000000000) 4 (IntervalRat.scale (573 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (52956092591 / 1000000000000) (52956092686 / 1000000000000), orderedInterval (-625209171 / 1000000000000) (-625209075 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1239742974248727 / 4000000000000) 4 (IntervalRat.scale (573 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (13260609182 / 1000000000000) (13260609298 / 1000000000000), orderedInterval (-43359555665 / 1000000000000) (-43359555548 / 1000000000000)))) (orderedInterval (-1840491023 / 1000000000000) (-1840490976 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (524211465488949 / 4000000000000) 4 (IntervalRat.scale (573 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-7622190139 / 1000000000000) (-7622190111 / 1000000000000), orderedInterval (69308725475 / 1000000000000) (69308725503 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2130890503862229 / 4000000000000) 4 (IntervalRat.scale (573 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-18449347257 / 1000000000000) (-18449346410 / 1000000000000), orderedInterval (29251752560 / 1000000000000) (29251753408 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1423336102454811 / 4000000000000) 4 (IntervalRat.scale (573 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-42248296455 / 1000000000000) (-42248296069 / 1000000000000), orderedInterval (2101815047 / 1000000000000) (2101815433 / 1000000000000)))) (orderedInterval (36700139011 / 1000000000000) (36700140419 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate415_chunkChecks4 :
    compactCertificate415.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate415.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate415_chunkChecks4_0
    compactCertificate415_chunkChecks4_1 compactCertificate415_chunkChecks4_2

theorem compactCertificate415_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate415.chunkCheck r b = true :=
  compactCertificate415.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate415_chunkChecks0
    · exact compactCertificate415_chunkChecks1
    · exact compactCertificate415_chunkChecks2
    · exact compactCertificate415_chunkChecks3
    · exact compactCertificate415_chunkChecks4)

theorem compactCertificate415_coefficient0 :
    compactCertificate415.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate415_coefficient1 :
    compactCertificate415.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate415_coefficient2 :
    compactCertificate415.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate415_coefficient3 :
    compactCertificate415.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate415_coefficient4 :
    compactCertificate415.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate415_coefficients : ∀ r : Fin 5,
    compactCertificate415.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate415_coefficient0
  · exact compactCertificate415_coefficient1
  · exact compactCertificate415_coefficient2
  · exact compactCertificate415_coefficient3
  · exact compactCertificate415_coefficient4

theorem compactCertificate415_lower : (1 : ℚ) ≤ compactCertificate415.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate415, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate415_proves {t : ℝ} (ht : t ∈ compactCertificate415.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate415.proves compactCertificate415_states compactCertificate415_chunks
    compactCertificate415_coefficients compactCertificate415_lower ht

end Erdos232
