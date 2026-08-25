/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate532 : CompactCertificate where
  left := 403
  right := 404
  center := 807 / 2
  grid := fun i =>
    match i.val with
    | 0 => 129
    | 1 => 95
    | 2 => 153
    | 3 => 28
    | 4 => 74
    | 5 => 201
    | 6 => 148
    | 7 => 254
    | 8 => 187
    | 9 => 287
    | 10 => 166
    | 11 => 294
    | 12 => 275
    | 13 => 196
    | 14 => 223
    | 15 => 186
    | 16 => 164
    | 17 => 238
    | 18 => 131
    | 19 => 111
    | 20 => 70
    | 21 => 37
    | 22 => 102
    | 23 => 139
    | 24 => 59
    | 25 => 239
    | _ => 160
  point := fun i =>
    match i.val with
    | 0 => 807 / 2
    | 1 => 1188865094956107 / 4000000000000
    | 2 => 384454544933931 / 800000000000
    | 3 => 346907869636449 / 4000000000000
    | 4 => 931843334471853 / 4000000000000
    | 5 => 2530135922435001 / 4000000000000
    | 6 => 1863686668944513 / 4000000000000
    | 7 => 3193458872758149 / 4000000000000
    | 8 => 2352287351918991 / 4000000000000
    | 9 => 3609013715684193 / 4000000000000
    | 10 => 2083665040259097 / 4000000000000
    | 11 => 3697500178768173 / 4000000000000
    | 12 => 3454684294113537 / 4000000000000
    | 13 => 2465425723885521 / 4000000000000
    | 14 => 2795530003415559 / 4000000000000
    | 15 => 2330621468194071 / 4000000000000
    | 16 => 2059174747807491 / 4000000000000
    | 17 => 596829102105609 / 800000000000
    | 18 => 1650860705818923 / 4000000000000
    | 19 => 1399452903104403 / 4000000000000
    | 20 => 875712648081009 / 4000000000000
    | 21 => 470961174626703 / 4000000000000
    | 22 => 1278751204109109 / 4000000000000
    | 23 => 1746025445407893 / 4000000000000
    | 24 => 738287351918991 / 4000000000000
    | 25 => 3001097097062511 / 4000000000000
    | _ => 2004593777802849 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (32996026694 / 1000000000000) (32996130776 / 1000000000000), orderedInterval (-22154336496 / 1000000000000) (-22154232414 / 1000000000000))
    | 1 => (orderedInterval (20132788262 / 1000000000000) (20132789176 / 1000000000000), orderedInterval (-41706568594 / 1000000000000) (-41706567680 / 1000000000000))
    | 2 => (orderedInterval (-23157859239 / 1000000000000) (-23157859238 / 1000000000000), orderedInterval (-28055022490 / 1000000000000) (-28055022489 / 1000000000000))
    | 3 => (orderedInterval (-37548996768 / 1000000000000) (-37548993581 / 1000000000000), orderedInterval (77227205349 / 1000000000000) (77227208536 / 1000000000000))
    | 4 => (orderedInterval (49894775485 / 1000000000000) (49894775487 / 1000000000000), orderedInterval (15489042077 / 1000000000000) (15489042079 / 1000000000000))
    | 5 => (orderedInterval (-30415774641 / 1000000000000) (-30415750536 / 1000000000000), orderedInterval (9042927669 / 1000000000000) (9042951773 / 1000000000000))
    | 6 => (orderedInterval (36365267269 / 1000000000000) (36365270769 / 1000000000000), orderedInterval (-6667224149 / 1000000000000) (-6667220649 / 1000000000000))
    | 7 => (orderedInterval (26167328962 / 1000000000000) (26167328982 / 1000000000000), orderedInterval (10598482358 / 1000000000000) (10598482378 / 1000000000000))
    | 8 => (orderedInterval (-32300111866 / 1000000000000) (-32300111792 / 1000000000000), orderedInterval (-6238065334 / 1000000000000) (-6238065261 / 1000000000000))
    | 9 => (orderedInterval (-26183595934 / 1000000000000) (-26183595126 / 1000000000000), orderedInterval (-4458505525 / 1000000000000) (-4458504717 / 1000000000000))
    | 10 => (orderedInterval (6843711260 / 1000000000000) (6843711261 / 1000000000000), orderedInterval (34275780987 / 1000000000000) (34275780988 / 1000000000000))
    | 11 => (orderedInterval (26223466656 / 1000000000000) (26223470698 / 1000000000000), orderedInterval (1001926673 / 1000000000000) (1001930715 / 1000000000000))
    | 12 => (orderedInterval (-13451212026 / 1000000000000) (-13451212025 / 1000000000000), orderedInterval (-23575554711 / 1000000000000) (-23575554710 / 1000000000000))
    | 13 => (orderedInterval (31611464522 / 1000000000000) (31611464626 / 1000000000000), orderedInterval (5770130608 / 1000000000000) (5770130712 / 1000000000000))
    | 14 => (orderedInterval (23780771902 / 1000000000000) (23780785982 / 1000000000000), orderedInterval (-18601570643 / 1000000000000) (-18601556563 / 1000000000000))
    | 15 => (orderedInterval (-25803754125 / 1000000000000) (-25803732039 / 1000000000000), orderedInterval (20680902323 / 1000000000000) (20680924409 / 1000000000000))
    | 16 => (orderedInterval (12310614591 / 1000000000000) (12310614592 / 1000000000000), orderedInterval (32928891948 / 1000000000000) (32928891949 / 1000000000000))
    | 17 => (orderedInterval (-22467102037 / 1000000000000) (-22467093786 / 1000000000000), orderedInterval (18684964304 / 1000000000000) (18684972555 / 1000000000000))
    | 18 => (orderedInterval (-36460968709 / 1000000000000) (-36460948505 / 1000000000000), orderedInterval (14642575200 / 1000000000000) (14642595404 / 1000000000000))
    | 19 => (orderedInterval (-39912277286 / 1000000000000) (-39912265039 / 1000000000000), orderedInterval (15111398701 / 1000000000000) (15111410948 / 1000000000000))
    | 20 => (orderedInterval (-10633736727 / 1000000000000) (-10633736672 / 1000000000000), orderedInterval (52890381745 / 1000000000000) (52890381800 / 1000000000000))
    | 21 => (orderedInterval (-55528005830 / 1000000000000) (-55527901494 / 1000000000000), orderedInterval (48439713107 / 1000000000000) (48439817443 / 1000000000000))
    | 22 => (orderedInterval (1354491692 / 1000000000000) (1354491694 / 1000000000000), orderedInterval (44602224442 / 1000000000000) (44602224444 / 1000000000000))
    | 23 => (orderedInterval (-21880506777 / 1000000000000) (-21880506776 / 1000000000000), orderedInterval (-31274889511 / 1000000000000) (-31274889510 / 1000000000000))
    | 24 => (orderedInterval (-152247255 / 1000000000000) (-152247251 / 1000000000000), orderedInterval (-58729138552 / 1000000000000) (-58729138548 / 1000000000000))
    | 25 => (orderedInterval (-6324510039 / 1000000000000) (-6324510038 / 1000000000000), orderedInterval (-28430215128 / 1000000000000) (-28430215127 / 1000000000000))
    | _ => (orderedInterval (-23534482073 / 1000000000000) (-23534476134 / 1000000000000), orderedInterval (26790063517 / 1000000000000) (26790069456 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (11907138824 / 1000000000000) (11907180116 / 1000000000000)
      | 1 => orderedInterval (4391370089 / 1000000000000) (4391371886 / 1000000000000)
      | 2 => orderedInterval (-1587735109 / 1000000000000) (-1587735083 / 1000000000000)
      | 3 => orderedInterval (8887391614 / 1000000000000) (8887392493 / 1000000000000)
      | 4 => orderedInterval (3111762072 / 1000000000000) (3111762202 / 1000000000000)
      | 5 => orderedInterval (-1577715379 / 1000000000000) (-1577714874 / 1000000000000)
      | 6 => orderedInterval (7742678308 / 1000000000000) (7742682334 / 1000000000000)
      | 7 => orderedInterval (2671497322 / 1000000000000) (2671499297 / 1000000000000)
      | _ => orderedInterval (4929600525 / 1000000000000) (4929601752 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-11028205189 / 1000000000000) (-11028163896 / 1000000000000)
      | 1 => orderedInterval (-861336374 / 1000000000000) (-861333625 / 1000000000000)
      | 2 => orderedInterval (-866527495 / 1000000000000) (-866527452 / 1000000000000)
      | 3 => orderedInterval (5376303619 / 1000000000000) (5376305588 / 1000000000000)
      | 4 => orderedInterval (1907524498 / 1000000000000) (1907524714 / 1000000000000)
      | 5 => orderedInterval (-1174782980 / 1000000000000) (-1174782165 / 1000000000000)
      | 6 => orderedInterval (-2202085431 / 1000000000000) (-2202081430 / 1000000000000)
      | 7 => orderedInterval (1530236371 / 1000000000000) (1530236977 / 1000000000000)
      | _ => orderedInterval (-2101722019 / 1000000000000) (-2101720477 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-11225352550 / 1000000000000) (-11225311152 / 1000000000000)
      | 1 => orderedInterval (-5937497059 / 1000000000000) (-5937492763 / 1000000000000)
      | 2 => orderedInterval (4819977644 / 1000000000000) (4819977721 / 1000000000000)
      | 3 => orderedInterval (-43685276361 / 1000000000000) (-43685271913 / 1000000000000)
      | 4 => orderedInterval (-7731216942 / 1000000000000) (-7731216575 / 1000000000000)
      | 5 => orderedInterval (3737416756 / 1000000000000) (3737418096 / 1000000000000)
      | 6 => orderedInterval (-7690159053 / 1000000000000) (-7690155052 / 1000000000000)
      | 7 => orderedInterval (-2034264571 / 1000000000000) (-2034264362 / 1000000000000)
      | _ => orderedInterval (-8586102482 / 1000000000000) (-8586100528 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (11745503361 / 1000000000000) (11745544763 / 1000000000000)
      | 1 => orderedInterval (2390681239 / 1000000000000) (2390687966 / 1000000000000)
      | 2 => orderedInterval (2986904456 / 1000000000000) (2986904594 / 1000000000000)
      | 3 => orderedInterval (-15925713333 / 1000000000000) (-15925703253 / 1000000000000)
      | 4 => orderedInterval (-6588514311 / 1000000000000) (-6588513686 / 1000000000000)
      | 5 => orderedInterval (161207078 / 1000000000000) (161209313 / 1000000000000)
      | 6 => orderedInterval (2806908223 / 1000000000000) (2806912229 / 1000000000000)
      | 7 => orderedInterval (-2503974353 / 1000000000000) (-2503974260 / 1000000000000)
      | _ => orderedInterval (-5192587957 / 1000000000000) (-5192585460 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (10341129914 / 1000000000000) (10341171424 / 1000000000000)
      | 1 => orderedInterval (13249083106 / 1000000000000) (13249093663 / 1000000000000)
      | 2 => orderedInterval (-15906562296 / 1000000000000) (-15906562042 / 1000000000000)
      | 3 => orderedInterval (220477008907 / 1000000000000) (220477031822 / 1000000000000)
      | 4 => orderedInterval (20321633298 / 1000000000000) (20321634375 / 1000000000000)
      | 5 => orderedInterval (-9885183527 / 1000000000000) (-9885179736 / 1000000000000)
      | 6 => orderedInterval (7613816332 / 1000000000000) (7613820365 / 1000000000000)
      | 7 => orderedInterval (2304372907 / 1000000000000) (2304372968 / 1000000000000)
      | _ => orderedInterval (16687053594 / 1000000000000) (16687056831 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (40475988266 / 1000000000000) (40476040123 / 1000000000000)
    | 1 => orderedInterval (-9420595000 / 1000000000000) (-9420541766 / 1000000000000)
    | 2 => orderedInterval (-78332474618 / 1000000000000) (-78332416528 / 1000000000000)
    | 3 => orderedInterval (-10119585597 / 1000000000000) (-10119517794 / 1000000000000)
    | _ => orderedInterval (265202352235 / 1000000000000) (265202439670 / 1000000000000)

theorem compactCertificate532_stateChecks0 :
    compactCertificate532.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 129 12 (807 / 2)) (orderedInterval (32996026694 / 1000000000000) (32996130776 / 1000000000000), orderedInterval (-22154336496 / 1000000000000) (-22154232414 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 95 12 (1188865094956107 / 4000000000000)) (orderedInterval (20132788262 / 1000000000000) (20132789176 / 1000000000000), orderedInterval (-41706568594 / 1000000000000) (-41706567680 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 153 12 (384454544933931 / 800000000000)) (orderedInterval (-23157859239 / 1000000000000) (-23157859238 / 1000000000000), orderedInterval (-28055022490 / 1000000000000) (-28055022489 / 1000000000000))) = true
  rfl'

theorem compactCertificate532_stateChecks1 :
    compactCertificate532.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 28 12 (346907869636449 / 4000000000000)) (orderedInterval (-37548996768 / 1000000000000) (-37548993581 / 1000000000000), orderedInterval (77227205349 / 1000000000000) (77227208536 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (931843334471853 / 4000000000000)) (orderedInterval (49894775485 / 1000000000000) (49894775487 / 1000000000000), orderedInterval (15489042077 / 1000000000000) (15489042079 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 201 12 (2530135922435001 / 4000000000000)) (orderedInterval (-30415774641 / 1000000000000) (-30415750536 / 1000000000000), orderedInterval (9042927669 / 1000000000000) (9042951773 / 1000000000000))) = true
  rfl'

theorem compactCertificate532_stateChecks2 :
    compactCertificate532.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 148 12 (1863686668944513 / 4000000000000)) (orderedInterval (36365267269 / 1000000000000) (36365270769 / 1000000000000), orderedInterval (-6667224149 / 1000000000000) (-6667220649 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 254 12 (3193458872758149 / 4000000000000)) (orderedInterval (26167328962 / 1000000000000) (26167328982 / 1000000000000), orderedInterval (10598482358 / 1000000000000) (10598482378 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 187 12 (2352287351918991 / 4000000000000)) (orderedInterval (-32300111866 / 1000000000000) (-32300111792 / 1000000000000), orderedInterval (-6238065334 / 1000000000000) (-6238065261 / 1000000000000))) = true
  rfl'

theorem compactCertificate532_stateChecks3 :
    compactCertificate532.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 287 12 (3609013715684193 / 4000000000000)) (orderedInterval (-26183595934 / 1000000000000) (-26183595126 / 1000000000000), orderedInterval (-4458505525 / 1000000000000) (-4458504717 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 166 12 (2083665040259097 / 4000000000000)) (orderedInterval (6843711260 / 1000000000000) (6843711261 / 1000000000000), orderedInterval (34275780987 / 1000000000000) (34275780988 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 294 12 (3697500178768173 / 4000000000000)) (orderedInterval (26223466656 / 1000000000000) (26223470698 / 1000000000000), orderedInterval (1001926673 / 1000000000000) (1001930715 / 1000000000000))) = true
  rfl'

theorem compactCertificate532_stateChecks4 :
    compactCertificate532.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 275 12 (3454684294113537 / 4000000000000)) (orderedInterval (-13451212026 / 1000000000000) (-13451212025 / 1000000000000), orderedInterval (-23575554711 / 1000000000000) (-23575554710 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 196 12 (2465425723885521 / 4000000000000)) (orderedInterval (31611464522 / 1000000000000) (31611464626 / 1000000000000), orderedInterval (5770130608 / 1000000000000) (5770130712 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 223 12 (2795530003415559 / 4000000000000)) (orderedInterval (23780771902 / 1000000000000) (23780785982 / 1000000000000), orderedInterval (-18601570643 / 1000000000000) (-18601556563 / 1000000000000))) = true
  rfl'

theorem compactCertificate532_stateChecks5 :
    compactCertificate532.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 186 12 (2330621468194071 / 4000000000000)) (orderedInterval (-25803754125 / 1000000000000) (-25803732039 / 1000000000000), orderedInterval (20680902323 / 1000000000000) (20680924409 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 164 12 (2059174747807491 / 4000000000000)) (orderedInterval (12310614591 / 1000000000000) (12310614592 / 1000000000000), orderedInterval (32928891948 / 1000000000000) (32928891949 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 238 12 (596829102105609 / 800000000000)) (orderedInterval (-22467102037 / 1000000000000) (-22467093786 / 1000000000000), orderedInterval (18684964304 / 1000000000000) (18684972555 / 1000000000000))) = true
  rfl'

theorem compactCertificate532_stateChecks6 :
    compactCertificate532.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 131 12 (1650860705818923 / 4000000000000)) (orderedInterval (-36460968709 / 1000000000000) (-36460948505 / 1000000000000), orderedInterval (14642575200 / 1000000000000) (14642595404 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 111 12 (1399452903104403 / 4000000000000)) (orderedInterval (-39912277286 / 1000000000000) (-39912265039 / 1000000000000), orderedInterval (15111398701 / 1000000000000) (15111410948 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (875712648081009 / 4000000000000)) (orderedInterval (-10633736727 / 1000000000000) (-10633736672 / 1000000000000), orderedInterval (52890381745 / 1000000000000) (52890381800 / 1000000000000))) = true
  rfl'

theorem compactCertificate532_stateChecks7 :
    compactCertificate532.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (470961174626703 / 4000000000000)) (orderedInterval (-55528005830 / 1000000000000) (-55527901494 / 1000000000000), orderedInterval (48439713107 / 1000000000000) (48439817443 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 102 12 (1278751204109109 / 4000000000000)) (orderedInterval (1354491692 / 1000000000000) (1354491694 / 1000000000000), orderedInterval (44602224442 / 1000000000000) (44602224444 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 139 12 (1746025445407893 / 4000000000000)) (orderedInterval (-21880506777 / 1000000000000) (-21880506776 / 1000000000000), orderedInterval (-31274889511 / 1000000000000) (-31274889510 / 1000000000000))) = true
  rfl'

theorem compactCertificate532_stateChecks8 :
    compactCertificate532.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (738287351918991 / 4000000000000)) (orderedInterval (-152247255 / 1000000000000) (-152247251 / 1000000000000), orderedInterval (-58729138552 / 1000000000000) (-58729138548 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 239 12 (3001097097062511 / 4000000000000)) (orderedInterval (-6324510039 / 1000000000000) (-6324510038 / 1000000000000), orderedInterval (-28430215128 / 1000000000000) (-28430215127 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 160 12 (2004593777802849 / 4000000000000)) (orderedInterval (-23534482073 / 1000000000000) (-23534476134 / 1000000000000), orderedInterval (26790063517 / 1000000000000) (26790069456 / 1000000000000))) = true
  rfl'

theorem compactCertificate532_states : ∀ j,
    BesselStateValid (compactCertificate532.point j) (compactCertificate532.state j) :=
  compactCertificate532.statesValid_of_checks3 compactCertificate532_stateChecks0
    compactCertificate532_stateChecks1 compactCertificate532_stateChecks2
    compactCertificate532_stateChecks3 compactCertificate532_stateChecks4
    compactCertificate532_stateChecks5 compactCertificate532_stateChecks6
    compactCertificate532_stateChecks7 compactCertificate532_stateChecks8

theorem compactCertificate532_chunkChecks0_0 :
    compactCertificate532.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (807 / 2) 0 (IntervalRat.scale (807 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (32996026694 / 1000000000000) (32996130776 / 1000000000000), orderedInterval (-22154336496 / 1000000000000) (-22154232414 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1188865094956107 / 4000000000000) 0 (IntervalRat.scale (807 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (20132788262 / 1000000000000) (20132789176 / 1000000000000), orderedInterval (-41706568594 / 1000000000000) (-41706567680 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (384454544933931 / 800000000000) 0 (IntervalRat.scale (807 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-23157859239 / 1000000000000) (-23157859238 / 1000000000000), orderedInterval (-28055022490 / 1000000000000) (-28055022489 / 1000000000000)))) (orderedInterval (11907138824 / 1000000000000) (11907180116 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (346907869636449 / 4000000000000) 0 (IntervalRat.scale (807 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-37548996768 / 1000000000000) (-37548993581 / 1000000000000), orderedInterval (77227205349 / 1000000000000) (77227208536 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (931843334471853 / 4000000000000) 0 (IntervalRat.scale (807 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (49894775485 / 1000000000000) (49894775487 / 1000000000000), orderedInterval (15489042077 / 1000000000000) (15489042079 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2530135922435001 / 4000000000000) 0 (IntervalRat.scale (807 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30415774641 / 1000000000000) (-30415750536 / 1000000000000), orderedInterval (9042927669 / 1000000000000) (9042951773 / 1000000000000)))) (orderedInterval (4391370089 / 1000000000000) (4391371886 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1863686668944513 / 4000000000000) 0 (IntervalRat.scale (807 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (36365267269 / 1000000000000) (36365270769 / 1000000000000), orderedInterval (-6667224149 / 1000000000000) (-6667220649 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3193458872758149 / 4000000000000) 0 (IntervalRat.scale (807 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (26167328962 / 1000000000000) (26167328982 / 1000000000000), orderedInterval (10598482358 / 1000000000000) (10598482378 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2352287351918991 / 4000000000000) 0 (IntervalRat.scale (807 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-32300111866 / 1000000000000) (-32300111792 / 1000000000000), orderedInterval (-6238065334 / 1000000000000) (-6238065261 / 1000000000000)))) (orderedInterval (-1587735109 / 1000000000000) (-1587735083 / 1000000000000))) = true
  rfl'

theorem compactCertificate532_chunkChecks0_1 :
    compactCertificate532.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3609013715684193 / 4000000000000) 0 (IntervalRat.scale (807 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-26183595934 / 1000000000000) (-26183595126 / 1000000000000), orderedInterval (-4458505525 / 1000000000000) (-4458504717 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2083665040259097 / 4000000000000) 0 (IntervalRat.scale (807 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (6843711260 / 1000000000000) (6843711261 / 1000000000000), orderedInterval (34275780987 / 1000000000000) (34275780988 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3697500178768173 / 4000000000000) 0 (IntervalRat.scale (807 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (26223466656 / 1000000000000) (26223470698 / 1000000000000), orderedInterval (1001926673 / 1000000000000) (1001930715 / 1000000000000)))) (orderedInterval (8887391614 / 1000000000000) (8887392493 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3454684294113537 / 4000000000000) 0 (IntervalRat.scale (807 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-13451212026 / 1000000000000) (-13451212025 / 1000000000000), orderedInterval (-23575554711 / 1000000000000) (-23575554710 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2465425723885521 / 4000000000000) 0 (IntervalRat.scale (807 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (31611464522 / 1000000000000) (31611464626 / 1000000000000), orderedInterval (5770130608 / 1000000000000) (5770130712 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2795530003415559 / 4000000000000) 0 (IntervalRat.scale (807 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (23780771902 / 1000000000000) (23780785982 / 1000000000000), orderedInterval (-18601570643 / 1000000000000) (-18601556563 / 1000000000000)))) (orderedInterval (3111762072 / 1000000000000) (3111762202 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2330621468194071 / 4000000000000) 0 (IntervalRat.scale (807 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-25803754125 / 1000000000000) (-25803732039 / 1000000000000), orderedInterval (20680902323 / 1000000000000) (20680924409 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2059174747807491 / 4000000000000) 0 (IntervalRat.scale (807 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (12310614591 / 1000000000000) (12310614592 / 1000000000000), orderedInterval (32928891948 / 1000000000000) (32928891949 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (596829102105609 / 800000000000) 0 (IntervalRat.scale (807 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-22467102037 / 1000000000000) (-22467093786 / 1000000000000), orderedInterval (18684964304 / 1000000000000) (18684972555 / 1000000000000)))) (orderedInterval (-1577715379 / 1000000000000) (-1577714874 / 1000000000000))) = true
  rfl'

theorem compactCertificate532_chunkChecks0_2 :
    compactCertificate532.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1650860705818923 / 4000000000000) 0 (IntervalRat.scale (807 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-36460968709 / 1000000000000) (-36460948505 / 1000000000000), orderedInterval (14642575200 / 1000000000000) (14642595404 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1399452903104403 / 4000000000000) 0 (IntervalRat.scale (807 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-39912277286 / 1000000000000) (-39912265039 / 1000000000000), orderedInterval (15111398701 / 1000000000000) (15111410948 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (875712648081009 / 4000000000000) 0 (IntervalRat.scale (807 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-10633736727 / 1000000000000) (-10633736672 / 1000000000000), orderedInterval (52890381745 / 1000000000000) (52890381800 / 1000000000000)))) (orderedInterval (7742678308 / 1000000000000) (7742682334 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (470961174626703 / 4000000000000) 0 (IntervalRat.scale (807 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-55528005830 / 1000000000000) (-55527901494 / 1000000000000), orderedInterval (48439713107 / 1000000000000) (48439817443 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1278751204109109 / 4000000000000) 0 (IntervalRat.scale (807 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (1354491692 / 1000000000000) (1354491694 / 1000000000000), orderedInterval (44602224442 / 1000000000000) (44602224444 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1746025445407893 / 4000000000000) 0 (IntervalRat.scale (807 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-21880506777 / 1000000000000) (-21880506776 / 1000000000000), orderedInterval (-31274889511 / 1000000000000) (-31274889510 / 1000000000000)))) (orderedInterval (2671497322 / 1000000000000) (2671499297 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (738287351918991 / 4000000000000) 0 (IntervalRat.scale (807 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-152247255 / 1000000000000) (-152247251 / 1000000000000), orderedInterval (-58729138552 / 1000000000000) (-58729138548 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3001097097062511 / 4000000000000) 0 (IntervalRat.scale (807 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-6324510039 / 1000000000000) (-6324510038 / 1000000000000), orderedInterval (-28430215128 / 1000000000000) (-28430215127 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2004593777802849 / 4000000000000) 0 (IntervalRat.scale (807 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-23534482073 / 1000000000000) (-23534476134 / 1000000000000), orderedInterval (26790063517 / 1000000000000) (26790069456 / 1000000000000)))) (orderedInterval (4929600525 / 1000000000000) (4929601752 / 1000000000000))) = true
  rfl'

theorem compactCertificate532_chunkChecks0 :
    compactCertificate532.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate532.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate532_chunkChecks0_0
    compactCertificate532_chunkChecks0_1 compactCertificate532_chunkChecks0_2

theorem compactCertificate532_chunkChecks1_0 :
    compactCertificate532.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (807 / 2) 1 (IntervalRat.scale (807 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (32996026694 / 1000000000000) (32996130776 / 1000000000000), orderedInterval (-22154336496 / 1000000000000) (-22154232414 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1188865094956107 / 4000000000000) 1 (IntervalRat.scale (807 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (20132788262 / 1000000000000) (20132789176 / 1000000000000), orderedInterval (-41706568594 / 1000000000000) (-41706567680 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (384454544933931 / 800000000000) 1 (IntervalRat.scale (807 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-23157859239 / 1000000000000) (-23157859238 / 1000000000000), orderedInterval (-28055022490 / 1000000000000) (-28055022489 / 1000000000000)))) (orderedInterval (-11028205189 / 1000000000000) (-11028163896 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (346907869636449 / 4000000000000) 1 (IntervalRat.scale (807 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-37548996768 / 1000000000000) (-37548993581 / 1000000000000), orderedInterval (77227205349 / 1000000000000) (77227208536 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (931843334471853 / 4000000000000) 1 (IntervalRat.scale (807 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (49894775485 / 1000000000000) (49894775487 / 1000000000000), orderedInterval (15489042077 / 1000000000000) (15489042079 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2530135922435001 / 4000000000000) 1 (IntervalRat.scale (807 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30415774641 / 1000000000000) (-30415750536 / 1000000000000), orderedInterval (9042927669 / 1000000000000) (9042951773 / 1000000000000)))) (orderedInterval (-861336374 / 1000000000000) (-861333625 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1863686668944513 / 4000000000000) 1 (IntervalRat.scale (807 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (36365267269 / 1000000000000) (36365270769 / 1000000000000), orderedInterval (-6667224149 / 1000000000000) (-6667220649 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3193458872758149 / 4000000000000) 1 (IntervalRat.scale (807 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (26167328962 / 1000000000000) (26167328982 / 1000000000000), orderedInterval (10598482358 / 1000000000000) (10598482378 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2352287351918991 / 4000000000000) 1 (IntervalRat.scale (807 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-32300111866 / 1000000000000) (-32300111792 / 1000000000000), orderedInterval (-6238065334 / 1000000000000) (-6238065261 / 1000000000000)))) (orderedInterval (-866527495 / 1000000000000) (-866527452 / 1000000000000))) = true
  rfl'

theorem compactCertificate532_chunkChecks1_1 :
    compactCertificate532.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3609013715684193 / 4000000000000) 1 (IntervalRat.scale (807 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-26183595934 / 1000000000000) (-26183595126 / 1000000000000), orderedInterval (-4458505525 / 1000000000000) (-4458504717 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2083665040259097 / 4000000000000) 1 (IntervalRat.scale (807 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (6843711260 / 1000000000000) (6843711261 / 1000000000000), orderedInterval (34275780987 / 1000000000000) (34275780988 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3697500178768173 / 4000000000000) 1 (IntervalRat.scale (807 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (26223466656 / 1000000000000) (26223470698 / 1000000000000), orderedInterval (1001926673 / 1000000000000) (1001930715 / 1000000000000)))) (orderedInterval (5376303619 / 1000000000000) (5376305588 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3454684294113537 / 4000000000000) 1 (IntervalRat.scale (807 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-13451212026 / 1000000000000) (-13451212025 / 1000000000000), orderedInterval (-23575554711 / 1000000000000) (-23575554710 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2465425723885521 / 4000000000000) 1 (IntervalRat.scale (807 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (31611464522 / 1000000000000) (31611464626 / 1000000000000), orderedInterval (5770130608 / 1000000000000) (5770130712 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2795530003415559 / 4000000000000) 1 (IntervalRat.scale (807 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (23780771902 / 1000000000000) (23780785982 / 1000000000000), orderedInterval (-18601570643 / 1000000000000) (-18601556563 / 1000000000000)))) (orderedInterval (1907524498 / 1000000000000) (1907524714 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2330621468194071 / 4000000000000) 1 (IntervalRat.scale (807 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-25803754125 / 1000000000000) (-25803732039 / 1000000000000), orderedInterval (20680902323 / 1000000000000) (20680924409 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2059174747807491 / 4000000000000) 1 (IntervalRat.scale (807 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (12310614591 / 1000000000000) (12310614592 / 1000000000000), orderedInterval (32928891948 / 1000000000000) (32928891949 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (596829102105609 / 800000000000) 1 (IntervalRat.scale (807 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-22467102037 / 1000000000000) (-22467093786 / 1000000000000), orderedInterval (18684964304 / 1000000000000) (18684972555 / 1000000000000)))) (orderedInterval (-1174782980 / 1000000000000) (-1174782165 / 1000000000000))) = true
  rfl'

theorem compactCertificate532_chunkChecks1_2 :
    compactCertificate532.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1650860705818923 / 4000000000000) 1 (IntervalRat.scale (807 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-36460968709 / 1000000000000) (-36460948505 / 1000000000000), orderedInterval (14642575200 / 1000000000000) (14642595404 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1399452903104403 / 4000000000000) 1 (IntervalRat.scale (807 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-39912277286 / 1000000000000) (-39912265039 / 1000000000000), orderedInterval (15111398701 / 1000000000000) (15111410948 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (875712648081009 / 4000000000000) 1 (IntervalRat.scale (807 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-10633736727 / 1000000000000) (-10633736672 / 1000000000000), orderedInterval (52890381745 / 1000000000000) (52890381800 / 1000000000000)))) (orderedInterval (-2202085431 / 1000000000000) (-2202081430 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (470961174626703 / 4000000000000) 1 (IntervalRat.scale (807 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-55528005830 / 1000000000000) (-55527901494 / 1000000000000), orderedInterval (48439713107 / 1000000000000) (48439817443 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1278751204109109 / 4000000000000) 1 (IntervalRat.scale (807 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (1354491692 / 1000000000000) (1354491694 / 1000000000000), orderedInterval (44602224442 / 1000000000000) (44602224444 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1746025445407893 / 4000000000000) 1 (IntervalRat.scale (807 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-21880506777 / 1000000000000) (-21880506776 / 1000000000000), orderedInterval (-31274889511 / 1000000000000) (-31274889510 / 1000000000000)))) (orderedInterval (1530236371 / 1000000000000) (1530236977 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (738287351918991 / 4000000000000) 1 (IntervalRat.scale (807 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-152247255 / 1000000000000) (-152247251 / 1000000000000), orderedInterval (-58729138552 / 1000000000000) (-58729138548 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3001097097062511 / 4000000000000) 1 (IntervalRat.scale (807 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-6324510039 / 1000000000000) (-6324510038 / 1000000000000), orderedInterval (-28430215128 / 1000000000000) (-28430215127 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2004593777802849 / 4000000000000) 1 (IntervalRat.scale (807 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-23534482073 / 1000000000000) (-23534476134 / 1000000000000), orderedInterval (26790063517 / 1000000000000) (26790069456 / 1000000000000)))) (orderedInterval (-2101722019 / 1000000000000) (-2101720477 / 1000000000000))) = true
  rfl'

theorem compactCertificate532_chunkChecks1 :
    compactCertificate532.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate532.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate532_chunkChecks1_0
    compactCertificate532_chunkChecks1_1 compactCertificate532_chunkChecks1_2

theorem compactCertificate532_chunkChecks2_0 :
    compactCertificate532.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (807 / 2) 2 (IntervalRat.scale (807 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (32996026694 / 1000000000000) (32996130776 / 1000000000000), orderedInterval (-22154336496 / 1000000000000) (-22154232414 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1188865094956107 / 4000000000000) 2 (IntervalRat.scale (807 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (20132788262 / 1000000000000) (20132789176 / 1000000000000), orderedInterval (-41706568594 / 1000000000000) (-41706567680 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (384454544933931 / 800000000000) 2 (IntervalRat.scale (807 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-23157859239 / 1000000000000) (-23157859238 / 1000000000000), orderedInterval (-28055022490 / 1000000000000) (-28055022489 / 1000000000000)))) (orderedInterval (-11225352550 / 1000000000000) (-11225311152 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (346907869636449 / 4000000000000) 2 (IntervalRat.scale (807 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-37548996768 / 1000000000000) (-37548993581 / 1000000000000), orderedInterval (77227205349 / 1000000000000) (77227208536 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (931843334471853 / 4000000000000) 2 (IntervalRat.scale (807 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (49894775485 / 1000000000000) (49894775487 / 1000000000000), orderedInterval (15489042077 / 1000000000000) (15489042079 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2530135922435001 / 4000000000000) 2 (IntervalRat.scale (807 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30415774641 / 1000000000000) (-30415750536 / 1000000000000), orderedInterval (9042927669 / 1000000000000) (9042951773 / 1000000000000)))) (orderedInterval (-5937497059 / 1000000000000) (-5937492763 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1863686668944513 / 4000000000000) 2 (IntervalRat.scale (807 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (36365267269 / 1000000000000) (36365270769 / 1000000000000), orderedInterval (-6667224149 / 1000000000000) (-6667220649 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3193458872758149 / 4000000000000) 2 (IntervalRat.scale (807 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (26167328962 / 1000000000000) (26167328982 / 1000000000000), orderedInterval (10598482358 / 1000000000000) (10598482378 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2352287351918991 / 4000000000000) 2 (IntervalRat.scale (807 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-32300111866 / 1000000000000) (-32300111792 / 1000000000000), orderedInterval (-6238065334 / 1000000000000) (-6238065261 / 1000000000000)))) (orderedInterval (4819977644 / 1000000000000) (4819977721 / 1000000000000))) = true
  rfl'

theorem compactCertificate532_chunkChecks2_1 :
    compactCertificate532.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3609013715684193 / 4000000000000) 2 (IntervalRat.scale (807 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-26183595934 / 1000000000000) (-26183595126 / 1000000000000), orderedInterval (-4458505525 / 1000000000000) (-4458504717 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2083665040259097 / 4000000000000) 2 (IntervalRat.scale (807 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (6843711260 / 1000000000000) (6843711261 / 1000000000000), orderedInterval (34275780987 / 1000000000000) (34275780988 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3697500178768173 / 4000000000000) 2 (IntervalRat.scale (807 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (26223466656 / 1000000000000) (26223470698 / 1000000000000), orderedInterval (1001926673 / 1000000000000) (1001930715 / 1000000000000)))) (orderedInterval (-43685276361 / 1000000000000) (-43685271913 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3454684294113537 / 4000000000000) 2 (IntervalRat.scale (807 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-13451212026 / 1000000000000) (-13451212025 / 1000000000000), orderedInterval (-23575554711 / 1000000000000) (-23575554710 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2465425723885521 / 4000000000000) 2 (IntervalRat.scale (807 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (31611464522 / 1000000000000) (31611464626 / 1000000000000), orderedInterval (5770130608 / 1000000000000) (5770130712 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2795530003415559 / 4000000000000) 2 (IntervalRat.scale (807 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (23780771902 / 1000000000000) (23780785982 / 1000000000000), orderedInterval (-18601570643 / 1000000000000) (-18601556563 / 1000000000000)))) (orderedInterval (-7731216942 / 1000000000000) (-7731216575 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2330621468194071 / 4000000000000) 2 (IntervalRat.scale (807 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-25803754125 / 1000000000000) (-25803732039 / 1000000000000), orderedInterval (20680902323 / 1000000000000) (20680924409 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2059174747807491 / 4000000000000) 2 (IntervalRat.scale (807 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (12310614591 / 1000000000000) (12310614592 / 1000000000000), orderedInterval (32928891948 / 1000000000000) (32928891949 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (596829102105609 / 800000000000) 2 (IntervalRat.scale (807 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-22467102037 / 1000000000000) (-22467093786 / 1000000000000), orderedInterval (18684964304 / 1000000000000) (18684972555 / 1000000000000)))) (orderedInterval (3737416756 / 1000000000000) (3737418096 / 1000000000000))) = true
  rfl'

theorem compactCertificate532_chunkChecks2_2 :
    compactCertificate532.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1650860705818923 / 4000000000000) 2 (IntervalRat.scale (807 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-36460968709 / 1000000000000) (-36460948505 / 1000000000000), orderedInterval (14642575200 / 1000000000000) (14642595404 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1399452903104403 / 4000000000000) 2 (IntervalRat.scale (807 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-39912277286 / 1000000000000) (-39912265039 / 1000000000000), orderedInterval (15111398701 / 1000000000000) (15111410948 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (875712648081009 / 4000000000000) 2 (IntervalRat.scale (807 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-10633736727 / 1000000000000) (-10633736672 / 1000000000000), orderedInterval (52890381745 / 1000000000000) (52890381800 / 1000000000000)))) (orderedInterval (-7690159053 / 1000000000000) (-7690155052 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (470961174626703 / 4000000000000) 2 (IntervalRat.scale (807 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-55528005830 / 1000000000000) (-55527901494 / 1000000000000), orderedInterval (48439713107 / 1000000000000) (48439817443 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1278751204109109 / 4000000000000) 2 (IntervalRat.scale (807 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (1354491692 / 1000000000000) (1354491694 / 1000000000000), orderedInterval (44602224442 / 1000000000000) (44602224444 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1746025445407893 / 4000000000000) 2 (IntervalRat.scale (807 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-21880506777 / 1000000000000) (-21880506776 / 1000000000000), orderedInterval (-31274889511 / 1000000000000) (-31274889510 / 1000000000000)))) (orderedInterval (-2034264571 / 1000000000000) (-2034264362 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (738287351918991 / 4000000000000) 2 (IntervalRat.scale (807 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-152247255 / 1000000000000) (-152247251 / 1000000000000), orderedInterval (-58729138552 / 1000000000000) (-58729138548 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3001097097062511 / 4000000000000) 2 (IntervalRat.scale (807 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-6324510039 / 1000000000000) (-6324510038 / 1000000000000), orderedInterval (-28430215128 / 1000000000000) (-28430215127 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2004593777802849 / 4000000000000) 2 (IntervalRat.scale (807 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-23534482073 / 1000000000000) (-23534476134 / 1000000000000), orderedInterval (26790063517 / 1000000000000) (26790069456 / 1000000000000)))) (orderedInterval (-8586102482 / 1000000000000) (-8586100528 / 1000000000000))) = true
  rfl'

theorem compactCertificate532_chunkChecks2 :
    compactCertificate532.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate532.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate532_chunkChecks2_0
    compactCertificate532_chunkChecks2_1 compactCertificate532_chunkChecks2_2

theorem compactCertificate532_chunkChecks3_0 :
    compactCertificate532.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (807 / 2) 3 (IntervalRat.scale (807 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (32996026694 / 1000000000000) (32996130776 / 1000000000000), orderedInterval (-22154336496 / 1000000000000) (-22154232414 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1188865094956107 / 4000000000000) 3 (IntervalRat.scale (807 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (20132788262 / 1000000000000) (20132789176 / 1000000000000), orderedInterval (-41706568594 / 1000000000000) (-41706567680 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (384454544933931 / 800000000000) 3 (IntervalRat.scale (807 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-23157859239 / 1000000000000) (-23157859238 / 1000000000000), orderedInterval (-28055022490 / 1000000000000) (-28055022489 / 1000000000000)))) (orderedInterval (11745503361 / 1000000000000) (11745544763 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (346907869636449 / 4000000000000) 3 (IntervalRat.scale (807 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-37548996768 / 1000000000000) (-37548993581 / 1000000000000), orderedInterval (77227205349 / 1000000000000) (77227208536 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (931843334471853 / 4000000000000) 3 (IntervalRat.scale (807 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (49894775485 / 1000000000000) (49894775487 / 1000000000000), orderedInterval (15489042077 / 1000000000000) (15489042079 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2530135922435001 / 4000000000000) 3 (IntervalRat.scale (807 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30415774641 / 1000000000000) (-30415750536 / 1000000000000), orderedInterval (9042927669 / 1000000000000) (9042951773 / 1000000000000)))) (orderedInterval (2390681239 / 1000000000000) (2390687966 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1863686668944513 / 4000000000000) 3 (IntervalRat.scale (807 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (36365267269 / 1000000000000) (36365270769 / 1000000000000), orderedInterval (-6667224149 / 1000000000000) (-6667220649 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3193458872758149 / 4000000000000) 3 (IntervalRat.scale (807 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (26167328962 / 1000000000000) (26167328982 / 1000000000000), orderedInterval (10598482358 / 1000000000000) (10598482378 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2352287351918991 / 4000000000000) 3 (IntervalRat.scale (807 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-32300111866 / 1000000000000) (-32300111792 / 1000000000000), orderedInterval (-6238065334 / 1000000000000) (-6238065261 / 1000000000000)))) (orderedInterval (2986904456 / 1000000000000) (2986904594 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate532_chunkChecks3_1 :
    compactCertificate532.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3609013715684193 / 4000000000000) 3 (IntervalRat.scale (807 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-26183595934 / 1000000000000) (-26183595126 / 1000000000000), orderedInterval (-4458505525 / 1000000000000) (-4458504717 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2083665040259097 / 4000000000000) 3 (IntervalRat.scale (807 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (6843711260 / 1000000000000) (6843711261 / 1000000000000), orderedInterval (34275780987 / 1000000000000) (34275780988 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3697500178768173 / 4000000000000) 3 (IntervalRat.scale (807 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (26223466656 / 1000000000000) (26223470698 / 1000000000000), orderedInterval (1001926673 / 1000000000000) (1001930715 / 1000000000000)))) (orderedInterval (-15925713333 / 1000000000000) (-15925703253 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3454684294113537 / 4000000000000) 3 (IntervalRat.scale (807 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-13451212026 / 1000000000000) (-13451212025 / 1000000000000), orderedInterval (-23575554711 / 1000000000000) (-23575554710 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2465425723885521 / 4000000000000) 3 (IntervalRat.scale (807 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (31611464522 / 1000000000000) (31611464626 / 1000000000000), orderedInterval (5770130608 / 1000000000000) (5770130712 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2795530003415559 / 4000000000000) 3 (IntervalRat.scale (807 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (23780771902 / 1000000000000) (23780785982 / 1000000000000), orderedInterval (-18601570643 / 1000000000000) (-18601556563 / 1000000000000)))) (orderedInterval (-6588514311 / 1000000000000) (-6588513686 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2330621468194071 / 4000000000000) 3 (IntervalRat.scale (807 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-25803754125 / 1000000000000) (-25803732039 / 1000000000000), orderedInterval (20680902323 / 1000000000000) (20680924409 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2059174747807491 / 4000000000000) 3 (IntervalRat.scale (807 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (12310614591 / 1000000000000) (12310614592 / 1000000000000), orderedInterval (32928891948 / 1000000000000) (32928891949 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (596829102105609 / 800000000000) 3 (IntervalRat.scale (807 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-22467102037 / 1000000000000) (-22467093786 / 1000000000000), orderedInterval (18684964304 / 1000000000000) (18684972555 / 1000000000000)))) (orderedInterval (161207078 / 1000000000000) (161209313 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate532_chunkChecks3_2 :
    compactCertificate532.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1650860705818923 / 4000000000000) 3 (IntervalRat.scale (807 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-36460968709 / 1000000000000) (-36460948505 / 1000000000000), orderedInterval (14642575200 / 1000000000000) (14642595404 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1399452903104403 / 4000000000000) 3 (IntervalRat.scale (807 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-39912277286 / 1000000000000) (-39912265039 / 1000000000000), orderedInterval (15111398701 / 1000000000000) (15111410948 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (875712648081009 / 4000000000000) 3 (IntervalRat.scale (807 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-10633736727 / 1000000000000) (-10633736672 / 1000000000000), orderedInterval (52890381745 / 1000000000000) (52890381800 / 1000000000000)))) (orderedInterval (2806908223 / 1000000000000) (2806912229 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (470961174626703 / 4000000000000) 3 (IntervalRat.scale (807 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-55528005830 / 1000000000000) (-55527901494 / 1000000000000), orderedInterval (48439713107 / 1000000000000) (48439817443 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1278751204109109 / 4000000000000) 3 (IntervalRat.scale (807 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (1354491692 / 1000000000000) (1354491694 / 1000000000000), orderedInterval (44602224442 / 1000000000000) (44602224444 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1746025445407893 / 4000000000000) 3 (IntervalRat.scale (807 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-21880506777 / 1000000000000) (-21880506776 / 1000000000000), orderedInterval (-31274889511 / 1000000000000) (-31274889510 / 1000000000000)))) (orderedInterval (-2503974353 / 1000000000000) (-2503974260 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (738287351918991 / 4000000000000) 3 (IntervalRat.scale (807 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-152247255 / 1000000000000) (-152247251 / 1000000000000), orderedInterval (-58729138552 / 1000000000000) (-58729138548 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3001097097062511 / 4000000000000) 3 (IntervalRat.scale (807 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-6324510039 / 1000000000000) (-6324510038 / 1000000000000), orderedInterval (-28430215128 / 1000000000000) (-28430215127 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2004593777802849 / 4000000000000) 3 (IntervalRat.scale (807 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-23534482073 / 1000000000000) (-23534476134 / 1000000000000), orderedInterval (26790063517 / 1000000000000) (26790069456 / 1000000000000)))) (orderedInterval (-5192587957 / 1000000000000) (-5192585460 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate532_chunkChecks3 :
    compactCertificate532.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate532.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate532_chunkChecks3_0
    compactCertificate532_chunkChecks3_1 compactCertificate532_chunkChecks3_2

theorem compactCertificate532_chunkChecks4_0 :
    compactCertificate532.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (807 / 2) 4 (IntervalRat.scale (807 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (32996026694 / 1000000000000) (32996130776 / 1000000000000), orderedInterval (-22154336496 / 1000000000000) (-22154232414 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1188865094956107 / 4000000000000) 4 (IntervalRat.scale (807 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (20132788262 / 1000000000000) (20132789176 / 1000000000000), orderedInterval (-41706568594 / 1000000000000) (-41706567680 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (384454544933931 / 800000000000) 4 (IntervalRat.scale (807 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-23157859239 / 1000000000000) (-23157859238 / 1000000000000), orderedInterval (-28055022490 / 1000000000000) (-28055022489 / 1000000000000)))) (orderedInterval (10341129914 / 1000000000000) (10341171424 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (346907869636449 / 4000000000000) 4 (IntervalRat.scale (807 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-37548996768 / 1000000000000) (-37548993581 / 1000000000000), orderedInterval (77227205349 / 1000000000000) (77227208536 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (931843334471853 / 4000000000000) 4 (IntervalRat.scale (807 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (49894775485 / 1000000000000) (49894775487 / 1000000000000), orderedInterval (15489042077 / 1000000000000) (15489042079 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2530135922435001 / 4000000000000) 4 (IntervalRat.scale (807 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30415774641 / 1000000000000) (-30415750536 / 1000000000000), orderedInterval (9042927669 / 1000000000000) (9042951773 / 1000000000000)))) (orderedInterval (13249083106 / 1000000000000) (13249093663 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1863686668944513 / 4000000000000) 4 (IntervalRat.scale (807 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (36365267269 / 1000000000000) (36365270769 / 1000000000000), orderedInterval (-6667224149 / 1000000000000) (-6667220649 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3193458872758149 / 4000000000000) 4 (IntervalRat.scale (807 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (26167328962 / 1000000000000) (26167328982 / 1000000000000), orderedInterval (10598482358 / 1000000000000) (10598482378 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2352287351918991 / 4000000000000) 4 (IntervalRat.scale (807 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-32300111866 / 1000000000000) (-32300111792 / 1000000000000), orderedInterval (-6238065334 / 1000000000000) (-6238065261 / 1000000000000)))) (orderedInterval (-15906562296 / 1000000000000) (-15906562042 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate532_chunkChecks4_1 :
    compactCertificate532.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3609013715684193 / 4000000000000) 4 (IntervalRat.scale (807 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-26183595934 / 1000000000000) (-26183595126 / 1000000000000), orderedInterval (-4458505525 / 1000000000000) (-4458504717 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2083665040259097 / 4000000000000) 4 (IntervalRat.scale (807 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (6843711260 / 1000000000000) (6843711261 / 1000000000000), orderedInterval (34275780987 / 1000000000000) (34275780988 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3697500178768173 / 4000000000000) 4 (IntervalRat.scale (807 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (26223466656 / 1000000000000) (26223470698 / 1000000000000), orderedInterval (1001926673 / 1000000000000) (1001930715 / 1000000000000)))) (orderedInterval (220477008907 / 1000000000000) (220477031822 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3454684294113537 / 4000000000000) 4 (IntervalRat.scale (807 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-13451212026 / 1000000000000) (-13451212025 / 1000000000000), orderedInterval (-23575554711 / 1000000000000) (-23575554710 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2465425723885521 / 4000000000000) 4 (IntervalRat.scale (807 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (31611464522 / 1000000000000) (31611464626 / 1000000000000), orderedInterval (5770130608 / 1000000000000) (5770130712 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2795530003415559 / 4000000000000) 4 (IntervalRat.scale (807 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (23780771902 / 1000000000000) (23780785982 / 1000000000000), orderedInterval (-18601570643 / 1000000000000) (-18601556563 / 1000000000000)))) (orderedInterval (20321633298 / 1000000000000) (20321634375 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2330621468194071 / 4000000000000) 4 (IntervalRat.scale (807 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-25803754125 / 1000000000000) (-25803732039 / 1000000000000), orderedInterval (20680902323 / 1000000000000) (20680924409 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2059174747807491 / 4000000000000) 4 (IntervalRat.scale (807 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (12310614591 / 1000000000000) (12310614592 / 1000000000000), orderedInterval (32928891948 / 1000000000000) (32928891949 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (596829102105609 / 800000000000) 4 (IntervalRat.scale (807 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-22467102037 / 1000000000000) (-22467093786 / 1000000000000), orderedInterval (18684964304 / 1000000000000) (18684972555 / 1000000000000)))) (orderedInterval (-9885183527 / 1000000000000) (-9885179736 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate532_chunkChecks4_2 :
    compactCertificate532.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1650860705818923 / 4000000000000) 4 (IntervalRat.scale (807 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-36460968709 / 1000000000000) (-36460948505 / 1000000000000), orderedInterval (14642575200 / 1000000000000) (14642595404 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1399452903104403 / 4000000000000) 4 (IntervalRat.scale (807 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-39912277286 / 1000000000000) (-39912265039 / 1000000000000), orderedInterval (15111398701 / 1000000000000) (15111410948 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (875712648081009 / 4000000000000) 4 (IntervalRat.scale (807 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-10633736727 / 1000000000000) (-10633736672 / 1000000000000), orderedInterval (52890381745 / 1000000000000) (52890381800 / 1000000000000)))) (orderedInterval (7613816332 / 1000000000000) (7613820365 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (470961174626703 / 4000000000000) 4 (IntervalRat.scale (807 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-55528005830 / 1000000000000) (-55527901494 / 1000000000000), orderedInterval (48439713107 / 1000000000000) (48439817443 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1278751204109109 / 4000000000000) 4 (IntervalRat.scale (807 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (1354491692 / 1000000000000) (1354491694 / 1000000000000), orderedInterval (44602224442 / 1000000000000) (44602224444 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1746025445407893 / 4000000000000) 4 (IntervalRat.scale (807 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-21880506777 / 1000000000000) (-21880506776 / 1000000000000), orderedInterval (-31274889511 / 1000000000000) (-31274889510 / 1000000000000)))) (orderedInterval (2304372907 / 1000000000000) (2304372968 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (738287351918991 / 4000000000000) 4 (IntervalRat.scale (807 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-152247255 / 1000000000000) (-152247251 / 1000000000000), orderedInterval (-58729138552 / 1000000000000) (-58729138548 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3001097097062511 / 4000000000000) 4 (IntervalRat.scale (807 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-6324510039 / 1000000000000) (-6324510038 / 1000000000000), orderedInterval (-28430215128 / 1000000000000) (-28430215127 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2004593777802849 / 4000000000000) 4 (IntervalRat.scale (807 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-23534482073 / 1000000000000) (-23534476134 / 1000000000000), orderedInterval (26790063517 / 1000000000000) (26790069456 / 1000000000000)))) (orderedInterval (16687053594 / 1000000000000) (16687056831 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate532_chunkChecks4 :
    compactCertificate532.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate532.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate532_chunkChecks4_0
    compactCertificate532_chunkChecks4_1 compactCertificate532_chunkChecks4_2

theorem compactCertificate532_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate532.chunkCheck r b = true :=
  compactCertificate532.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate532_chunkChecks0
    · exact compactCertificate532_chunkChecks1
    · exact compactCertificate532_chunkChecks2
    · exact compactCertificate532_chunkChecks3
    · exact compactCertificate532_chunkChecks4)

theorem compactCertificate532_coefficient0 :
    compactCertificate532.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate532_coefficient1 :
    compactCertificate532.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate532_coefficient2 :
    compactCertificate532.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate532_coefficient3 :
    compactCertificate532.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate532_coefficient4 :
    compactCertificate532.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate532_coefficients : ∀ r : Fin 5,
    compactCertificate532.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate532_coefficient0
  · exact compactCertificate532_coefficient1
  · exact compactCertificate532_coefficient2
  · exact compactCertificate532_coefficient3
  · exact compactCertificate532_coefficient4

theorem compactCertificate532_lower : (1 : ℚ) ≤ compactCertificate532.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate532, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate532_proves {t : ℝ} (ht : t ∈ compactCertificate532.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate532.proves compactCertificate532_states compactCertificate532_chunks
    compactCertificate532_coefficients compactCertificate532_lower ht

end Erdos232
