/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate545 : CompactCertificate where
  left := 416
  right := 417
  center := 833 / 2
  grid := fun i =>
    match i.val with
    | 0 => 133
    | 1 => 98
    | 2 => 158
    | 3 => 29
    | 4 => 77
    | 5 => 208
    | 6 => 153
    | 7 => 262
    | 8 => 193
    | 9 => 297
    | 10 => 171
    | 11 => 304
    | 12 => 284
    | 13 => 203
    | 14 => 230
    | 15 => 192
    | 16 => 169
    | 17 => 245
    | 18 => 136
    | 19 => 115
    | 20 => 72
    | 21 => 39
    | 22 => 105
    | 23 => 143
    | 24 => 61
    | 25 => 247
    | _ => 165
  point := fun i =>
    match i.val with
    | 0 => 833 / 2
    | 1 => 1227168059601533 / 4000000000000
    | 2 => 396840936716189 / 800000000000
    | 3 => 358084579191031 / 4000000000000
    | 4 => 961865548469707 / 4000000000000
    | 5 => 2611652073591519 / 4000000000000
    | 6 => 1923731096940247 / 4000000000000
    | 7 => 3296346023553331 / 4000000000000
    | 8 => 2428073561522329 / 4000000000000
    | 9 => 3725289250514167 / 4000000000000
    | 10 => 2150796751593343 / 4000000000000
    | 11 => 3816626578579787 / 4000000000000
    | 12 => 3565987629487703 / 4000000000000
    | 13 => 2544857035931399 / 4000000000000
    | 14 => 2885596645409121 / 4000000000000
    | 15 => 2405709644368849 / 4000000000000
    | 16 => 2125517428653829 / 4000000000000
    | 17 => 616057796845071 / 800000000000
    | 18 => 1704048287419037 / 4000000000000
    | 19 => 1444540605063157 / 4000000000000
    | 20 => 903926438477671 / 4000000000000
    | 21 => 486134644936857 / 4000000000000
    | 22 => 1319950127661571 / 4000000000000
    | 23 => 1802279053314467 / 4000000000000
    | 24 => 762073561522329 / 4000000000000
    | 25 => 3097786718529209 / 4000000000000
    | _ => 2069177963952631 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (20325712717 / 1000000000000) (20325714119 / 1000000000000), orderedInterval (-33421477972 / 1000000000000) (-33421476570 / 1000000000000))
    | 1 => (orderedInterval (-13421570412 / 1000000000000) (-13421570290 / 1000000000000), orderedInterval (43552892616 / 1000000000000) (43552892738 / 1000000000000))
    | 2 => (orderedInterval (16054078154 / 1000000000000) (16054078155 / 1000000000000), orderedInterval (32009466737 / 1000000000000) (32009466738 / 1000000000000))
    | 3 => (orderedInterval (60554527654 / 1000000000000) (60554614815 / 1000000000000), orderedInterval (-59028363625 / 1000000000000) (-59028276464 / 1000000000000))
    | 4 => (orderedInterval (31194813240 / 1000000000000) (31194824379 / 1000000000000), orderedInterval (-40983353764 / 1000000000000) (-40983342624 / 1000000000000))
    | 5 => (orderedInterval (7633146853 / 1000000000000) (7633146854 / 1000000000000), orderedInterval (30272539985 / 1000000000000) (30272539986 / 1000000000000))
    | 6 => (orderedInterval (-31635814879 / 1000000000000) (-31635814878 / 1000000000000), orderedInterval (-17936352787 / 1000000000000) (-17936352786 / 1000000000000))
    | 7 => (orderedInterval (27219608289 / 1000000000000) (27219635367 / 1000000000000), orderedInterval (-5638605323 / 1000000000000) (-5638578245 / 1000000000000))
    | 8 => (orderedInterval (-32239852463 / 1000000000000) (-32239852148 / 1000000000000), orderedInterval (-3032331002 / 1000000000000) (-3032330687 / 1000000000000))
    | 9 => (orderedInterval (21197266265 / 1000000000000) (21197272593 / 1000000000000), orderedInterval (-15316323794 / 1000000000000) (-15316317466 / 1000000000000))
    | 10 => (orderedInterval (-32884354268 / 1000000000000) (-32884354258 / 1000000000000), orderedInterval (-10098041221 / 1000000000000) (-10098041211 / 1000000000000))
    | 11 => (orderedInterval (-2636678472 / 1000000000000) (-2636678471 / 1000000000000), orderedInterval (25696805119 / 1000000000000) (25696805120 / 1000000000000))
    | 12 => (orderedInterval (1865107511 / 1000000000000) (1865107512 / 1000000000000), orderedInterval (26656477065 / 1000000000000) (26656477066 / 1000000000000))
    | 13 => (orderedInterval (21419375950 / 1000000000000) (21419379607 / 1000000000000), orderedInterval (-23294456784 / 1000000000000) (-23294453127 / 1000000000000))
    | 14 => (orderedInterval (-11071826944 / 1000000000000) (-11071826925 / 1000000000000), orderedInterval (27573849236 / 1000000000000) (27573849254 / 1000000000000))
    | 15 => (orderedInterval (-26896024543 / 1000000000000) (-26895983370 / 1000000000000), orderedInterval (18328609571 / 1000000000000) (18328650745 / 1000000000000))
    | 16 => (orderedInterval (-32683802633 / 1000000000000) (-32683802628 / 1000000000000), orderedInterval (-11363104752 / 1000000000000) (-11363104746 / 1000000000000))
    | 17 => (orderedInterval (-26443210009 / 1000000000000) (-26443209997 / 1000000000000), orderedInterval (-11272555384 / 1000000000000) (-11272555372 / 1000000000000))
    | 18 => (orderedInterval (-17141789477 / 1000000000000) (-17141789016 / 1000000000000), orderedInterval (34668783113 / 1000000000000) (34668783573 / 1000000000000))
    | 19 => (orderedInterval (-24974356485 / 1000000000000) (-24974356484 / 1000000000000), orderedInterval (-33716151634 / 1000000000000) (-33716151633 / 1000000000000))
    | 20 => (orderedInterval (28721481318 / 1000000000000) (28721481319 / 1000000000000), orderedInterval (44570634624 / 1000000000000) (44570634625 / 1000000000000))
    | 21 => (orderedInterval (14668204646 / 1000000000000) (14668204766 / 1000000000000), orderedInterval (-70934191884 / 1000000000000) (-70934191765 / 1000000000000))
    | 22 => (orderedInterval (-34550828542 / 1000000000000) (-34550828541 / 1000000000000), orderedInterval (-27067077534 / 1000000000000) (-27067077533 / 1000000000000))
    | 23 => (orderedInterval (-32310868815 / 1000000000000) (-32310773271 / 1000000000000), orderedInterval (19243408862 / 1000000000000) (19243504406 / 1000000000000))
    | 24 => (orderedInterval (18951199154 / 1000000000000) (18951199579 / 1000000000000), orderedInterval (-54660857044 / 1000000000000) (-54660856619 / 1000000000000))
    | 25 => (orderedInterval (19363653646 / 1000000000000) (19363655282 / 1000000000000), orderedInterval (-21156784541 / 1000000000000) (-21156782906 / 1000000000000))
    | _ => (orderedInterval (9800639129 / 1000000000000) (9800639150 / 1000000000000), orderedInterval (-33693591131 / 1000000000000) (-33693591110 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (8873409573 / 1000000000000) (8873410160 / 1000000000000)
      | 1 => orderedInterval (-60635235 / 1000000000000) (-60633832 / 1000000000000)
      | 2 => orderedInterval (-1618736097 / 1000000000000) (-1618735231 / 1000000000000)
      | 3 => orderedInterval (-6577778912 / 1000000000000) (-6577777622 / 1000000000000)
      | 4 => orderedInterval (2047836428 / 1000000000000) (2047836824 / 1000000000000)
      | 5 => orderedInterval (882748353 / 1000000000000) (882748870 / 1000000000000)
      | 6 => orderedInterval (5089425540 / 1000000000000) (5089425718 / 1000000000000)
      | 7 => orderedInterval (2989260889 / 1000000000000) (2989268264 / 1000000000000)
      | _ => orderedInterval (-3300851849 / 1000000000000) (-3300851593 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-10711056741 / 1000000000000) (-10711056151 / 1000000000000)
      | 1 => orderedInterval (-4099898047 / 1000000000000) (-4099897552 / 1000000000000)
      | 2 => orderedInterval (237302419 / 1000000000000) (237304124 / 1000000000000)
      | 3 => orderedInterval (13488135734 / 1000000000000) (13488138592 / 1000000000000)
      | 4 => orderedInterval (-4636559598 / 1000000000000) (-4636558989 / 1000000000000)
      | 5 => orderedInterval (601621844 / 1000000000000) (601622589 / 1000000000000)
      | 6 => orderedInterval (-3227935955 / 1000000000000) (-3227935783 / 1000000000000)
      | 7 => orderedInterval (-726723266 / 1000000000000) (-726715298 / 1000000000000)
      | _ => orderedInterval (10903269342 / 1000000000000) (10903269758 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-9299137843 / 1000000000000) (-9299137247 / 1000000000000)
      | 1 => orderedInterval (994027738 / 1000000000000) (994027998 / 1000000000000)
      | 2 => orderedInterval (4941229403 / 1000000000000) (4941232766 / 1000000000000)
      | 3 => orderedInterval (24827995690 / 1000000000000) (24828002053 / 1000000000000)
      | 4 => orderedInterval (-4728808349 / 1000000000000) (-4728807407 / 1000000000000)
      | 5 => orderedInterval (-83805397 / 1000000000000) (-83804316 / 1000000000000)
      | 6 => orderedInterval (-4197696735 / 1000000000000) (-4197696565 / 1000000000000)
      | 7 => orderedInterval (-3365186790 / 1000000000000) (-3365178156 / 1000000000000)
      | _ => orderedInterval (8236213033 / 1000000000000) (8236213740 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (9933874368 / 1000000000000) (9933874970 / 1000000000000)
      | 1 => orderedInterval (8569620487 / 1000000000000) (8569620693 / 1000000000000)
      | 2 => orderedInterval (-1132141274 / 1000000000000) (-1132134641 / 1000000000000)
      | 3 => orderedInterval (-72796850368 / 1000000000000) (-72796836173 / 1000000000000)
      | 4 => orderedInterval (13306840467 / 1000000000000) (13306841928 / 1000000000000)
      | 5 => orderedInterval (-163254411 / 1000000000000) (-163252842 / 1000000000000)
      | 6 => orderedInterval (4466112493 / 1000000000000) (4466112661 / 1000000000000)
      | 7 => orderedInterval (1537256744 / 1000000000000) (1537266081 / 1000000000000)
      | _ => orderedInterval (-23171681769 / 1000000000000) (-23171680535 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (9867355375 / 1000000000000) (9867355985 / 1000000000000)
      | 1 => orderedInterval (-3192954735 / 1000000000000) (-3192954506 / 1000000000000)
      | 2 => orderedInterval (-16377195201 / 1000000000000) (-16377182092 / 1000000000000)
      | 3 => orderedInterval (-110904551179 / 1000000000000) (-110904519435 / 1000000000000)
      | 4 => orderedInterval (10761178353 / 1000000000000) (10761180635 / 1000000000000)
      | 5 => orderedInterval (-4306081315 / 1000000000000) (-4306079027 / 1000000000000)
      | 6 => orderedInterval (3858464570 / 1000000000000) (3858464740 / 1000000000000)
      | 7 => orderedInterval (3690939676 / 1000000000000) (3690949798 / 1000000000000)
      | _ => orderedInterval (-23101319757 / 1000000000000) (-23101317559 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (8324678690 / 1000000000000) (8324691558 / 1000000000000)
    | 1 => orderedInterval (1828155732 / 1000000000000) (1828171290 / 1000000000000)
    | 2 => orderedInterval (17324830750 / 1000000000000) (17324852866 / 1000000000000)
    | 3 => orderedInterval (-59450223263 / 1000000000000) (-59450187858 / 1000000000000)
    | _ => orderedInterval (-129704164213 / 1000000000000) (-129704101461 / 1000000000000)

theorem compactCertificate545_stateChecks0 :
    compactCertificate545.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 133 12 (833 / 2)) (orderedInterval (20325712717 / 1000000000000) (20325714119 / 1000000000000), orderedInterval (-33421477972 / 1000000000000) (-33421476570 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 98 12 (1227168059601533 / 4000000000000)) (orderedInterval (-13421570412 / 1000000000000) (-13421570290 / 1000000000000), orderedInterval (43552892616 / 1000000000000) (43552892738 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 158 12 (396840936716189 / 800000000000)) (orderedInterval (16054078154 / 1000000000000) (16054078155 / 1000000000000), orderedInterval (32009466737 / 1000000000000) (32009466738 / 1000000000000))) = true
  rfl'

theorem compactCertificate545_stateChecks1 :
    compactCertificate545.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (358084579191031 / 4000000000000)) (orderedInterval (60554527654 / 1000000000000) (60554614815 / 1000000000000), orderedInterval (-59028363625 / 1000000000000) (-59028276464 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (961865548469707 / 4000000000000)) (orderedInterval (31194813240 / 1000000000000) (31194824379 / 1000000000000), orderedInterval (-40983353764 / 1000000000000) (-40983342624 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 208 12 (2611652073591519 / 4000000000000)) (orderedInterval (7633146853 / 1000000000000) (7633146854 / 1000000000000), orderedInterval (30272539985 / 1000000000000) (30272539986 / 1000000000000))) = true
  rfl'

theorem compactCertificate545_stateChecks2 :
    compactCertificate545.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 153 12 (1923731096940247 / 4000000000000)) (orderedInterval (-31635814879 / 1000000000000) (-31635814878 / 1000000000000), orderedInterval (-17936352787 / 1000000000000) (-17936352786 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 262 12 (3296346023553331 / 4000000000000)) (orderedInterval (27219608289 / 1000000000000) (27219635367 / 1000000000000), orderedInterval (-5638605323 / 1000000000000) (-5638578245 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 193 12 (2428073561522329 / 4000000000000)) (orderedInterval (-32239852463 / 1000000000000) (-32239852148 / 1000000000000), orderedInterval (-3032331002 / 1000000000000) (-3032330687 / 1000000000000))) = true
  rfl'

theorem compactCertificate545_stateChecks3 :
    compactCertificate545.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 297 12 (3725289250514167 / 4000000000000)) (orderedInterval (21197266265 / 1000000000000) (21197272593 / 1000000000000), orderedInterval (-15316323794 / 1000000000000) (-15316317466 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 171 12 (2150796751593343 / 4000000000000)) (orderedInterval (-32884354268 / 1000000000000) (-32884354258 / 1000000000000), orderedInterval (-10098041221 / 1000000000000) (-10098041211 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 304 12 (3816626578579787 / 4000000000000)) (orderedInterval (-2636678472 / 1000000000000) (-2636678471 / 1000000000000), orderedInterval (25696805119 / 1000000000000) (25696805120 / 1000000000000))) = true
  rfl'

theorem compactCertificate545_stateChecks4 :
    compactCertificate545.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 284 12 (3565987629487703 / 4000000000000)) (orderedInterval (1865107511 / 1000000000000) (1865107512 / 1000000000000), orderedInterval (26656477065 / 1000000000000) (26656477066 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 203 12 (2544857035931399 / 4000000000000)) (orderedInterval (21419375950 / 1000000000000) (21419379607 / 1000000000000), orderedInterval (-23294456784 / 1000000000000) (-23294453127 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 230 12 (2885596645409121 / 4000000000000)) (orderedInterval (-11071826944 / 1000000000000) (-11071826925 / 1000000000000), orderedInterval (27573849236 / 1000000000000) (27573849254 / 1000000000000))) = true
  rfl'

theorem compactCertificate545_stateChecks5 :
    compactCertificate545.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 192 12 (2405709644368849 / 4000000000000)) (orderedInterval (-26896024543 / 1000000000000) (-26895983370 / 1000000000000), orderedInterval (18328609571 / 1000000000000) (18328650745 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 169 12 (2125517428653829 / 4000000000000)) (orderedInterval (-32683802633 / 1000000000000) (-32683802628 / 1000000000000), orderedInterval (-11363104752 / 1000000000000) (-11363104746 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 245 12 (616057796845071 / 800000000000)) (orderedInterval (-26443210009 / 1000000000000) (-26443209997 / 1000000000000), orderedInterval (-11272555384 / 1000000000000) (-11272555372 / 1000000000000))) = true
  rfl'

theorem compactCertificate545_stateChecks6 :
    compactCertificate545.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 136 12 (1704048287419037 / 4000000000000)) (orderedInterval (-17141789477 / 1000000000000) (-17141789016 / 1000000000000), orderedInterval (34668783113 / 1000000000000) (34668783573 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 115 12 (1444540605063157 / 4000000000000)) (orderedInterval (-24974356485 / 1000000000000) (-24974356484 / 1000000000000), orderedInterval (-33716151634 / 1000000000000) (-33716151633 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (903926438477671 / 4000000000000)) (orderedInterval (28721481318 / 1000000000000) (28721481319 / 1000000000000), orderedInterval (44570634624 / 1000000000000) (44570634625 / 1000000000000))) = true
  rfl'

theorem compactCertificate545_stateChecks7 :
    compactCertificate545.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (486134644936857 / 4000000000000)) (orderedInterval (14668204646 / 1000000000000) (14668204766 / 1000000000000), orderedInterval (-70934191884 / 1000000000000) (-70934191765 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 105 12 (1319950127661571 / 4000000000000)) (orderedInterval (-34550828542 / 1000000000000) (-34550828541 / 1000000000000), orderedInterval (-27067077534 / 1000000000000) (-27067077533 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 143 12 (1802279053314467 / 4000000000000)) (orderedInterval (-32310868815 / 1000000000000) (-32310773271 / 1000000000000), orderedInterval (19243408862 / 1000000000000) (19243504406 / 1000000000000))) = true
  rfl'

theorem compactCertificate545_stateChecks8 :
    compactCertificate545.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (762073561522329 / 4000000000000)) (orderedInterval (18951199154 / 1000000000000) (18951199579 / 1000000000000), orderedInterval (-54660857044 / 1000000000000) (-54660856619 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 247 12 (3097786718529209 / 4000000000000)) (orderedInterval (19363653646 / 1000000000000) (19363655282 / 1000000000000), orderedInterval (-21156784541 / 1000000000000) (-21156782906 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 165 12 (2069177963952631 / 4000000000000)) (orderedInterval (9800639129 / 1000000000000) (9800639150 / 1000000000000), orderedInterval (-33693591131 / 1000000000000) (-33693591110 / 1000000000000))) = true
  rfl'

theorem compactCertificate545_states : ∀ j,
    BesselStateValid (compactCertificate545.point j) (compactCertificate545.state j) :=
  compactCertificate545.statesValid_of_checks3 compactCertificate545_stateChecks0
    compactCertificate545_stateChecks1 compactCertificate545_stateChecks2
    compactCertificate545_stateChecks3 compactCertificate545_stateChecks4
    compactCertificate545_stateChecks5 compactCertificate545_stateChecks6
    compactCertificate545_stateChecks7 compactCertificate545_stateChecks8

theorem compactCertificate545_chunkChecks0_0 :
    compactCertificate545.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (833 / 2) 0 (IntervalRat.scale (833 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (20325712717 / 1000000000000) (20325714119 / 1000000000000), orderedInterval (-33421477972 / 1000000000000) (-33421476570 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1227168059601533 / 4000000000000) 0 (IntervalRat.scale (833 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-13421570412 / 1000000000000) (-13421570290 / 1000000000000), orderedInterval (43552892616 / 1000000000000) (43552892738 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (396840936716189 / 800000000000) 0 (IntervalRat.scale (833 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (16054078154 / 1000000000000) (16054078155 / 1000000000000), orderedInterval (32009466737 / 1000000000000) (32009466738 / 1000000000000)))) (orderedInterval (8873409573 / 1000000000000) (8873410160 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (358084579191031 / 4000000000000) 0 (IntervalRat.scale (833 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (60554527654 / 1000000000000) (60554614815 / 1000000000000), orderedInterval (-59028363625 / 1000000000000) (-59028276464 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (961865548469707 / 4000000000000) 0 (IntervalRat.scale (833 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (31194813240 / 1000000000000) (31194824379 / 1000000000000), orderedInterval (-40983353764 / 1000000000000) (-40983342624 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2611652073591519 / 4000000000000) 0 (IntervalRat.scale (833 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (7633146853 / 1000000000000) (7633146854 / 1000000000000), orderedInterval (30272539985 / 1000000000000) (30272539986 / 1000000000000)))) (orderedInterval (-60635235 / 1000000000000) (-60633832 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1923731096940247 / 4000000000000) 0 (IntervalRat.scale (833 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-31635814879 / 1000000000000) (-31635814878 / 1000000000000), orderedInterval (-17936352787 / 1000000000000) (-17936352786 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3296346023553331 / 4000000000000) 0 (IntervalRat.scale (833 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (27219608289 / 1000000000000) (27219635367 / 1000000000000), orderedInterval (-5638605323 / 1000000000000) (-5638578245 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2428073561522329 / 4000000000000) 0 (IntervalRat.scale (833 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-32239852463 / 1000000000000) (-32239852148 / 1000000000000), orderedInterval (-3032331002 / 1000000000000) (-3032330687 / 1000000000000)))) (orderedInterval (-1618736097 / 1000000000000) (-1618735231 / 1000000000000))) = true
  rfl'

theorem compactCertificate545_chunkChecks0_1 :
    compactCertificate545.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3725289250514167 / 4000000000000) 0 (IntervalRat.scale (833 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (21197266265 / 1000000000000) (21197272593 / 1000000000000), orderedInterval (-15316323794 / 1000000000000) (-15316317466 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2150796751593343 / 4000000000000) 0 (IntervalRat.scale (833 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-32884354268 / 1000000000000) (-32884354258 / 1000000000000), orderedInterval (-10098041221 / 1000000000000) (-10098041211 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3816626578579787 / 4000000000000) 0 (IntervalRat.scale (833 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-2636678472 / 1000000000000) (-2636678471 / 1000000000000), orderedInterval (25696805119 / 1000000000000) (25696805120 / 1000000000000)))) (orderedInterval (-6577778912 / 1000000000000) (-6577777622 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3565987629487703 / 4000000000000) 0 (IntervalRat.scale (833 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (1865107511 / 1000000000000) (1865107512 / 1000000000000), orderedInterval (26656477065 / 1000000000000) (26656477066 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2544857035931399 / 4000000000000) 0 (IntervalRat.scale (833 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (21419375950 / 1000000000000) (21419379607 / 1000000000000), orderedInterval (-23294456784 / 1000000000000) (-23294453127 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2885596645409121 / 4000000000000) 0 (IntervalRat.scale (833 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-11071826944 / 1000000000000) (-11071826925 / 1000000000000), orderedInterval (27573849236 / 1000000000000) (27573849254 / 1000000000000)))) (orderedInterval (2047836428 / 1000000000000) (2047836824 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2405709644368849 / 4000000000000) 0 (IntervalRat.scale (833 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-26896024543 / 1000000000000) (-26895983370 / 1000000000000), orderedInterval (18328609571 / 1000000000000) (18328650745 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2125517428653829 / 4000000000000) 0 (IntervalRat.scale (833 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-32683802633 / 1000000000000) (-32683802628 / 1000000000000), orderedInterval (-11363104752 / 1000000000000) (-11363104746 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (616057796845071 / 800000000000) 0 (IntervalRat.scale (833 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-26443210009 / 1000000000000) (-26443209997 / 1000000000000), orderedInterval (-11272555384 / 1000000000000) (-11272555372 / 1000000000000)))) (orderedInterval (882748353 / 1000000000000) (882748870 / 1000000000000))) = true
  rfl'

theorem compactCertificate545_chunkChecks0_2 :
    compactCertificate545.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1704048287419037 / 4000000000000) 0 (IntervalRat.scale (833 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-17141789477 / 1000000000000) (-17141789016 / 1000000000000), orderedInterval (34668783113 / 1000000000000) (34668783573 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1444540605063157 / 4000000000000) 0 (IntervalRat.scale (833 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-24974356485 / 1000000000000) (-24974356484 / 1000000000000), orderedInterval (-33716151634 / 1000000000000) (-33716151633 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (903926438477671 / 4000000000000) 0 (IntervalRat.scale (833 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (28721481318 / 1000000000000) (28721481319 / 1000000000000), orderedInterval (44570634624 / 1000000000000) (44570634625 / 1000000000000)))) (orderedInterval (5089425540 / 1000000000000) (5089425718 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (486134644936857 / 4000000000000) 0 (IntervalRat.scale (833 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (14668204646 / 1000000000000) (14668204766 / 1000000000000), orderedInterval (-70934191884 / 1000000000000) (-70934191765 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1319950127661571 / 4000000000000) 0 (IntervalRat.scale (833 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-34550828542 / 1000000000000) (-34550828541 / 1000000000000), orderedInterval (-27067077534 / 1000000000000) (-27067077533 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1802279053314467 / 4000000000000) 0 (IntervalRat.scale (833 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-32310868815 / 1000000000000) (-32310773271 / 1000000000000), orderedInterval (19243408862 / 1000000000000) (19243504406 / 1000000000000)))) (orderedInterval (2989260889 / 1000000000000) (2989268264 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (762073561522329 / 4000000000000) 0 (IntervalRat.scale (833 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (18951199154 / 1000000000000) (18951199579 / 1000000000000), orderedInterval (-54660857044 / 1000000000000) (-54660856619 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3097786718529209 / 4000000000000) 0 (IntervalRat.scale (833 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (19363653646 / 1000000000000) (19363655282 / 1000000000000), orderedInterval (-21156784541 / 1000000000000) (-21156782906 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2069177963952631 / 4000000000000) 0 (IntervalRat.scale (833 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (9800639129 / 1000000000000) (9800639150 / 1000000000000), orderedInterval (-33693591131 / 1000000000000) (-33693591110 / 1000000000000)))) (orderedInterval (-3300851849 / 1000000000000) (-3300851593 / 1000000000000))) = true
  rfl'

theorem compactCertificate545_chunkChecks0 :
    compactCertificate545.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate545.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate545_chunkChecks0_0
    compactCertificate545_chunkChecks0_1 compactCertificate545_chunkChecks0_2

theorem compactCertificate545_chunkChecks1_0 :
    compactCertificate545.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (833 / 2) 1 (IntervalRat.scale (833 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (20325712717 / 1000000000000) (20325714119 / 1000000000000), orderedInterval (-33421477972 / 1000000000000) (-33421476570 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1227168059601533 / 4000000000000) 1 (IntervalRat.scale (833 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-13421570412 / 1000000000000) (-13421570290 / 1000000000000), orderedInterval (43552892616 / 1000000000000) (43552892738 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (396840936716189 / 800000000000) 1 (IntervalRat.scale (833 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (16054078154 / 1000000000000) (16054078155 / 1000000000000), orderedInterval (32009466737 / 1000000000000) (32009466738 / 1000000000000)))) (orderedInterval (-10711056741 / 1000000000000) (-10711056151 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (358084579191031 / 4000000000000) 1 (IntervalRat.scale (833 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (60554527654 / 1000000000000) (60554614815 / 1000000000000), orderedInterval (-59028363625 / 1000000000000) (-59028276464 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (961865548469707 / 4000000000000) 1 (IntervalRat.scale (833 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (31194813240 / 1000000000000) (31194824379 / 1000000000000), orderedInterval (-40983353764 / 1000000000000) (-40983342624 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2611652073591519 / 4000000000000) 1 (IntervalRat.scale (833 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (7633146853 / 1000000000000) (7633146854 / 1000000000000), orderedInterval (30272539985 / 1000000000000) (30272539986 / 1000000000000)))) (orderedInterval (-4099898047 / 1000000000000) (-4099897552 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1923731096940247 / 4000000000000) 1 (IntervalRat.scale (833 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-31635814879 / 1000000000000) (-31635814878 / 1000000000000), orderedInterval (-17936352787 / 1000000000000) (-17936352786 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3296346023553331 / 4000000000000) 1 (IntervalRat.scale (833 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (27219608289 / 1000000000000) (27219635367 / 1000000000000), orderedInterval (-5638605323 / 1000000000000) (-5638578245 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2428073561522329 / 4000000000000) 1 (IntervalRat.scale (833 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-32239852463 / 1000000000000) (-32239852148 / 1000000000000), orderedInterval (-3032331002 / 1000000000000) (-3032330687 / 1000000000000)))) (orderedInterval (237302419 / 1000000000000) (237304124 / 1000000000000))) = true
  rfl'

theorem compactCertificate545_chunkChecks1_1 :
    compactCertificate545.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3725289250514167 / 4000000000000) 1 (IntervalRat.scale (833 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (21197266265 / 1000000000000) (21197272593 / 1000000000000), orderedInterval (-15316323794 / 1000000000000) (-15316317466 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2150796751593343 / 4000000000000) 1 (IntervalRat.scale (833 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-32884354268 / 1000000000000) (-32884354258 / 1000000000000), orderedInterval (-10098041221 / 1000000000000) (-10098041211 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3816626578579787 / 4000000000000) 1 (IntervalRat.scale (833 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-2636678472 / 1000000000000) (-2636678471 / 1000000000000), orderedInterval (25696805119 / 1000000000000) (25696805120 / 1000000000000)))) (orderedInterval (13488135734 / 1000000000000) (13488138592 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3565987629487703 / 4000000000000) 1 (IntervalRat.scale (833 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (1865107511 / 1000000000000) (1865107512 / 1000000000000), orderedInterval (26656477065 / 1000000000000) (26656477066 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2544857035931399 / 4000000000000) 1 (IntervalRat.scale (833 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (21419375950 / 1000000000000) (21419379607 / 1000000000000), orderedInterval (-23294456784 / 1000000000000) (-23294453127 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2885596645409121 / 4000000000000) 1 (IntervalRat.scale (833 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-11071826944 / 1000000000000) (-11071826925 / 1000000000000), orderedInterval (27573849236 / 1000000000000) (27573849254 / 1000000000000)))) (orderedInterval (-4636559598 / 1000000000000) (-4636558989 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2405709644368849 / 4000000000000) 1 (IntervalRat.scale (833 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-26896024543 / 1000000000000) (-26895983370 / 1000000000000), orderedInterval (18328609571 / 1000000000000) (18328650745 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2125517428653829 / 4000000000000) 1 (IntervalRat.scale (833 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-32683802633 / 1000000000000) (-32683802628 / 1000000000000), orderedInterval (-11363104752 / 1000000000000) (-11363104746 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (616057796845071 / 800000000000) 1 (IntervalRat.scale (833 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-26443210009 / 1000000000000) (-26443209997 / 1000000000000), orderedInterval (-11272555384 / 1000000000000) (-11272555372 / 1000000000000)))) (orderedInterval (601621844 / 1000000000000) (601622589 / 1000000000000))) = true
  rfl'

theorem compactCertificate545_chunkChecks1_2 :
    compactCertificate545.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1704048287419037 / 4000000000000) 1 (IntervalRat.scale (833 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-17141789477 / 1000000000000) (-17141789016 / 1000000000000), orderedInterval (34668783113 / 1000000000000) (34668783573 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1444540605063157 / 4000000000000) 1 (IntervalRat.scale (833 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-24974356485 / 1000000000000) (-24974356484 / 1000000000000), orderedInterval (-33716151634 / 1000000000000) (-33716151633 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (903926438477671 / 4000000000000) 1 (IntervalRat.scale (833 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (28721481318 / 1000000000000) (28721481319 / 1000000000000), orderedInterval (44570634624 / 1000000000000) (44570634625 / 1000000000000)))) (orderedInterval (-3227935955 / 1000000000000) (-3227935783 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (486134644936857 / 4000000000000) 1 (IntervalRat.scale (833 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (14668204646 / 1000000000000) (14668204766 / 1000000000000), orderedInterval (-70934191884 / 1000000000000) (-70934191765 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1319950127661571 / 4000000000000) 1 (IntervalRat.scale (833 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-34550828542 / 1000000000000) (-34550828541 / 1000000000000), orderedInterval (-27067077534 / 1000000000000) (-27067077533 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1802279053314467 / 4000000000000) 1 (IntervalRat.scale (833 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-32310868815 / 1000000000000) (-32310773271 / 1000000000000), orderedInterval (19243408862 / 1000000000000) (19243504406 / 1000000000000)))) (orderedInterval (-726723266 / 1000000000000) (-726715298 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (762073561522329 / 4000000000000) 1 (IntervalRat.scale (833 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (18951199154 / 1000000000000) (18951199579 / 1000000000000), orderedInterval (-54660857044 / 1000000000000) (-54660856619 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3097786718529209 / 4000000000000) 1 (IntervalRat.scale (833 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (19363653646 / 1000000000000) (19363655282 / 1000000000000), orderedInterval (-21156784541 / 1000000000000) (-21156782906 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2069177963952631 / 4000000000000) 1 (IntervalRat.scale (833 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (9800639129 / 1000000000000) (9800639150 / 1000000000000), orderedInterval (-33693591131 / 1000000000000) (-33693591110 / 1000000000000)))) (orderedInterval (10903269342 / 1000000000000) (10903269758 / 1000000000000))) = true
  rfl'

theorem compactCertificate545_chunkChecks1 :
    compactCertificate545.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate545.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate545_chunkChecks1_0
    compactCertificate545_chunkChecks1_1 compactCertificate545_chunkChecks1_2

theorem compactCertificate545_chunkChecks2_0 :
    compactCertificate545.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (833 / 2) 2 (IntervalRat.scale (833 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (20325712717 / 1000000000000) (20325714119 / 1000000000000), orderedInterval (-33421477972 / 1000000000000) (-33421476570 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1227168059601533 / 4000000000000) 2 (IntervalRat.scale (833 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-13421570412 / 1000000000000) (-13421570290 / 1000000000000), orderedInterval (43552892616 / 1000000000000) (43552892738 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (396840936716189 / 800000000000) 2 (IntervalRat.scale (833 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (16054078154 / 1000000000000) (16054078155 / 1000000000000), orderedInterval (32009466737 / 1000000000000) (32009466738 / 1000000000000)))) (orderedInterval (-9299137843 / 1000000000000) (-9299137247 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (358084579191031 / 4000000000000) 2 (IntervalRat.scale (833 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (60554527654 / 1000000000000) (60554614815 / 1000000000000), orderedInterval (-59028363625 / 1000000000000) (-59028276464 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (961865548469707 / 4000000000000) 2 (IntervalRat.scale (833 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (31194813240 / 1000000000000) (31194824379 / 1000000000000), orderedInterval (-40983353764 / 1000000000000) (-40983342624 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2611652073591519 / 4000000000000) 2 (IntervalRat.scale (833 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (7633146853 / 1000000000000) (7633146854 / 1000000000000), orderedInterval (30272539985 / 1000000000000) (30272539986 / 1000000000000)))) (orderedInterval (994027738 / 1000000000000) (994027998 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1923731096940247 / 4000000000000) 2 (IntervalRat.scale (833 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-31635814879 / 1000000000000) (-31635814878 / 1000000000000), orderedInterval (-17936352787 / 1000000000000) (-17936352786 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3296346023553331 / 4000000000000) 2 (IntervalRat.scale (833 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (27219608289 / 1000000000000) (27219635367 / 1000000000000), orderedInterval (-5638605323 / 1000000000000) (-5638578245 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2428073561522329 / 4000000000000) 2 (IntervalRat.scale (833 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-32239852463 / 1000000000000) (-32239852148 / 1000000000000), orderedInterval (-3032331002 / 1000000000000) (-3032330687 / 1000000000000)))) (orderedInterval (4941229403 / 1000000000000) (4941232766 / 1000000000000))) = true
  rfl'

theorem compactCertificate545_chunkChecks2_1 :
    compactCertificate545.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3725289250514167 / 4000000000000) 2 (IntervalRat.scale (833 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (21197266265 / 1000000000000) (21197272593 / 1000000000000), orderedInterval (-15316323794 / 1000000000000) (-15316317466 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2150796751593343 / 4000000000000) 2 (IntervalRat.scale (833 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-32884354268 / 1000000000000) (-32884354258 / 1000000000000), orderedInterval (-10098041221 / 1000000000000) (-10098041211 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3816626578579787 / 4000000000000) 2 (IntervalRat.scale (833 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-2636678472 / 1000000000000) (-2636678471 / 1000000000000), orderedInterval (25696805119 / 1000000000000) (25696805120 / 1000000000000)))) (orderedInterval (24827995690 / 1000000000000) (24828002053 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3565987629487703 / 4000000000000) 2 (IntervalRat.scale (833 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (1865107511 / 1000000000000) (1865107512 / 1000000000000), orderedInterval (26656477065 / 1000000000000) (26656477066 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2544857035931399 / 4000000000000) 2 (IntervalRat.scale (833 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (21419375950 / 1000000000000) (21419379607 / 1000000000000), orderedInterval (-23294456784 / 1000000000000) (-23294453127 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2885596645409121 / 4000000000000) 2 (IntervalRat.scale (833 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-11071826944 / 1000000000000) (-11071826925 / 1000000000000), orderedInterval (27573849236 / 1000000000000) (27573849254 / 1000000000000)))) (orderedInterval (-4728808349 / 1000000000000) (-4728807407 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2405709644368849 / 4000000000000) 2 (IntervalRat.scale (833 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-26896024543 / 1000000000000) (-26895983370 / 1000000000000), orderedInterval (18328609571 / 1000000000000) (18328650745 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2125517428653829 / 4000000000000) 2 (IntervalRat.scale (833 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-32683802633 / 1000000000000) (-32683802628 / 1000000000000), orderedInterval (-11363104752 / 1000000000000) (-11363104746 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (616057796845071 / 800000000000) 2 (IntervalRat.scale (833 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-26443210009 / 1000000000000) (-26443209997 / 1000000000000), orderedInterval (-11272555384 / 1000000000000) (-11272555372 / 1000000000000)))) (orderedInterval (-83805397 / 1000000000000) (-83804316 / 1000000000000))) = true
  rfl'

theorem compactCertificate545_chunkChecks2_2 :
    compactCertificate545.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1704048287419037 / 4000000000000) 2 (IntervalRat.scale (833 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-17141789477 / 1000000000000) (-17141789016 / 1000000000000), orderedInterval (34668783113 / 1000000000000) (34668783573 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1444540605063157 / 4000000000000) 2 (IntervalRat.scale (833 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-24974356485 / 1000000000000) (-24974356484 / 1000000000000), orderedInterval (-33716151634 / 1000000000000) (-33716151633 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (903926438477671 / 4000000000000) 2 (IntervalRat.scale (833 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (28721481318 / 1000000000000) (28721481319 / 1000000000000), orderedInterval (44570634624 / 1000000000000) (44570634625 / 1000000000000)))) (orderedInterval (-4197696735 / 1000000000000) (-4197696565 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (486134644936857 / 4000000000000) 2 (IntervalRat.scale (833 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (14668204646 / 1000000000000) (14668204766 / 1000000000000), orderedInterval (-70934191884 / 1000000000000) (-70934191765 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1319950127661571 / 4000000000000) 2 (IntervalRat.scale (833 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-34550828542 / 1000000000000) (-34550828541 / 1000000000000), orderedInterval (-27067077534 / 1000000000000) (-27067077533 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1802279053314467 / 4000000000000) 2 (IntervalRat.scale (833 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-32310868815 / 1000000000000) (-32310773271 / 1000000000000), orderedInterval (19243408862 / 1000000000000) (19243504406 / 1000000000000)))) (orderedInterval (-3365186790 / 1000000000000) (-3365178156 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (762073561522329 / 4000000000000) 2 (IntervalRat.scale (833 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (18951199154 / 1000000000000) (18951199579 / 1000000000000), orderedInterval (-54660857044 / 1000000000000) (-54660856619 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3097786718529209 / 4000000000000) 2 (IntervalRat.scale (833 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (19363653646 / 1000000000000) (19363655282 / 1000000000000), orderedInterval (-21156784541 / 1000000000000) (-21156782906 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2069177963952631 / 4000000000000) 2 (IntervalRat.scale (833 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (9800639129 / 1000000000000) (9800639150 / 1000000000000), orderedInterval (-33693591131 / 1000000000000) (-33693591110 / 1000000000000)))) (orderedInterval (8236213033 / 1000000000000) (8236213740 / 1000000000000))) = true
  rfl'

theorem compactCertificate545_chunkChecks2 :
    compactCertificate545.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate545.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate545_chunkChecks2_0
    compactCertificate545_chunkChecks2_1 compactCertificate545_chunkChecks2_2

theorem compactCertificate545_chunkChecks3_0 :
    compactCertificate545.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (833 / 2) 3 (IntervalRat.scale (833 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (20325712717 / 1000000000000) (20325714119 / 1000000000000), orderedInterval (-33421477972 / 1000000000000) (-33421476570 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1227168059601533 / 4000000000000) 3 (IntervalRat.scale (833 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-13421570412 / 1000000000000) (-13421570290 / 1000000000000), orderedInterval (43552892616 / 1000000000000) (43552892738 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (396840936716189 / 800000000000) 3 (IntervalRat.scale (833 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (16054078154 / 1000000000000) (16054078155 / 1000000000000), orderedInterval (32009466737 / 1000000000000) (32009466738 / 1000000000000)))) (orderedInterval (9933874368 / 1000000000000) (9933874970 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (358084579191031 / 4000000000000) 3 (IntervalRat.scale (833 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (60554527654 / 1000000000000) (60554614815 / 1000000000000), orderedInterval (-59028363625 / 1000000000000) (-59028276464 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (961865548469707 / 4000000000000) 3 (IntervalRat.scale (833 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (31194813240 / 1000000000000) (31194824379 / 1000000000000), orderedInterval (-40983353764 / 1000000000000) (-40983342624 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2611652073591519 / 4000000000000) 3 (IntervalRat.scale (833 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (7633146853 / 1000000000000) (7633146854 / 1000000000000), orderedInterval (30272539985 / 1000000000000) (30272539986 / 1000000000000)))) (orderedInterval (8569620487 / 1000000000000) (8569620693 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1923731096940247 / 4000000000000) 3 (IntervalRat.scale (833 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-31635814879 / 1000000000000) (-31635814878 / 1000000000000), orderedInterval (-17936352787 / 1000000000000) (-17936352786 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3296346023553331 / 4000000000000) 3 (IntervalRat.scale (833 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (27219608289 / 1000000000000) (27219635367 / 1000000000000), orderedInterval (-5638605323 / 1000000000000) (-5638578245 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2428073561522329 / 4000000000000) 3 (IntervalRat.scale (833 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-32239852463 / 1000000000000) (-32239852148 / 1000000000000), orderedInterval (-3032331002 / 1000000000000) (-3032330687 / 1000000000000)))) (orderedInterval (-1132141274 / 1000000000000) (-1132134641 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate545_chunkChecks3_1 :
    compactCertificate545.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3725289250514167 / 4000000000000) 3 (IntervalRat.scale (833 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (21197266265 / 1000000000000) (21197272593 / 1000000000000), orderedInterval (-15316323794 / 1000000000000) (-15316317466 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2150796751593343 / 4000000000000) 3 (IntervalRat.scale (833 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-32884354268 / 1000000000000) (-32884354258 / 1000000000000), orderedInterval (-10098041221 / 1000000000000) (-10098041211 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3816626578579787 / 4000000000000) 3 (IntervalRat.scale (833 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-2636678472 / 1000000000000) (-2636678471 / 1000000000000), orderedInterval (25696805119 / 1000000000000) (25696805120 / 1000000000000)))) (orderedInterval (-72796850368 / 1000000000000) (-72796836173 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3565987629487703 / 4000000000000) 3 (IntervalRat.scale (833 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (1865107511 / 1000000000000) (1865107512 / 1000000000000), orderedInterval (26656477065 / 1000000000000) (26656477066 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2544857035931399 / 4000000000000) 3 (IntervalRat.scale (833 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (21419375950 / 1000000000000) (21419379607 / 1000000000000), orderedInterval (-23294456784 / 1000000000000) (-23294453127 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2885596645409121 / 4000000000000) 3 (IntervalRat.scale (833 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-11071826944 / 1000000000000) (-11071826925 / 1000000000000), orderedInterval (27573849236 / 1000000000000) (27573849254 / 1000000000000)))) (orderedInterval (13306840467 / 1000000000000) (13306841928 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2405709644368849 / 4000000000000) 3 (IntervalRat.scale (833 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-26896024543 / 1000000000000) (-26895983370 / 1000000000000), orderedInterval (18328609571 / 1000000000000) (18328650745 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2125517428653829 / 4000000000000) 3 (IntervalRat.scale (833 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-32683802633 / 1000000000000) (-32683802628 / 1000000000000), orderedInterval (-11363104752 / 1000000000000) (-11363104746 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (616057796845071 / 800000000000) 3 (IntervalRat.scale (833 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-26443210009 / 1000000000000) (-26443209997 / 1000000000000), orderedInterval (-11272555384 / 1000000000000) (-11272555372 / 1000000000000)))) (orderedInterval (-163254411 / 1000000000000) (-163252842 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate545_chunkChecks3_2 :
    compactCertificate545.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1704048287419037 / 4000000000000) 3 (IntervalRat.scale (833 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-17141789477 / 1000000000000) (-17141789016 / 1000000000000), orderedInterval (34668783113 / 1000000000000) (34668783573 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1444540605063157 / 4000000000000) 3 (IntervalRat.scale (833 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-24974356485 / 1000000000000) (-24974356484 / 1000000000000), orderedInterval (-33716151634 / 1000000000000) (-33716151633 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (903926438477671 / 4000000000000) 3 (IntervalRat.scale (833 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (28721481318 / 1000000000000) (28721481319 / 1000000000000), orderedInterval (44570634624 / 1000000000000) (44570634625 / 1000000000000)))) (orderedInterval (4466112493 / 1000000000000) (4466112661 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (486134644936857 / 4000000000000) 3 (IntervalRat.scale (833 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (14668204646 / 1000000000000) (14668204766 / 1000000000000), orderedInterval (-70934191884 / 1000000000000) (-70934191765 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1319950127661571 / 4000000000000) 3 (IntervalRat.scale (833 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-34550828542 / 1000000000000) (-34550828541 / 1000000000000), orderedInterval (-27067077534 / 1000000000000) (-27067077533 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1802279053314467 / 4000000000000) 3 (IntervalRat.scale (833 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-32310868815 / 1000000000000) (-32310773271 / 1000000000000), orderedInterval (19243408862 / 1000000000000) (19243504406 / 1000000000000)))) (orderedInterval (1537256744 / 1000000000000) (1537266081 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (762073561522329 / 4000000000000) 3 (IntervalRat.scale (833 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (18951199154 / 1000000000000) (18951199579 / 1000000000000), orderedInterval (-54660857044 / 1000000000000) (-54660856619 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3097786718529209 / 4000000000000) 3 (IntervalRat.scale (833 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (19363653646 / 1000000000000) (19363655282 / 1000000000000), orderedInterval (-21156784541 / 1000000000000) (-21156782906 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2069177963952631 / 4000000000000) 3 (IntervalRat.scale (833 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (9800639129 / 1000000000000) (9800639150 / 1000000000000), orderedInterval (-33693591131 / 1000000000000) (-33693591110 / 1000000000000)))) (orderedInterval (-23171681769 / 1000000000000) (-23171680535 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate545_chunkChecks3 :
    compactCertificate545.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate545.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate545_chunkChecks3_0
    compactCertificate545_chunkChecks3_1 compactCertificate545_chunkChecks3_2

theorem compactCertificate545_chunkChecks4_0 :
    compactCertificate545.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (833 / 2) 4 (IntervalRat.scale (833 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (20325712717 / 1000000000000) (20325714119 / 1000000000000), orderedInterval (-33421477972 / 1000000000000) (-33421476570 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1227168059601533 / 4000000000000) 4 (IntervalRat.scale (833 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-13421570412 / 1000000000000) (-13421570290 / 1000000000000), orderedInterval (43552892616 / 1000000000000) (43552892738 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (396840936716189 / 800000000000) 4 (IntervalRat.scale (833 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (16054078154 / 1000000000000) (16054078155 / 1000000000000), orderedInterval (32009466737 / 1000000000000) (32009466738 / 1000000000000)))) (orderedInterval (9867355375 / 1000000000000) (9867355985 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (358084579191031 / 4000000000000) 4 (IntervalRat.scale (833 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (60554527654 / 1000000000000) (60554614815 / 1000000000000), orderedInterval (-59028363625 / 1000000000000) (-59028276464 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (961865548469707 / 4000000000000) 4 (IntervalRat.scale (833 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (31194813240 / 1000000000000) (31194824379 / 1000000000000), orderedInterval (-40983353764 / 1000000000000) (-40983342624 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2611652073591519 / 4000000000000) 4 (IntervalRat.scale (833 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (7633146853 / 1000000000000) (7633146854 / 1000000000000), orderedInterval (30272539985 / 1000000000000) (30272539986 / 1000000000000)))) (orderedInterval (-3192954735 / 1000000000000) (-3192954506 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1923731096940247 / 4000000000000) 4 (IntervalRat.scale (833 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-31635814879 / 1000000000000) (-31635814878 / 1000000000000), orderedInterval (-17936352787 / 1000000000000) (-17936352786 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3296346023553331 / 4000000000000) 4 (IntervalRat.scale (833 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (27219608289 / 1000000000000) (27219635367 / 1000000000000), orderedInterval (-5638605323 / 1000000000000) (-5638578245 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2428073561522329 / 4000000000000) 4 (IntervalRat.scale (833 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-32239852463 / 1000000000000) (-32239852148 / 1000000000000), orderedInterval (-3032331002 / 1000000000000) (-3032330687 / 1000000000000)))) (orderedInterval (-16377195201 / 1000000000000) (-16377182092 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate545_chunkChecks4_1 :
    compactCertificate545.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3725289250514167 / 4000000000000) 4 (IntervalRat.scale (833 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (21197266265 / 1000000000000) (21197272593 / 1000000000000), orderedInterval (-15316323794 / 1000000000000) (-15316317466 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2150796751593343 / 4000000000000) 4 (IntervalRat.scale (833 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-32884354268 / 1000000000000) (-32884354258 / 1000000000000), orderedInterval (-10098041221 / 1000000000000) (-10098041211 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3816626578579787 / 4000000000000) 4 (IntervalRat.scale (833 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-2636678472 / 1000000000000) (-2636678471 / 1000000000000), orderedInterval (25696805119 / 1000000000000) (25696805120 / 1000000000000)))) (orderedInterval (-110904551179 / 1000000000000) (-110904519435 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3565987629487703 / 4000000000000) 4 (IntervalRat.scale (833 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (1865107511 / 1000000000000) (1865107512 / 1000000000000), orderedInterval (26656477065 / 1000000000000) (26656477066 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2544857035931399 / 4000000000000) 4 (IntervalRat.scale (833 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (21419375950 / 1000000000000) (21419379607 / 1000000000000), orderedInterval (-23294456784 / 1000000000000) (-23294453127 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2885596645409121 / 4000000000000) 4 (IntervalRat.scale (833 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-11071826944 / 1000000000000) (-11071826925 / 1000000000000), orderedInterval (27573849236 / 1000000000000) (27573849254 / 1000000000000)))) (orderedInterval (10761178353 / 1000000000000) (10761180635 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2405709644368849 / 4000000000000) 4 (IntervalRat.scale (833 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-26896024543 / 1000000000000) (-26895983370 / 1000000000000), orderedInterval (18328609571 / 1000000000000) (18328650745 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2125517428653829 / 4000000000000) 4 (IntervalRat.scale (833 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-32683802633 / 1000000000000) (-32683802628 / 1000000000000), orderedInterval (-11363104752 / 1000000000000) (-11363104746 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (616057796845071 / 800000000000) 4 (IntervalRat.scale (833 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-26443210009 / 1000000000000) (-26443209997 / 1000000000000), orderedInterval (-11272555384 / 1000000000000) (-11272555372 / 1000000000000)))) (orderedInterval (-4306081315 / 1000000000000) (-4306079027 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate545_chunkChecks4_2 :
    compactCertificate545.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1704048287419037 / 4000000000000) 4 (IntervalRat.scale (833 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-17141789477 / 1000000000000) (-17141789016 / 1000000000000), orderedInterval (34668783113 / 1000000000000) (34668783573 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1444540605063157 / 4000000000000) 4 (IntervalRat.scale (833 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-24974356485 / 1000000000000) (-24974356484 / 1000000000000), orderedInterval (-33716151634 / 1000000000000) (-33716151633 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (903926438477671 / 4000000000000) 4 (IntervalRat.scale (833 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (28721481318 / 1000000000000) (28721481319 / 1000000000000), orderedInterval (44570634624 / 1000000000000) (44570634625 / 1000000000000)))) (orderedInterval (3858464570 / 1000000000000) (3858464740 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (486134644936857 / 4000000000000) 4 (IntervalRat.scale (833 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (14668204646 / 1000000000000) (14668204766 / 1000000000000), orderedInterval (-70934191884 / 1000000000000) (-70934191765 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1319950127661571 / 4000000000000) 4 (IntervalRat.scale (833 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-34550828542 / 1000000000000) (-34550828541 / 1000000000000), orderedInterval (-27067077534 / 1000000000000) (-27067077533 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1802279053314467 / 4000000000000) 4 (IntervalRat.scale (833 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-32310868815 / 1000000000000) (-32310773271 / 1000000000000), orderedInterval (19243408862 / 1000000000000) (19243504406 / 1000000000000)))) (orderedInterval (3690939676 / 1000000000000) (3690949798 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (762073561522329 / 4000000000000) 4 (IntervalRat.scale (833 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (18951199154 / 1000000000000) (18951199579 / 1000000000000), orderedInterval (-54660857044 / 1000000000000) (-54660856619 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3097786718529209 / 4000000000000) 4 (IntervalRat.scale (833 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (19363653646 / 1000000000000) (19363655282 / 1000000000000), orderedInterval (-21156784541 / 1000000000000) (-21156782906 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2069177963952631 / 4000000000000) 4 (IntervalRat.scale (833 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (9800639129 / 1000000000000) (9800639150 / 1000000000000), orderedInterval (-33693591131 / 1000000000000) (-33693591110 / 1000000000000)))) (orderedInterval (-23101319757 / 1000000000000) (-23101317559 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate545_chunkChecks4 :
    compactCertificate545.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate545.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate545_chunkChecks4_0
    compactCertificate545_chunkChecks4_1 compactCertificate545_chunkChecks4_2

theorem compactCertificate545_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate545.chunkCheck r b = true :=
  compactCertificate545.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate545_chunkChecks0
    · exact compactCertificate545_chunkChecks1
    · exact compactCertificate545_chunkChecks2
    · exact compactCertificate545_chunkChecks3
    · exact compactCertificate545_chunkChecks4)

theorem compactCertificate545_coefficient0 :
    compactCertificate545.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate545_coefficient1 :
    compactCertificate545.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate545_coefficient2 :
    compactCertificate545.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate545_coefficient3 :
    compactCertificate545.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate545_coefficient4 :
    compactCertificate545.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate545_coefficients : ∀ r : Fin 5,
    compactCertificate545.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate545_coefficient0
  · exact compactCertificate545_coefficient1
  · exact compactCertificate545_coefficient2
  · exact compactCertificate545_coefficient3
  · exact compactCertificate545_coefficient4

theorem compactCertificate545_lower : (1 : ℚ) ≤ compactCertificate545.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate545, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate545_proves {t : ℝ} (ht : t ∈ compactCertificate545.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate545.proves compactCertificate545_states compactCertificate545_chunks
    compactCertificate545_coefficients compactCertificate545_lower ht

end Erdos232
