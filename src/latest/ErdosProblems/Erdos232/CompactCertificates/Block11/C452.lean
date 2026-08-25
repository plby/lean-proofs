/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate452 : CompactCertificate where
  left := 323
  right := 324
  center := 647 / 2
  grid := fun i =>
    match i.val with
    | 0 => 103
    | 1 => 76
    | 2 => 123
    | 3 => 22
    | 4 => 59
    | 5 => 162
    | 6 => 119
    | 7 => 204
    | 8 => 150
    | 9 => 230
    | 10 => 133
    | 11 => 236
    | 12 => 221
    | 13 => 157
    | 14 => 178
    | 15 => 149
    | 16 => 131
    | 17 => 190
    | 18 => 105
    | 19 => 89
    | 20 => 56
    | 21 => 30
    | 22 => 82
    | 23 => 111
    | 24 => 47
    | 25 => 192
    | _ => 128
  point := fun i =>
    match i.val with
    | 0 => 647 / 2
    | 1 => 953154543291947 / 4000000000000
    | 2 => 308230595504651 / 800000000000
    | 3 => 278128118531329 / 4000000000000
    | 4 => 747091248331213 / 4000000000000
    | 5 => 2028498069164121 / 4000000000000
    | 6 => 1494182496663073 / 4000000000000
    | 7 => 2560307175557029 / 4000000000000
    | 8 => 1885910677436911 / 4000000000000
    | 9 => 2893471962884353 / 4000000000000
    | 10 => 1670546816663737 / 4000000000000
    | 11 => 2964414641465933 / 4000000000000
    | 12 => 2769740691810977 / 4000000000000
    | 13 => 1976617649757041 / 4000000000000
    | 14 => 2241273744993639 / 4000000000000
    | 15 => 1868540384041591 / 4000000000000
    | 16 => 1650912096445411 / 4000000000000
    | 17 => 478498672939689 / 800000000000
    | 18 => 1323552511356683 / 4000000000000
    | 19 => 1121990121819763 / 4000000000000
    | 20 => 702089322563089 / 4000000000000
    | 21 => 377585972718063 / 4000000000000
    | 22 => 1025219366863189 / 4000000000000
    | 23 => 1399849396752053 / 4000000000000
    | 24 => 591910677436911 / 4000000000000
    | 25 => 2406084041882831 / 4000000000000
    | _ => 1607152632265729 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-28611073761 / 1000000000000) (-28611073760 / 1000000000000), orderedInterval (-33857395398 / 1000000000000) (-33857395397 / 1000000000000))
    | 1 => (orderedInterval (15889229232 / 1000000000000) (15889229233 / 1000000000000), orderedInterval (49151719768 / 1000000000000) (49151719769 / 1000000000000))
    | 2 => (orderedInterval (13654586329 / 1000000000000) (13654586459 / 1000000000000), orderedInterval (-38304455654 / 1000000000000) (-38304455525 / 1000000000000))
    | 3 => (orderedInterval (89202282887 / 1000000000000) (89202282888 / 1000000000000), orderedInterval (33978742500 / 1000000000000) (33978742501 / 1000000000000))
    | 4 => (orderedInterval (-47078937325 / 1000000000000) (-47078867508 / 1000000000000), orderedInterval (34652767499 / 1000000000000) (34652837316 / 1000000000000))
    | 5 => (orderedInterval (-30344651638 / 1000000000000) (-30344551407 / 1000000000000), orderedInterval (18320760423 / 1000000000000) (18320860654 / 1000000000000))
    | 6 => (orderedInterval (-19106022684 / 1000000000000) (-19106022683 / 1000000000000), orderedInterval (-36569824753 / 1000000000000) (-36569824752 / 1000000000000))
    | 7 => (orderedInterval (-722284167 / 1000000000000) (-722284166 / 1000000000000), orderedInterval (31529561356 / 1000000000000) (31529561357 / 1000000000000))
    | 8 => (orderedInterval (31386359402 / 1000000000000) (31386359403 / 1000000000000), orderedInterval (19075902428 / 1000000000000) (19075902429 / 1000000000000))
    | 9 => (orderedInterval (29662243295 / 1000000000000) (29662245714 / 1000000000000), orderedInterval (-498387345 / 1000000000000) (-498384925 / 1000000000000))
    | 10 => (orderedInterval (-21721227517 / 1000000000000) (-21721227516 / 1000000000000), orderedInterval (-32416672978 / 1000000000000) (-32416672977 / 1000000000000))
    | 11 => (orderedInterval (13352578974 / 1000000000000) (13352578975 / 1000000000000), orderedInterval (26081690426 / 1000000000000) (26081690427 / 1000000000000))
    | 12 => (orderedInterval (26621040512 / 1000000000000) (26621105687 / 1000000000000), orderedInterval (-14535138948 / 1000000000000) (-14535073772 / 1000000000000))
    | 13 => (orderedInterval (-35548138286 / 1000000000000) (-35548135689 / 1000000000000), orderedInterval (4998891896 / 1000000000000) (4998894493 / 1000000000000))
    | 14 => (orderedInterval (31895804890 / 1000000000000) (31895830015 / 1000000000000), orderedInterval (-10929456184 / 1000000000000) (-10929431058 / 1000000000000))
    | 15 => (orderedInterval (6502991567 / 1000000000000) (6502991573 / 1000000000000), orderedInterval (-36346045442 / 1000000000000) (-36346045436 / 1000000000000))
    | 16 => (orderedInterval (-36269846068 / 1000000000000) (-36269823268 / 1000000000000), orderedInterval (15109327341 / 1000000000000) (15109350140 / 1000000000000))
    | 17 => (orderedInterval (29584407914 / 1000000000000) (29584484318 / 1000000000000), orderedInterval (-13776942029 / 1000000000000) (-13776865624 / 1000000000000))
    | 18 => (orderedInterval (-42656225950 / 1000000000000) (-42656222930 / 1000000000000), orderedInterval (10282938633 / 1000000000000) (10282941654 / 1000000000000))
    | 19 => (orderedInterval (-47352755278 / 1000000000000) (-47352754758 / 1000000000000), orderedInterval (5311477949 / 1000000000000) (5311478468 / 1000000000000))
    | 20 => (orderedInterval (22216963095 / 1000000000000) (22216963096 / 1000000000000), orderedInterval (55913661660 / 1000000000000) (55913661661 / 1000000000000))
    | 21 => (orderedInterval (65967169856 / 1000000000000) (65967169857 / 1000000000000), orderedInterval (48562853382 / 1000000000000) (48562853383 / 1000000000000))
    | 22 => (orderedInterval (-24800105486 / 1000000000000) (-24800102867 / 1000000000000), orderedInterval (43277945724 / 1000000000000) (43277948343 / 1000000000000))
    | 23 => (orderedInterval (-38221156974 / 1000000000000) (-38221125652 / 1000000000000), orderedInterval (18982151014 / 1000000000000) (18982182336 / 1000000000000))
    | 24 => (orderedInterval (-58672331938 / 1000000000000) (-58672331937 / 1000000000000), orderedInterval (-29122000383 / 1000000000000) (-29122000382 / 1000000000000))
    | 25 => (orderedInterval (-25065377939 / 1000000000000) (-25065360618 / 1000000000000), orderedInterval (20759128927 / 1000000000000) (20759146249 / 1000000000000))
    | _ => (orderedInterval (17291920639 / 1000000000000) (17291920640 / 1000000000000), orderedInterval (35831744571 / 1000000000000) (35831744572 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-10391104579 / 1000000000000) (-10391104548 / 1000000000000)
      | 1 => orderedInterval (-529532480 / 1000000000000) (-529522766 / 1000000000000)
      | 2 => orderedInterval (780824506 / 1000000000000) (780824524 / 1000000000000)
      | 3 => orderedInterval (-4981839426 / 1000000000000) (-4981838868 / 1000000000000)
      | 4 => orderedInterval (-4003538239 / 1000000000000) (-4003536651 / 1000000000000)
      | 5 => orderedInterval (2908173547 / 1000000000000) (2908176839 / 1000000000000)
      | 6 => orderedInterval (10223850700 / 1000000000000) (10223851294 / 1000000000000)
      | 7 => orderedInterval (2273768862 / 1000000000000) (2273771361 / 1000000000000)
      | _ => orderedInterval (-1557754226 / 1000000000000) (-1557752726 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-15759593984 / 1000000000000) (-15759593949 / 1000000000000)
      | 1 => orderedInterval (-1390455544 / 1000000000000) (-1390442857 / 1000000000000)
      | 2 => orderedInterval (-1252270149 / 1000000000000) (-1252270116 / 1000000000000)
      | 3 => orderedInterval (5591161021 / 1000000000000) (5591162248 / 1000000000000)
      | 4 => orderedInterval (1379534138 / 1000000000000) (1379537315 / 1000000000000)
      | 5 => orderedInterval (-2361407495 / 1000000000000) (-2361402168 / 1000000000000)
      | 6 => orderedInterval (-954744457 / 1000000000000) (-954743861 / 1000000000000)
      | 7 => orderedInterval (-2613333702 / 1000000000000) (-2613331023 / 1000000000000)
      | _ => orderedInterval (-11572376187 / 1000000000000) (-11572373439 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (10172232254 / 1000000000000) (10172232295 / 1000000000000)
      | 1 => orderedInterval (-4679153462 / 1000000000000) (-4679135001 / 1000000000000)
      | 2 => orderedInterval (-1694568315 / 1000000000000) (-1694568258 / 1000000000000)
      | 3 => orderedInterval (19056267003 / 1000000000000) (19056269725 / 1000000000000)
      | 4 => orderedInterval (10525389331 / 1000000000000) (10525395790 / 1000000000000)
      | 5 => orderedInterval (-6117209041 / 1000000000000) (-6117200147 / 1000000000000)
      | 6 => orderedInterval (-9360448065 / 1000000000000) (-9360447464 / 1000000000000)
      | 7 => orderedInterval (-3669432661 / 1000000000000) (-3669429771 / 1000000000000)
      | _ => orderedInterval (-1939879259 / 1000000000000) (-1939874190 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (17002613359 / 1000000000000) (17002613406 / 1000000000000)
      | 1 => orderedInterval (4791924809 / 1000000000000) (4791952898 / 1000000000000)
      | 2 => orderedInterval (6110916690 / 1000000000000) (6110916793 / 1000000000000)
      | 3 => orderedInterval (-40458474514 / 1000000000000) (-40458468449 / 1000000000000)
      | 4 => orderedInterval (-4578031733 / 1000000000000) (-4578018463 / 1000000000000)
      | 5 => orderedInterval (5307731472 / 1000000000000) (5307746677 / 1000000000000)
      | 6 => orderedInterval (1693557926 / 1000000000000) (1693558534 / 1000000000000)
      | 7 => orderedInterval (2363670348 / 1000000000000) (2363673462 / 1000000000000)
      | _ => orderedInterval (23766699627 / 1000000000000) (23766708994 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-9789646181 / 1000000000000) (-9789646125 / 1000000000000)
      | 1 => orderedInterval (12804388969 / 1000000000000) (12804432595 / 1000000000000)
      | 2 => orderedInterval (3726030391 / 1000000000000) (3726030581 / 1000000000000)
      | 3 => orderedInterval (-83704137889 / 1000000000000) (-83704124338 / 1000000000000)
      | 4 => orderedInterval (-29813791949 / 1000000000000) (-29813764384 / 1000000000000)
      | 5 => orderedInterval (14644748796 / 1000000000000) (14644775370 / 1000000000000)
      | 6 => orderedInterval (9032148738 / 1000000000000) (9032149356 / 1000000000000)
      | 7 => orderedInterval (4210030365 / 1000000000000) (4210033733 / 1000000000000)
      | _ => orderedInterval (16507474341 / 1000000000000) (16507491712 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-5277151335 / 1000000000000) (-5277131541 / 1000000000000)
    | 1 => orderedInterval (-28933486359 / 1000000000000) (-28933457850 / 1000000000000)
    | 2 => orderedInterval (12293197785 / 1000000000000) (12293242979 / 1000000000000)
    | 3 => orderedInterval (16000607984 / 1000000000000) (16000683852 / 1000000000000)
    | _ => orderedInterval (-62382754419 / 1000000000000) (-62382621500 / 1000000000000)

theorem compactCertificate452_stateChecks0 :
    compactCertificate452.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 103 12 (647 / 2)) (orderedInterval (-28611073761 / 1000000000000) (-28611073760 / 1000000000000), orderedInterval (-33857395398 / 1000000000000) (-33857395397 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (953154543291947 / 4000000000000)) (orderedInterval (15889229232 / 1000000000000) (15889229233 / 1000000000000), orderedInterval (49151719768 / 1000000000000) (49151719769 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 123 12 (308230595504651 / 800000000000)) (orderedInterval (13654586329 / 1000000000000) (13654586459 / 1000000000000), orderedInterval (-38304455654 / 1000000000000) (-38304455525 / 1000000000000))) = true
  rfl'

theorem compactCertificate452_stateChecks1 :
    compactCertificate452.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 22 12 (278128118531329 / 4000000000000)) (orderedInterval (89202282887 / 1000000000000) (89202282888 / 1000000000000), orderedInterval (33978742500 / 1000000000000) (33978742501 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (747091248331213 / 4000000000000)) (orderedInterval (-47078937325 / 1000000000000) (-47078867508 / 1000000000000), orderedInterval (34652767499 / 1000000000000) (34652837316 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 162 12 (2028498069164121 / 4000000000000)) (orderedInterval (-30344651638 / 1000000000000) (-30344551407 / 1000000000000), orderedInterval (18320760423 / 1000000000000) (18320860654 / 1000000000000))) = true
  rfl'

theorem compactCertificate452_stateChecks2 :
    compactCertificate452.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 119 12 (1494182496663073 / 4000000000000)) (orderedInterval (-19106022684 / 1000000000000) (-19106022683 / 1000000000000), orderedInterval (-36569824753 / 1000000000000) (-36569824752 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 204 12 (2560307175557029 / 4000000000000)) (orderedInterval (-722284167 / 1000000000000) (-722284166 / 1000000000000), orderedInterval (31529561356 / 1000000000000) (31529561357 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 150 12 (1885910677436911 / 4000000000000)) (orderedInterval (31386359402 / 1000000000000) (31386359403 / 1000000000000), orderedInterval (19075902428 / 1000000000000) (19075902429 / 1000000000000))) = true
  rfl'

theorem compactCertificate452_stateChecks3 :
    compactCertificate452.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 230 12 (2893471962884353 / 4000000000000)) (orderedInterval (29662243295 / 1000000000000) (29662245714 / 1000000000000), orderedInterval (-498387345 / 1000000000000) (-498384925 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 133 12 (1670546816663737 / 4000000000000)) (orderedInterval (-21721227517 / 1000000000000) (-21721227516 / 1000000000000), orderedInterval (-32416672978 / 1000000000000) (-32416672977 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 236 12 (2964414641465933 / 4000000000000)) (orderedInterval (13352578974 / 1000000000000) (13352578975 / 1000000000000), orderedInterval (26081690426 / 1000000000000) (26081690427 / 1000000000000))) = true
  rfl'

theorem compactCertificate452_stateChecks4 :
    compactCertificate452.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 221 12 (2769740691810977 / 4000000000000)) (orderedInterval (26621040512 / 1000000000000) (26621105687 / 1000000000000), orderedInterval (-14535138948 / 1000000000000) (-14535073772 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 157 12 (1976617649757041 / 4000000000000)) (orderedInterval (-35548138286 / 1000000000000) (-35548135689 / 1000000000000), orderedInterval (4998891896 / 1000000000000) (4998894493 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 178 12 (2241273744993639 / 4000000000000)) (orderedInterval (31895804890 / 1000000000000) (31895830015 / 1000000000000), orderedInterval (-10929456184 / 1000000000000) (-10929431058 / 1000000000000))) = true
  rfl'

theorem compactCertificate452_stateChecks5 :
    compactCertificate452.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 149 12 (1868540384041591 / 4000000000000)) (orderedInterval (6502991567 / 1000000000000) (6502991573 / 1000000000000), orderedInterval (-36346045442 / 1000000000000) (-36346045436 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 131 12 (1650912096445411 / 4000000000000)) (orderedInterval (-36269846068 / 1000000000000) (-36269823268 / 1000000000000), orderedInterval (15109327341 / 1000000000000) (15109350140 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 190 12 (478498672939689 / 800000000000)) (orderedInterval (29584407914 / 1000000000000) (29584484318 / 1000000000000), orderedInterval (-13776942029 / 1000000000000) (-13776865624 / 1000000000000))) = true
  rfl'

theorem compactCertificate452_stateChecks6 :
    compactCertificate452.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 105 12 (1323552511356683 / 4000000000000)) (orderedInterval (-42656225950 / 1000000000000) (-42656222930 / 1000000000000), orderedInterval (10282938633 / 1000000000000) (10282941654 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (1121990121819763 / 4000000000000)) (orderedInterval (-47352755278 / 1000000000000) (-47352754758 / 1000000000000), orderedInterval (5311477949 / 1000000000000) (5311478468 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (702089322563089 / 4000000000000)) (orderedInterval (22216963095 / 1000000000000) (22216963096 / 1000000000000), orderedInterval (55913661660 / 1000000000000) (55913661661 / 1000000000000))) = true
  rfl'

theorem compactCertificate452_stateChecks7 :
    compactCertificate452.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (377585972718063 / 4000000000000)) (orderedInterval (65967169856 / 1000000000000) (65967169857 / 1000000000000), orderedInterval (48562853382 / 1000000000000) (48562853383 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (1025219366863189 / 4000000000000)) (orderedInterval (-24800105486 / 1000000000000) (-24800102867 / 1000000000000), orderedInterval (43277945724 / 1000000000000) (43277948343 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 111 12 (1399849396752053 / 4000000000000)) (orderedInterval (-38221156974 / 1000000000000) (-38221125652 / 1000000000000), orderedInterval (18982151014 / 1000000000000) (18982182336 / 1000000000000))) = true
  rfl'

theorem compactCertificate452_stateChecks8 :
    compactCertificate452.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (591910677436911 / 4000000000000)) (orderedInterval (-58672331938 / 1000000000000) (-58672331937 / 1000000000000), orderedInterval (-29122000383 / 1000000000000) (-29122000382 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 192 12 (2406084041882831 / 4000000000000)) (orderedInterval (-25065377939 / 1000000000000) (-25065360618 / 1000000000000), orderedInterval (20759128927 / 1000000000000) (20759146249 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 128 12 (1607152632265729 / 4000000000000)) (orderedInterval (17291920639 / 1000000000000) (17291920640 / 1000000000000), orderedInterval (35831744571 / 1000000000000) (35831744572 / 1000000000000))) = true
  rfl'

theorem compactCertificate452_states : ∀ j,
    BesselStateValid (compactCertificate452.point j) (compactCertificate452.state j) :=
  compactCertificate452.statesValid_of_checks3 compactCertificate452_stateChecks0
    compactCertificate452_stateChecks1 compactCertificate452_stateChecks2
    compactCertificate452_stateChecks3 compactCertificate452_stateChecks4
    compactCertificate452_stateChecks5 compactCertificate452_stateChecks6
    compactCertificate452_stateChecks7 compactCertificate452_stateChecks8

theorem compactCertificate452_chunkChecks0_0 :
    compactCertificate452.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (647 / 2) 0 (IntervalRat.scale (647 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-28611073761 / 1000000000000) (-28611073760 / 1000000000000), orderedInterval (-33857395398 / 1000000000000) (-33857395397 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (953154543291947 / 4000000000000) 0 (IntervalRat.scale (647 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (15889229232 / 1000000000000) (15889229233 / 1000000000000), orderedInterval (49151719768 / 1000000000000) (49151719769 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (308230595504651 / 800000000000) 0 (IntervalRat.scale (647 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (13654586329 / 1000000000000) (13654586459 / 1000000000000), orderedInterval (-38304455654 / 1000000000000) (-38304455525 / 1000000000000)))) (orderedInterval (-10391104579 / 1000000000000) (-10391104548 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (278128118531329 / 4000000000000) 0 (IntervalRat.scale (647 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (89202282887 / 1000000000000) (89202282888 / 1000000000000), orderedInterval (33978742500 / 1000000000000) (33978742501 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (747091248331213 / 4000000000000) 0 (IntervalRat.scale (647 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-47078937325 / 1000000000000) (-47078867508 / 1000000000000), orderedInterval (34652767499 / 1000000000000) (34652837316 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2028498069164121 / 4000000000000) 0 (IntervalRat.scale (647 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30344651638 / 1000000000000) (-30344551407 / 1000000000000), orderedInterval (18320760423 / 1000000000000) (18320860654 / 1000000000000)))) (orderedInterval (-529532480 / 1000000000000) (-529522766 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1494182496663073 / 4000000000000) 0 (IntervalRat.scale (647 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-19106022684 / 1000000000000) (-19106022683 / 1000000000000), orderedInterval (-36569824753 / 1000000000000) (-36569824752 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2560307175557029 / 4000000000000) 0 (IntervalRat.scale (647 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-722284167 / 1000000000000) (-722284166 / 1000000000000), orderedInterval (31529561356 / 1000000000000) (31529561357 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1885910677436911 / 4000000000000) 0 (IntervalRat.scale (647 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (31386359402 / 1000000000000) (31386359403 / 1000000000000), orderedInterval (19075902428 / 1000000000000) (19075902429 / 1000000000000)))) (orderedInterval (780824506 / 1000000000000) (780824524 / 1000000000000))) = true
  rfl'

theorem compactCertificate452_chunkChecks0_1 :
    compactCertificate452.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2893471962884353 / 4000000000000) 0 (IntervalRat.scale (647 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (29662243295 / 1000000000000) (29662245714 / 1000000000000), orderedInterval (-498387345 / 1000000000000) (-498384925 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1670546816663737 / 4000000000000) 0 (IntervalRat.scale (647 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-21721227517 / 1000000000000) (-21721227516 / 1000000000000), orderedInterval (-32416672978 / 1000000000000) (-32416672977 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2964414641465933 / 4000000000000) 0 (IntervalRat.scale (647 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (13352578974 / 1000000000000) (13352578975 / 1000000000000), orderedInterval (26081690426 / 1000000000000) (26081690427 / 1000000000000)))) (orderedInterval (-4981839426 / 1000000000000) (-4981838868 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2769740691810977 / 4000000000000) 0 (IntervalRat.scale (647 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (26621040512 / 1000000000000) (26621105687 / 1000000000000), orderedInterval (-14535138948 / 1000000000000) (-14535073772 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1976617649757041 / 4000000000000) 0 (IntervalRat.scale (647 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-35548138286 / 1000000000000) (-35548135689 / 1000000000000), orderedInterval (4998891896 / 1000000000000) (4998894493 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2241273744993639 / 4000000000000) 0 (IntervalRat.scale (647 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (31895804890 / 1000000000000) (31895830015 / 1000000000000), orderedInterval (-10929456184 / 1000000000000) (-10929431058 / 1000000000000)))) (orderedInterval (-4003538239 / 1000000000000) (-4003536651 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1868540384041591 / 4000000000000) 0 (IntervalRat.scale (647 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (6502991567 / 1000000000000) (6502991573 / 1000000000000), orderedInterval (-36346045442 / 1000000000000) (-36346045436 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1650912096445411 / 4000000000000) 0 (IntervalRat.scale (647 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-36269846068 / 1000000000000) (-36269823268 / 1000000000000), orderedInterval (15109327341 / 1000000000000) (15109350140 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (478498672939689 / 800000000000) 0 (IntervalRat.scale (647 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (29584407914 / 1000000000000) (29584484318 / 1000000000000), orderedInterval (-13776942029 / 1000000000000) (-13776865624 / 1000000000000)))) (orderedInterval (2908173547 / 1000000000000) (2908176839 / 1000000000000))) = true
  rfl'

theorem compactCertificate452_chunkChecks0_2 :
    compactCertificate452.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1323552511356683 / 4000000000000) 0 (IntervalRat.scale (647 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-42656225950 / 1000000000000) (-42656222930 / 1000000000000), orderedInterval (10282938633 / 1000000000000) (10282941654 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1121990121819763 / 4000000000000) 0 (IntervalRat.scale (647 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-47352755278 / 1000000000000) (-47352754758 / 1000000000000), orderedInterval (5311477949 / 1000000000000) (5311478468 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (702089322563089 / 4000000000000) 0 (IntervalRat.scale (647 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (22216963095 / 1000000000000) (22216963096 / 1000000000000), orderedInterval (55913661660 / 1000000000000) (55913661661 / 1000000000000)))) (orderedInterval (10223850700 / 1000000000000) (10223851294 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (377585972718063 / 4000000000000) 0 (IntervalRat.scale (647 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (65967169856 / 1000000000000) (65967169857 / 1000000000000), orderedInterval (48562853382 / 1000000000000) (48562853383 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1025219366863189 / 4000000000000) 0 (IntervalRat.scale (647 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-24800105486 / 1000000000000) (-24800102867 / 1000000000000), orderedInterval (43277945724 / 1000000000000) (43277948343 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1399849396752053 / 4000000000000) 0 (IntervalRat.scale (647 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-38221156974 / 1000000000000) (-38221125652 / 1000000000000), orderedInterval (18982151014 / 1000000000000) (18982182336 / 1000000000000)))) (orderedInterval (2273768862 / 1000000000000) (2273771361 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (591910677436911 / 4000000000000) 0 (IntervalRat.scale (647 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-58672331938 / 1000000000000) (-58672331937 / 1000000000000), orderedInterval (-29122000383 / 1000000000000) (-29122000382 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2406084041882831 / 4000000000000) 0 (IntervalRat.scale (647 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25065377939 / 1000000000000) (-25065360618 / 1000000000000), orderedInterval (20759128927 / 1000000000000) (20759146249 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1607152632265729 / 4000000000000) 0 (IntervalRat.scale (647 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (17291920639 / 1000000000000) (17291920640 / 1000000000000), orderedInterval (35831744571 / 1000000000000) (35831744572 / 1000000000000)))) (orderedInterval (-1557754226 / 1000000000000) (-1557752726 / 1000000000000))) = true
  rfl'

theorem compactCertificate452_chunkChecks0 :
    compactCertificate452.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate452.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate452_chunkChecks0_0
    compactCertificate452_chunkChecks0_1 compactCertificate452_chunkChecks0_2

theorem compactCertificate452_chunkChecks1_0 :
    compactCertificate452.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (647 / 2) 1 (IntervalRat.scale (647 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-28611073761 / 1000000000000) (-28611073760 / 1000000000000), orderedInterval (-33857395398 / 1000000000000) (-33857395397 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (953154543291947 / 4000000000000) 1 (IntervalRat.scale (647 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (15889229232 / 1000000000000) (15889229233 / 1000000000000), orderedInterval (49151719768 / 1000000000000) (49151719769 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (308230595504651 / 800000000000) 1 (IntervalRat.scale (647 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (13654586329 / 1000000000000) (13654586459 / 1000000000000), orderedInterval (-38304455654 / 1000000000000) (-38304455525 / 1000000000000)))) (orderedInterval (-15759593984 / 1000000000000) (-15759593949 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (278128118531329 / 4000000000000) 1 (IntervalRat.scale (647 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (89202282887 / 1000000000000) (89202282888 / 1000000000000), orderedInterval (33978742500 / 1000000000000) (33978742501 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (747091248331213 / 4000000000000) 1 (IntervalRat.scale (647 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-47078937325 / 1000000000000) (-47078867508 / 1000000000000), orderedInterval (34652767499 / 1000000000000) (34652837316 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2028498069164121 / 4000000000000) 1 (IntervalRat.scale (647 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30344651638 / 1000000000000) (-30344551407 / 1000000000000), orderedInterval (18320760423 / 1000000000000) (18320860654 / 1000000000000)))) (orderedInterval (-1390455544 / 1000000000000) (-1390442857 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1494182496663073 / 4000000000000) 1 (IntervalRat.scale (647 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-19106022684 / 1000000000000) (-19106022683 / 1000000000000), orderedInterval (-36569824753 / 1000000000000) (-36569824752 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2560307175557029 / 4000000000000) 1 (IntervalRat.scale (647 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-722284167 / 1000000000000) (-722284166 / 1000000000000), orderedInterval (31529561356 / 1000000000000) (31529561357 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1885910677436911 / 4000000000000) 1 (IntervalRat.scale (647 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (31386359402 / 1000000000000) (31386359403 / 1000000000000), orderedInterval (19075902428 / 1000000000000) (19075902429 / 1000000000000)))) (orderedInterval (-1252270149 / 1000000000000) (-1252270116 / 1000000000000))) = true
  rfl'

theorem compactCertificate452_chunkChecks1_1 :
    compactCertificate452.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2893471962884353 / 4000000000000) 1 (IntervalRat.scale (647 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (29662243295 / 1000000000000) (29662245714 / 1000000000000), orderedInterval (-498387345 / 1000000000000) (-498384925 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1670546816663737 / 4000000000000) 1 (IntervalRat.scale (647 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-21721227517 / 1000000000000) (-21721227516 / 1000000000000), orderedInterval (-32416672978 / 1000000000000) (-32416672977 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2964414641465933 / 4000000000000) 1 (IntervalRat.scale (647 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (13352578974 / 1000000000000) (13352578975 / 1000000000000), orderedInterval (26081690426 / 1000000000000) (26081690427 / 1000000000000)))) (orderedInterval (5591161021 / 1000000000000) (5591162248 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2769740691810977 / 4000000000000) 1 (IntervalRat.scale (647 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (26621040512 / 1000000000000) (26621105687 / 1000000000000), orderedInterval (-14535138948 / 1000000000000) (-14535073772 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1976617649757041 / 4000000000000) 1 (IntervalRat.scale (647 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-35548138286 / 1000000000000) (-35548135689 / 1000000000000), orderedInterval (4998891896 / 1000000000000) (4998894493 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2241273744993639 / 4000000000000) 1 (IntervalRat.scale (647 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (31895804890 / 1000000000000) (31895830015 / 1000000000000), orderedInterval (-10929456184 / 1000000000000) (-10929431058 / 1000000000000)))) (orderedInterval (1379534138 / 1000000000000) (1379537315 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1868540384041591 / 4000000000000) 1 (IntervalRat.scale (647 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (6502991567 / 1000000000000) (6502991573 / 1000000000000), orderedInterval (-36346045442 / 1000000000000) (-36346045436 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1650912096445411 / 4000000000000) 1 (IntervalRat.scale (647 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-36269846068 / 1000000000000) (-36269823268 / 1000000000000), orderedInterval (15109327341 / 1000000000000) (15109350140 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (478498672939689 / 800000000000) 1 (IntervalRat.scale (647 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (29584407914 / 1000000000000) (29584484318 / 1000000000000), orderedInterval (-13776942029 / 1000000000000) (-13776865624 / 1000000000000)))) (orderedInterval (-2361407495 / 1000000000000) (-2361402168 / 1000000000000))) = true
  rfl'

theorem compactCertificate452_chunkChecks1_2 :
    compactCertificate452.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1323552511356683 / 4000000000000) 1 (IntervalRat.scale (647 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-42656225950 / 1000000000000) (-42656222930 / 1000000000000), orderedInterval (10282938633 / 1000000000000) (10282941654 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1121990121819763 / 4000000000000) 1 (IntervalRat.scale (647 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-47352755278 / 1000000000000) (-47352754758 / 1000000000000), orderedInterval (5311477949 / 1000000000000) (5311478468 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (702089322563089 / 4000000000000) 1 (IntervalRat.scale (647 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (22216963095 / 1000000000000) (22216963096 / 1000000000000), orderedInterval (55913661660 / 1000000000000) (55913661661 / 1000000000000)))) (orderedInterval (-954744457 / 1000000000000) (-954743861 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (377585972718063 / 4000000000000) 1 (IntervalRat.scale (647 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (65967169856 / 1000000000000) (65967169857 / 1000000000000), orderedInterval (48562853382 / 1000000000000) (48562853383 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1025219366863189 / 4000000000000) 1 (IntervalRat.scale (647 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-24800105486 / 1000000000000) (-24800102867 / 1000000000000), orderedInterval (43277945724 / 1000000000000) (43277948343 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1399849396752053 / 4000000000000) 1 (IntervalRat.scale (647 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-38221156974 / 1000000000000) (-38221125652 / 1000000000000), orderedInterval (18982151014 / 1000000000000) (18982182336 / 1000000000000)))) (orderedInterval (-2613333702 / 1000000000000) (-2613331023 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (591910677436911 / 4000000000000) 1 (IntervalRat.scale (647 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-58672331938 / 1000000000000) (-58672331937 / 1000000000000), orderedInterval (-29122000383 / 1000000000000) (-29122000382 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2406084041882831 / 4000000000000) 1 (IntervalRat.scale (647 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25065377939 / 1000000000000) (-25065360618 / 1000000000000), orderedInterval (20759128927 / 1000000000000) (20759146249 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1607152632265729 / 4000000000000) 1 (IntervalRat.scale (647 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (17291920639 / 1000000000000) (17291920640 / 1000000000000), orderedInterval (35831744571 / 1000000000000) (35831744572 / 1000000000000)))) (orderedInterval (-11572376187 / 1000000000000) (-11572373439 / 1000000000000))) = true
  rfl'

theorem compactCertificate452_chunkChecks1 :
    compactCertificate452.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate452.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate452_chunkChecks1_0
    compactCertificate452_chunkChecks1_1 compactCertificate452_chunkChecks1_2

theorem compactCertificate452_chunkChecks2_0 :
    compactCertificate452.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (647 / 2) 2 (IntervalRat.scale (647 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-28611073761 / 1000000000000) (-28611073760 / 1000000000000), orderedInterval (-33857395398 / 1000000000000) (-33857395397 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (953154543291947 / 4000000000000) 2 (IntervalRat.scale (647 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (15889229232 / 1000000000000) (15889229233 / 1000000000000), orderedInterval (49151719768 / 1000000000000) (49151719769 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (308230595504651 / 800000000000) 2 (IntervalRat.scale (647 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (13654586329 / 1000000000000) (13654586459 / 1000000000000), orderedInterval (-38304455654 / 1000000000000) (-38304455525 / 1000000000000)))) (orderedInterval (10172232254 / 1000000000000) (10172232295 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (278128118531329 / 4000000000000) 2 (IntervalRat.scale (647 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (89202282887 / 1000000000000) (89202282888 / 1000000000000), orderedInterval (33978742500 / 1000000000000) (33978742501 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (747091248331213 / 4000000000000) 2 (IntervalRat.scale (647 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-47078937325 / 1000000000000) (-47078867508 / 1000000000000), orderedInterval (34652767499 / 1000000000000) (34652837316 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2028498069164121 / 4000000000000) 2 (IntervalRat.scale (647 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30344651638 / 1000000000000) (-30344551407 / 1000000000000), orderedInterval (18320760423 / 1000000000000) (18320860654 / 1000000000000)))) (orderedInterval (-4679153462 / 1000000000000) (-4679135001 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1494182496663073 / 4000000000000) 2 (IntervalRat.scale (647 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-19106022684 / 1000000000000) (-19106022683 / 1000000000000), orderedInterval (-36569824753 / 1000000000000) (-36569824752 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2560307175557029 / 4000000000000) 2 (IntervalRat.scale (647 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-722284167 / 1000000000000) (-722284166 / 1000000000000), orderedInterval (31529561356 / 1000000000000) (31529561357 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1885910677436911 / 4000000000000) 2 (IntervalRat.scale (647 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (31386359402 / 1000000000000) (31386359403 / 1000000000000), orderedInterval (19075902428 / 1000000000000) (19075902429 / 1000000000000)))) (orderedInterval (-1694568315 / 1000000000000) (-1694568258 / 1000000000000))) = true
  rfl'

theorem compactCertificate452_chunkChecks2_1 :
    compactCertificate452.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2893471962884353 / 4000000000000) 2 (IntervalRat.scale (647 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (29662243295 / 1000000000000) (29662245714 / 1000000000000), orderedInterval (-498387345 / 1000000000000) (-498384925 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1670546816663737 / 4000000000000) 2 (IntervalRat.scale (647 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-21721227517 / 1000000000000) (-21721227516 / 1000000000000), orderedInterval (-32416672978 / 1000000000000) (-32416672977 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2964414641465933 / 4000000000000) 2 (IntervalRat.scale (647 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (13352578974 / 1000000000000) (13352578975 / 1000000000000), orderedInterval (26081690426 / 1000000000000) (26081690427 / 1000000000000)))) (orderedInterval (19056267003 / 1000000000000) (19056269725 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2769740691810977 / 4000000000000) 2 (IntervalRat.scale (647 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (26621040512 / 1000000000000) (26621105687 / 1000000000000), orderedInterval (-14535138948 / 1000000000000) (-14535073772 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1976617649757041 / 4000000000000) 2 (IntervalRat.scale (647 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-35548138286 / 1000000000000) (-35548135689 / 1000000000000), orderedInterval (4998891896 / 1000000000000) (4998894493 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2241273744993639 / 4000000000000) 2 (IntervalRat.scale (647 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (31895804890 / 1000000000000) (31895830015 / 1000000000000), orderedInterval (-10929456184 / 1000000000000) (-10929431058 / 1000000000000)))) (orderedInterval (10525389331 / 1000000000000) (10525395790 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1868540384041591 / 4000000000000) 2 (IntervalRat.scale (647 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (6502991567 / 1000000000000) (6502991573 / 1000000000000), orderedInterval (-36346045442 / 1000000000000) (-36346045436 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1650912096445411 / 4000000000000) 2 (IntervalRat.scale (647 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-36269846068 / 1000000000000) (-36269823268 / 1000000000000), orderedInterval (15109327341 / 1000000000000) (15109350140 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (478498672939689 / 800000000000) 2 (IntervalRat.scale (647 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (29584407914 / 1000000000000) (29584484318 / 1000000000000), orderedInterval (-13776942029 / 1000000000000) (-13776865624 / 1000000000000)))) (orderedInterval (-6117209041 / 1000000000000) (-6117200147 / 1000000000000))) = true
  rfl'

theorem compactCertificate452_chunkChecks2_2 :
    compactCertificate452.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1323552511356683 / 4000000000000) 2 (IntervalRat.scale (647 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-42656225950 / 1000000000000) (-42656222930 / 1000000000000), orderedInterval (10282938633 / 1000000000000) (10282941654 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1121990121819763 / 4000000000000) 2 (IntervalRat.scale (647 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-47352755278 / 1000000000000) (-47352754758 / 1000000000000), orderedInterval (5311477949 / 1000000000000) (5311478468 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (702089322563089 / 4000000000000) 2 (IntervalRat.scale (647 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (22216963095 / 1000000000000) (22216963096 / 1000000000000), orderedInterval (55913661660 / 1000000000000) (55913661661 / 1000000000000)))) (orderedInterval (-9360448065 / 1000000000000) (-9360447464 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (377585972718063 / 4000000000000) 2 (IntervalRat.scale (647 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (65967169856 / 1000000000000) (65967169857 / 1000000000000), orderedInterval (48562853382 / 1000000000000) (48562853383 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1025219366863189 / 4000000000000) 2 (IntervalRat.scale (647 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-24800105486 / 1000000000000) (-24800102867 / 1000000000000), orderedInterval (43277945724 / 1000000000000) (43277948343 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1399849396752053 / 4000000000000) 2 (IntervalRat.scale (647 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-38221156974 / 1000000000000) (-38221125652 / 1000000000000), orderedInterval (18982151014 / 1000000000000) (18982182336 / 1000000000000)))) (orderedInterval (-3669432661 / 1000000000000) (-3669429771 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (591910677436911 / 4000000000000) 2 (IntervalRat.scale (647 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-58672331938 / 1000000000000) (-58672331937 / 1000000000000), orderedInterval (-29122000383 / 1000000000000) (-29122000382 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2406084041882831 / 4000000000000) 2 (IntervalRat.scale (647 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25065377939 / 1000000000000) (-25065360618 / 1000000000000), orderedInterval (20759128927 / 1000000000000) (20759146249 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1607152632265729 / 4000000000000) 2 (IntervalRat.scale (647 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (17291920639 / 1000000000000) (17291920640 / 1000000000000), orderedInterval (35831744571 / 1000000000000) (35831744572 / 1000000000000)))) (orderedInterval (-1939879259 / 1000000000000) (-1939874190 / 1000000000000))) = true
  rfl'

theorem compactCertificate452_chunkChecks2 :
    compactCertificate452.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate452.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate452_chunkChecks2_0
    compactCertificate452_chunkChecks2_1 compactCertificate452_chunkChecks2_2

theorem compactCertificate452_chunkChecks3_0 :
    compactCertificate452.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (647 / 2) 3 (IntervalRat.scale (647 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-28611073761 / 1000000000000) (-28611073760 / 1000000000000), orderedInterval (-33857395398 / 1000000000000) (-33857395397 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (953154543291947 / 4000000000000) 3 (IntervalRat.scale (647 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (15889229232 / 1000000000000) (15889229233 / 1000000000000), orderedInterval (49151719768 / 1000000000000) (49151719769 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (308230595504651 / 800000000000) 3 (IntervalRat.scale (647 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (13654586329 / 1000000000000) (13654586459 / 1000000000000), orderedInterval (-38304455654 / 1000000000000) (-38304455525 / 1000000000000)))) (orderedInterval (17002613359 / 1000000000000) (17002613406 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (278128118531329 / 4000000000000) 3 (IntervalRat.scale (647 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (89202282887 / 1000000000000) (89202282888 / 1000000000000), orderedInterval (33978742500 / 1000000000000) (33978742501 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (747091248331213 / 4000000000000) 3 (IntervalRat.scale (647 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-47078937325 / 1000000000000) (-47078867508 / 1000000000000), orderedInterval (34652767499 / 1000000000000) (34652837316 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2028498069164121 / 4000000000000) 3 (IntervalRat.scale (647 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30344651638 / 1000000000000) (-30344551407 / 1000000000000), orderedInterval (18320760423 / 1000000000000) (18320860654 / 1000000000000)))) (orderedInterval (4791924809 / 1000000000000) (4791952898 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1494182496663073 / 4000000000000) 3 (IntervalRat.scale (647 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-19106022684 / 1000000000000) (-19106022683 / 1000000000000), orderedInterval (-36569824753 / 1000000000000) (-36569824752 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2560307175557029 / 4000000000000) 3 (IntervalRat.scale (647 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-722284167 / 1000000000000) (-722284166 / 1000000000000), orderedInterval (31529561356 / 1000000000000) (31529561357 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1885910677436911 / 4000000000000) 3 (IntervalRat.scale (647 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (31386359402 / 1000000000000) (31386359403 / 1000000000000), orderedInterval (19075902428 / 1000000000000) (19075902429 / 1000000000000)))) (orderedInterval (6110916690 / 1000000000000) (6110916793 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate452_chunkChecks3_1 :
    compactCertificate452.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2893471962884353 / 4000000000000) 3 (IntervalRat.scale (647 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (29662243295 / 1000000000000) (29662245714 / 1000000000000), orderedInterval (-498387345 / 1000000000000) (-498384925 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1670546816663737 / 4000000000000) 3 (IntervalRat.scale (647 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-21721227517 / 1000000000000) (-21721227516 / 1000000000000), orderedInterval (-32416672978 / 1000000000000) (-32416672977 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2964414641465933 / 4000000000000) 3 (IntervalRat.scale (647 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (13352578974 / 1000000000000) (13352578975 / 1000000000000), orderedInterval (26081690426 / 1000000000000) (26081690427 / 1000000000000)))) (orderedInterval (-40458474514 / 1000000000000) (-40458468449 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2769740691810977 / 4000000000000) 3 (IntervalRat.scale (647 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (26621040512 / 1000000000000) (26621105687 / 1000000000000), orderedInterval (-14535138948 / 1000000000000) (-14535073772 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1976617649757041 / 4000000000000) 3 (IntervalRat.scale (647 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-35548138286 / 1000000000000) (-35548135689 / 1000000000000), orderedInterval (4998891896 / 1000000000000) (4998894493 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2241273744993639 / 4000000000000) 3 (IntervalRat.scale (647 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (31895804890 / 1000000000000) (31895830015 / 1000000000000), orderedInterval (-10929456184 / 1000000000000) (-10929431058 / 1000000000000)))) (orderedInterval (-4578031733 / 1000000000000) (-4578018463 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1868540384041591 / 4000000000000) 3 (IntervalRat.scale (647 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (6502991567 / 1000000000000) (6502991573 / 1000000000000), orderedInterval (-36346045442 / 1000000000000) (-36346045436 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1650912096445411 / 4000000000000) 3 (IntervalRat.scale (647 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-36269846068 / 1000000000000) (-36269823268 / 1000000000000), orderedInterval (15109327341 / 1000000000000) (15109350140 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (478498672939689 / 800000000000) 3 (IntervalRat.scale (647 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (29584407914 / 1000000000000) (29584484318 / 1000000000000), orderedInterval (-13776942029 / 1000000000000) (-13776865624 / 1000000000000)))) (orderedInterval (5307731472 / 1000000000000) (5307746677 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate452_chunkChecks3_2 :
    compactCertificate452.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1323552511356683 / 4000000000000) 3 (IntervalRat.scale (647 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-42656225950 / 1000000000000) (-42656222930 / 1000000000000), orderedInterval (10282938633 / 1000000000000) (10282941654 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1121990121819763 / 4000000000000) 3 (IntervalRat.scale (647 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-47352755278 / 1000000000000) (-47352754758 / 1000000000000), orderedInterval (5311477949 / 1000000000000) (5311478468 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (702089322563089 / 4000000000000) 3 (IntervalRat.scale (647 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (22216963095 / 1000000000000) (22216963096 / 1000000000000), orderedInterval (55913661660 / 1000000000000) (55913661661 / 1000000000000)))) (orderedInterval (1693557926 / 1000000000000) (1693558534 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (377585972718063 / 4000000000000) 3 (IntervalRat.scale (647 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (65967169856 / 1000000000000) (65967169857 / 1000000000000), orderedInterval (48562853382 / 1000000000000) (48562853383 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1025219366863189 / 4000000000000) 3 (IntervalRat.scale (647 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-24800105486 / 1000000000000) (-24800102867 / 1000000000000), orderedInterval (43277945724 / 1000000000000) (43277948343 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1399849396752053 / 4000000000000) 3 (IntervalRat.scale (647 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-38221156974 / 1000000000000) (-38221125652 / 1000000000000), orderedInterval (18982151014 / 1000000000000) (18982182336 / 1000000000000)))) (orderedInterval (2363670348 / 1000000000000) (2363673462 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (591910677436911 / 4000000000000) 3 (IntervalRat.scale (647 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-58672331938 / 1000000000000) (-58672331937 / 1000000000000), orderedInterval (-29122000383 / 1000000000000) (-29122000382 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2406084041882831 / 4000000000000) 3 (IntervalRat.scale (647 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25065377939 / 1000000000000) (-25065360618 / 1000000000000), orderedInterval (20759128927 / 1000000000000) (20759146249 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1607152632265729 / 4000000000000) 3 (IntervalRat.scale (647 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (17291920639 / 1000000000000) (17291920640 / 1000000000000), orderedInterval (35831744571 / 1000000000000) (35831744572 / 1000000000000)))) (orderedInterval (23766699627 / 1000000000000) (23766708994 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate452_chunkChecks3 :
    compactCertificate452.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate452.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate452_chunkChecks3_0
    compactCertificate452_chunkChecks3_1 compactCertificate452_chunkChecks3_2

theorem compactCertificate452_chunkChecks4_0 :
    compactCertificate452.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (647 / 2) 4 (IntervalRat.scale (647 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-28611073761 / 1000000000000) (-28611073760 / 1000000000000), orderedInterval (-33857395398 / 1000000000000) (-33857395397 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (953154543291947 / 4000000000000) 4 (IntervalRat.scale (647 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (15889229232 / 1000000000000) (15889229233 / 1000000000000), orderedInterval (49151719768 / 1000000000000) (49151719769 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (308230595504651 / 800000000000) 4 (IntervalRat.scale (647 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (13654586329 / 1000000000000) (13654586459 / 1000000000000), orderedInterval (-38304455654 / 1000000000000) (-38304455525 / 1000000000000)))) (orderedInterval (-9789646181 / 1000000000000) (-9789646125 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (278128118531329 / 4000000000000) 4 (IntervalRat.scale (647 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (89202282887 / 1000000000000) (89202282888 / 1000000000000), orderedInterval (33978742500 / 1000000000000) (33978742501 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (747091248331213 / 4000000000000) 4 (IntervalRat.scale (647 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-47078937325 / 1000000000000) (-47078867508 / 1000000000000), orderedInterval (34652767499 / 1000000000000) (34652837316 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2028498069164121 / 4000000000000) 4 (IntervalRat.scale (647 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30344651638 / 1000000000000) (-30344551407 / 1000000000000), orderedInterval (18320760423 / 1000000000000) (18320860654 / 1000000000000)))) (orderedInterval (12804388969 / 1000000000000) (12804432595 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1494182496663073 / 4000000000000) 4 (IntervalRat.scale (647 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-19106022684 / 1000000000000) (-19106022683 / 1000000000000), orderedInterval (-36569824753 / 1000000000000) (-36569824752 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2560307175557029 / 4000000000000) 4 (IntervalRat.scale (647 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-722284167 / 1000000000000) (-722284166 / 1000000000000), orderedInterval (31529561356 / 1000000000000) (31529561357 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1885910677436911 / 4000000000000) 4 (IntervalRat.scale (647 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (31386359402 / 1000000000000) (31386359403 / 1000000000000), orderedInterval (19075902428 / 1000000000000) (19075902429 / 1000000000000)))) (orderedInterval (3726030391 / 1000000000000) (3726030581 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate452_chunkChecks4_1 :
    compactCertificate452.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2893471962884353 / 4000000000000) 4 (IntervalRat.scale (647 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (29662243295 / 1000000000000) (29662245714 / 1000000000000), orderedInterval (-498387345 / 1000000000000) (-498384925 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1670546816663737 / 4000000000000) 4 (IntervalRat.scale (647 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-21721227517 / 1000000000000) (-21721227516 / 1000000000000), orderedInterval (-32416672978 / 1000000000000) (-32416672977 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2964414641465933 / 4000000000000) 4 (IntervalRat.scale (647 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (13352578974 / 1000000000000) (13352578975 / 1000000000000), orderedInterval (26081690426 / 1000000000000) (26081690427 / 1000000000000)))) (orderedInterval (-83704137889 / 1000000000000) (-83704124338 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2769740691810977 / 4000000000000) 4 (IntervalRat.scale (647 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (26621040512 / 1000000000000) (26621105687 / 1000000000000), orderedInterval (-14535138948 / 1000000000000) (-14535073772 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1976617649757041 / 4000000000000) 4 (IntervalRat.scale (647 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-35548138286 / 1000000000000) (-35548135689 / 1000000000000), orderedInterval (4998891896 / 1000000000000) (4998894493 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2241273744993639 / 4000000000000) 4 (IntervalRat.scale (647 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (31895804890 / 1000000000000) (31895830015 / 1000000000000), orderedInterval (-10929456184 / 1000000000000) (-10929431058 / 1000000000000)))) (orderedInterval (-29813791949 / 1000000000000) (-29813764384 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1868540384041591 / 4000000000000) 4 (IntervalRat.scale (647 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (6502991567 / 1000000000000) (6502991573 / 1000000000000), orderedInterval (-36346045442 / 1000000000000) (-36346045436 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1650912096445411 / 4000000000000) 4 (IntervalRat.scale (647 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-36269846068 / 1000000000000) (-36269823268 / 1000000000000), orderedInterval (15109327341 / 1000000000000) (15109350140 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (478498672939689 / 800000000000) 4 (IntervalRat.scale (647 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (29584407914 / 1000000000000) (29584484318 / 1000000000000), orderedInterval (-13776942029 / 1000000000000) (-13776865624 / 1000000000000)))) (orderedInterval (14644748796 / 1000000000000) (14644775370 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate452_chunkChecks4_2 :
    compactCertificate452.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1323552511356683 / 4000000000000) 4 (IntervalRat.scale (647 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-42656225950 / 1000000000000) (-42656222930 / 1000000000000), orderedInterval (10282938633 / 1000000000000) (10282941654 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1121990121819763 / 4000000000000) 4 (IntervalRat.scale (647 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-47352755278 / 1000000000000) (-47352754758 / 1000000000000), orderedInterval (5311477949 / 1000000000000) (5311478468 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (702089322563089 / 4000000000000) 4 (IntervalRat.scale (647 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (22216963095 / 1000000000000) (22216963096 / 1000000000000), orderedInterval (55913661660 / 1000000000000) (55913661661 / 1000000000000)))) (orderedInterval (9032148738 / 1000000000000) (9032149356 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (377585972718063 / 4000000000000) 4 (IntervalRat.scale (647 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (65967169856 / 1000000000000) (65967169857 / 1000000000000), orderedInterval (48562853382 / 1000000000000) (48562853383 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1025219366863189 / 4000000000000) 4 (IntervalRat.scale (647 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-24800105486 / 1000000000000) (-24800102867 / 1000000000000), orderedInterval (43277945724 / 1000000000000) (43277948343 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1399849396752053 / 4000000000000) 4 (IntervalRat.scale (647 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-38221156974 / 1000000000000) (-38221125652 / 1000000000000), orderedInterval (18982151014 / 1000000000000) (18982182336 / 1000000000000)))) (orderedInterval (4210030365 / 1000000000000) (4210033733 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (591910677436911 / 4000000000000) 4 (IntervalRat.scale (647 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-58672331938 / 1000000000000) (-58672331937 / 1000000000000), orderedInterval (-29122000383 / 1000000000000) (-29122000382 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2406084041882831 / 4000000000000) 4 (IntervalRat.scale (647 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25065377939 / 1000000000000) (-25065360618 / 1000000000000), orderedInterval (20759128927 / 1000000000000) (20759146249 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1607152632265729 / 4000000000000) 4 (IntervalRat.scale (647 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (17291920639 / 1000000000000) (17291920640 / 1000000000000), orderedInterval (35831744571 / 1000000000000) (35831744572 / 1000000000000)))) (orderedInterval (16507474341 / 1000000000000) (16507491712 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate452_chunkChecks4 :
    compactCertificate452.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate452.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate452_chunkChecks4_0
    compactCertificate452_chunkChecks4_1 compactCertificate452_chunkChecks4_2

theorem compactCertificate452_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate452.chunkCheck r b = true :=
  compactCertificate452.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate452_chunkChecks0
    · exact compactCertificate452_chunkChecks1
    · exact compactCertificate452_chunkChecks2
    · exact compactCertificate452_chunkChecks3
    · exact compactCertificate452_chunkChecks4)

theorem compactCertificate452_coefficient0 :
    compactCertificate452.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate452_coefficient1 :
    compactCertificate452.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate452_coefficient2 :
    compactCertificate452.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate452_coefficient3 :
    compactCertificate452.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate452_coefficient4 :
    compactCertificate452.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate452_coefficients : ∀ r : Fin 5,
    compactCertificate452.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate452_coefficient0
  · exact compactCertificate452_coefficient1
  · exact compactCertificate452_coefficient2
  · exact compactCertificate452_coefficient3
  · exact compactCertificate452_coefficient4

theorem compactCertificate452_lower : (1 : ℚ) ≤ compactCertificate452.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate452, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate452_proves {t : ℝ} (ht : t ∈ compactCertificate452.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate452.proves compactCertificate452_states compactCertificate452_chunks
    compactCertificate452_coefficients compactCertificate452_lower ht

end Erdos232
