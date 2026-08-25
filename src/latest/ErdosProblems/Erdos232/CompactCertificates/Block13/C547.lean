/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate547 : CompactCertificate where
  left := 418
  right := 419
  center := 837 / 2
  grid := fun i =>
    match i.val with
    | 0 => 133
    | 1 => 98
    | 2 => 159
    | 3 => 29
    | 4 => 77
    | 5 => 209
    | 6 => 154
    | 7 => 264
    | 8 => 194
    | 9 => 298
    | 10 => 172
    | 11 => 305
    | 12 => 285
    | 13 => 204
    | 14 => 231
    | 15 => 192
    | 16 => 170
    | 17 => 246
    | 18 => 136
    | 19 => 116
    | 20 => 72
    | 21 => 39
    | 22 => 106
    | 23 => 144
    | 24 => 61
    | 25 => 248
    | _ => 166
  point := fun i =>
    match i.val with
    | 0 => 837 / 2
    | 1 => 1233060823393137 / 4000000000000
    | 2 => 398746535451921 / 800000000000
    | 3 => 359804072968659 / 4000000000000
    | 4 => 966484350623223 / 4000000000000
    | 5 => 2624193019923291 / 4000000000000
    | 6 => 1932968701247283 / 4000000000000
    | 7 => 3312174815983359 / 4000000000000
    | 8 => 2439732978384381 / 4000000000000
    | 9 => 3743177794334163 / 4000000000000
    | 10 => 2161124707183227 / 4000000000000
    | 11 => 3834953717012343 / 4000000000000
    | 12 => 3583111219545267 / 4000000000000
    | 13 => 2557077237784611 / 4000000000000
    | 14 => 2899453051869669 / 4000000000000
    | 15 => 2417261671472661 / 4000000000000
    | 16 => 2135723994937881 / 4000000000000
    | 17 => 619016057574219 / 800000000000
    | 18 => 1712230992280593 / 4000000000000
    | 19 => 1451477174595273 / 4000000000000
    | 20 => 908267021615619 / 4000000000000
    | 21 => 488469024984573 / 4000000000000
    | 22 => 1326288423592719 / 4000000000000
    | 23 => 1810933454530863 / 4000000000000
    | 24 => 765732978384381 / 4000000000000
    | 25 => 3112662044908701 / 4000000000000
    | _ => 2079113992591059 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-38733455996 / 1000000000000) (-38733455934 / 1000000000000), orderedInterval (-4526745798 / 1000000000000) (-4526745736 / 1000000000000))
    | 1 => (orderedInterval (41915349405 / 1000000000000) (41915349406 / 1000000000000), orderedInterval (17489652583 / 1000000000000) (17489652584 / 1000000000000))
    | 2 => (orderedInterval (10387711244 / 1000000000000) (10387711272 / 1000000000000), orderedInterval (-34206004549 / 1000000000000) (-34206004521 / 1000000000000))
    | 3 => (orderedInterval (30512469800 / 1000000000000) (30512471033 / 1000000000000), orderedInterval (-78569056402 / 1000000000000) (-78569055169 / 1000000000000))
    | 4 => (orderedInterval (-24759019533 / 1000000000000) (-24759019532 / 1000000000000), orderedInterval (-44912968642 / 1000000000000) (-44912968641 / 1000000000000))
    | 5 => (orderedInterval (-7422769786 / 1000000000000) (-7422769785 / 1000000000000), orderedInterval (-30248075278 / 1000000000000) (-30248075277 / 1000000000000))
    | 6 => (orderedInterval (7993300171 / 1000000000000) (7993300172 / 1000000000000), orderedInterval (35396540063 / 1000000000000) (35396540064 / 1000000000000))
    | 7 => (orderedInterval (-14528561763 / 1000000000000) (-14528561659 / 1000000000000), orderedInterval (23625394808 / 1000000000000) (23625394912 / 1000000000000))
    | 8 => (orderedInterval (30653526996 / 1000000000000) (30653527008 / 1000000000000), orderedInterval (10178507824 / 1000000000000) (10178507837 / 1000000000000))
    | 9 => (orderedInterval (9798009627 / 1000000000000) (9798009628 / 1000000000000), orderedInterval (24167017649 / 1000000000000) (24167017650 / 1000000000000))
    | 10 => (orderedInterval (22437797739 / 1000000000000) (22437797740 / 1000000000000), orderedInterval (25957250141 / 1000000000000) (25957250142 / 1000000000000))
    | 11 => (orderedInterval (-25073074470 / 1000000000000) (-25073073945 / 1000000000000), orderedInterval (-5933273942 / 1000000000000) (-5933273417 / 1000000000000))
    | 12 => (orderedInterval (-24934418494 / 1000000000000) (-24934418434 / 1000000000000), orderedInterval (-9418159067 / 1000000000000) (-9418159007 / 1000000000000))
    | 13 => (orderedInterval (-23295319337 / 1000000000000) (-23295310476 / 1000000000000), orderedInterval (21306325985 / 1000000000000) (21306334846 / 1000000000000))
    | 14 => (orderedInterval (1759735380 / 1000000000000) (1759735381 / 1000000000000), orderedInterval (-29584408719 / 1000000000000) (-29584408718 / 1000000000000))
    | 15 => (orderedInterval (30555157731 / 1000000000000) (30555193007 / 1000000000000), orderedInterval (-10972309848 / 1000000000000) (-10972274571 / 1000000000000))
    | 16 => (orderedInterval (20770778868 / 1000000000000) (20770778869 / 1000000000000), orderedInterval (27564979880 / 1000000000000) (27564979881 / 1000000000000))
    | 17 => (orderedInterval (28349771458 / 1000000000000) (28349784555 / 1000000000000), orderedInterval (-4381866672 / 1000000000000) (-4381853575 / 1000000000000))
    | 18 => (orderedInterval (38559984188 / 1000000000000) (38559984593 / 1000000000000), orderedInterval (-641110431 / 1000000000000) (-641110026 / 1000000000000))
    | 19 => (orderedInterval (-29170091928 / 1000000000000) (-29170072562 / 1000000000000), orderedInterval (30098652084 / 1000000000000) (30098671450 / 1000000000000))
    | 20 => (orderedInterval (52753304307 / 1000000000000) (52753304578 / 1000000000000), orderedInterval (-4671386526 / 1000000000000) (-4671386255 / 1000000000000))
    | 21 => (orderedInterval (-26748864641 / 1000000000000) (-26748864640 / 1000000000000), orderedInterval (-66955481286 / 1000000000000) (-66955481285 / 1000000000000))
    | 22 => (orderedInterval (-26577016096 / 1000000000000) (-26577009067 / 1000000000000), orderedInterval (34877797114 / 1000000000000) (34877804143 / 1000000000000))
    | 23 => (orderedInterval (33900759456 / 1000000000000) (33900759457 / 1000000000000), orderedInterval (15990887936 / 1000000000000) (15990887937 / 1000000000000))
    | 24 => (orderedInterval (-31643543060 / 1000000000000) (-31643543059 / 1000000000000), orderedInterval (-48127673958 / 1000000000000) (-48127673957 / 1000000000000))
    | 25 => (orderedInterval (-4676282659 / 1000000000000) (-4676282658 / 1000000000000), orderedInterval (28220655894 / 1000000000000) (28220655896 / 1000000000000))
    | _ => (orderedInterval (-28277082061 / 1000000000000) (-28277037480 / 1000000000000), orderedInterval (20647512778 / 1000000000000) (20647557359 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-14352453551 / 1000000000000) (-14352453495 / 1000000000000)
      | 1 => orderedInterval (-707351696 / 1000000000000) (-707351632 / 1000000000000)
      | 2 => orderedInterval (1188954226 / 1000000000000) (1188954254 / 1000000000000)
      | 3 => orderedInterval (-3642817187 / 1000000000000) (-3642816947 / 1000000000000)
      | 4 => orderedInterval (-1761634260 / 1000000000000) (-1761633371 / 1000000000000)
      | 5 => orderedInterval (-109935664 / 1000000000000) (-109934881 / 1000000000000)
      | 6 => orderedInterval (-2797027211 / 1000000000000) (-2797025936 / 1000000000000)
      | 7 => orderedInterval (-1501246070 / 1000000000000) (-1501245860 / 1000000000000)
      | _ => orderedInterval (5495422340 / 1000000000000) (5495430820 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-4064830888 / 1000000000000) (-4064830828 / 1000000000000)
      | 1 => orderedInterval (2607336167 / 1000000000000) (2607336227 / 1000000000000)
      | 2 => orderedInterval (-1083289541 / 1000000000000) (-1083289493 / 1000000000000)
      | 3 => orderedInterval (-9051482947 / 1000000000000) (-9051482432 / 1000000000000)
      | 4 => orderedInterval (3700884558 / 1000000000000) (3700885921 / 1000000000000)
      | 5 => orderedInterval (-2402943492 / 1000000000000) (-2402942226 / 1000000000000)
      | 6 => orderedInterval (-1454791993 / 1000000000000) (-1454790875 / 1000000000000)
      | 7 => orderedInterval (-1591921746 / 1000000000000) (-1591921574 / 1000000000000)
      | _ => orderedInterval (-9215743040 / 1000000000000) (-9215732488 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (14285734258 / 1000000000000) (14285734323 / 1000000000000)
      | 1 => orderedInterval (-986345448 / 1000000000000) (-986345368 / 1000000000000)
      | 2 => orderedInterval (-3325335565 / 1000000000000) (-3325335479 / 1000000000000)
      | 3 => orderedInterval (24661844951 / 1000000000000) (24661846080 / 1000000000000)
      | 4 => orderedInterval (3095565150 / 1000000000000) (3095567248 / 1000000000000)
      | 5 => orderedInterval (-1276567276 / 1000000000000) (-1276565190 / 1000000000000)
      | 6 => orderedInterval (4706917705 / 1000000000000) (4706918695 / 1000000000000)
      | 7 => orderedInterval (2623819289 / 1000000000000) (2623819434 / 1000000000000)
      | _ => orderedInterval (-9438329358 / 1000000000000) (-9438316189 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (5086011562 / 1000000000000) (5086011633 / 1000000000000)
      | 1 => orderedInterval (-7974215836 / 1000000000000) (-7974215717 / 1000000000000)
      | 2 => orderedInterval (4890881722 / 1000000000000) (4890881880 / 1000000000000)
      | 3 => orderedInterval (53954207692 / 1000000000000) (53954210207 / 1000000000000)
      | 4 => orderedInterval (-9633842472 / 1000000000000) (-9633839243 / 1000000000000)
      | 5 => orderedInterval (4369507756 / 1000000000000) (4369511240 / 1000000000000)
      | 6 => orderedInterval (1013864285 / 1000000000000) (1013865162 / 1000000000000)
      | 7 => orderedInterval (1908067182 / 1000000000000) (1908067308 / 1000000000000)
      | _ => orderedInterval (22240733490 / 1000000000000) (22240749918 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-14035341494 / 1000000000000) (-14035341415 / 1000000000000)
      | 1 => orderedInterval (3123596783 / 1000000000000) (3123596965 / 1000000000000)
      | 2 => orderedInterval (10186997856 / 1000000000000) (10186998151 / 1000000000000)
      | 3 => orderedInterval (-137337266365 / 1000000000000) (-137337260715 / 1000000000000)
      | 4 => orderedInterval (-2578849349 / 1000000000000) (-2578844356 / 1000000000000)
      | 5 => orderedInterval (6846404505 / 1000000000000) (6846410422 / 1000000000000)
      | 6 => orderedInterval (-5671057505 / 1000000000000) (-5671056721 / 1000000000000)
      | 7 => orderedInterval (-3326276071 / 1000000000000) (-3326275959 / 1000000000000)
      | _ => orderedInterval (17060269028 / 1000000000000) (17060289605 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-18188089073 / 1000000000000) (-18188077048 / 1000000000000)
    | 1 => orderedInterval (-22556782922 / 1000000000000) (-22556767768 / 1000000000000)
    | 2 => orderedInterval (34347303706 / 1000000000000) (34347323554 / 1000000000000)
    | 3 => orderedInterval (75855215381 / 1000000000000) (75855242388 / 1000000000000)
    | _ => orderedInterval (-125731522612 / 1000000000000) (-125731484023 / 1000000000000)

theorem compactCertificate547_stateChecks0 :
    compactCertificate547.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 133 12 (837 / 2)) (orderedInterval (-38733455996 / 1000000000000) (-38733455934 / 1000000000000), orderedInterval (-4526745798 / 1000000000000) (-4526745736 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 98 12 (1233060823393137 / 4000000000000)) (orderedInterval (41915349405 / 1000000000000) (41915349406 / 1000000000000), orderedInterval (17489652583 / 1000000000000) (17489652584 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 159 12 (398746535451921 / 800000000000)) (orderedInterval (10387711244 / 1000000000000) (10387711272 / 1000000000000), orderedInterval (-34206004549 / 1000000000000) (-34206004521 / 1000000000000))) = true
  rfl'

theorem compactCertificate547_stateChecks1 :
    compactCertificate547.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (359804072968659 / 4000000000000)) (orderedInterval (30512469800 / 1000000000000) (30512471033 / 1000000000000), orderedInterval (-78569056402 / 1000000000000) (-78569055169 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (966484350623223 / 4000000000000)) (orderedInterval (-24759019533 / 1000000000000) (-24759019532 / 1000000000000), orderedInterval (-44912968642 / 1000000000000) (-44912968641 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 209 12 (2624193019923291 / 4000000000000)) (orderedInterval (-7422769786 / 1000000000000) (-7422769785 / 1000000000000), orderedInterval (-30248075278 / 1000000000000) (-30248075277 / 1000000000000))) = true
  rfl'

theorem compactCertificate547_stateChecks2 :
    compactCertificate547.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 154 12 (1932968701247283 / 4000000000000)) (orderedInterval (7993300171 / 1000000000000) (7993300172 / 1000000000000), orderedInterval (35396540063 / 1000000000000) (35396540064 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 264 12 (3312174815983359 / 4000000000000)) (orderedInterval (-14528561763 / 1000000000000) (-14528561659 / 1000000000000), orderedInterval (23625394808 / 1000000000000) (23625394912 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 194 12 (2439732978384381 / 4000000000000)) (orderedInterval (30653526996 / 1000000000000) (30653527008 / 1000000000000), orderedInterval (10178507824 / 1000000000000) (10178507837 / 1000000000000))) = true
  rfl'

theorem compactCertificate547_stateChecks3 :
    compactCertificate547.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 298 12 (3743177794334163 / 4000000000000)) (orderedInterval (9798009627 / 1000000000000) (9798009628 / 1000000000000), orderedInterval (24167017649 / 1000000000000) (24167017650 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 172 12 (2161124707183227 / 4000000000000)) (orderedInterval (22437797739 / 1000000000000) (22437797740 / 1000000000000), orderedInterval (25957250141 / 1000000000000) (25957250142 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 305 12 (3834953717012343 / 4000000000000)) (orderedInterval (-25073074470 / 1000000000000) (-25073073945 / 1000000000000), orderedInterval (-5933273942 / 1000000000000) (-5933273417 / 1000000000000))) = true
  rfl'

theorem compactCertificate547_stateChecks4 :
    compactCertificate547.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 285 12 (3583111219545267 / 4000000000000)) (orderedInterval (-24934418494 / 1000000000000) (-24934418434 / 1000000000000), orderedInterval (-9418159067 / 1000000000000) (-9418159007 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 204 12 (2557077237784611 / 4000000000000)) (orderedInterval (-23295319337 / 1000000000000) (-23295310476 / 1000000000000), orderedInterval (21306325985 / 1000000000000) (21306334846 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 231 12 (2899453051869669 / 4000000000000)) (orderedInterval (1759735380 / 1000000000000) (1759735381 / 1000000000000), orderedInterval (-29584408719 / 1000000000000) (-29584408718 / 1000000000000))) = true
  rfl'

theorem compactCertificate547_stateChecks5 :
    compactCertificate547.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 192 12 (2417261671472661 / 4000000000000)) (orderedInterval (30555157731 / 1000000000000) (30555193007 / 1000000000000), orderedInterval (-10972309848 / 1000000000000) (-10972274571 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 170 12 (2135723994937881 / 4000000000000)) (orderedInterval (20770778868 / 1000000000000) (20770778869 / 1000000000000), orderedInterval (27564979880 / 1000000000000) (27564979881 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 246 12 (619016057574219 / 800000000000)) (orderedInterval (28349771458 / 1000000000000) (28349784555 / 1000000000000), orderedInterval (-4381866672 / 1000000000000) (-4381853575 / 1000000000000))) = true
  rfl'

theorem compactCertificate547_stateChecks6 :
    compactCertificate547.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 136 12 (1712230992280593 / 4000000000000)) (orderedInterval (38559984188 / 1000000000000) (38559984593 / 1000000000000), orderedInterval (-641110431 / 1000000000000) (-641110026 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 116 12 (1451477174595273 / 4000000000000)) (orderedInterval (-29170091928 / 1000000000000) (-29170072562 / 1000000000000), orderedInterval (30098652084 / 1000000000000) (30098671450 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (908267021615619 / 4000000000000)) (orderedInterval (52753304307 / 1000000000000) (52753304578 / 1000000000000), orderedInterval (-4671386526 / 1000000000000) (-4671386255 / 1000000000000))) = true
  rfl'

theorem compactCertificate547_stateChecks7 :
    compactCertificate547.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (488469024984573 / 4000000000000)) (orderedInterval (-26748864641 / 1000000000000) (-26748864640 / 1000000000000), orderedInterval (-66955481286 / 1000000000000) (-66955481285 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 106 12 (1326288423592719 / 4000000000000)) (orderedInterval (-26577016096 / 1000000000000) (-26577009067 / 1000000000000), orderedInterval (34877797114 / 1000000000000) (34877804143 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 144 12 (1810933454530863 / 4000000000000)) (orderedInterval (33900759456 / 1000000000000) (33900759457 / 1000000000000), orderedInterval (15990887936 / 1000000000000) (15990887937 / 1000000000000))) = true
  rfl'

theorem compactCertificate547_stateChecks8 :
    compactCertificate547.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (765732978384381 / 4000000000000)) (orderedInterval (-31643543060 / 1000000000000) (-31643543059 / 1000000000000), orderedInterval (-48127673958 / 1000000000000) (-48127673957 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 248 12 (3112662044908701 / 4000000000000)) (orderedInterval (-4676282659 / 1000000000000) (-4676282658 / 1000000000000), orderedInterval (28220655894 / 1000000000000) (28220655896 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 166 12 (2079113992591059 / 4000000000000)) (orderedInterval (-28277082061 / 1000000000000) (-28277037480 / 1000000000000), orderedInterval (20647512778 / 1000000000000) (20647557359 / 1000000000000))) = true
  rfl'

theorem compactCertificate547_states : ∀ j,
    BesselStateValid (compactCertificate547.point j) (compactCertificate547.state j) :=
  compactCertificate547.statesValid_of_checks3 compactCertificate547_stateChecks0
    compactCertificate547_stateChecks1 compactCertificate547_stateChecks2
    compactCertificate547_stateChecks3 compactCertificate547_stateChecks4
    compactCertificate547_stateChecks5 compactCertificate547_stateChecks6
    compactCertificate547_stateChecks7 compactCertificate547_stateChecks8

theorem compactCertificate547_chunkChecks0_0 :
    compactCertificate547.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (837 / 2) 0 (IntervalRat.scale (837 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-38733455996 / 1000000000000) (-38733455934 / 1000000000000), orderedInterval (-4526745798 / 1000000000000) (-4526745736 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1233060823393137 / 4000000000000) 0 (IntervalRat.scale (837 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (41915349405 / 1000000000000) (41915349406 / 1000000000000), orderedInterval (17489652583 / 1000000000000) (17489652584 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (398746535451921 / 800000000000) 0 (IntervalRat.scale (837 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (10387711244 / 1000000000000) (10387711272 / 1000000000000), orderedInterval (-34206004549 / 1000000000000) (-34206004521 / 1000000000000)))) (orderedInterval (-14352453551 / 1000000000000) (-14352453495 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (359804072968659 / 4000000000000) 0 (IntervalRat.scale (837 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (30512469800 / 1000000000000) (30512471033 / 1000000000000), orderedInterval (-78569056402 / 1000000000000) (-78569055169 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (966484350623223 / 4000000000000) 0 (IntervalRat.scale (837 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-24759019533 / 1000000000000) (-24759019532 / 1000000000000), orderedInterval (-44912968642 / 1000000000000) (-44912968641 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2624193019923291 / 4000000000000) 0 (IntervalRat.scale (837 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-7422769786 / 1000000000000) (-7422769785 / 1000000000000), orderedInterval (-30248075278 / 1000000000000) (-30248075277 / 1000000000000)))) (orderedInterval (-707351696 / 1000000000000) (-707351632 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1932968701247283 / 4000000000000) 0 (IntervalRat.scale (837 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (7993300171 / 1000000000000) (7993300172 / 1000000000000), orderedInterval (35396540063 / 1000000000000) (35396540064 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3312174815983359 / 4000000000000) 0 (IntervalRat.scale (837 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-14528561763 / 1000000000000) (-14528561659 / 1000000000000), orderedInterval (23625394808 / 1000000000000) (23625394912 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2439732978384381 / 4000000000000) 0 (IntervalRat.scale (837 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (30653526996 / 1000000000000) (30653527008 / 1000000000000), orderedInterval (10178507824 / 1000000000000) (10178507837 / 1000000000000)))) (orderedInterval (1188954226 / 1000000000000) (1188954254 / 1000000000000))) = true
  rfl'

theorem compactCertificate547_chunkChecks0_1 :
    compactCertificate547.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3743177794334163 / 4000000000000) 0 (IntervalRat.scale (837 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (9798009627 / 1000000000000) (9798009628 / 1000000000000), orderedInterval (24167017649 / 1000000000000) (24167017650 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2161124707183227 / 4000000000000) 0 (IntervalRat.scale (837 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (22437797739 / 1000000000000) (22437797740 / 1000000000000), orderedInterval (25957250141 / 1000000000000) (25957250142 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3834953717012343 / 4000000000000) 0 (IntervalRat.scale (837 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-25073074470 / 1000000000000) (-25073073945 / 1000000000000), orderedInterval (-5933273942 / 1000000000000) (-5933273417 / 1000000000000)))) (orderedInterval (-3642817187 / 1000000000000) (-3642816947 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3583111219545267 / 4000000000000) 0 (IntervalRat.scale (837 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24934418494 / 1000000000000) (-24934418434 / 1000000000000), orderedInterval (-9418159067 / 1000000000000) (-9418159007 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2557077237784611 / 4000000000000) 0 (IntervalRat.scale (837 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-23295319337 / 1000000000000) (-23295310476 / 1000000000000), orderedInterval (21306325985 / 1000000000000) (21306334846 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2899453051869669 / 4000000000000) 0 (IntervalRat.scale (837 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (1759735380 / 1000000000000) (1759735381 / 1000000000000), orderedInterval (-29584408719 / 1000000000000) (-29584408718 / 1000000000000)))) (orderedInterval (-1761634260 / 1000000000000) (-1761633371 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2417261671472661 / 4000000000000) 0 (IntervalRat.scale (837 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30555157731 / 1000000000000) (30555193007 / 1000000000000), orderedInterval (-10972309848 / 1000000000000) (-10972274571 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2135723994937881 / 4000000000000) 0 (IntervalRat.scale (837 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (20770778868 / 1000000000000) (20770778869 / 1000000000000), orderedInterval (27564979880 / 1000000000000) (27564979881 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (619016057574219 / 800000000000) 0 (IntervalRat.scale (837 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (28349771458 / 1000000000000) (28349784555 / 1000000000000), orderedInterval (-4381866672 / 1000000000000) (-4381853575 / 1000000000000)))) (orderedInterval (-109935664 / 1000000000000) (-109934881 / 1000000000000))) = true
  rfl'

theorem compactCertificate547_chunkChecks0_2 :
    compactCertificate547.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1712230992280593 / 4000000000000) 0 (IntervalRat.scale (837 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (38559984188 / 1000000000000) (38559984593 / 1000000000000), orderedInterval (-641110431 / 1000000000000) (-641110026 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1451477174595273 / 4000000000000) 0 (IntervalRat.scale (837 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-29170091928 / 1000000000000) (-29170072562 / 1000000000000), orderedInterval (30098652084 / 1000000000000) (30098671450 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (908267021615619 / 4000000000000) 0 (IntervalRat.scale (837 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (52753304307 / 1000000000000) (52753304578 / 1000000000000), orderedInterval (-4671386526 / 1000000000000) (-4671386255 / 1000000000000)))) (orderedInterval (-2797027211 / 1000000000000) (-2797025936 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (488469024984573 / 4000000000000) 0 (IntervalRat.scale (837 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-26748864641 / 1000000000000) (-26748864640 / 1000000000000), orderedInterval (-66955481286 / 1000000000000) (-66955481285 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1326288423592719 / 4000000000000) 0 (IntervalRat.scale (837 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-26577016096 / 1000000000000) (-26577009067 / 1000000000000), orderedInterval (34877797114 / 1000000000000) (34877804143 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1810933454530863 / 4000000000000) 0 (IntervalRat.scale (837 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (33900759456 / 1000000000000) (33900759457 / 1000000000000), orderedInterval (15990887936 / 1000000000000) (15990887937 / 1000000000000)))) (orderedInterval (-1501246070 / 1000000000000) (-1501245860 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (765732978384381 / 4000000000000) 0 (IntervalRat.scale (837 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-31643543060 / 1000000000000) (-31643543059 / 1000000000000), orderedInterval (-48127673958 / 1000000000000) (-48127673957 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3112662044908701 / 4000000000000) 0 (IntervalRat.scale (837 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-4676282659 / 1000000000000) (-4676282658 / 1000000000000), orderedInterval (28220655894 / 1000000000000) (28220655896 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2079113992591059 / 4000000000000) 0 (IntervalRat.scale (837 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-28277082061 / 1000000000000) (-28277037480 / 1000000000000), orderedInterval (20647512778 / 1000000000000) (20647557359 / 1000000000000)))) (orderedInterval (5495422340 / 1000000000000) (5495430820 / 1000000000000))) = true
  rfl'

theorem compactCertificate547_chunkChecks0 :
    compactCertificate547.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate547.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate547_chunkChecks0_0
    compactCertificate547_chunkChecks0_1 compactCertificate547_chunkChecks0_2

theorem compactCertificate547_chunkChecks1_0 :
    compactCertificate547.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (837 / 2) 1 (IntervalRat.scale (837 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-38733455996 / 1000000000000) (-38733455934 / 1000000000000), orderedInterval (-4526745798 / 1000000000000) (-4526745736 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1233060823393137 / 4000000000000) 1 (IntervalRat.scale (837 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (41915349405 / 1000000000000) (41915349406 / 1000000000000), orderedInterval (17489652583 / 1000000000000) (17489652584 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (398746535451921 / 800000000000) 1 (IntervalRat.scale (837 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (10387711244 / 1000000000000) (10387711272 / 1000000000000), orderedInterval (-34206004549 / 1000000000000) (-34206004521 / 1000000000000)))) (orderedInterval (-4064830888 / 1000000000000) (-4064830828 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (359804072968659 / 4000000000000) 1 (IntervalRat.scale (837 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (30512469800 / 1000000000000) (30512471033 / 1000000000000), orderedInterval (-78569056402 / 1000000000000) (-78569055169 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (966484350623223 / 4000000000000) 1 (IntervalRat.scale (837 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-24759019533 / 1000000000000) (-24759019532 / 1000000000000), orderedInterval (-44912968642 / 1000000000000) (-44912968641 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2624193019923291 / 4000000000000) 1 (IntervalRat.scale (837 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-7422769786 / 1000000000000) (-7422769785 / 1000000000000), orderedInterval (-30248075278 / 1000000000000) (-30248075277 / 1000000000000)))) (orderedInterval (2607336167 / 1000000000000) (2607336227 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1932968701247283 / 4000000000000) 1 (IntervalRat.scale (837 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (7993300171 / 1000000000000) (7993300172 / 1000000000000), orderedInterval (35396540063 / 1000000000000) (35396540064 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3312174815983359 / 4000000000000) 1 (IntervalRat.scale (837 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-14528561763 / 1000000000000) (-14528561659 / 1000000000000), orderedInterval (23625394808 / 1000000000000) (23625394912 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2439732978384381 / 4000000000000) 1 (IntervalRat.scale (837 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (30653526996 / 1000000000000) (30653527008 / 1000000000000), orderedInterval (10178507824 / 1000000000000) (10178507837 / 1000000000000)))) (orderedInterval (-1083289541 / 1000000000000) (-1083289493 / 1000000000000))) = true
  rfl'

theorem compactCertificate547_chunkChecks1_1 :
    compactCertificate547.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3743177794334163 / 4000000000000) 1 (IntervalRat.scale (837 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (9798009627 / 1000000000000) (9798009628 / 1000000000000), orderedInterval (24167017649 / 1000000000000) (24167017650 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2161124707183227 / 4000000000000) 1 (IntervalRat.scale (837 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (22437797739 / 1000000000000) (22437797740 / 1000000000000), orderedInterval (25957250141 / 1000000000000) (25957250142 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3834953717012343 / 4000000000000) 1 (IntervalRat.scale (837 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-25073074470 / 1000000000000) (-25073073945 / 1000000000000), orderedInterval (-5933273942 / 1000000000000) (-5933273417 / 1000000000000)))) (orderedInterval (-9051482947 / 1000000000000) (-9051482432 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3583111219545267 / 4000000000000) 1 (IntervalRat.scale (837 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24934418494 / 1000000000000) (-24934418434 / 1000000000000), orderedInterval (-9418159067 / 1000000000000) (-9418159007 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2557077237784611 / 4000000000000) 1 (IntervalRat.scale (837 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-23295319337 / 1000000000000) (-23295310476 / 1000000000000), orderedInterval (21306325985 / 1000000000000) (21306334846 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2899453051869669 / 4000000000000) 1 (IntervalRat.scale (837 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (1759735380 / 1000000000000) (1759735381 / 1000000000000), orderedInterval (-29584408719 / 1000000000000) (-29584408718 / 1000000000000)))) (orderedInterval (3700884558 / 1000000000000) (3700885921 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2417261671472661 / 4000000000000) 1 (IntervalRat.scale (837 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30555157731 / 1000000000000) (30555193007 / 1000000000000), orderedInterval (-10972309848 / 1000000000000) (-10972274571 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2135723994937881 / 4000000000000) 1 (IntervalRat.scale (837 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (20770778868 / 1000000000000) (20770778869 / 1000000000000), orderedInterval (27564979880 / 1000000000000) (27564979881 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (619016057574219 / 800000000000) 1 (IntervalRat.scale (837 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (28349771458 / 1000000000000) (28349784555 / 1000000000000), orderedInterval (-4381866672 / 1000000000000) (-4381853575 / 1000000000000)))) (orderedInterval (-2402943492 / 1000000000000) (-2402942226 / 1000000000000))) = true
  rfl'

theorem compactCertificate547_chunkChecks1_2 :
    compactCertificate547.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1712230992280593 / 4000000000000) 1 (IntervalRat.scale (837 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (38559984188 / 1000000000000) (38559984593 / 1000000000000), orderedInterval (-641110431 / 1000000000000) (-641110026 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1451477174595273 / 4000000000000) 1 (IntervalRat.scale (837 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-29170091928 / 1000000000000) (-29170072562 / 1000000000000), orderedInterval (30098652084 / 1000000000000) (30098671450 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (908267021615619 / 4000000000000) 1 (IntervalRat.scale (837 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (52753304307 / 1000000000000) (52753304578 / 1000000000000), orderedInterval (-4671386526 / 1000000000000) (-4671386255 / 1000000000000)))) (orderedInterval (-1454791993 / 1000000000000) (-1454790875 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (488469024984573 / 4000000000000) 1 (IntervalRat.scale (837 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-26748864641 / 1000000000000) (-26748864640 / 1000000000000), orderedInterval (-66955481286 / 1000000000000) (-66955481285 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1326288423592719 / 4000000000000) 1 (IntervalRat.scale (837 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-26577016096 / 1000000000000) (-26577009067 / 1000000000000), orderedInterval (34877797114 / 1000000000000) (34877804143 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1810933454530863 / 4000000000000) 1 (IntervalRat.scale (837 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (33900759456 / 1000000000000) (33900759457 / 1000000000000), orderedInterval (15990887936 / 1000000000000) (15990887937 / 1000000000000)))) (orderedInterval (-1591921746 / 1000000000000) (-1591921574 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (765732978384381 / 4000000000000) 1 (IntervalRat.scale (837 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-31643543060 / 1000000000000) (-31643543059 / 1000000000000), orderedInterval (-48127673958 / 1000000000000) (-48127673957 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3112662044908701 / 4000000000000) 1 (IntervalRat.scale (837 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-4676282659 / 1000000000000) (-4676282658 / 1000000000000), orderedInterval (28220655894 / 1000000000000) (28220655896 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2079113992591059 / 4000000000000) 1 (IntervalRat.scale (837 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-28277082061 / 1000000000000) (-28277037480 / 1000000000000), orderedInterval (20647512778 / 1000000000000) (20647557359 / 1000000000000)))) (orderedInterval (-9215743040 / 1000000000000) (-9215732488 / 1000000000000))) = true
  rfl'

theorem compactCertificate547_chunkChecks1 :
    compactCertificate547.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate547.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate547_chunkChecks1_0
    compactCertificate547_chunkChecks1_1 compactCertificate547_chunkChecks1_2

theorem compactCertificate547_chunkChecks2_0 :
    compactCertificate547.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (837 / 2) 2 (IntervalRat.scale (837 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-38733455996 / 1000000000000) (-38733455934 / 1000000000000), orderedInterval (-4526745798 / 1000000000000) (-4526745736 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1233060823393137 / 4000000000000) 2 (IntervalRat.scale (837 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (41915349405 / 1000000000000) (41915349406 / 1000000000000), orderedInterval (17489652583 / 1000000000000) (17489652584 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (398746535451921 / 800000000000) 2 (IntervalRat.scale (837 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (10387711244 / 1000000000000) (10387711272 / 1000000000000), orderedInterval (-34206004549 / 1000000000000) (-34206004521 / 1000000000000)))) (orderedInterval (14285734258 / 1000000000000) (14285734323 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (359804072968659 / 4000000000000) 2 (IntervalRat.scale (837 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (30512469800 / 1000000000000) (30512471033 / 1000000000000), orderedInterval (-78569056402 / 1000000000000) (-78569055169 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (966484350623223 / 4000000000000) 2 (IntervalRat.scale (837 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-24759019533 / 1000000000000) (-24759019532 / 1000000000000), orderedInterval (-44912968642 / 1000000000000) (-44912968641 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2624193019923291 / 4000000000000) 2 (IntervalRat.scale (837 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-7422769786 / 1000000000000) (-7422769785 / 1000000000000), orderedInterval (-30248075278 / 1000000000000) (-30248075277 / 1000000000000)))) (orderedInterval (-986345448 / 1000000000000) (-986345368 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1932968701247283 / 4000000000000) 2 (IntervalRat.scale (837 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (7993300171 / 1000000000000) (7993300172 / 1000000000000), orderedInterval (35396540063 / 1000000000000) (35396540064 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3312174815983359 / 4000000000000) 2 (IntervalRat.scale (837 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-14528561763 / 1000000000000) (-14528561659 / 1000000000000), orderedInterval (23625394808 / 1000000000000) (23625394912 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2439732978384381 / 4000000000000) 2 (IntervalRat.scale (837 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (30653526996 / 1000000000000) (30653527008 / 1000000000000), orderedInterval (10178507824 / 1000000000000) (10178507837 / 1000000000000)))) (orderedInterval (-3325335565 / 1000000000000) (-3325335479 / 1000000000000))) = true
  rfl'

theorem compactCertificate547_chunkChecks2_1 :
    compactCertificate547.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3743177794334163 / 4000000000000) 2 (IntervalRat.scale (837 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (9798009627 / 1000000000000) (9798009628 / 1000000000000), orderedInterval (24167017649 / 1000000000000) (24167017650 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2161124707183227 / 4000000000000) 2 (IntervalRat.scale (837 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (22437797739 / 1000000000000) (22437797740 / 1000000000000), orderedInterval (25957250141 / 1000000000000) (25957250142 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3834953717012343 / 4000000000000) 2 (IntervalRat.scale (837 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-25073074470 / 1000000000000) (-25073073945 / 1000000000000), orderedInterval (-5933273942 / 1000000000000) (-5933273417 / 1000000000000)))) (orderedInterval (24661844951 / 1000000000000) (24661846080 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3583111219545267 / 4000000000000) 2 (IntervalRat.scale (837 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24934418494 / 1000000000000) (-24934418434 / 1000000000000), orderedInterval (-9418159067 / 1000000000000) (-9418159007 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2557077237784611 / 4000000000000) 2 (IntervalRat.scale (837 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-23295319337 / 1000000000000) (-23295310476 / 1000000000000), orderedInterval (21306325985 / 1000000000000) (21306334846 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2899453051869669 / 4000000000000) 2 (IntervalRat.scale (837 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (1759735380 / 1000000000000) (1759735381 / 1000000000000), orderedInterval (-29584408719 / 1000000000000) (-29584408718 / 1000000000000)))) (orderedInterval (3095565150 / 1000000000000) (3095567248 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2417261671472661 / 4000000000000) 2 (IntervalRat.scale (837 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30555157731 / 1000000000000) (30555193007 / 1000000000000), orderedInterval (-10972309848 / 1000000000000) (-10972274571 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2135723994937881 / 4000000000000) 2 (IntervalRat.scale (837 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (20770778868 / 1000000000000) (20770778869 / 1000000000000), orderedInterval (27564979880 / 1000000000000) (27564979881 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (619016057574219 / 800000000000) 2 (IntervalRat.scale (837 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (28349771458 / 1000000000000) (28349784555 / 1000000000000), orderedInterval (-4381866672 / 1000000000000) (-4381853575 / 1000000000000)))) (orderedInterval (-1276567276 / 1000000000000) (-1276565190 / 1000000000000))) = true
  rfl'

theorem compactCertificate547_chunkChecks2_2 :
    compactCertificate547.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1712230992280593 / 4000000000000) 2 (IntervalRat.scale (837 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (38559984188 / 1000000000000) (38559984593 / 1000000000000), orderedInterval (-641110431 / 1000000000000) (-641110026 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1451477174595273 / 4000000000000) 2 (IntervalRat.scale (837 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-29170091928 / 1000000000000) (-29170072562 / 1000000000000), orderedInterval (30098652084 / 1000000000000) (30098671450 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (908267021615619 / 4000000000000) 2 (IntervalRat.scale (837 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (52753304307 / 1000000000000) (52753304578 / 1000000000000), orderedInterval (-4671386526 / 1000000000000) (-4671386255 / 1000000000000)))) (orderedInterval (4706917705 / 1000000000000) (4706918695 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (488469024984573 / 4000000000000) 2 (IntervalRat.scale (837 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-26748864641 / 1000000000000) (-26748864640 / 1000000000000), orderedInterval (-66955481286 / 1000000000000) (-66955481285 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1326288423592719 / 4000000000000) 2 (IntervalRat.scale (837 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-26577016096 / 1000000000000) (-26577009067 / 1000000000000), orderedInterval (34877797114 / 1000000000000) (34877804143 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1810933454530863 / 4000000000000) 2 (IntervalRat.scale (837 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (33900759456 / 1000000000000) (33900759457 / 1000000000000), orderedInterval (15990887936 / 1000000000000) (15990887937 / 1000000000000)))) (orderedInterval (2623819289 / 1000000000000) (2623819434 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (765732978384381 / 4000000000000) 2 (IntervalRat.scale (837 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-31643543060 / 1000000000000) (-31643543059 / 1000000000000), orderedInterval (-48127673958 / 1000000000000) (-48127673957 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3112662044908701 / 4000000000000) 2 (IntervalRat.scale (837 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-4676282659 / 1000000000000) (-4676282658 / 1000000000000), orderedInterval (28220655894 / 1000000000000) (28220655896 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2079113992591059 / 4000000000000) 2 (IntervalRat.scale (837 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-28277082061 / 1000000000000) (-28277037480 / 1000000000000), orderedInterval (20647512778 / 1000000000000) (20647557359 / 1000000000000)))) (orderedInterval (-9438329358 / 1000000000000) (-9438316189 / 1000000000000))) = true
  rfl'

theorem compactCertificate547_chunkChecks2 :
    compactCertificate547.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate547.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate547_chunkChecks2_0
    compactCertificate547_chunkChecks2_1 compactCertificate547_chunkChecks2_2

theorem compactCertificate547_chunkChecks3_0 :
    compactCertificate547.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (837 / 2) 3 (IntervalRat.scale (837 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-38733455996 / 1000000000000) (-38733455934 / 1000000000000), orderedInterval (-4526745798 / 1000000000000) (-4526745736 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1233060823393137 / 4000000000000) 3 (IntervalRat.scale (837 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (41915349405 / 1000000000000) (41915349406 / 1000000000000), orderedInterval (17489652583 / 1000000000000) (17489652584 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (398746535451921 / 800000000000) 3 (IntervalRat.scale (837 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (10387711244 / 1000000000000) (10387711272 / 1000000000000), orderedInterval (-34206004549 / 1000000000000) (-34206004521 / 1000000000000)))) (orderedInterval (5086011562 / 1000000000000) (5086011633 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (359804072968659 / 4000000000000) 3 (IntervalRat.scale (837 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (30512469800 / 1000000000000) (30512471033 / 1000000000000), orderedInterval (-78569056402 / 1000000000000) (-78569055169 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (966484350623223 / 4000000000000) 3 (IntervalRat.scale (837 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-24759019533 / 1000000000000) (-24759019532 / 1000000000000), orderedInterval (-44912968642 / 1000000000000) (-44912968641 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2624193019923291 / 4000000000000) 3 (IntervalRat.scale (837 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-7422769786 / 1000000000000) (-7422769785 / 1000000000000), orderedInterval (-30248075278 / 1000000000000) (-30248075277 / 1000000000000)))) (orderedInterval (-7974215836 / 1000000000000) (-7974215717 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1932968701247283 / 4000000000000) 3 (IntervalRat.scale (837 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (7993300171 / 1000000000000) (7993300172 / 1000000000000), orderedInterval (35396540063 / 1000000000000) (35396540064 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3312174815983359 / 4000000000000) 3 (IntervalRat.scale (837 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-14528561763 / 1000000000000) (-14528561659 / 1000000000000), orderedInterval (23625394808 / 1000000000000) (23625394912 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2439732978384381 / 4000000000000) 3 (IntervalRat.scale (837 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (30653526996 / 1000000000000) (30653527008 / 1000000000000), orderedInterval (10178507824 / 1000000000000) (10178507837 / 1000000000000)))) (orderedInterval (4890881722 / 1000000000000) (4890881880 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate547_chunkChecks3_1 :
    compactCertificate547.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3743177794334163 / 4000000000000) 3 (IntervalRat.scale (837 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (9798009627 / 1000000000000) (9798009628 / 1000000000000), orderedInterval (24167017649 / 1000000000000) (24167017650 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2161124707183227 / 4000000000000) 3 (IntervalRat.scale (837 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (22437797739 / 1000000000000) (22437797740 / 1000000000000), orderedInterval (25957250141 / 1000000000000) (25957250142 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3834953717012343 / 4000000000000) 3 (IntervalRat.scale (837 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-25073074470 / 1000000000000) (-25073073945 / 1000000000000), orderedInterval (-5933273942 / 1000000000000) (-5933273417 / 1000000000000)))) (orderedInterval (53954207692 / 1000000000000) (53954210207 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3583111219545267 / 4000000000000) 3 (IntervalRat.scale (837 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24934418494 / 1000000000000) (-24934418434 / 1000000000000), orderedInterval (-9418159067 / 1000000000000) (-9418159007 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2557077237784611 / 4000000000000) 3 (IntervalRat.scale (837 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-23295319337 / 1000000000000) (-23295310476 / 1000000000000), orderedInterval (21306325985 / 1000000000000) (21306334846 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2899453051869669 / 4000000000000) 3 (IntervalRat.scale (837 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (1759735380 / 1000000000000) (1759735381 / 1000000000000), orderedInterval (-29584408719 / 1000000000000) (-29584408718 / 1000000000000)))) (orderedInterval (-9633842472 / 1000000000000) (-9633839243 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2417261671472661 / 4000000000000) 3 (IntervalRat.scale (837 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30555157731 / 1000000000000) (30555193007 / 1000000000000), orderedInterval (-10972309848 / 1000000000000) (-10972274571 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2135723994937881 / 4000000000000) 3 (IntervalRat.scale (837 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (20770778868 / 1000000000000) (20770778869 / 1000000000000), orderedInterval (27564979880 / 1000000000000) (27564979881 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (619016057574219 / 800000000000) 3 (IntervalRat.scale (837 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (28349771458 / 1000000000000) (28349784555 / 1000000000000), orderedInterval (-4381866672 / 1000000000000) (-4381853575 / 1000000000000)))) (orderedInterval (4369507756 / 1000000000000) (4369511240 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate547_chunkChecks3_2 :
    compactCertificate547.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1712230992280593 / 4000000000000) 3 (IntervalRat.scale (837 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (38559984188 / 1000000000000) (38559984593 / 1000000000000), orderedInterval (-641110431 / 1000000000000) (-641110026 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1451477174595273 / 4000000000000) 3 (IntervalRat.scale (837 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-29170091928 / 1000000000000) (-29170072562 / 1000000000000), orderedInterval (30098652084 / 1000000000000) (30098671450 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (908267021615619 / 4000000000000) 3 (IntervalRat.scale (837 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (52753304307 / 1000000000000) (52753304578 / 1000000000000), orderedInterval (-4671386526 / 1000000000000) (-4671386255 / 1000000000000)))) (orderedInterval (1013864285 / 1000000000000) (1013865162 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (488469024984573 / 4000000000000) 3 (IntervalRat.scale (837 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-26748864641 / 1000000000000) (-26748864640 / 1000000000000), orderedInterval (-66955481286 / 1000000000000) (-66955481285 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1326288423592719 / 4000000000000) 3 (IntervalRat.scale (837 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-26577016096 / 1000000000000) (-26577009067 / 1000000000000), orderedInterval (34877797114 / 1000000000000) (34877804143 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1810933454530863 / 4000000000000) 3 (IntervalRat.scale (837 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (33900759456 / 1000000000000) (33900759457 / 1000000000000), orderedInterval (15990887936 / 1000000000000) (15990887937 / 1000000000000)))) (orderedInterval (1908067182 / 1000000000000) (1908067308 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (765732978384381 / 4000000000000) 3 (IntervalRat.scale (837 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-31643543060 / 1000000000000) (-31643543059 / 1000000000000), orderedInterval (-48127673958 / 1000000000000) (-48127673957 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3112662044908701 / 4000000000000) 3 (IntervalRat.scale (837 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-4676282659 / 1000000000000) (-4676282658 / 1000000000000), orderedInterval (28220655894 / 1000000000000) (28220655896 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2079113992591059 / 4000000000000) 3 (IntervalRat.scale (837 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-28277082061 / 1000000000000) (-28277037480 / 1000000000000), orderedInterval (20647512778 / 1000000000000) (20647557359 / 1000000000000)))) (orderedInterval (22240733490 / 1000000000000) (22240749918 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate547_chunkChecks3 :
    compactCertificate547.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate547.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate547_chunkChecks3_0
    compactCertificate547_chunkChecks3_1 compactCertificate547_chunkChecks3_2

theorem compactCertificate547_chunkChecks4_0 :
    compactCertificate547.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (837 / 2) 4 (IntervalRat.scale (837 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-38733455996 / 1000000000000) (-38733455934 / 1000000000000), orderedInterval (-4526745798 / 1000000000000) (-4526745736 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1233060823393137 / 4000000000000) 4 (IntervalRat.scale (837 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (41915349405 / 1000000000000) (41915349406 / 1000000000000), orderedInterval (17489652583 / 1000000000000) (17489652584 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (398746535451921 / 800000000000) 4 (IntervalRat.scale (837 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (10387711244 / 1000000000000) (10387711272 / 1000000000000), orderedInterval (-34206004549 / 1000000000000) (-34206004521 / 1000000000000)))) (orderedInterval (-14035341494 / 1000000000000) (-14035341415 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (359804072968659 / 4000000000000) 4 (IntervalRat.scale (837 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (30512469800 / 1000000000000) (30512471033 / 1000000000000), orderedInterval (-78569056402 / 1000000000000) (-78569055169 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (966484350623223 / 4000000000000) 4 (IntervalRat.scale (837 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-24759019533 / 1000000000000) (-24759019532 / 1000000000000), orderedInterval (-44912968642 / 1000000000000) (-44912968641 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2624193019923291 / 4000000000000) 4 (IntervalRat.scale (837 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-7422769786 / 1000000000000) (-7422769785 / 1000000000000), orderedInterval (-30248075278 / 1000000000000) (-30248075277 / 1000000000000)))) (orderedInterval (3123596783 / 1000000000000) (3123596965 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1932968701247283 / 4000000000000) 4 (IntervalRat.scale (837 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (7993300171 / 1000000000000) (7993300172 / 1000000000000), orderedInterval (35396540063 / 1000000000000) (35396540064 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3312174815983359 / 4000000000000) 4 (IntervalRat.scale (837 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-14528561763 / 1000000000000) (-14528561659 / 1000000000000), orderedInterval (23625394808 / 1000000000000) (23625394912 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2439732978384381 / 4000000000000) 4 (IntervalRat.scale (837 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (30653526996 / 1000000000000) (30653527008 / 1000000000000), orderedInterval (10178507824 / 1000000000000) (10178507837 / 1000000000000)))) (orderedInterval (10186997856 / 1000000000000) (10186998151 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate547_chunkChecks4_1 :
    compactCertificate547.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3743177794334163 / 4000000000000) 4 (IntervalRat.scale (837 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (9798009627 / 1000000000000) (9798009628 / 1000000000000), orderedInterval (24167017649 / 1000000000000) (24167017650 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2161124707183227 / 4000000000000) 4 (IntervalRat.scale (837 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (22437797739 / 1000000000000) (22437797740 / 1000000000000), orderedInterval (25957250141 / 1000000000000) (25957250142 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3834953717012343 / 4000000000000) 4 (IntervalRat.scale (837 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-25073074470 / 1000000000000) (-25073073945 / 1000000000000), orderedInterval (-5933273942 / 1000000000000) (-5933273417 / 1000000000000)))) (orderedInterval (-137337266365 / 1000000000000) (-137337260715 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3583111219545267 / 4000000000000) 4 (IntervalRat.scale (837 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24934418494 / 1000000000000) (-24934418434 / 1000000000000), orderedInterval (-9418159067 / 1000000000000) (-9418159007 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2557077237784611 / 4000000000000) 4 (IntervalRat.scale (837 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-23295319337 / 1000000000000) (-23295310476 / 1000000000000), orderedInterval (21306325985 / 1000000000000) (21306334846 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2899453051869669 / 4000000000000) 4 (IntervalRat.scale (837 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (1759735380 / 1000000000000) (1759735381 / 1000000000000), orderedInterval (-29584408719 / 1000000000000) (-29584408718 / 1000000000000)))) (orderedInterval (-2578849349 / 1000000000000) (-2578844356 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2417261671472661 / 4000000000000) 4 (IntervalRat.scale (837 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30555157731 / 1000000000000) (30555193007 / 1000000000000), orderedInterval (-10972309848 / 1000000000000) (-10972274571 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2135723994937881 / 4000000000000) 4 (IntervalRat.scale (837 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (20770778868 / 1000000000000) (20770778869 / 1000000000000), orderedInterval (27564979880 / 1000000000000) (27564979881 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (619016057574219 / 800000000000) 4 (IntervalRat.scale (837 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (28349771458 / 1000000000000) (28349784555 / 1000000000000), orderedInterval (-4381866672 / 1000000000000) (-4381853575 / 1000000000000)))) (orderedInterval (6846404505 / 1000000000000) (6846410422 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate547_chunkChecks4_2 :
    compactCertificate547.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1712230992280593 / 4000000000000) 4 (IntervalRat.scale (837 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (38559984188 / 1000000000000) (38559984593 / 1000000000000), orderedInterval (-641110431 / 1000000000000) (-641110026 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1451477174595273 / 4000000000000) 4 (IntervalRat.scale (837 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-29170091928 / 1000000000000) (-29170072562 / 1000000000000), orderedInterval (30098652084 / 1000000000000) (30098671450 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (908267021615619 / 4000000000000) 4 (IntervalRat.scale (837 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (52753304307 / 1000000000000) (52753304578 / 1000000000000), orderedInterval (-4671386526 / 1000000000000) (-4671386255 / 1000000000000)))) (orderedInterval (-5671057505 / 1000000000000) (-5671056721 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (488469024984573 / 4000000000000) 4 (IntervalRat.scale (837 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-26748864641 / 1000000000000) (-26748864640 / 1000000000000), orderedInterval (-66955481286 / 1000000000000) (-66955481285 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1326288423592719 / 4000000000000) 4 (IntervalRat.scale (837 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-26577016096 / 1000000000000) (-26577009067 / 1000000000000), orderedInterval (34877797114 / 1000000000000) (34877804143 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1810933454530863 / 4000000000000) 4 (IntervalRat.scale (837 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (33900759456 / 1000000000000) (33900759457 / 1000000000000), orderedInterval (15990887936 / 1000000000000) (15990887937 / 1000000000000)))) (orderedInterval (-3326276071 / 1000000000000) (-3326275959 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (765732978384381 / 4000000000000) 4 (IntervalRat.scale (837 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-31643543060 / 1000000000000) (-31643543059 / 1000000000000), orderedInterval (-48127673958 / 1000000000000) (-48127673957 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3112662044908701 / 4000000000000) 4 (IntervalRat.scale (837 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-4676282659 / 1000000000000) (-4676282658 / 1000000000000), orderedInterval (28220655894 / 1000000000000) (28220655896 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2079113992591059 / 4000000000000) 4 (IntervalRat.scale (837 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-28277082061 / 1000000000000) (-28277037480 / 1000000000000), orderedInterval (20647512778 / 1000000000000) (20647557359 / 1000000000000)))) (orderedInterval (17060269028 / 1000000000000) (17060289605 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate547_chunkChecks4 :
    compactCertificate547.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate547.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate547_chunkChecks4_0
    compactCertificate547_chunkChecks4_1 compactCertificate547_chunkChecks4_2

theorem compactCertificate547_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate547.chunkCheck r b = true :=
  compactCertificate547.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate547_chunkChecks0
    · exact compactCertificate547_chunkChecks1
    · exact compactCertificate547_chunkChecks2
    · exact compactCertificate547_chunkChecks3
    · exact compactCertificate547_chunkChecks4)

theorem compactCertificate547_coefficient0 :
    compactCertificate547.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate547_coefficient1 :
    compactCertificate547.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate547_coefficient2 :
    compactCertificate547.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate547_coefficient3 :
    compactCertificate547.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate547_coefficient4 :
    compactCertificate547.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate547_coefficients : ∀ r : Fin 5,
    compactCertificate547.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate547_coefficient0
  · exact compactCertificate547_coefficient1
  · exact compactCertificate547_coefficient2
  · exact compactCertificate547_coefficient3
  · exact compactCertificate547_coefficient4

theorem compactCertificate547_lower : (1 : ℚ) ≤ compactCertificate547.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate547, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate547_proves {t : ℝ} (ht : t ∈ compactCertificate547.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate547.proves compactCertificate547_states compactCertificate547_chunks
    compactCertificate547_coefficients compactCertificate547_lower ht

end Erdos232
