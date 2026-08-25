/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate337 : CompactCertificate where
  left := 209
  right := 210
  center := 419 / 2
  grid := fun i =>
    match i.val with
    | 0 => 67
    | 1 => 49
    | 2 => 79
    | 3 => 14
    | 4 => 39
    | 5 => 105
    | 6 => 77
    | 7 => 132
    | 8 => 97
    | 9 => 149
    | 10 => 86
    | 11 => 153
    | 12 => 143
    | 13 => 102
    | 14 => 116
    | 15 => 96
    | 16 => 85
    | 17 => 123
    | 18 => 68
    | 19 => 58
    | 20 => 36
    | 21 => 19
    | 22 => 53
    | 23 => 72
    | 24 => 31
    | 25 => 124
    | _ => 83
  point := fun i =>
    match i.val with
    | 0 => 419 / 2
    | 1 => 617267007170519 / 4000000000000
    | 2 => 199611467567927 / 800000000000
    | 3 => 180116973206533 / 4000000000000
    | 4 => 483819525580801 / 4000000000000
    | 5 => 1313664128253117 / 4000000000000
    | 6 => 967639051162021 / 4000000000000
    | 7 => 1658066007045433 / 4000000000000
    | 8 => 1221323916299947 / 4000000000000
    | 9 => 1873824965144581 / 4000000000000
    | 10 => 1081853348040349 / 4000000000000
    | 11 => 1919767750810241 / 4000000000000
    | 12 => 1793696058529829 / 4000000000000
    | 13 => 1280066144123957 / 4000000000000
    | 14 => 1451458576742403 / 4000000000000
    | 15 => 1210074839124307 / 4000000000000
    | 16 => 1069137818254447 / 4000000000000
    | 17 => 309877811378253 / 800000000000
    | 18 => 857138334247991 / 4000000000000
    | 19 => 726605658489151 / 4000000000000
    | 20 => 454676083700053 / 4000000000000
    | 21 => 244526309998251 / 4000000000000
    | 22 => 663936498787753 / 4000000000000
    | 23 => 906548527417481 / 4000000000000
    | 24 => 383323916299947 / 4000000000000
    | 25 => 1558190438251787 / 4000000000000
    | _ => 1040798999875333 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (11054585948 / 1000000000000) (11054586010 / 1000000000000), orderedInterval (-54031586132 / 1000000000000) (-54031586070 / 1000000000000))
    | 1 => (orderedInterval (-58969832777 / 1000000000000) (-58969832776 / 1000000000000), orderedInterval (-25263861960 / 1000000000000) (-25263861959 / 1000000000000))
    | 2 => (orderedInterval (-43256255416 / 1000000000000) (-43256213595 / 1000000000000), orderedInterval (26169821784 / 1000000000000) (26169863605 / 1000000000000))
    | 3 => (orderedInterval (114940535415 / 1000000000000) (114940536183 / 1000000000000), orderedInterval (-31703666692 / 1000000000000) (-31703665924 / 1000000000000))
    | 4 => (orderedInterval (51169279958 / 1000000000000) (51169345298 / 1000000000000), orderedInterval (-51640962675 / 1000000000000) (-51640897336 / 1000000000000))
    | 5 => (orderedInterval (27208621966 / 1000000000000) (27208630246 / 1000000000000), orderedInterval (-34655679512 / 1000000000000) (-34655671232 / 1000000000000))
    | 6 => (orderedInterval (-36513246173 / 1000000000000) (-36513246172 / 1000000000000), orderedInterval (-35958186487 / 1000000000000) (-35958186486 / 1000000000000))
    | 7 => (orderedInterval (22494275846 / 1000000000000) (22494275847 / 1000000000000), orderedInterval (32063687868 / 1000000000000) (32063687869 / 1000000000000))
    | 8 => (orderedInterval (-44846105163 / 1000000000000) (-44846105154 / 1000000000000), orderedInterval (-8519557991 / 1000000000000) (-8519557982 / 1000000000000))
    | 9 => (orderedInterval (-33558428927 / 1000000000000) (-33558428925 / 1000000000000), orderedInterval (-15222136226 / 1000000000000) (-15222136224 / 1000000000000))
    | 10 => (orderedInterval (42588666243 / 1000000000000) (42588666244 / 1000000000000), orderedInterval (23159491390 / 1000000000000) (23159491391 / 1000000000000))
    | 11 => (orderedInterval (-2307490349 / 1000000000000) (-2307490348 / 1000000000000), orderedInterval (-36344918488 / 1000000000000) (-36344918487 / 1000000000000))
    | 12 => (orderedInterval (1454615893 / 1000000000000) (1454615894 / 1000000000000), orderedInterval (-37652220527 / 1000000000000) (-37652220525 / 1000000000000))
    | 13 => (orderedInterval (15674238040 / 1000000000000) (15674238041 / 1000000000000), orderedInterval (41732594515 / 1000000000000) (41732594516 / 1000000000000))
    | 14 => (orderedInterval (-29309720069 / 1000000000000) (-29309699831 / 1000000000000), orderedInterval (29963086362 / 1000000000000) (29963106600 / 1000000000000))
    | 15 => (orderedInterval (45424834487 / 1000000000000) (45424835348 / 1000000000000), orderedInterval (-6476610885 / 1000000000000) (-6476610024 / 1000000000000))
    | 16 => (orderedInterval (-41939773225 / 1000000000000) (-41939773224 / 1000000000000), orderedInterval (-24878701027 / 1000000000000) (-24878701026 / 1000000000000))
    | 17 => (orderedInterval (-40111316020 / 1000000000000) (-40111314495 / 1000000000000), orderedInterval (5935535211 / 1000000000000) (5935536736 / 1000000000000))
    | 18 => (orderedInterval (54048163364 / 1000000000000) (54048163375 / 1000000000000), orderedInterval (6923438497 / 1000000000000) (6923438507 / 1000000000000))
    | 19 => (orderedInterval (13135739025 / 1000000000000) (13135739026 / 1000000000000), orderedInterval (57688081247 / 1000000000000) (57688081248 / 1000000000000))
    | 20 => (orderedInterval (73117065813 / 1000000000000) (73117065815 / 1000000000000), orderedInterval (15631122966 / 1000000000000) (15631122968 / 1000000000000))
    | 21 => (orderedInterval (-80998056978 / 1000000000000) (-80998008232 / 1000000000000), orderedInterval (62736203273 / 1000000000000) (62736252019 / 1000000000000))
    | 22 => (orderedInterval (-16181911095 / 1000000000000) (-16181911094 / 1000000000000), orderedInterval (-59730736901 / 1000000000000) (-59730736900 / 1000000000000))
    | 23 => (orderedInterval (49903812757 / 1000000000000) (49903812758 / 1000000000000), orderedInterval (17738905403 / 1000000000000) (17738905404 / 1000000000000))
    | 24 => (orderedInterval (56989495378 / 1000000000000) (56989562954 / 1000000000000), orderedInterval (-58566978042 / 1000000000000) (-58566910466 / 1000000000000))
    | 25 => (orderedInterval (28292358501 / 1000000000000) (28292358502 / 1000000000000), orderedInterval (28839221403 / 1000000000000) (28839221404 / 1000000000000))
    | _ => (orderedInterval (-11395885870 / 1000000000000) (-11395885869 / 1000000000000), orderedInterval (-48111205911 / 1000000000000) (-48111205910 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (1293840054 / 1000000000000) (1293842548 / 1000000000000)
      | 1 => orderedInterval (-1312995341 / 1000000000000) (-1312992333 / 1000000000000)
      | 2 => orderedInterval (-1777655353 / 1000000000000) (-1777655341 / 1000000000000)
      | 3 => orderedInterval (8790373951 / 1000000000000) (8790374035 / 1000000000000)
      | 4 => orderedInterval (1604264516 / 1000000000000) (1604264644 / 1000000000000)
      | 5 => orderedInterval (1897616714 / 1000000000000) (1897616784 / 1000000000000)
      | 6 => orderedInterval (-7005029213 / 1000000000000) (-7005029158 / 1000000000000)
      | 7 => orderedInterval (-1961817349 / 1000000000000) (-1961816423 / 1000000000000)
      | _ => orderedInterval (178673571 / 1000000000000) (178674038 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-19760643659 / 1000000000000) (-19760640694 / 1000000000000)
      | 1 => orderedInterval (2847412460 / 1000000000000) (2847414791 / 1000000000000)
      | 2 => orderedInterval (-2256865471 / 1000000000000) (-2256865449 / 1000000000000)
      | 3 => orderedInterval (-3572878700 / 1000000000000) (-3572878526 / 1000000000000)
      | 4 => orderedInterval (7220469046 / 1000000000000) (7220469265 / 1000000000000)
      | 5 => orderedInterval (1989406873 / 1000000000000) (1989406990 / 1000000000000)
      | 6 => orderedInterval (-3687296714 / 1000000000000) (-3687296663 / 1000000000000)
      | 7 => orderedInterval (-735093308 / 1000000000000) (-735093022 / 1000000000000)
      | _ => orderedInterval (6684892864 / 1000000000000) (6684893133 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-388633204 / 1000000000000) (-388629665 / 1000000000000)
      | 1 => orderedInterval (4174538768 / 1000000000000) (4174541061 / 1000000000000)
      | 2 => orderedInterval (5029132974 / 1000000000000) (5029133012 / 1000000000000)
      | 3 => orderedInterval (-33335172174 / 1000000000000) (-33335171802 / 1000000000000)
      | 4 => orderedInterval (-3817594039 / 1000000000000) (-3817593663 / 1000000000000)
      | 5 => orderedInterval (-1499100650 / 1000000000000) (-1499100452 / 1000000000000)
      | 6 => orderedInterval (8916949924 / 1000000000000) (8916949973 / 1000000000000)
      | 7 => orderedInterval (4121579556 / 1000000000000) (4121579657 / 1000000000000)
      | _ => orderedInterval (4560544162 / 1000000000000) (4560544369 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (18917332313 / 1000000000000) (18917336523 / 1000000000000)
      | 1 => orderedInterval (-9151187895 / 1000000000000) (-9151185098 / 1000000000000)
      | 2 => orderedInterval (8273861039 / 1000000000000) (8273861107 / 1000000000000)
      | 3 => orderedInterval (28345210114 / 1000000000000) (28345210929 / 1000000000000)
      | 4 => orderedInterval (-19925278438 / 1000000000000) (-19925277790 / 1000000000000)
      | 5 => orderedInterval (-3684770551 / 1000000000000) (-3684770207 / 1000000000000)
      | 6 => orderedInterval (3189133883 / 1000000000000) (3189133931 / 1000000000000)
      | 7 => orderedInterval (1056296816 / 1000000000000) (1056296862 / 1000000000000)
      | _ => orderedInterval (-2190358930 / 1000000000000) (-2190358704 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-1068034477 / 1000000000000) (-1068029449 / 1000000000000)
      | 1 => orderedInterval (-11388463652 / 1000000000000) (-11388459714 / 1000000000000)
      | 2 => orderedInterval (-15602365126 / 1000000000000) (-15602365001 / 1000000000000)
      | 3 => orderedInterval (148532123723 / 1000000000000) (148532125531 / 1000000000000)
      | 4 => orderedInterval (9043592977 / 1000000000000) (9043594103 / 1000000000000)
      | 5 => orderedInterval (-3326894884 / 1000000000000) (-3326894275 / 1000000000000)
      | 6 => orderedInterval (-9702996318 / 1000000000000) (-9702996271 / 1000000000000)
      | 7 => orderedInterval (-5092557711 / 1000000000000) (-5092557679 / 1000000000000)
      | _ => orderedInterval (-22406285642 / 1000000000000) (-22406285323 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (1707271550 / 1000000000000) (1707278794 / 1000000000000)
    | 1 => orderedInterval (-11270596609 / 1000000000000) (-11270590175 / 1000000000000)
    | 2 => orderedInterval (-12237754683 / 1000000000000) (-12237747510 / 1000000000000)
    | 3 => orderedInterval (24830238351 / 1000000000000) (24830247553 / 1000000000000)
    | _ => orderedInterval (88988118890 / 1000000000000) (88988131922 / 1000000000000)

theorem compactCertificate337_stateChecks0 :
    compactCertificate337.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (419 / 2)) (orderedInterval (11054585948 / 1000000000000) (11054586010 / 1000000000000), orderedInterval (-54031586132 / 1000000000000) (-54031586070 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (617267007170519 / 4000000000000)) (orderedInterval (-58969832777 / 1000000000000) (-58969832776 / 1000000000000), orderedInterval (-25263861960 / 1000000000000) (-25263861959 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (199611467567927 / 800000000000)) (orderedInterval (-43256255416 / 1000000000000) (-43256213595 / 1000000000000), orderedInterval (26169821784 / 1000000000000) (26169863605 / 1000000000000))) = true
  rfl'

theorem compactCertificate337_stateChecks1 :
    compactCertificate337.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 14 12 (180116973206533 / 4000000000000)) (orderedInterval (114940535415 / 1000000000000) (114940536183 / 1000000000000), orderedInterval (-31703666692 / 1000000000000) (-31703665924 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (483819525580801 / 4000000000000)) (orderedInterval (51169279958 / 1000000000000) (51169345298 / 1000000000000), orderedInterval (-51640962675 / 1000000000000) (-51640897336 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 105 12 (1313664128253117 / 4000000000000)) (orderedInterval (27208621966 / 1000000000000) (27208630246 / 1000000000000), orderedInterval (-34655679512 / 1000000000000) (-34655671232 / 1000000000000))) = true
  rfl'

theorem compactCertificate337_stateChecks2 :
    compactCertificate337.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (967639051162021 / 4000000000000)) (orderedInterval (-36513246173 / 1000000000000) (-36513246172 / 1000000000000), orderedInterval (-35958186487 / 1000000000000) (-35958186486 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 132 12 (1658066007045433 / 4000000000000)) (orderedInterval (22494275846 / 1000000000000) (22494275847 / 1000000000000), orderedInterval (32063687868 / 1000000000000) (32063687869 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 97 12 (1221323916299947 / 4000000000000)) (orderedInterval (-44846105163 / 1000000000000) (-44846105154 / 1000000000000), orderedInterval (-8519557991 / 1000000000000) (-8519557982 / 1000000000000))) = true
  rfl'

theorem compactCertificate337_stateChecks3 :
    compactCertificate337.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 149 12 (1873824965144581 / 4000000000000)) (orderedInterval (-33558428927 / 1000000000000) (-33558428925 / 1000000000000), orderedInterval (-15222136226 / 1000000000000) (-15222136224 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (1081853348040349 / 4000000000000)) (orderedInterval (42588666243 / 1000000000000) (42588666244 / 1000000000000), orderedInterval (23159491390 / 1000000000000) (23159491391 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 153 12 (1919767750810241 / 4000000000000)) (orderedInterval (-2307490349 / 1000000000000) (-2307490348 / 1000000000000), orderedInterval (-36344918488 / 1000000000000) (-36344918487 / 1000000000000))) = true
  rfl'

theorem compactCertificate337_stateChecks4 :
    compactCertificate337.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 143 12 (1793696058529829 / 4000000000000)) (orderedInterval (1454615893 / 1000000000000) (1454615894 / 1000000000000), orderedInterval (-37652220527 / 1000000000000) (-37652220525 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 102 12 (1280066144123957 / 4000000000000)) (orderedInterval (15674238040 / 1000000000000) (15674238041 / 1000000000000), orderedInterval (41732594515 / 1000000000000) (41732594516 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 116 12 (1451458576742403 / 4000000000000)) (orderedInterval (-29309720069 / 1000000000000) (-29309699831 / 1000000000000), orderedInterval (29963086362 / 1000000000000) (29963106600 / 1000000000000))) = true
  rfl'

theorem compactCertificate337_stateChecks5 :
    compactCertificate337.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 96 12 (1210074839124307 / 4000000000000)) (orderedInterval (45424834487 / 1000000000000) (45424835348 / 1000000000000), orderedInterval (-6476610885 / 1000000000000) (-6476610024 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (1069137818254447 / 4000000000000)) (orderedInterval (-41939773225 / 1000000000000) (-41939773224 / 1000000000000), orderedInterval (-24878701027 / 1000000000000) (-24878701026 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 123 12 (309877811378253 / 800000000000)) (orderedInterval (-40111316020 / 1000000000000) (-40111314495 / 1000000000000), orderedInterval (5935535211 / 1000000000000) (5935536736 / 1000000000000))) = true
  rfl'

theorem compactCertificate337_stateChecks6 :
    compactCertificate337.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (857138334247991 / 4000000000000)) (orderedInterval (54048163364 / 1000000000000) (54048163375 / 1000000000000), orderedInterval (6923438497 / 1000000000000) (6923438507 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (726605658489151 / 4000000000000)) (orderedInterval (13135739025 / 1000000000000) (13135739026 / 1000000000000), orderedInterval (57688081247 / 1000000000000) (57688081248 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (454676083700053 / 4000000000000)) (orderedInterval (73117065813 / 1000000000000) (73117065815 / 1000000000000), orderedInterval (15631122966 / 1000000000000) (15631122968 / 1000000000000))) = true
  rfl'

theorem compactCertificate337_stateChecks7 :
    compactCertificate337.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 19 12 (244526309998251 / 4000000000000)) (orderedInterval (-80998056978 / 1000000000000) (-80998008232 / 1000000000000), orderedInterval (62736203273 / 1000000000000) (62736252019 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (663936498787753 / 4000000000000)) (orderedInterval (-16181911095 / 1000000000000) (-16181911094 / 1000000000000), orderedInterval (-59730736901 / 1000000000000) (-59730736900 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (906548527417481 / 4000000000000)) (orderedInterval (49903812757 / 1000000000000) (49903812758 / 1000000000000), orderedInterval (17738905403 / 1000000000000) (17738905404 / 1000000000000))) = true
  rfl'

theorem compactCertificate337_stateChecks8 :
    compactCertificate337.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (383323916299947 / 4000000000000)) (orderedInterval (56989495378 / 1000000000000) (56989562954 / 1000000000000), orderedInterval (-58566978042 / 1000000000000) (-58566910466 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 124 12 (1558190438251787 / 4000000000000)) (orderedInterval (28292358501 / 1000000000000) (28292358502 / 1000000000000), orderedInterval (28839221403 / 1000000000000) (28839221404 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (1040798999875333 / 4000000000000)) (orderedInterval (-11395885870 / 1000000000000) (-11395885869 / 1000000000000), orderedInterval (-48111205911 / 1000000000000) (-48111205910 / 1000000000000))) = true
  rfl'

theorem compactCertificate337_states : ∀ j,
    BesselStateValid (compactCertificate337.point j) (compactCertificate337.state j) :=
  compactCertificate337.statesValid_of_checks3 compactCertificate337_stateChecks0
    compactCertificate337_stateChecks1 compactCertificate337_stateChecks2
    compactCertificate337_stateChecks3 compactCertificate337_stateChecks4
    compactCertificate337_stateChecks5 compactCertificate337_stateChecks6
    compactCertificate337_stateChecks7 compactCertificate337_stateChecks8

theorem compactCertificate337_chunkChecks0_0 :
    compactCertificate337.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (419 / 2) 0 (IntervalRat.scale (419 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (11054585948 / 1000000000000) (11054586010 / 1000000000000), orderedInterval (-54031586132 / 1000000000000) (-54031586070 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (617267007170519 / 4000000000000) 0 (IntervalRat.scale (419 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-58969832777 / 1000000000000) (-58969832776 / 1000000000000), orderedInterval (-25263861960 / 1000000000000) (-25263861959 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (199611467567927 / 800000000000) 0 (IntervalRat.scale (419 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-43256255416 / 1000000000000) (-43256213595 / 1000000000000), orderedInterval (26169821784 / 1000000000000) (26169863605 / 1000000000000)))) (orderedInterval (1293840054 / 1000000000000) (1293842548 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (180116973206533 / 4000000000000) 0 (IntervalRat.scale (419 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (114940535415 / 1000000000000) (114940536183 / 1000000000000), orderedInterval (-31703666692 / 1000000000000) (-31703665924 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (483819525580801 / 4000000000000) 0 (IntervalRat.scale (419 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (51169279958 / 1000000000000) (51169345298 / 1000000000000), orderedInterval (-51640962675 / 1000000000000) (-51640897336 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1313664128253117 / 4000000000000) 0 (IntervalRat.scale (419 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (27208621966 / 1000000000000) (27208630246 / 1000000000000), orderedInterval (-34655679512 / 1000000000000) (-34655671232 / 1000000000000)))) (orderedInterval (-1312995341 / 1000000000000) (-1312992333 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (967639051162021 / 4000000000000) 0 (IntervalRat.scale (419 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-36513246173 / 1000000000000) (-36513246172 / 1000000000000), orderedInterval (-35958186487 / 1000000000000) (-35958186486 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1658066007045433 / 4000000000000) 0 (IntervalRat.scale (419 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (22494275846 / 1000000000000) (22494275847 / 1000000000000), orderedInterval (32063687868 / 1000000000000) (32063687869 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1221323916299947 / 4000000000000) 0 (IntervalRat.scale (419 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-44846105163 / 1000000000000) (-44846105154 / 1000000000000), orderedInterval (-8519557991 / 1000000000000) (-8519557982 / 1000000000000)))) (orderedInterval (-1777655353 / 1000000000000) (-1777655341 / 1000000000000))) = true
  rfl'

theorem compactCertificate337_chunkChecks0_1 :
    compactCertificate337.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1873824965144581 / 4000000000000) 0 (IntervalRat.scale (419 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-33558428927 / 1000000000000) (-33558428925 / 1000000000000), orderedInterval (-15222136226 / 1000000000000) (-15222136224 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1081853348040349 / 4000000000000) 0 (IntervalRat.scale (419 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (42588666243 / 1000000000000) (42588666244 / 1000000000000), orderedInterval (23159491390 / 1000000000000) (23159491391 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1919767750810241 / 4000000000000) 0 (IntervalRat.scale (419 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-2307490349 / 1000000000000) (-2307490348 / 1000000000000), orderedInterval (-36344918488 / 1000000000000) (-36344918487 / 1000000000000)))) (orderedInterval (8790373951 / 1000000000000) (8790374035 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1793696058529829 / 4000000000000) 0 (IntervalRat.scale (419 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (1454615893 / 1000000000000) (1454615894 / 1000000000000), orderedInterval (-37652220527 / 1000000000000) (-37652220525 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1280066144123957 / 4000000000000) 0 (IntervalRat.scale (419 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (15674238040 / 1000000000000) (15674238041 / 1000000000000), orderedInterval (41732594515 / 1000000000000) (41732594516 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1451458576742403 / 4000000000000) 0 (IntervalRat.scale (419 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-29309720069 / 1000000000000) (-29309699831 / 1000000000000), orderedInterval (29963086362 / 1000000000000) (29963106600 / 1000000000000)))) (orderedInterval (1604264516 / 1000000000000) (1604264644 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1210074839124307 / 4000000000000) 0 (IntervalRat.scale (419 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (45424834487 / 1000000000000) (45424835348 / 1000000000000), orderedInterval (-6476610885 / 1000000000000) (-6476610024 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1069137818254447 / 4000000000000) 0 (IntervalRat.scale (419 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-41939773225 / 1000000000000) (-41939773224 / 1000000000000), orderedInterval (-24878701027 / 1000000000000) (-24878701026 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (309877811378253 / 800000000000) 0 (IntervalRat.scale (419 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-40111316020 / 1000000000000) (-40111314495 / 1000000000000), orderedInterval (5935535211 / 1000000000000) (5935536736 / 1000000000000)))) (orderedInterval (1897616714 / 1000000000000) (1897616784 / 1000000000000))) = true
  rfl'

theorem compactCertificate337_chunkChecks0_2 :
    compactCertificate337.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (857138334247991 / 4000000000000) 0 (IntervalRat.scale (419 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (54048163364 / 1000000000000) (54048163375 / 1000000000000), orderedInterval (6923438497 / 1000000000000) (6923438507 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (726605658489151 / 4000000000000) 0 (IntervalRat.scale (419 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (13135739025 / 1000000000000) (13135739026 / 1000000000000), orderedInterval (57688081247 / 1000000000000) (57688081248 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (454676083700053 / 4000000000000) 0 (IntervalRat.scale (419 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (73117065813 / 1000000000000) (73117065815 / 1000000000000), orderedInterval (15631122966 / 1000000000000) (15631122968 / 1000000000000)))) (orderedInterval (-7005029213 / 1000000000000) (-7005029158 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (244526309998251 / 4000000000000) 0 (IntervalRat.scale (419 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-80998056978 / 1000000000000) (-80998008232 / 1000000000000), orderedInterval (62736203273 / 1000000000000) (62736252019 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (663936498787753 / 4000000000000) 0 (IntervalRat.scale (419 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-16181911095 / 1000000000000) (-16181911094 / 1000000000000), orderedInterval (-59730736901 / 1000000000000) (-59730736900 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (906548527417481 / 4000000000000) 0 (IntervalRat.scale (419 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (49903812757 / 1000000000000) (49903812758 / 1000000000000), orderedInterval (17738905403 / 1000000000000) (17738905404 / 1000000000000)))) (orderedInterval (-1961817349 / 1000000000000) (-1961816423 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (383323916299947 / 4000000000000) 0 (IntervalRat.scale (419 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (56989495378 / 1000000000000) (56989562954 / 1000000000000), orderedInterval (-58566978042 / 1000000000000) (-58566910466 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1558190438251787 / 4000000000000) 0 (IntervalRat.scale (419 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (28292358501 / 1000000000000) (28292358502 / 1000000000000), orderedInterval (28839221403 / 1000000000000) (28839221404 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1040798999875333 / 4000000000000) 0 (IntervalRat.scale (419 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-11395885870 / 1000000000000) (-11395885869 / 1000000000000), orderedInterval (-48111205911 / 1000000000000) (-48111205910 / 1000000000000)))) (orderedInterval (178673571 / 1000000000000) (178674038 / 1000000000000))) = true
  rfl'

theorem compactCertificate337_chunkChecks0 :
    compactCertificate337.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate337.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate337_chunkChecks0_0
    compactCertificate337_chunkChecks0_1 compactCertificate337_chunkChecks0_2

theorem compactCertificate337_chunkChecks1_0 :
    compactCertificate337.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (419 / 2) 1 (IntervalRat.scale (419 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (11054585948 / 1000000000000) (11054586010 / 1000000000000), orderedInterval (-54031586132 / 1000000000000) (-54031586070 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (617267007170519 / 4000000000000) 1 (IntervalRat.scale (419 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-58969832777 / 1000000000000) (-58969832776 / 1000000000000), orderedInterval (-25263861960 / 1000000000000) (-25263861959 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (199611467567927 / 800000000000) 1 (IntervalRat.scale (419 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-43256255416 / 1000000000000) (-43256213595 / 1000000000000), orderedInterval (26169821784 / 1000000000000) (26169863605 / 1000000000000)))) (orderedInterval (-19760643659 / 1000000000000) (-19760640694 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (180116973206533 / 4000000000000) 1 (IntervalRat.scale (419 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (114940535415 / 1000000000000) (114940536183 / 1000000000000), orderedInterval (-31703666692 / 1000000000000) (-31703665924 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (483819525580801 / 4000000000000) 1 (IntervalRat.scale (419 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (51169279958 / 1000000000000) (51169345298 / 1000000000000), orderedInterval (-51640962675 / 1000000000000) (-51640897336 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1313664128253117 / 4000000000000) 1 (IntervalRat.scale (419 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (27208621966 / 1000000000000) (27208630246 / 1000000000000), orderedInterval (-34655679512 / 1000000000000) (-34655671232 / 1000000000000)))) (orderedInterval (2847412460 / 1000000000000) (2847414791 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (967639051162021 / 4000000000000) 1 (IntervalRat.scale (419 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-36513246173 / 1000000000000) (-36513246172 / 1000000000000), orderedInterval (-35958186487 / 1000000000000) (-35958186486 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1658066007045433 / 4000000000000) 1 (IntervalRat.scale (419 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (22494275846 / 1000000000000) (22494275847 / 1000000000000), orderedInterval (32063687868 / 1000000000000) (32063687869 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1221323916299947 / 4000000000000) 1 (IntervalRat.scale (419 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-44846105163 / 1000000000000) (-44846105154 / 1000000000000), orderedInterval (-8519557991 / 1000000000000) (-8519557982 / 1000000000000)))) (orderedInterval (-2256865471 / 1000000000000) (-2256865449 / 1000000000000))) = true
  rfl'

theorem compactCertificate337_chunkChecks1_1 :
    compactCertificate337.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1873824965144581 / 4000000000000) 1 (IntervalRat.scale (419 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-33558428927 / 1000000000000) (-33558428925 / 1000000000000), orderedInterval (-15222136226 / 1000000000000) (-15222136224 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1081853348040349 / 4000000000000) 1 (IntervalRat.scale (419 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (42588666243 / 1000000000000) (42588666244 / 1000000000000), orderedInterval (23159491390 / 1000000000000) (23159491391 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1919767750810241 / 4000000000000) 1 (IntervalRat.scale (419 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-2307490349 / 1000000000000) (-2307490348 / 1000000000000), orderedInterval (-36344918488 / 1000000000000) (-36344918487 / 1000000000000)))) (orderedInterval (-3572878700 / 1000000000000) (-3572878526 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1793696058529829 / 4000000000000) 1 (IntervalRat.scale (419 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (1454615893 / 1000000000000) (1454615894 / 1000000000000), orderedInterval (-37652220527 / 1000000000000) (-37652220525 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1280066144123957 / 4000000000000) 1 (IntervalRat.scale (419 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (15674238040 / 1000000000000) (15674238041 / 1000000000000), orderedInterval (41732594515 / 1000000000000) (41732594516 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1451458576742403 / 4000000000000) 1 (IntervalRat.scale (419 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-29309720069 / 1000000000000) (-29309699831 / 1000000000000), orderedInterval (29963086362 / 1000000000000) (29963106600 / 1000000000000)))) (orderedInterval (7220469046 / 1000000000000) (7220469265 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1210074839124307 / 4000000000000) 1 (IntervalRat.scale (419 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (45424834487 / 1000000000000) (45424835348 / 1000000000000), orderedInterval (-6476610885 / 1000000000000) (-6476610024 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1069137818254447 / 4000000000000) 1 (IntervalRat.scale (419 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-41939773225 / 1000000000000) (-41939773224 / 1000000000000), orderedInterval (-24878701027 / 1000000000000) (-24878701026 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (309877811378253 / 800000000000) 1 (IntervalRat.scale (419 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-40111316020 / 1000000000000) (-40111314495 / 1000000000000), orderedInterval (5935535211 / 1000000000000) (5935536736 / 1000000000000)))) (orderedInterval (1989406873 / 1000000000000) (1989406990 / 1000000000000))) = true
  rfl'

theorem compactCertificate337_chunkChecks1_2 :
    compactCertificate337.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (857138334247991 / 4000000000000) 1 (IntervalRat.scale (419 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (54048163364 / 1000000000000) (54048163375 / 1000000000000), orderedInterval (6923438497 / 1000000000000) (6923438507 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (726605658489151 / 4000000000000) 1 (IntervalRat.scale (419 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (13135739025 / 1000000000000) (13135739026 / 1000000000000), orderedInterval (57688081247 / 1000000000000) (57688081248 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (454676083700053 / 4000000000000) 1 (IntervalRat.scale (419 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (73117065813 / 1000000000000) (73117065815 / 1000000000000), orderedInterval (15631122966 / 1000000000000) (15631122968 / 1000000000000)))) (orderedInterval (-3687296714 / 1000000000000) (-3687296663 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (244526309998251 / 4000000000000) 1 (IntervalRat.scale (419 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-80998056978 / 1000000000000) (-80998008232 / 1000000000000), orderedInterval (62736203273 / 1000000000000) (62736252019 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (663936498787753 / 4000000000000) 1 (IntervalRat.scale (419 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-16181911095 / 1000000000000) (-16181911094 / 1000000000000), orderedInterval (-59730736901 / 1000000000000) (-59730736900 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (906548527417481 / 4000000000000) 1 (IntervalRat.scale (419 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (49903812757 / 1000000000000) (49903812758 / 1000000000000), orderedInterval (17738905403 / 1000000000000) (17738905404 / 1000000000000)))) (orderedInterval (-735093308 / 1000000000000) (-735093022 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (383323916299947 / 4000000000000) 1 (IntervalRat.scale (419 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (56989495378 / 1000000000000) (56989562954 / 1000000000000), orderedInterval (-58566978042 / 1000000000000) (-58566910466 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1558190438251787 / 4000000000000) 1 (IntervalRat.scale (419 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (28292358501 / 1000000000000) (28292358502 / 1000000000000), orderedInterval (28839221403 / 1000000000000) (28839221404 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1040798999875333 / 4000000000000) 1 (IntervalRat.scale (419 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-11395885870 / 1000000000000) (-11395885869 / 1000000000000), orderedInterval (-48111205911 / 1000000000000) (-48111205910 / 1000000000000)))) (orderedInterval (6684892864 / 1000000000000) (6684893133 / 1000000000000))) = true
  rfl'

theorem compactCertificate337_chunkChecks1 :
    compactCertificate337.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate337.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate337_chunkChecks1_0
    compactCertificate337_chunkChecks1_1 compactCertificate337_chunkChecks1_2

theorem compactCertificate337_chunkChecks2_0 :
    compactCertificate337.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (419 / 2) 2 (IntervalRat.scale (419 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (11054585948 / 1000000000000) (11054586010 / 1000000000000), orderedInterval (-54031586132 / 1000000000000) (-54031586070 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (617267007170519 / 4000000000000) 2 (IntervalRat.scale (419 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-58969832777 / 1000000000000) (-58969832776 / 1000000000000), orderedInterval (-25263861960 / 1000000000000) (-25263861959 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (199611467567927 / 800000000000) 2 (IntervalRat.scale (419 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-43256255416 / 1000000000000) (-43256213595 / 1000000000000), orderedInterval (26169821784 / 1000000000000) (26169863605 / 1000000000000)))) (orderedInterval (-388633204 / 1000000000000) (-388629665 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (180116973206533 / 4000000000000) 2 (IntervalRat.scale (419 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (114940535415 / 1000000000000) (114940536183 / 1000000000000), orderedInterval (-31703666692 / 1000000000000) (-31703665924 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (483819525580801 / 4000000000000) 2 (IntervalRat.scale (419 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (51169279958 / 1000000000000) (51169345298 / 1000000000000), orderedInterval (-51640962675 / 1000000000000) (-51640897336 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1313664128253117 / 4000000000000) 2 (IntervalRat.scale (419 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (27208621966 / 1000000000000) (27208630246 / 1000000000000), orderedInterval (-34655679512 / 1000000000000) (-34655671232 / 1000000000000)))) (orderedInterval (4174538768 / 1000000000000) (4174541061 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (967639051162021 / 4000000000000) 2 (IntervalRat.scale (419 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-36513246173 / 1000000000000) (-36513246172 / 1000000000000), orderedInterval (-35958186487 / 1000000000000) (-35958186486 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1658066007045433 / 4000000000000) 2 (IntervalRat.scale (419 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (22494275846 / 1000000000000) (22494275847 / 1000000000000), orderedInterval (32063687868 / 1000000000000) (32063687869 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1221323916299947 / 4000000000000) 2 (IntervalRat.scale (419 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-44846105163 / 1000000000000) (-44846105154 / 1000000000000), orderedInterval (-8519557991 / 1000000000000) (-8519557982 / 1000000000000)))) (orderedInterval (5029132974 / 1000000000000) (5029133012 / 1000000000000))) = true
  rfl'

theorem compactCertificate337_chunkChecks2_1 :
    compactCertificate337.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1873824965144581 / 4000000000000) 2 (IntervalRat.scale (419 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-33558428927 / 1000000000000) (-33558428925 / 1000000000000), orderedInterval (-15222136226 / 1000000000000) (-15222136224 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1081853348040349 / 4000000000000) 2 (IntervalRat.scale (419 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (42588666243 / 1000000000000) (42588666244 / 1000000000000), orderedInterval (23159491390 / 1000000000000) (23159491391 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1919767750810241 / 4000000000000) 2 (IntervalRat.scale (419 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-2307490349 / 1000000000000) (-2307490348 / 1000000000000), orderedInterval (-36344918488 / 1000000000000) (-36344918487 / 1000000000000)))) (orderedInterval (-33335172174 / 1000000000000) (-33335171802 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1793696058529829 / 4000000000000) 2 (IntervalRat.scale (419 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (1454615893 / 1000000000000) (1454615894 / 1000000000000), orderedInterval (-37652220527 / 1000000000000) (-37652220525 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1280066144123957 / 4000000000000) 2 (IntervalRat.scale (419 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (15674238040 / 1000000000000) (15674238041 / 1000000000000), orderedInterval (41732594515 / 1000000000000) (41732594516 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1451458576742403 / 4000000000000) 2 (IntervalRat.scale (419 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-29309720069 / 1000000000000) (-29309699831 / 1000000000000), orderedInterval (29963086362 / 1000000000000) (29963106600 / 1000000000000)))) (orderedInterval (-3817594039 / 1000000000000) (-3817593663 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1210074839124307 / 4000000000000) 2 (IntervalRat.scale (419 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (45424834487 / 1000000000000) (45424835348 / 1000000000000), orderedInterval (-6476610885 / 1000000000000) (-6476610024 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1069137818254447 / 4000000000000) 2 (IntervalRat.scale (419 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-41939773225 / 1000000000000) (-41939773224 / 1000000000000), orderedInterval (-24878701027 / 1000000000000) (-24878701026 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (309877811378253 / 800000000000) 2 (IntervalRat.scale (419 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-40111316020 / 1000000000000) (-40111314495 / 1000000000000), orderedInterval (5935535211 / 1000000000000) (5935536736 / 1000000000000)))) (orderedInterval (-1499100650 / 1000000000000) (-1499100452 / 1000000000000))) = true
  rfl'

theorem compactCertificate337_chunkChecks2_2 :
    compactCertificate337.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (857138334247991 / 4000000000000) 2 (IntervalRat.scale (419 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (54048163364 / 1000000000000) (54048163375 / 1000000000000), orderedInterval (6923438497 / 1000000000000) (6923438507 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (726605658489151 / 4000000000000) 2 (IntervalRat.scale (419 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (13135739025 / 1000000000000) (13135739026 / 1000000000000), orderedInterval (57688081247 / 1000000000000) (57688081248 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (454676083700053 / 4000000000000) 2 (IntervalRat.scale (419 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (73117065813 / 1000000000000) (73117065815 / 1000000000000), orderedInterval (15631122966 / 1000000000000) (15631122968 / 1000000000000)))) (orderedInterval (8916949924 / 1000000000000) (8916949973 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (244526309998251 / 4000000000000) 2 (IntervalRat.scale (419 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-80998056978 / 1000000000000) (-80998008232 / 1000000000000), orderedInterval (62736203273 / 1000000000000) (62736252019 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (663936498787753 / 4000000000000) 2 (IntervalRat.scale (419 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-16181911095 / 1000000000000) (-16181911094 / 1000000000000), orderedInterval (-59730736901 / 1000000000000) (-59730736900 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (906548527417481 / 4000000000000) 2 (IntervalRat.scale (419 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (49903812757 / 1000000000000) (49903812758 / 1000000000000), orderedInterval (17738905403 / 1000000000000) (17738905404 / 1000000000000)))) (orderedInterval (4121579556 / 1000000000000) (4121579657 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (383323916299947 / 4000000000000) 2 (IntervalRat.scale (419 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (56989495378 / 1000000000000) (56989562954 / 1000000000000), orderedInterval (-58566978042 / 1000000000000) (-58566910466 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1558190438251787 / 4000000000000) 2 (IntervalRat.scale (419 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (28292358501 / 1000000000000) (28292358502 / 1000000000000), orderedInterval (28839221403 / 1000000000000) (28839221404 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1040798999875333 / 4000000000000) 2 (IntervalRat.scale (419 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-11395885870 / 1000000000000) (-11395885869 / 1000000000000), orderedInterval (-48111205911 / 1000000000000) (-48111205910 / 1000000000000)))) (orderedInterval (4560544162 / 1000000000000) (4560544369 / 1000000000000))) = true
  rfl'

theorem compactCertificate337_chunkChecks2 :
    compactCertificate337.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate337.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate337_chunkChecks2_0
    compactCertificate337_chunkChecks2_1 compactCertificate337_chunkChecks2_2

theorem compactCertificate337_chunkChecks3_0 :
    compactCertificate337.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (419 / 2) 3 (IntervalRat.scale (419 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (11054585948 / 1000000000000) (11054586010 / 1000000000000), orderedInterval (-54031586132 / 1000000000000) (-54031586070 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (617267007170519 / 4000000000000) 3 (IntervalRat.scale (419 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-58969832777 / 1000000000000) (-58969832776 / 1000000000000), orderedInterval (-25263861960 / 1000000000000) (-25263861959 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (199611467567927 / 800000000000) 3 (IntervalRat.scale (419 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-43256255416 / 1000000000000) (-43256213595 / 1000000000000), orderedInterval (26169821784 / 1000000000000) (26169863605 / 1000000000000)))) (orderedInterval (18917332313 / 1000000000000) (18917336523 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (180116973206533 / 4000000000000) 3 (IntervalRat.scale (419 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (114940535415 / 1000000000000) (114940536183 / 1000000000000), orderedInterval (-31703666692 / 1000000000000) (-31703665924 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (483819525580801 / 4000000000000) 3 (IntervalRat.scale (419 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (51169279958 / 1000000000000) (51169345298 / 1000000000000), orderedInterval (-51640962675 / 1000000000000) (-51640897336 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1313664128253117 / 4000000000000) 3 (IntervalRat.scale (419 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (27208621966 / 1000000000000) (27208630246 / 1000000000000), orderedInterval (-34655679512 / 1000000000000) (-34655671232 / 1000000000000)))) (orderedInterval (-9151187895 / 1000000000000) (-9151185098 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (967639051162021 / 4000000000000) 3 (IntervalRat.scale (419 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-36513246173 / 1000000000000) (-36513246172 / 1000000000000), orderedInterval (-35958186487 / 1000000000000) (-35958186486 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1658066007045433 / 4000000000000) 3 (IntervalRat.scale (419 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (22494275846 / 1000000000000) (22494275847 / 1000000000000), orderedInterval (32063687868 / 1000000000000) (32063687869 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1221323916299947 / 4000000000000) 3 (IntervalRat.scale (419 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-44846105163 / 1000000000000) (-44846105154 / 1000000000000), orderedInterval (-8519557991 / 1000000000000) (-8519557982 / 1000000000000)))) (orderedInterval (8273861039 / 1000000000000) (8273861107 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate337_chunkChecks3_1 :
    compactCertificate337.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1873824965144581 / 4000000000000) 3 (IntervalRat.scale (419 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-33558428927 / 1000000000000) (-33558428925 / 1000000000000), orderedInterval (-15222136226 / 1000000000000) (-15222136224 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1081853348040349 / 4000000000000) 3 (IntervalRat.scale (419 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (42588666243 / 1000000000000) (42588666244 / 1000000000000), orderedInterval (23159491390 / 1000000000000) (23159491391 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1919767750810241 / 4000000000000) 3 (IntervalRat.scale (419 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-2307490349 / 1000000000000) (-2307490348 / 1000000000000), orderedInterval (-36344918488 / 1000000000000) (-36344918487 / 1000000000000)))) (orderedInterval (28345210114 / 1000000000000) (28345210929 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1793696058529829 / 4000000000000) 3 (IntervalRat.scale (419 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (1454615893 / 1000000000000) (1454615894 / 1000000000000), orderedInterval (-37652220527 / 1000000000000) (-37652220525 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1280066144123957 / 4000000000000) 3 (IntervalRat.scale (419 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (15674238040 / 1000000000000) (15674238041 / 1000000000000), orderedInterval (41732594515 / 1000000000000) (41732594516 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1451458576742403 / 4000000000000) 3 (IntervalRat.scale (419 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-29309720069 / 1000000000000) (-29309699831 / 1000000000000), orderedInterval (29963086362 / 1000000000000) (29963106600 / 1000000000000)))) (orderedInterval (-19925278438 / 1000000000000) (-19925277790 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1210074839124307 / 4000000000000) 3 (IntervalRat.scale (419 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (45424834487 / 1000000000000) (45424835348 / 1000000000000), orderedInterval (-6476610885 / 1000000000000) (-6476610024 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1069137818254447 / 4000000000000) 3 (IntervalRat.scale (419 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-41939773225 / 1000000000000) (-41939773224 / 1000000000000), orderedInterval (-24878701027 / 1000000000000) (-24878701026 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (309877811378253 / 800000000000) 3 (IntervalRat.scale (419 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-40111316020 / 1000000000000) (-40111314495 / 1000000000000), orderedInterval (5935535211 / 1000000000000) (5935536736 / 1000000000000)))) (orderedInterval (-3684770551 / 1000000000000) (-3684770207 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate337_chunkChecks3_2 :
    compactCertificate337.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (857138334247991 / 4000000000000) 3 (IntervalRat.scale (419 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (54048163364 / 1000000000000) (54048163375 / 1000000000000), orderedInterval (6923438497 / 1000000000000) (6923438507 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (726605658489151 / 4000000000000) 3 (IntervalRat.scale (419 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (13135739025 / 1000000000000) (13135739026 / 1000000000000), orderedInterval (57688081247 / 1000000000000) (57688081248 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (454676083700053 / 4000000000000) 3 (IntervalRat.scale (419 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (73117065813 / 1000000000000) (73117065815 / 1000000000000), orderedInterval (15631122966 / 1000000000000) (15631122968 / 1000000000000)))) (orderedInterval (3189133883 / 1000000000000) (3189133931 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (244526309998251 / 4000000000000) 3 (IntervalRat.scale (419 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-80998056978 / 1000000000000) (-80998008232 / 1000000000000), orderedInterval (62736203273 / 1000000000000) (62736252019 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (663936498787753 / 4000000000000) 3 (IntervalRat.scale (419 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-16181911095 / 1000000000000) (-16181911094 / 1000000000000), orderedInterval (-59730736901 / 1000000000000) (-59730736900 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (906548527417481 / 4000000000000) 3 (IntervalRat.scale (419 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (49903812757 / 1000000000000) (49903812758 / 1000000000000), orderedInterval (17738905403 / 1000000000000) (17738905404 / 1000000000000)))) (orderedInterval (1056296816 / 1000000000000) (1056296862 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (383323916299947 / 4000000000000) 3 (IntervalRat.scale (419 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (56989495378 / 1000000000000) (56989562954 / 1000000000000), orderedInterval (-58566978042 / 1000000000000) (-58566910466 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1558190438251787 / 4000000000000) 3 (IntervalRat.scale (419 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (28292358501 / 1000000000000) (28292358502 / 1000000000000), orderedInterval (28839221403 / 1000000000000) (28839221404 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1040798999875333 / 4000000000000) 3 (IntervalRat.scale (419 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-11395885870 / 1000000000000) (-11395885869 / 1000000000000), orderedInterval (-48111205911 / 1000000000000) (-48111205910 / 1000000000000)))) (orderedInterval (-2190358930 / 1000000000000) (-2190358704 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate337_chunkChecks3 :
    compactCertificate337.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate337.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate337_chunkChecks3_0
    compactCertificate337_chunkChecks3_1 compactCertificate337_chunkChecks3_2

theorem compactCertificate337_chunkChecks4_0 :
    compactCertificate337.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (419 / 2) 4 (IntervalRat.scale (419 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (11054585948 / 1000000000000) (11054586010 / 1000000000000), orderedInterval (-54031586132 / 1000000000000) (-54031586070 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (617267007170519 / 4000000000000) 4 (IntervalRat.scale (419 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-58969832777 / 1000000000000) (-58969832776 / 1000000000000), orderedInterval (-25263861960 / 1000000000000) (-25263861959 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (199611467567927 / 800000000000) 4 (IntervalRat.scale (419 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-43256255416 / 1000000000000) (-43256213595 / 1000000000000), orderedInterval (26169821784 / 1000000000000) (26169863605 / 1000000000000)))) (orderedInterval (-1068034477 / 1000000000000) (-1068029449 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (180116973206533 / 4000000000000) 4 (IntervalRat.scale (419 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (114940535415 / 1000000000000) (114940536183 / 1000000000000), orderedInterval (-31703666692 / 1000000000000) (-31703665924 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (483819525580801 / 4000000000000) 4 (IntervalRat.scale (419 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (51169279958 / 1000000000000) (51169345298 / 1000000000000), orderedInterval (-51640962675 / 1000000000000) (-51640897336 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1313664128253117 / 4000000000000) 4 (IntervalRat.scale (419 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (27208621966 / 1000000000000) (27208630246 / 1000000000000), orderedInterval (-34655679512 / 1000000000000) (-34655671232 / 1000000000000)))) (orderedInterval (-11388463652 / 1000000000000) (-11388459714 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (967639051162021 / 4000000000000) 4 (IntervalRat.scale (419 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-36513246173 / 1000000000000) (-36513246172 / 1000000000000), orderedInterval (-35958186487 / 1000000000000) (-35958186486 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1658066007045433 / 4000000000000) 4 (IntervalRat.scale (419 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (22494275846 / 1000000000000) (22494275847 / 1000000000000), orderedInterval (32063687868 / 1000000000000) (32063687869 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1221323916299947 / 4000000000000) 4 (IntervalRat.scale (419 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-44846105163 / 1000000000000) (-44846105154 / 1000000000000), orderedInterval (-8519557991 / 1000000000000) (-8519557982 / 1000000000000)))) (orderedInterval (-15602365126 / 1000000000000) (-15602365001 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate337_chunkChecks4_1 :
    compactCertificate337.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1873824965144581 / 4000000000000) 4 (IntervalRat.scale (419 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-33558428927 / 1000000000000) (-33558428925 / 1000000000000), orderedInterval (-15222136226 / 1000000000000) (-15222136224 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1081853348040349 / 4000000000000) 4 (IntervalRat.scale (419 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (42588666243 / 1000000000000) (42588666244 / 1000000000000), orderedInterval (23159491390 / 1000000000000) (23159491391 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1919767750810241 / 4000000000000) 4 (IntervalRat.scale (419 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-2307490349 / 1000000000000) (-2307490348 / 1000000000000), orderedInterval (-36344918488 / 1000000000000) (-36344918487 / 1000000000000)))) (orderedInterval (148532123723 / 1000000000000) (148532125531 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1793696058529829 / 4000000000000) 4 (IntervalRat.scale (419 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (1454615893 / 1000000000000) (1454615894 / 1000000000000), orderedInterval (-37652220527 / 1000000000000) (-37652220525 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1280066144123957 / 4000000000000) 4 (IntervalRat.scale (419 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (15674238040 / 1000000000000) (15674238041 / 1000000000000), orderedInterval (41732594515 / 1000000000000) (41732594516 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1451458576742403 / 4000000000000) 4 (IntervalRat.scale (419 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-29309720069 / 1000000000000) (-29309699831 / 1000000000000), orderedInterval (29963086362 / 1000000000000) (29963106600 / 1000000000000)))) (orderedInterval (9043592977 / 1000000000000) (9043594103 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1210074839124307 / 4000000000000) 4 (IntervalRat.scale (419 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (45424834487 / 1000000000000) (45424835348 / 1000000000000), orderedInterval (-6476610885 / 1000000000000) (-6476610024 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1069137818254447 / 4000000000000) 4 (IntervalRat.scale (419 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-41939773225 / 1000000000000) (-41939773224 / 1000000000000), orderedInterval (-24878701027 / 1000000000000) (-24878701026 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (309877811378253 / 800000000000) 4 (IntervalRat.scale (419 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-40111316020 / 1000000000000) (-40111314495 / 1000000000000), orderedInterval (5935535211 / 1000000000000) (5935536736 / 1000000000000)))) (orderedInterval (-3326894884 / 1000000000000) (-3326894275 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate337_chunkChecks4_2 :
    compactCertificate337.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (857138334247991 / 4000000000000) 4 (IntervalRat.scale (419 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (54048163364 / 1000000000000) (54048163375 / 1000000000000), orderedInterval (6923438497 / 1000000000000) (6923438507 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (726605658489151 / 4000000000000) 4 (IntervalRat.scale (419 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (13135739025 / 1000000000000) (13135739026 / 1000000000000), orderedInterval (57688081247 / 1000000000000) (57688081248 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (454676083700053 / 4000000000000) 4 (IntervalRat.scale (419 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (73117065813 / 1000000000000) (73117065815 / 1000000000000), orderedInterval (15631122966 / 1000000000000) (15631122968 / 1000000000000)))) (orderedInterval (-9702996318 / 1000000000000) (-9702996271 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (244526309998251 / 4000000000000) 4 (IntervalRat.scale (419 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-80998056978 / 1000000000000) (-80998008232 / 1000000000000), orderedInterval (62736203273 / 1000000000000) (62736252019 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (663936498787753 / 4000000000000) 4 (IntervalRat.scale (419 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-16181911095 / 1000000000000) (-16181911094 / 1000000000000), orderedInterval (-59730736901 / 1000000000000) (-59730736900 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (906548527417481 / 4000000000000) 4 (IntervalRat.scale (419 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (49903812757 / 1000000000000) (49903812758 / 1000000000000), orderedInterval (17738905403 / 1000000000000) (17738905404 / 1000000000000)))) (orderedInterval (-5092557711 / 1000000000000) (-5092557679 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (383323916299947 / 4000000000000) 4 (IntervalRat.scale (419 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (56989495378 / 1000000000000) (56989562954 / 1000000000000), orderedInterval (-58566978042 / 1000000000000) (-58566910466 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1558190438251787 / 4000000000000) 4 (IntervalRat.scale (419 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (28292358501 / 1000000000000) (28292358502 / 1000000000000), orderedInterval (28839221403 / 1000000000000) (28839221404 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1040798999875333 / 4000000000000) 4 (IntervalRat.scale (419 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-11395885870 / 1000000000000) (-11395885869 / 1000000000000), orderedInterval (-48111205911 / 1000000000000) (-48111205910 / 1000000000000)))) (orderedInterval (-22406285642 / 1000000000000) (-22406285323 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate337_chunkChecks4 :
    compactCertificate337.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate337.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate337_chunkChecks4_0
    compactCertificate337_chunkChecks4_1 compactCertificate337_chunkChecks4_2

theorem compactCertificate337_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate337.chunkCheck r b = true :=
  compactCertificate337.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate337_chunkChecks0
    · exact compactCertificate337_chunkChecks1
    · exact compactCertificate337_chunkChecks2
    · exact compactCertificate337_chunkChecks3
    · exact compactCertificate337_chunkChecks4)

theorem compactCertificate337_coefficient0 :
    compactCertificate337.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate337_coefficient1 :
    compactCertificate337.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate337_coefficient2 :
    compactCertificate337.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate337_coefficient3 :
    compactCertificate337.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate337_coefficient4 :
    compactCertificate337.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate337_coefficients : ∀ r : Fin 5,
    compactCertificate337.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate337_coefficient0
  · exact compactCertificate337_coefficient1
  · exact compactCertificate337_coefficient2
  · exact compactCertificate337_coefficient3
  · exact compactCertificate337_coefficient4

theorem compactCertificate337_lower : (1 : ℚ) ≤ compactCertificate337.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate337, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate337_proves {t : ℝ} (ht : t ∈ compactCertificate337.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate337.proves compactCertificate337_states compactCertificate337_chunks
    compactCertificate337_coefficients compactCertificate337_lower ht

end Erdos232
