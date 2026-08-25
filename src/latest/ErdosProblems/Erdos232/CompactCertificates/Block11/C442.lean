/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate442 : CompactCertificate where
  left := 313
  right := 314
  center := 627 / 2
  grid := fun i =>
    match i.val with
    | 0 => 100
    | 1 => 74
    | 2 => 119
    | 3 => 21
    | 4 => 58
    | 5 => 157
    | 6 => 115
    | 7 => 198
    | 8 => 146
    | 9 => 223
    | 10 => 129
    | 11 => 229
    | 12 => 214
    | 13 => 153
    | 14 => 173
    | 15 => 144
    | 16 => 127
    | 17 => 185
    | 18 => 102
    | 19 => 87
    | 20 => 54
    | 21 => 29
    | 22 => 79
    | 23 => 108
    | 24 => 46
    | 25 => 186
    | _ => 124
  point := fun i =>
    match i.val with
    | 0 => 627 / 2
    | 1 => 923690724333927 / 4000000000000
    | 2 => 298702601825991 / 800000000000
    | 3 => 269530649643189 / 4000000000000
    | 4 => 723997237563633 / 4000000000000
    | 5 => 1965793337505261 / 4000000000000
    | 6 => 1447994475127893 / 4000000000000
    | 7 => 2481163213406889 / 4000000000000
    | 8 => 1827613593126651 / 4000000000000
    | 9 => 2804029243784373 / 4000000000000
    | 10 => 1618907038714317 / 4000000000000
    | 11 => 2872778949303153 / 4000000000000
    | 12 => 2684122741523157 / 4000000000000
    | 13 => 1915516640490981 / 4000000000000
    | 14 => 2171991712690899 / 4000000000000
    | 15 => 1810780248522531 / 4000000000000
    | 16 => 1599879265025151 / 4000000000000
    | 17 => 463707369293949 / 800000000000
    | 18 => 1282638987048903 / 4000000000000
    | 19 => 1087307274159183 / 4000000000000
    | 20 => 680386406873349 / 4000000000000
    | 21 => 365914072479483 / 4000000000000
    | 22 => 993527887207449 / 4000000000000
    | 23 => 1356577390670073 / 4000000000000
    | 24 => 573613593126651 / 4000000000000
    | 25 => 2331707409985371 / 4000000000000
    | _ => 1557472489073589 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (5651049715 / 1000000000000) (5651049716 / 1000000000000), orderedInterval (44698405113 / 1000000000000) (44698405114 / 1000000000000))
    | 1 => (orderedInterval (-36563069480 / 1000000000000) (-36563033592 / 1000000000000), orderedInterval (37761981533 / 1000000000000) (37762017421 / 1000000000000))
    | 2 => (orderedInterval (-12745406598 / 1000000000000) (-12745406597 / 1000000000000), orderedInterval (-39258653022 / 1000000000000) (-39258653021 / 1000000000000))
    | 3 => (orderedInterval (-78996811343 / 1000000000000) (-78996773681 / 1000000000000), orderedInterval (57218721331 / 1000000000000) (57218758993 / 1000000000000))
    | 4 => (orderedInterval (-24634456665 / 1000000000000) (-24634455252 / 1000000000000), orderedInterval (54016192669 / 1000000000000) (54016194083 / 1000000000000))
    | 5 => (orderedInterval (30218925341 / 1000000000000) (30219007355 / 1000000000000), orderedInterval (-19580947160 / 1000000000000) (-19580865147 / 1000000000000))
    | 6 => (orderedInterval (-41832417949 / 1000000000000) (-41832417868 / 1000000000000), orderedInterval (-2887049147 / 1000000000000) (-2887049066 / 1000000000000))
    | 7 => (orderedInterval (-26231848444 / 1000000000000) (-26231815105 / 1000000000000), orderedInterval (18411765788 / 1000000000000) (18411799128 / 1000000000000))
    | 8 => (orderedInterval (-31083363466 / 1000000000000) (-31083277949 / 1000000000000), orderedInterval (20701878380 / 1000000000000) (20701963897 / 1000000000000))
    | 9 => (orderedInterval (-28272906285 / 1000000000000) (-28272906270 / 1000000000000), orderedInterval (-10410201815 / 1000000000000) (-10410201800 / 1000000000000))
    | 10 => (orderedInterval (-9673651267 / 1000000000000) (-9673651266 / 1000000000000), orderedInterval (-38450802944 / 1000000000000) (-38450802943 / 1000000000000))
    | 11 => (orderedInterval (12809362069 / 1000000000000) (12809362119 / 1000000000000), orderedInterval (-26885246147 / 1000000000000) (-26885246097 / 1000000000000))
    | 12 => (orderedInterval (-14357924806 / 1000000000000) (-14357924681 / 1000000000000), orderedInterval (27260826071 / 1000000000000) (27260826195 / 1000000000000))
    | 13 => (orderedInterval (30668469976 / 1000000000000) (30668558610 / 1000000000000), orderedInterval (-19751022177 / 1000000000000) (-19750933543 / 1000000000000))
    | 14 => (orderedInterval (-9711309307 / 1000000000000) (-9711309306 / 1000000000000), orderedInterval (-32825604534 / 1000000000000) (-32825604533 / 1000000000000))
    | 15 => (orderedInterval (33263544310 / 1000000000000) (33263544312 / 1000000000000), orderedInterval (17278699780 / 1000000000000) (17278699781 / 1000000000000))
    | 16 => (orderedInterval (-39085822401 / 1000000000000) (-39085819324 / 1000000000000), orderedInterval (8046796380 / 1000000000000) (8046799457 / 1000000000000))
    | 17 => (orderedInterval (23194988620 / 1000000000000) (23194995498 / 1000000000000), orderedInterval (-23690780926 / 1000000000000) (-23690774047 / 1000000000000))
    | 18 => (orderedInterval (37548941885 / 1000000000000) (37548941886 / 1000000000000), orderedInterval (23929354615 / 1000000000000) (23929354616 / 1000000000000))
    | 19 => (orderedInterval (31427527022 / 1000000000000) (31427543406 / 1000000000000), orderedInterval (-36858843568 / 1000000000000) (-36858827185 / 1000000000000))
    | 20 => (orderedInterval (57765844878 / 1000000000000) (57765844879 / 1000000000000), orderedInterval (19974426461 / 1000000000000) (19974426462 / 1000000000000))
    | 21 => (orderedInterval (-76359293369 / 1000000000000) (-76359293368 / 1000000000000), orderedInterval (-33174540670 / 1000000000000) (-33174540669 / 1000000000000))
    | 22 => (orderedInterval (-42074842783 / 1000000000000) (-42074842782 / 1000000000000), orderedInterval (-28071530499 / 1000000000000) (-28071530498 / 1000000000000))
    | 23 => (orderedInterval (25782563921 / 1000000000000) (25782563922 / 1000000000000), orderedInterval (34781453735 / 1000000000000) (34781453736 / 1000000000000))
    | 24 => (orderedInterval (-21296309741 / 1000000000000) (-21296309228 / 1000000000000), orderedInterval (63207855508 / 1000000000000) (63207856022 / 1000000000000))
    | 25 => (orderedInterval (-19314233336 / 1000000000000) (-19314232041 / 1000000000000), orderedInterval (26832041531 / 1000000000000) (26832042826 / 1000000000000))
    | _ => (orderedInterval (22688069787 / 1000000000000) (22688069788 / 1000000000000), orderedInterval (33441142197 / 1000000000000) (33441142198 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (1151266405 / 1000000000000) (1151266763 / 1000000000000)
      | 1 => orderedInterval (-2190646442 / 1000000000000) (-2190640114 / 1000000000000)
      | 2 => orderedInterval (57870555 / 1000000000000) (57873668 / 1000000000000)
      | 3 => orderedInterval (6127942351 / 1000000000000) (6127942486 / 1000000000000)
      | 4 => orderedInterval (3208448066 / 1000000000000) (3208456487 / 1000000000000)
      | 5 => orderedInterval (3214751304 / 1000000000000) (3214751687 / 1000000000000)
      | 6 => orderedInterval (-5902006892 / 1000000000000) (-5902005885 / 1000000000000)
      | 7 => orderedInterval (388582854 / 1000000000000) (388582892 / 1000000000000)
      | _ => orderedInterval (-2813052113 / 1000000000000) (-2813051917 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (15232312181 / 1000000000000) (15232312453 / 1000000000000)
      | 1 => orderedInterval (3187355297 / 1000000000000) (3187364597 / 1000000000000)
      | 2 => orderedInterval (-394448545 / 1000000000000) (-394443467 / 1000000000000)
      | 3 => orderedInterval (-8297246177 / 1000000000000) (-8297245897 / 1000000000000)
      | 4 => orderedInterval (-3618661823 / 1000000000000) (-3618648955 / 1000000000000)
      | 5 => orderedInterval (-1420893745 / 1000000000000) (-1420893150 / 1000000000000)
      | 6 => orderedInterval (-1751793106 / 1000000000000) (-1751792229 / 1000000000000)
      | 7 => orderedInterval (-2200339940 / 1000000000000) (-2200339905 / 1000000000000)
      | _ => orderedInterval (-11679878002 / 1000000000000) (-11679877682 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-1042711713 / 1000000000000) (-1042711501 / 1000000000000)
      | 1 => orderedInterval (5529228402 / 1000000000000) (5529242855 / 1000000000000)
      | 2 => orderedInterval (-1570566518 / 1000000000000) (-1570558031 / 1000000000000)
      | 3 => orderedInterval (-33454303648 / 1000000000000) (-33454303045 / 1000000000000)
      | 4 => orderedInterval (-8090360068 / 1000000000000) (-8090340360 / 1000000000000)
      | 5 => orderedInterval (-6467387371 / 1000000000000) (-6467386415 / 1000000000000)
      | 6 => orderedInterval (7070447255 / 1000000000000) (7070448024 / 1000000000000)
      | 7 => orderedInterval (1600211636 / 1000000000000) (1600211670 / 1000000000000)
      | _ => orderedInterval (1194860620 / 1000000000000) (1194861166 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-13962068841 / 1000000000000) (-13962068673 / 1000000000000)
      | 1 => orderedInterval (-5753417556 / 1000000000000) (-5753394947 / 1000000000000)
      | 2 => orderedInterval (2854995670 / 1000000000000) (2855010160 / 1000000000000)
      | 3 => orderedInterval (31506214147 / 1000000000000) (31506215472 / 1000000000000)
      | 4 => orderedInterval (10645720713 / 1000000000000) (10645750841 / 1000000000000)
      | 5 => orderedInterval (4209989099 / 1000000000000) (4209990681 / 1000000000000)
      | 6 => orderedInterval (2607916067 / 1000000000000) (2607916742 / 1000000000000)
      | 7 => orderedInterval (3037646000 / 1000000000000) (3037646035 / 1000000000000)
      | _ => orderedInterval (26022308794 / 1000000000000) (26022309752 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (723776159 / 1000000000000) (723776298 / 1000000000000)
      | 1 => orderedInterval (-13034569682 / 1000000000000) (-13034534186 / 1000000000000)
      | 2 => orderedInterval (8992663168 / 1000000000000) (8992688527 / 1000000000000)
      | 3 => orderedInterval (173556208420 / 1000000000000) (173556211369 / 1000000000000)
      | 4 => orderedInterval (21604526511 / 1000000000000) (21604572676 / 1000000000000)
      | 5 => orderedInterval (14509472399 / 1000000000000) (14509475091 / 1000000000000)
      | 6 => orderedInterval (-7430333906 / 1000000000000) (-7430333311 / 1000000000000)
      | 7 => orderedInterval (-2339241512 / 1000000000000) (-2339241475 / 1000000000000)
      | _ => orderedInterval (8492913675 / 1000000000000) (8492915387 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (3243156088 / 1000000000000) (3243176067 / 1000000000000)
    | 1 => orderedInterval (-10943593860 / 1000000000000) (-10943564235 / 1000000000000)
    | 2 => orderedInterval (-35230581405 / 1000000000000) (-35230535637 / 1000000000000)
    | 3 => orderedInterval (61169304093 / 1000000000000) (61169376063 / 1000000000000)
    | _ => orderedInterval (205075415232 / 1000000000000) (205075530376 / 1000000000000)

theorem compactCertificate442_stateChecks0 :
    compactCertificate442.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 100 12 (627 / 2)) (orderedInterval (5651049715 / 1000000000000) (5651049716 / 1000000000000), orderedInterval (44698405113 / 1000000000000) (44698405114 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (923690724333927 / 4000000000000)) (orderedInterval (-36563069480 / 1000000000000) (-36563033592 / 1000000000000), orderedInterval (37761981533 / 1000000000000) (37762017421 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 119 12 (298702601825991 / 800000000000)) (orderedInterval (-12745406598 / 1000000000000) (-12745406597 / 1000000000000), orderedInterval (-39258653022 / 1000000000000) (-39258653021 / 1000000000000))) = true
  rfl'

theorem compactCertificate442_stateChecks1 :
    compactCertificate442.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 21 12 (269530649643189 / 4000000000000)) (orderedInterval (-78996811343 / 1000000000000) (-78996773681 / 1000000000000), orderedInterval (57218721331 / 1000000000000) (57218758993 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (723997237563633 / 4000000000000)) (orderedInterval (-24634456665 / 1000000000000) (-24634455252 / 1000000000000), orderedInterval (54016192669 / 1000000000000) (54016194083 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 157 12 (1965793337505261 / 4000000000000)) (orderedInterval (30218925341 / 1000000000000) (30219007355 / 1000000000000), orderedInterval (-19580947160 / 1000000000000) (-19580865147 / 1000000000000))) = true
  rfl'

theorem compactCertificate442_stateChecks2 :
    compactCertificate442.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 115 12 (1447994475127893 / 4000000000000)) (orderedInterval (-41832417949 / 1000000000000) (-41832417868 / 1000000000000), orderedInterval (-2887049147 / 1000000000000) (-2887049066 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 198 12 (2481163213406889 / 4000000000000)) (orderedInterval (-26231848444 / 1000000000000) (-26231815105 / 1000000000000), orderedInterval (18411765788 / 1000000000000) (18411799128 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 146 12 (1827613593126651 / 4000000000000)) (orderedInterval (-31083363466 / 1000000000000) (-31083277949 / 1000000000000), orderedInterval (20701878380 / 1000000000000) (20701963897 / 1000000000000))) = true
  rfl'

theorem compactCertificate442_stateChecks3 :
    compactCertificate442.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 223 12 (2804029243784373 / 4000000000000)) (orderedInterval (-28272906285 / 1000000000000) (-28272906270 / 1000000000000), orderedInterval (-10410201815 / 1000000000000) (-10410201800 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 129 12 (1618907038714317 / 4000000000000)) (orderedInterval (-9673651267 / 1000000000000) (-9673651266 / 1000000000000), orderedInterval (-38450802944 / 1000000000000) (-38450802943 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 229 12 (2872778949303153 / 4000000000000)) (orderedInterval (12809362069 / 1000000000000) (12809362119 / 1000000000000), orderedInterval (-26885246147 / 1000000000000) (-26885246097 / 1000000000000))) = true
  rfl'

theorem compactCertificate442_stateChecks4 :
    compactCertificate442.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 214 12 (2684122741523157 / 4000000000000)) (orderedInterval (-14357924806 / 1000000000000) (-14357924681 / 1000000000000), orderedInterval (27260826071 / 1000000000000) (27260826195 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 153 12 (1915516640490981 / 4000000000000)) (orderedInterval (30668469976 / 1000000000000) (30668558610 / 1000000000000), orderedInterval (-19751022177 / 1000000000000) (-19750933543 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 173 12 (2171991712690899 / 4000000000000)) (orderedInterval (-9711309307 / 1000000000000) (-9711309306 / 1000000000000), orderedInterval (-32825604534 / 1000000000000) (-32825604533 / 1000000000000))) = true
  rfl'

theorem compactCertificate442_stateChecks5 :
    compactCertificate442.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 144 12 (1810780248522531 / 4000000000000)) (orderedInterval (33263544310 / 1000000000000) (33263544312 / 1000000000000), orderedInterval (17278699780 / 1000000000000) (17278699781 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 127 12 (1599879265025151 / 4000000000000)) (orderedInterval (-39085822401 / 1000000000000) (-39085819324 / 1000000000000), orderedInterval (8046796380 / 1000000000000) (8046799457 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 185 12 (463707369293949 / 800000000000)) (orderedInterval (23194988620 / 1000000000000) (23194995498 / 1000000000000), orderedInterval (-23690780926 / 1000000000000) (-23690774047 / 1000000000000))) = true
  rfl'

theorem compactCertificate442_stateChecks6 :
    compactCertificate442.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 102 12 (1282638987048903 / 4000000000000)) (orderedInterval (37548941885 / 1000000000000) (37548941886 / 1000000000000), orderedInterval (23929354615 / 1000000000000) (23929354616 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (1087307274159183 / 4000000000000)) (orderedInterval (31427527022 / 1000000000000) (31427543406 / 1000000000000), orderedInterval (-36858843568 / 1000000000000) (-36858827185 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (680386406873349 / 4000000000000)) (orderedInterval (57765844878 / 1000000000000) (57765844879 / 1000000000000), orderedInterval (19974426461 / 1000000000000) (19974426462 / 1000000000000))) = true
  rfl'

theorem compactCertificate442_stateChecks7 :
    compactCertificate442.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (365914072479483 / 4000000000000)) (orderedInterval (-76359293369 / 1000000000000) (-76359293368 / 1000000000000), orderedInterval (-33174540670 / 1000000000000) (-33174540669 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (993527887207449 / 4000000000000)) (orderedInterval (-42074842783 / 1000000000000) (-42074842782 / 1000000000000), orderedInterval (-28071530499 / 1000000000000) (-28071530498 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 108 12 (1356577390670073 / 4000000000000)) (orderedInterval (25782563921 / 1000000000000) (25782563922 / 1000000000000), orderedInterval (34781453735 / 1000000000000) (34781453736 / 1000000000000))) = true
  rfl'

theorem compactCertificate442_stateChecks8 :
    compactCertificate442.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (573613593126651 / 4000000000000)) (orderedInterval (-21296309741 / 1000000000000) (-21296309228 / 1000000000000), orderedInterval (63207855508 / 1000000000000) (63207856022 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 186 12 (2331707409985371 / 4000000000000)) (orderedInterval (-19314233336 / 1000000000000) (-19314232041 / 1000000000000), orderedInterval (26832041531 / 1000000000000) (26832042826 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 124 12 (1557472489073589 / 4000000000000)) (orderedInterval (22688069787 / 1000000000000) (22688069788 / 1000000000000), orderedInterval (33441142197 / 1000000000000) (33441142198 / 1000000000000))) = true
  rfl'

theorem compactCertificate442_states : ∀ j,
    BesselStateValid (compactCertificate442.point j) (compactCertificate442.state j) :=
  compactCertificate442.statesValid_of_checks3 compactCertificate442_stateChecks0
    compactCertificate442_stateChecks1 compactCertificate442_stateChecks2
    compactCertificate442_stateChecks3 compactCertificate442_stateChecks4
    compactCertificate442_stateChecks5 compactCertificate442_stateChecks6
    compactCertificate442_stateChecks7 compactCertificate442_stateChecks8

theorem compactCertificate442_chunkChecks0_0 :
    compactCertificate442.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (627 / 2) 0 (IntervalRat.scale (627 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (5651049715 / 1000000000000) (5651049716 / 1000000000000), orderedInterval (44698405113 / 1000000000000) (44698405114 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (923690724333927 / 4000000000000) 0 (IntervalRat.scale (627 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-36563069480 / 1000000000000) (-36563033592 / 1000000000000), orderedInterval (37761981533 / 1000000000000) (37762017421 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (298702601825991 / 800000000000) 0 (IntervalRat.scale (627 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-12745406598 / 1000000000000) (-12745406597 / 1000000000000), orderedInterval (-39258653022 / 1000000000000) (-39258653021 / 1000000000000)))) (orderedInterval (1151266405 / 1000000000000) (1151266763 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (269530649643189 / 4000000000000) 0 (IntervalRat.scale (627 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-78996811343 / 1000000000000) (-78996773681 / 1000000000000), orderedInterval (57218721331 / 1000000000000) (57218758993 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (723997237563633 / 4000000000000) 0 (IntervalRat.scale (627 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-24634456665 / 1000000000000) (-24634455252 / 1000000000000), orderedInterval (54016192669 / 1000000000000) (54016194083 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1965793337505261 / 4000000000000) 0 (IntervalRat.scale (627 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30218925341 / 1000000000000) (30219007355 / 1000000000000), orderedInterval (-19580947160 / 1000000000000) (-19580865147 / 1000000000000)))) (orderedInterval (-2190646442 / 1000000000000) (-2190640114 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1447994475127893 / 4000000000000) 0 (IntervalRat.scale (627 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-41832417949 / 1000000000000) (-41832417868 / 1000000000000), orderedInterval (-2887049147 / 1000000000000) (-2887049066 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2481163213406889 / 4000000000000) 0 (IntervalRat.scale (627 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-26231848444 / 1000000000000) (-26231815105 / 1000000000000), orderedInterval (18411765788 / 1000000000000) (18411799128 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1827613593126651 / 4000000000000) 0 (IntervalRat.scale (627 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-31083363466 / 1000000000000) (-31083277949 / 1000000000000), orderedInterval (20701878380 / 1000000000000) (20701963897 / 1000000000000)))) (orderedInterval (57870555 / 1000000000000) (57873668 / 1000000000000))) = true
  rfl'

theorem compactCertificate442_chunkChecks0_1 :
    compactCertificate442.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2804029243784373 / 4000000000000) 0 (IntervalRat.scale (627 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-28272906285 / 1000000000000) (-28272906270 / 1000000000000), orderedInterval (-10410201815 / 1000000000000) (-10410201800 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1618907038714317 / 4000000000000) 0 (IntervalRat.scale (627 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-9673651267 / 1000000000000) (-9673651266 / 1000000000000), orderedInterval (-38450802944 / 1000000000000) (-38450802943 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2872778949303153 / 4000000000000) 0 (IntervalRat.scale (627 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (12809362069 / 1000000000000) (12809362119 / 1000000000000), orderedInterval (-26885246147 / 1000000000000) (-26885246097 / 1000000000000)))) (orderedInterval (6127942351 / 1000000000000) (6127942486 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2684122741523157 / 4000000000000) 0 (IntervalRat.scale (627 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-14357924806 / 1000000000000) (-14357924681 / 1000000000000), orderedInterval (27260826071 / 1000000000000) (27260826195 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1915516640490981 / 4000000000000) 0 (IntervalRat.scale (627 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (30668469976 / 1000000000000) (30668558610 / 1000000000000), orderedInterval (-19751022177 / 1000000000000) (-19750933543 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2171991712690899 / 4000000000000) 0 (IntervalRat.scale (627 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-9711309307 / 1000000000000) (-9711309306 / 1000000000000), orderedInterval (-32825604534 / 1000000000000) (-32825604533 / 1000000000000)))) (orderedInterval (3208448066 / 1000000000000) (3208456487 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1810780248522531 / 4000000000000) 0 (IntervalRat.scale (627 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (33263544310 / 1000000000000) (33263544312 / 1000000000000), orderedInterval (17278699780 / 1000000000000) (17278699781 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1599879265025151 / 4000000000000) 0 (IntervalRat.scale (627 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-39085822401 / 1000000000000) (-39085819324 / 1000000000000), orderedInterval (8046796380 / 1000000000000) (8046799457 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (463707369293949 / 800000000000) 0 (IntervalRat.scale (627 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (23194988620 / 1000000000000) (23194995498 / 1000000000000), orderedInterval (-23690780926 / 1000000000000) (-23690774047 / 1000000000000)))) (orderedInterval (3214751304 / 1000000000000) (3214751687 / 1000000000000))) = true
  rfl'

theorem compactCertificate442_chunkChecks0_2 :
    compactCertificate442.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1282638987048903 / 4000000000000) 0 (IntervalRat.scale (627 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (37548941885 / 1000000000000) (37548941886 / 1000000000000), orderedInterval (23929354615 / 1000000000000) (23929354616 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1087307274159183 / 4000000000000) 0 (IntervalRat.scale (627 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (31427527022 / 1000000000000) (31427543406 / 1000000000000), orderedInterval (-36858843568 / 1000000000000) (-36858827185 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (680386406873349 / 4000000000000) 0 (IntervalRat.scale (627 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (57765844878 / 1000000000000) (57765844879 / 1000000000000), orderedInterval (19974426461 / 1000000000000) (19974426462 / 1000000000000)))) (orderedInterval (-5902006892 / 1000000000000) (-5902005885 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (365914072479483 / 4000000000000) 0 (IntervalRat.scale (627 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-76359293369 / 1000000000000) (-76359293368 / 1000000000000), orderedInterval (-33174540670 / 1000000000000) (-33174540669 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (993527887207449 / 4000000000000) 0 (IntervalRat.scale (627 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-42074842783 / 1000000000000) (-42074842782 / 1000000000000), orderedInterval (-28071530499 / 1000000000000) (-28071530498 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1356577390670073 / 4000000000000) 0 (IntervalRat.scale (627 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (25782563921 / 1000000000000) (25782563922 / 1000000000000), orderedInterval (34781453735 / 1000000000000) (34781453736 / 1000000000000)))) (orderedInterval (388582854 / 1000000000000) (388582892 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (573613593126651 / 4000000000000) 0 (IntervalRat.scale (627 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-21296309741 / 1000000000000) (-21296309228 / 1000000000000), orderedInterval (63207855508 / 1000000000000) (63207856022 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2331707409985371 / 4000000000000) 0 (IntervalRat.scale (627 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-19314233336 / 1000000000000) (-19314232041 / 1000000000000), orderedInterval (26832041531 / 1000000000000) (26832042826 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1557472489073589 / 4000000000000) 0 (IntervalRat.scale (627 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (22688069787 / 1000000000000) (22688069788 / 1000000000000), orderedInterval (33441142197 / 1000000000000) (33441142198 / 1000000000000)))) (orderedInterval (-2813052113 / 1000000000000) (-2813051917 / 1000000000000))) = true
  rfl'

theorem compactCertificate442_chunkChecks0 :
    compactCertificate442.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate442.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate442_chunkChecks0_0
    compactCertificate442_chunkChecks0_1 compactCertificate442_chunkChecks0_2

theorem compactCertificate442_chunkChecks1_0 :
    compactCertificate442.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (627 / 2) 1 (IntervalRat.scale (627 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (5651049715 / 1000000000000) (5651049716 / 1000000000000), orderedInterval (44698405113 / 1000000000000) (44698405114 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (923690724333927 / 4000000000000) 1 (IntervalRat.scale (627 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-36563069480 / 1000000000000) (-36563033592 / 1000000000000), orderedInterval (37761981533 / 1000000000000) (37762017421 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (298702601825991 / 800000000000) 1 (IntervalRat.scale (627 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-12745406598 / 1000000000000) (-12745406597 / 1000000000000), orderedInterval (-39258653022 / 1000000000000) (-39258653021 / 1000000000000)))) (orderedInterval (15232312181 / 1000000000000) (15232312453 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (269530649643189 / 4000000000000) 1 (IntervalRat.scale (627 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-78996811343 / 1000000000000) (-78996773681 / 1000000000000), orderedInterval (57218721331 / 1000000000000) (57218758993 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (723997237563633 / 4000000000000) 1 (IntervalRat.scale (627 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-24634456665 / 1000000000000) (-24634455252 / 1000000000000), orderedInterval (54016192669 / 1000000000000) (54016194083 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1965793337505261 / 4000000000000) 1 (IntervalRat.scale (627 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30218925341 / 1000000000000) (30219007355 / 1000000000000), orderedInterval (-19580947160 / 1000000000000) (-19580865147 / 1000000000000)))) (orderedInterval (3187355297 / 1000000000000) (3187364597 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1447994475127893 / 4000000000000) 1 (IntervalRat.scale (627 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-41832417949 / 1000000000000) (-41832417868 / 1000000000000), orderedInterval (-2887049147 / 1000000000000) (-2887049066 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2481163213406889 / 4000000000000) 1 (IntervalRat.scale (627 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-26231848444 / 1000000000000) (-26231815105 / 1000000000000), orderedInterval (18411765788 / 1000000000000) (18411799128 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1827613593126651 / 4000000000000) 1 (IntervalRat.scale (627 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-31083363466 / 1000000000000) (-31083277949 / 1000000000000), orderedInterval (20701878380 / 1000000000000) (20701963897 / 1000000000000)))) (orderedInterval (-394448545 / 1000000000000) (-394443467 / 1000000000000))) = true
  rfl'

theorem compactCertificate442_chunkChecks1_1 :
    compactCertificate442.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2804029243784373 / 4000000000000) 1 (IntervalRat.scale (627 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-28272906285 / 1000000000000) (-28272906270 / 1000000000000), orderedInterval (-10410201815 / 1000000000000) (-10410201800 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1618907038714317 / 4000000000000) 1 (IntervalRat.scale (627 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-9673651267 / 1000000000000) (-9673651266 / 1000000000000), orderedInterval (-38450802944 / 1000000000000) (-38450802943 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2872778949303153 / 4000000000000) 1 (IntervalRat.scale (627 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (12809362069 / 1000000000000) (12809362119 / 1000000000000), orderedInterval (-26885246147 / 1000000000000) (-26885246097 / 1000000000000)))) (orderedInterval (-8297246177 / 1000000000000) (-8297245897 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2684122741523157 / 4000000000000) 1 (IntervalRat.scale (627 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-14357924806 / 1000000000000) (-14357924681 / 1000000000000), orderedInterval (27260826071 / 1000000000000) (27260826195 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1915516640490981 / 4000000000000) 1 (IntervalRat.scale (627 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (30668469976 / 1000000000000) (30668558610 / 1000000000000), orderedInterval (-19751022177 / 1000000000000) (-19750933543 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2171991712690899 / 4000000000000) 1 (IntervalRat.scale (627 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-9711309307 / 1000000000000) (-9711309306 / 1000000000000), orderedInterval (-32825604534 / 1000000000000) (-32825604533 / 1000000000000)))) (orderedInterval (-3618661823 / 1000000000000) (-3618648955 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1810780248522531 / 4000000000000) 1 (IntervalRat.scale (627 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (33263544310 / 1000000000000) (33263544312 / 1000000000000), orderedInterval (17278699780 / 1000000000000) (17278699781 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1599879265025151 / 4000000000000) 1 (IntervalRat.scale (627 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-39085822401 / 1000000000000) (-39085819324 / 1000000000000), orderedInterval (8046796380 / 1000000000000) (8046799457 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (463707369293949 / 800000000000) 1 (IntervalRat.scale (627 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (23194988620 / 1000000000000) (23194995498 / 1000000000000), orderedInterval (-23690780926 / 1000000000000) (-23690774047 / 1000000000000)))) (orderedInterval (-1420893745 / 1000000000000) (-1420893150 / 1000000000000))) = true
  rfl'

theorem compactCertificate442_chunkChecks1_2 :
    compactCertificate442.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1282638987048903 / 4000000000000) 1 (IntervalRat.scale (627 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (37548941885 / 1000000000000) (37548941886 / 1000000000000), orderedInterval (23929354615 / 1000000000000) (23929354616 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1087307274159183 / 4000000000000) 1 (IntervalRat.scale (627 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (31427527022 / 1000000000000) (31427543406 / 1000000000000), orderedInterval (-36858843568 / 1000000000000) (-36858827185 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (680386406873349 / 4000000000000) 1 (IntervalRat.scale (627 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (57765844878 / 1000000000000) (57765844879 / 1000000000000), orderedInterval (19974426461 / 1000000000000) (19974426462 / 1000000000000)))) (orderedInterval (-1751793106 / 1000000000000) (-1751792229 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (365914072479483 / 4000000000000) 1 (IntervalRat.scale (627 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-76359293369 / 1000000000000) (-76359293368 / 1000000000000), orderedInterval (-33174540670 / 1000000000000) (-33174540669 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (993527887207449 / 4000000000000) 1 (IntervalRat.scale (627 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-42074842783 / 1000000000000) (-42074842782 / 1000000000000), orderedInterval (-28071530499 / 1000000000000) (-28071530498 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1356577390670073 / 4000000000000) 1 (IntervalRat.scale (627 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (25782563921 / 1000000000000) (25782563922 / 1000000000000), orderedInterval (34781453735 / 1000000000000) (34781453736 / 1000000000000)))) (orderedInterval (-2200339940 / 1000000000000) (-2200339905 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (573613593126651 / 4000000000000) 1 (IntervalRat.scale (627 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-21296309741 / 1000000000000) (-21296309228 / 1000000000000), orderedInterval (63207855508 / 1000000000000) (63207856022 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2331707409985371 / 4000000000000) 1 (IntervalRat.scale (627 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-19314233336 / 1000000000000) (-19314232041 / 1000000000000), orderedInterval (26832041531 / 1000000000000) (26832042826 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1557472489073589 / 4000000000000) 1 (IntervalRat.scale (627 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (22688069787 / 1000000000000) (22688069788 / 1000000000000), orderedInterval (33441142197 / 1000000000000) (33441142198 / 1000000000000)))) (orderedInterval (-11679878002 / 1000000000000) (-11679877682 / 1000000000000))) = true
  rfl'

theorem compactCertificate442_chunkChecks1 :
    compactCertificate442.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate442.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate442_chunkChecks1_0
    compactCertificate442_chunkChecks1_1 compactCertificate442_chunkChecks1_2

theorem compactCertificate442_chunkChecks2_0 :
    compactCertificate442.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (627 / 2) 2 (IntervalRat.scale (627 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (5651049715 / 1000000000000) (5651049716 / 1000000000000), orderedInterval (44698405113 / 1000000000000) (44698405114 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (923690724333927 / 4000000000000) 2 (IntervalRat.scale (627 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-36563069480 / 1000000000000) (-36563033592 / 1000000000000), orderedInterval (37761981533 / 1000000000000) (37762017421 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (298702601825991 / 800000000000) 2 (IntervalRat.scale (627 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-12745406598 / 1000000000000) (-12745406597 / 1000000000000), orderedInterval (-39258653022 / 1000000000000) (-39258653021 / 1000000000000)))) (orderedInterval (-1042711713 / 1000000000000) (-1042711501 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (269530649643189 / 4000000000000) 2 (IntervalRat.scale (627 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-78996811343 / 1000000000000) (-78996773681 / 1000000000000), orderedInterval (57218721331 / 1000000000000) (57218758993 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (723997237563633 / 4000000000000) 2 (IntervalRat.scale (627 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-24634456665 / 1000000000000) (-24634455252 / 1000000000000), orderedInterval (54016192669 / 1000000000000) (54016194083 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1965793337505261 / 4000000000000) 2 (IntervalRat.scale (627 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30218925341 / 1000000000000) (30219007355 / 1000000000000), orderedInterval (-19580947160 / 1000000000000) (-19580865147 / 1000000000000)))) (orderedInterval (5529228402 / 1000000000000) (5529242855 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1447994475127893 / 4000000000000) 2 (IntervalRat.scale (627 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-41832417949 / 1000000000000) (-41832417868 / 1000000000000), orderedInterval (-2887049147 / 1000000000000) (-2887049066 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2481163213406889 / 4000000000000) 2 (IntervalRat.scale (627 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-26231848444 / 1000000000000) (-26231815105 / 1000000000000), orderedInterval (18411765788 / 1000000000000) (18411799128 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1827613593126651 / 4000000000000) 2 (IntervalRat.scale (627 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-31083363466 / 1000000000000) (-31083277949 / 1000000000000), orderedInterval (20701878380 / 1000000000000) (20701963897 / 1000000000000)))) (orderedInterval (-1570566518 / 1000000000000) (-1570558031 / 1000000000000))) = true
  rfl'

theorem compactCertificate442_chunkChecks2_1 :
    compactCertificate442.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2804029243784373 / 4000000000000) 2 (IntervalRat.scale (627 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-28272906285 / 1000000000000) (-28272906270 / 1000000000000), orderedInterval (-10410201815 / 1000000000000) (-10410201800 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1618907038714317 / 4000000000000) 2 (IntervalRat.scale (627 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-9673651267 / 1000000000000) (-9673651266 / 1000000000000), orderedInterval (-38450802944 / 1000000000000) (-38450802943 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2872778949303153 / 4000000000000) 2 (IntervalRat.scale (627 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (12809362069 / 1000000000000) (12809362119 / 1000000000000), orderedInterval (-26885246147 / 1000000000000) (-26885246097 / 1000000000000)))) (orderedInterval (-33454303648 / 1000000000000) (-33454303045 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2684122741523157 / 4000000000000) 2 (IntervalRat.scale (627 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-14357924806 / 1000000000000) (-14357924681 / 1000000000000), orderedInterval (27260826071 / 1000000000000) (27260826195 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1915516640490981 / 4000000000000) 2 (IntervalRat.scale (627 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (30668469976 / 1000000000000) (30668558610 / 1000000000000), orderedInterval (-19751022177 / 1000000000000) (-19750933543 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2171991712690899 / 4000000000000) 2 (IntervalRat.scale (627 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-9711309307 / 1000000000000) (-9711309306 / 1000000000000), orderedInterval (-32825604534 / 1000000000000) (-32825604533 / 1000000000000)))) (orderedInterval (-8090360068 / 1000000000000) (-8090340360 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1810780248522531 / 4000000000000) 2 (IntervalRat.scale (627 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (33263544310 / 1000000000000) (33263544312 / 1000000000000), orderedInterval (17278699780 / 1000000000000) (17278699781 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1599879265025151 / 4000000000000) 2 (IntervalRat.scale (627 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-39085822401 / 1000000000000) (-39085819324 / 1000000000000), orderedInterval (8046796380 / 1000000000000) (8046799457 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (463707369293949 / 800000000000) 2 (IntervalRat.scale (627 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (23194988620 / 1000000000000) (23194995498 / 1000000000000), orderedInterval (-23690780926 / 1000000000000) (-23690774047 / 1000000000000)))) (orderedInterval (-6467387371 / 1000000000000) (-6467386415 / 1000000000000))) = true
  rfl'

theorem compactCertificate442_chunkChecks2_2 :
    compactCertificate442.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1282638987048903 / 4000000000000) 2 (IntervalRat.scale (627 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (37548941885 / 1000000000000) (37548941886 / 1000000000000), orderedInterval (23929354615 / 1000000000000) (23929354616 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1087307274159183 / 4000000000000) 2 (IntervalRat.scale (627 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (31427527022 / 1000000000000) (31427543406 / 1000000000000), orderedInterval (-36858843568 / 1000000000000) (-36858827185 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (680386406873349 / 4000000000000) 2 (IntervalRat.scale (627 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (57765844878 / 1000000000000) (57765844879 / 1000000000000), orderedInterval (19974426461 / 1000000000000) (19974426462 / 1000000000000)))) (orderedInterval (7070447255 / 1000000000000) (7070448024 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (365914072479483 / 4000000000000) 2 (IntervalRat.scale (627 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-76359293369 / 1000000000000) (-76359293368 / 1000000000000), orderedInterval (-33174540670 / 1000000000000) (-33174540669 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (993527887207449 / 4000000000000) 2 (IntervalRat.scale (627 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-42074842783 / 1000000000000) (-42074842782 / 1000000000000), orderedInterval (-28071530499 / 1000000000000) (-28071530498 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1356577390670073 / 4000000000000) 2 (IntervalRat.scale (627 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (25782563921 / 1000000000000) (25782563922 / 1000000000000), orderedInterval (34781453735 / 1000000000000) (34781453736 / 1000000000000)))) (orderedInterval (1600211636 / 1000000000000) (1600211670 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (573613593126651 / 4000000000000) 2 (IntervalRat.scale (627 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-21296309741 / 1000000000000) (-21296309228 / 1000000000000), orderedInterval (63207855508 / 1000000000000) (63207856022 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2331707409985371 / 4000000000000) 2 (IntervalRat.scale (627 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-19314233336 / 1000000000000) (-19314232041 / 1000000000000), orderedInterval (26832041531 / 1000000000000) (26832042826 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1557472489073589 / 4000000000000) 2 (IntervalRat.scale (627 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (22688069787 / 1000000000000) (22688069788 / 1000000000000), orderedInterval (33441142197 / 1000000000000) (33441142198 / 1000000000000)))) (orderedInterval (1194860620 / 1000000000000) (1194861166 / 1000000000000))) = true
  rfl'

theorem compactCertificate442_chunkChecks2 :
    compactCertificate442.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate442.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate442_chunkChecks2_0
    compactCertificate442_chunkChecks2_1 compactCertificate442_chunkChecks2_2

theorem compactCertificate442_chunkChecks3_0 :
    compactCertificate442.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (627 / 2) 3 (IntervalRat.scale (627 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (5651049715 / 1000000000000) (5651049716 / 1000000000000), orderedInterval (44698405113 / 1000000000000) (44698405114 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (923690724333927 / 4000000000000) 3 (IntervalRat.scale (627 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-36563069480 / 1000000000000) (-36563033592 / 1000000000000), orderedInterval (37761981533 / 1000000000000) (37762017421 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (298702601825991 / 800000000000) 3 (IntervalRat.scale (627 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-12745406598 / 1000000000000) (-12745406597 / 1000000000000), orderedInterval (-39258653022 / 1000000000000) (-39258653021 / 1000000000000)))) (orderedInterval (-13962068841 / 1000000000000) (-13962068673 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (269530649643189 / 4000000000000) 3 (IntervalRat.scale (627 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-78996811343 / 1000000000000) (-78996773681 / 1000000000000), orderedInterval (57218721331 / 1000000000000) (57218758993 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (723997237563633 / 4000000000000) 3 (IntervalRat.scale (627 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-24634456665 / 1000000000000) (-24634455252 / 1000000000000), orderedInterval (54016192669 / 1000000000000) (54016194083 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1965793337505261 / 4000000000000) 3 (IntervalRat.scale (627 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30218925341 / 1000000000000) (30219007355 / 1000000000000), orderedInterval (-19580947160 / 1000000000000) (-19580865147 / 1000000000000)))) (orderedInterval (-5753417556 / 1000000000000) (-5753394947 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1447994475127893 / 4000000000000) 3 (IntervalRat.scale (627 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-41832417949 / 1000000000000) (-41832417868 / 1000000000000), orderedInterval (-2887049147 / 1000000000000) (-2887049066 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2481163213406889 / 4000000000000) 3 (IntervalRat.scale (627 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-26231848444 / 1000000000000) (-26231815105 / 1000000000000), orderedInterval (18411765788 / 1000000000000) (18411799128 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1827613593126651 / 4000000000000) 3 (IntervalRat.scale (627 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-31083363466 / 1000000000000) (-31083277949 / 1000000000000), orderedInterval (20701878380 / 1000000000000) (20701963897 / 1000000000000)))) (orderedInterval (2854995670 / 1000000000000) (2855010160 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate442_chunkChecks3_1 :
    compactCertificate442.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2804029243784373 / 4000000000000) 3 (IntervalRat.scale (627 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-28272906285 / 1000000000000) (-28272906270 / 1000000000000), orderedInterval (-10410201815 / 1000000000000) (-10410201800 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1618907038714317 / 4000000000000) 3 (IntervalRat.scale (627 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-9673651267 / 1000000000000) (-9673651266 / 1000000000000), orderedInterval (-38450802944 / 1000000000000) (-38450802943 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2872778949303153 / 4000000000000) 3 (IntervalRat.scale (627 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (12809362069 / 1000000000000) (12809362119 / 1000000000000), orderedInterval (-26885246147 / 1000000000000) (-26885246097 / 1000000000000)))) (orderedInterval (31506214147 / 1000000000000) (31506215472 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2684122741523157 / 4000000000000) 3 (IntervalRat.scale (627 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-14357924806 / 1000000000000) (-14357924681 / 1000000000000), orderedInterval (27260826071 / 1000000000000) (27260826195 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1915516640490981 / 4000000000000) 3 (IntervalRat.scale (627 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (30668469976 / 1000000000000) (30668558610 / 1000000000000), orderedInterval (-19751022177 / 1000000000000) (-19750933543 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2171991712690899 / 4000000000000) 3 (IntervalRat.scale (627 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-9711309307 / 1000000000000) (-9711309306 / 1000000000000), orderedInterval (-32825604534 / 1000000000000) (-32825604533 / 1000000000000)))) (orderedInterval (10645720713 / 1000000000000) (10645750841 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1810780248522531 / 4000000000000) 3 (IntervalRat.scale (627 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (33263544310 / 1000000000000) (33263544312 / 1000000000000), orderedInterval (17278699780 / 1000000000000) (17278699781 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1599879265025151 / 4000000000000) 3 (IntervalRat.scale (627 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-39085822401 / 1000000000000) (-39085819324 / 1000000000000), orderedInterval (8046796380 / 1000000000000) (8046799457 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (463707369293949 / 800000000000) 3 (IntervalRat.scale (627 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (23194988620 / 1000000000000) (23194995498 / 1000000000000), orderedInterval (-23690780926 / 1000000000000) (-23690774047 / 1000000000000)))) (orderedInterval (4209989099 / 1000000000000) (4209990681 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate442_chunkChecks3_2 :
    compactCertificate442.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1282638987048903 / 4000000000000) 3 (IntervalRat.scale (627 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (37548941885 / 1000000000000) (37548941886 / 1000000000000), orderedInterval (23929354615 / 1000000000000) (23929354616 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1087307274159183 / 4000000000000) 3 (IntervalRat.scale (627 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (31427527022 / 1000000000000) (31427543406 / 1000000000000), orderedInterval (-36858843568 / 1000000000000) (-36858827185 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (680386406873349 / 4000000000000) 3 (IntervalRat.scale (627 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (57765844878 / 1000000000000) (57765844879 / 1000000000000), orderedInterval (19974426461 / 1000000000000) (19974426462 / 1000000000000)))) (orderedInterval (2607916067 / 1000000000000) (2607916742 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (365914072479483 / 4000000000000) 3 (IntervalRat.scale (627 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-76359293369 / 1000000000000) (-76359293368 / 1000000000000), orderedInterval (-33174540670 / 1000000000000) (-33174540669 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (993527887207449 / 4000000000000) 3 (IntervalRat.scale (627 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-42074842783 / 1000000000000) (-42074842782 / 1000000000000), orderedInterval (-28071530499 / 1000000000000) (-28071530498 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1356577390670073 / 4000000000000) 3 (IntervalRat.scale (627 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (25782563921 / 1000000000000) (25782563922 / 1000000000000), orderedInterval (34781453735 / 1000000000000) (34781453736 / 1000000000000)))) (orderedInterval (3037646000 / 1000000000000) (3037646035 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (573613593126651 / 4000000000000) 3 (IntervalRat.scale (627 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-21296309741 / 1000000000000) (-21296309228 / 1000000000000), orderedInterval (63207855508 / 1000000000000) (63207856022 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2331707409985371 / 4000000000000) 3 (IntervalRat.scale (627 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-19314233336 / 1000000000000) (-19314232041 / 1000000000000), orderedInterval (26832041531 / 1000000000000) (26832042826 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1557472489073589 / 4000000000000) 3 (IntervalRat.scale (627 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (22688069787 / 1000000000000) (22688069788 / 1000000000000), orderedInterval (33441142197 / 1000000000000) (33441142198 / 1000000000000)))) (orderedInterval (26022308794 / 1000000000000) (26022309752 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate442_chunkChecks3 :
    compactCertificate442.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate442.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate442_chunkChecks3_0
    compactCertificate442_chunkChecks3_1 compactCertificate442_chunkChecks3_2

theorem compactCertificate442_chunkChecks4_0 :
    compactCertificate442.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (627 / 2) 4 (IntervalRat.scale (627 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (5651049715 / 1000000000000) (5651049716 / 1000000000000), orderedInterval (44698405113 / 1000000000000) (44698405114 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (923690724333927 / 4000000000000) 4 (IntervalRat.scale (627 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-36563069480 / 1000000000000) (-36563033592 / 1000000000000), orderedInterval (37761981533 / 1000000000000) (37762017421 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (298702601825991 / 800000000000) 4 (IntervalRat.scale (627 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-12745406598 / 1000000000000) (-12745406597 / 1000000000000), orderedInterval (-39258653022 / 1000000000000) (-39258653021 / 1000000000000)))) (orderedInterval (723776159 / 1000000000000) (723776298 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (269530649643189 / 4000000000000) 4 (IntervalRat.scale (627 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-78996811343 / 1000000000000) (-78996773681 / 1000000000000), orderedInterval (57218721331 / 1000000000000) (57218758993 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (723997237563633 / 4000000000000) 4 (IntervalRat.scale (627 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-24634456665 / 1000000000000) (-24634455252 / 1000000000000), orderedInterval (54016192669 / 1000000000000) (54016194083 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1965793337505261 / 4000000000000) 4 (IntervalRat.scale (627 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30218925341 / 1000000000000) (30219007355 / 1000000000000), orderedInterval (-19580947160 / 1000000000000) (-19580865147 / 1000000000000)))) (orderedInterval (-13034569682 / 1000000000000) (-13034534186 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1447994475127893 / 4000000000000) 4 (IntervalRat.scale (627 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-41832417949 / 1000000000000) (-41832417868 / 1000000000000), orderedInterval (-2887049147 / 1000000000000) (-2887049066 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2481163213406889 / 4000000000000) 4 (IntervalRat.scale (627 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-26231848444 / 1000000000000) (-26231815105 / 1000000000000), orderedInterval (18411765788 / 1000000000000) (18411799128 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1827613593126651 / 4000000000000) 4 (IntervalRat.scale (627 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-31083363466 / 1000000000000) (-31083277949 / 1000000000000), orderedInterval (20701878380 / 1000000000000) (20701963897 / 1000000000000)))) (orderedInterval (8992663168 / 1000000000000) (8992688527 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate442_chunkChecks4_1 :
    compactCertificate442.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2804029243784373 / 4000000000000) 4 (IntervalRat.scale (627 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-28272906285 / 1000000000000) (-28272906270 / 1000000000000), orderedInterval (-10410201815 / 1000000000000) (-10410201800 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1618907038714317 / 4000000000000) 4 (IntervalRat.scale (627 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-9673651267 / 1000000000000) (-9673651266 / 1000000000000), orderedInterval (-38450802944 / 1000000000000) (-38450802943 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2872778949303153 / 4000000000000) 4 (IntervalRat.scale (627 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (12809362069 / 1000000000000) (12809362119 / 1000000000000), orderedInterval (-26885246147 / 1000000000000) (-26885246097 / 1000000000000)))) (orderedInterval (173556208420 / 1000000000000) (173556211369 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2684122741523157 / 4000000000000) 4 (IntervalRat.scale (627 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-14357924806 / 1000000000000) (-14357924681 / 1000000000000), orderedInterval (27260826071 / 1000000000000) (27260826195 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1915516640490981 / 4000000000000) 4 (IntervalRat.scale (627 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (30668469976 / 1000000000000) (30668558610 / 1000000000000), orderedInterval (-19751022177 / 1000000000000) (-19750933543 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2171991712690899 / 4000000000000) 4 (IntervalRat.scale (627 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-9711309307 / 1000000000000) (-9711309306 / 1000000000000), orderedInterval (-32825604534 / 1000000000000) (-32825604533 / 1000000000000)))) (orderedInterval (21604526511 / 1000000000000) (21604572676 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1810780248522531 / 4000000000000) 4 (IntervalRat.scale (627 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (33263544310 / 1000000000000) (33263544312 / 1000000000000), orderedInterval (17278699780 / 1000000000000) (17278699781 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1599879265025151 / 4000000000000) 4 (IntervalRat.scale (627 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-39085822401 / 1000000000000) (-39085819324 / 1000000000000), orderedInterval (8046796380 / 1000000000000) (8046799457 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (463707369293949 / 800000000000) 4 (IntervalRat.scale (627 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (23194988620 / 1000000000000) (23194995498 / 1000000000000), orderedInterval (-23690780926 / 1000000000000) (-23690774047 / 1000000000000)))) (orderedInterval (14509472399 / 1000000000000) (14509475091 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate442_chunkChecks4_2 :
    compactCertificate442.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1282638987048903 / 4000000000000) 4 (IntervalRat.scale (627 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (37548941885 / 1000000000000) (37548941886 / 1000000000000), orderedInterval (23929354615 / 1000000000000) (23929354616 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1087307274159183 / 4000000000000) 4 (IntervalRat.scale (627 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (31427527022 / 1000000000000) (31427543406 / 1000000000000), orderedInterval (-36858843568 / 1000000000000) (-36858827185 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (680386406873349 / 4000000000000) 4 (IntervalRat.scale (627 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (57765844878 / 1000000000000) (57765844879 / 1000000000000), orderedInterval (19974426461 / 1000000000000) (19974426462 / 1000000000000)))) (orderedInterval (-7430333906 / 1000000000000) (-7430333311 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (365914072479483 / 4000000000000) 4 (IntervalRat.scale (627 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-76359293369 / 1000000000000) (-76359293368 / 1000000000000), orderedInterval (-33174540670 / 1000000000000) (-33174540669 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (993527887207449 / 4000000000000) 4 (IntervalRat.scale (627 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-42074842783 / 1000000000000) (-42074842782 / 1000000000000), orderedInterval (-28071530499 / 1000000000000) (-28071530498 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1356577390670073 / 4000000000000) 4 (IntervalRat.scale (627 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (25782563921 / 1000000000000) (25782563922 / 1000000000000), orderedInterval (34781453735 / 1000000000000) (34781453736 / 1000000000000)))) (orderedInterval (-2339241512 / 1000000000000) (-2339241475 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (573613593126651 / 4000000000000) 4 (IntervalRat.scale (627 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-21296309741 / 1000000000000) (-21296309228 / 1000000000000), orderedInterval (63207855508 / 1000000000000) (63207856022 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2331707409985371 / 4000000000000) 4 (IntervalRat.scale (627 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-19314233336 / 1000000000000) (-19314232041 / 1000000000000), orderedInterval (26832041531 / 1000000000000) (26832042826 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1557472489073589 / 4000000000000) 4 (IntervalRat.scale (627 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (22688069787 / 1000000000000) (22688069788 / 1000000000000), orderedInterval (33441142197 / 1000000000000) (33441142198 / 1000000000000)))) (orderedInterval (8492913675 / 1000000000000) (8492915387 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate442_chunkChecks4 :
    compactCertificate442.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate442.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate442_chunkChecks4_0
    compactCertificate442_chunkChecks4_1 compactCertificate442_chunkChecks4_2

theorem compactCertificate442_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate442.chunkCheck r b = true :=
  compactCertificate442.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate442_chunkChecks0
    · exact compactCertificate442_chunkChecks1
    · exact compactCertificate442_chunkChecks2
    · exact compactCertificate442_chunkChecks3
    · exact compactCertificate442_chunkChecks4)

theorem compactCertificate442_coefficient0 :
    compactCertificate442.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate442_coefficient1 :
    compactCertificate442.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate442_coefficient2 :
    compactCertificate442.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate442_coefficient3 :
    compactCertificate442.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate442_coefficient4 :
    compactCertificate442.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate442_coefficients : ∀ r : Fin 5,
    compactCertificate442.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate442_coefficient0
  · exact compactCertificate442_coefficient1
  · exact compactCertificate442_coefficient2
  · exact compactCertificate442_coefficient3
  · exact compactCertificate442_coefficient4

theorem compactCertificate442_lower : (1 : ℚ) ≤ compactCertificate442.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate442, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate442_proves {t : ℝ} (ht : t ∈ compactCertificate442.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate442.proves compactCertificate442_states compactCertificate442_chunks
    compactCertificate442_coefficients compactCertificate442_lower ht

end Erdos232
