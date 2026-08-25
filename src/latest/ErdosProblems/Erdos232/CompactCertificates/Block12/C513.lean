/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate513 : CompactCertificate where
  left := 384
  right := 385
  center := 769 / 2
  grid := fun i =>
    match i.val with
    | 0 => 122
    | 1 => 90
    | 2 => 146
    | 3 => 26
    | 4 => 71
    | 5 => 192
    | 6 => 141
    | 7 => 242
    | 8 => 178
    | 9 => 274
    | 10 => 158
    | 11 => 281
    | 12 => 262
    | 13 => 187
    | 14 => 212
    | 15 => 177
    | 16 => 156
    | 17 => 226
    | 18 => 125
    | 19 => 106
    | 20 => 66
    | 21 => 36
    | 22 => 97
    | 23 => 132
    | 24 => 56
    | 25 => 228
    | _ => 152
  point := fun i =>
    match i.val with
    | 0 => 769 / 2
    | 1 => 1132883838935869 / 4000000000000
    | 2 => 366351356944477 / 800000000000
    | 3 => 330572678748983 / 4000000000000
    | 4 => 887964714013451 / 4000000000000
    | 5 => 2410996932283167 / 4000000000000
    | 6 => 1775929428027671 / 4000000000000
    | 7 => 3043085344672883 / 4000000000000
    | 8 => 2241522891729497 / 4000000000000
    | 9 => 3439072549394231 / 4000000000000
    | 10 => 1985549462155199 / 4000000000000
    | 11 => 3523392363658891 / 4000000000000
    | 12 => 3292010188566679 / 4000000000000
    | 13 => 2349333806280007 / 4000000000000
    | 14 => 2663894142040353 / 4000000000000
    | 15 => 2220877210707857 / 4000000000000
    | 16 => 1962212368108997 / 4000000000000
    | 17 => 568725625178703 / 800000000000
    | 18 => 1573125009634141 / 4000000000000
    | 19 => 1333555492549301 / 4000000000000
    | 20 => 834477108270503 / 4000000000000
    | 21 => 448784564173401 / 4000000000000
    | 22 => 1218537392763203 / 4000000000000
    | 23 => 1663808633852131 / 4000000000000
    | 24 => 703522891729497 / 4000000000000
    | 25 => 2859781496457337 / 4000000000000
    | _ => 1910201505737783 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (36815137706 / 1000000000000) (36815168361 / 1000000000000), orderedInterval (-17378546737 / 1000000000000) (-17378516081 / 1000000000000))
    | 1 => (orderedInterval (45176562682 / 1000000000000) (45176562684 / 1000000000000), orderedInterval (14302878560 / 1000000000000) (14302878562 / 1000000000000))
    | 2 => (orderedInterval (1930282782 / 1000000000000) (1930282783 / 1000000000000), orderedInterval (37233075998 / 1000000000000) (37233075999 / 1000000000000))
    | 3 => (orderedInterval (86429052287 / 1000000000000) (86429052623 / 1000000000000), orderedInterval (-15791207966 / 1000000000000) (-15791207631 / 1000000000000))
    | 4 => (orderedInterval (14648134327 / 1000000000000) (14648134490 / 1000000000000), orderedInterval (-51542301685 / 1000000000000) (-51542301522 / 1000000000000))
    | 5 => (orderedInterval (11102176678 / 1000000000000) (11102176679 / 1000000000000), orderedInterval (30534781110 / 1000000000000) (30534781111 / 1000000000000))
    | 6 => (orderedInterval (-36851178112 / 1000000000000) (-36851172717 / 1000000000000), orderedInterval (8752143423 / 1000000000000) (8752148819 / 1000000000000))
    | 7 => (orderedInterval (27803870373 / 1000000000000) (27803870446 / 1000000000000), orderedInterval (7966270448 / 1000000000000) (7966270521 / 1000000000000))
    | 8 => (orderedInterval (31153664437 / 1000000000000) (31153708710 / 1000000000000), orderedInterval (-12892348107 / 1000000000000) (-12892303833 / 1000000000000))
    | 9 => (orderedInterval (-6547382981 / 1000000000000) (-6547382979 / 1000000000000), orderedInterval (26415681271 / 1000000000000) (26415681272 / 1000000000000))
    | 10 => (orderedInterval (25711778869 / 1000000000000) (25711778870 / 1000000000000), orderedInterval (24902205795 / 1000000000000) (24902205796 / 1000000000000))
    | 11 => (orderedInterval (24584250236 / 1000000000000) (24584308501 / 1000000000000), orderedInterval (-10892776209 / 1000000000000) (-10892717944 / 1000000000000))
    | 12 => (orderedInterval (17714778812 / 1000000000000) (17714778813 / 1000000000000), orderedInterval (21430315404 / 1000000000000) (21430315405 / 1000000000000))
    | 13 => (orderedInterval (-19682786149 / 1000000000000) (-19682786148 / 1000000000000), orderedInterval (-26374595573 / 1000000000000) (-26374595572 / 1000000000000))
    | 14 => (orderedInterval (20872820000 / 1000000000000) (20872820001 / 1000000000000), orderedInterval (22793295280 / 1000000000000) (22793295281 / 1000000000000))
    | 15 => (orderedInterval (1943400381 / 1000000000000) (1943400382 / 1000000000000), orderedInterval (-33807566756 / 1000000000000) (-33807566754 / 1000000000000))
    | 16 => (orderedInterval (34184132213 / 1000000000000) (34184132218 / 1000000000000), orderedInterval (11331939566 / 1000000000000) (11331939571 / 1000000000000))
    | 17 => (orderedInterval (29704285364 / 1000000000000) (29704292331 / 1000000000000), orderedInterval (-3648367712 / 1000000000000) (-3648360745 / 1000000000000))
    | 18 => (orderedInterval (-39402963605 / 1000000000000) (-39402963591 / 1000000000000), orderedInterval (-8082828107 / 1000000000000) (-8082828093 / 1000000000000))
    | 19 => (orderedInterval (40150758081 / 1000000000000) (40150758082 / 1000000000000), orderedInterval (17186705424 / 1000000000000) (17186705425 / 1000000000000))
    | 20 => (orderedInterval (48788650234 / 1000000000000) (48788671235 / 1000000000000), orderedInterval (-26025398812 / 1000000000000) (-26025377811 / 1000000000000))
    | 21 => (orderedInterval (-8786426972 / 1000000000000) (-8786426935 / 1000000000000), orderedInterval (74852401082 / 1000000000000) (74852401118 / 1000000000000))
    | 22 => (orderedInterval (-28916728889 / 1000000000000) (-28916728888 / 1000000000000), orderedInterval (-35358846796 / 1000000000000) (-35358846795 / 1000000000000))
    | 23 => (orderedInterval (34768632935 / 1000000000000) (34768681931 / 1000000000000), orderedInterval (-17976470770 / 1000000000000) (-17976421773 / 1000000000000))
    | 24 => (orderedInterval (40399088548 / 1000000000000) (40399088549 / 1000000000000), orderedInterval (44466829987 / 1000000000000) (44466829988 / 1000000000000))
    | 25 => (orderedInterval (-15661408685 / 1000000000000) (-15661408454 / 1000000000000), orderedInterval (25411065213 / 1000000000000) (25411065444 / 1000000000000))
    | _ => (orderedInterval (26531032859 / 1000000000000) (26531032860 / 1000000000000), orderedInterval (25056055968 / 1000000000000) (25056055969 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (15126460901 / 1000000000000) (15126473079 / 1000000000000)
      | 1 => orderedInterval (-1192114761 / 1000000000000) (-1192114704 / 1000000000000)
      | 2 => orderedInterval (-104660016 / 1000000000000) (-104658921 / 1000000000000)
      | 3 => orderedInterval (6563218079 / 1000000000000) (6563226515 / 1000000000000)
      | 4 => orderedInterval (-2286695610 / 1000000000000) (-2286695563 / 1000000000000)
      | 5 => orderedInterval (-1173255528 / 1000000000000) (-1173255312 / 1000000000000)
      | 6 => orderedInterval (5616032612 / 1000000000000) (5616033394 / 1000000000000)
      | 7 => orderedInterval (-1846360279 / 1000000000000) (-1846356477 / 1000000000000)
      | _ => orderedInterval (-3459520171 / 1000000000000) (-3459520046 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-4187888176 / 1000000000000) (-4187875995 / 1000000000000)
      | 1 => orderedInterval (-4452530890 / 1000000000000) (-4452530833 / 1000000000000)
      | 2 => orderedInterval (-940273821 / 1000000000000) (-940272219 / 1000000000000)
      | 3 => orderedInterval (-11660974812 / 1000000000000) (-11660955521 / 1000000000000)
      | 4 => orderedInterval (-4837626717 / 1000000000000) (-4837626642 / 1000000000000)
      | 5 => orderedInterval (-1563804833 / 1000000000000) (-1563804450 / 1000000000000)
      | 6 => orderedInterval (18738188 / 1000000000000) (18738651 / 1000000000000)
      | 7 => orderedInterval (1722635532 / 1000000000000) (1722639636 / 1000000000000)
      | _ => orderedInterval (-9562477724 / 1000000000000) (-9562477539 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-14970425403 / 1000000000000) (-14970413186 / 1000000000000)
      | 1 => orderedInterval (1816146829 / 1000000000000) (1816146904 / 1000000000000)
      | 2 => orderedInterval (1760475800 / 1000000000000) (1760478152 / 1000000000000)
      | 3 => orderedInterval (-27303067757 / 1000000000000) (-27303023559 / 1000000000000)
      | 4 => orderedInterval (6137608395 / 1000000000000) (6137608519 / 1000000000000)
      | 5 => orderedInterval (541573356 / 1000000000000) (541574047 / 1000000000000)
      | 6 => orderedInterval (-5350405261 / 1000000000000) (-5350404971 / 1000000000000)
      | 7 => orderedInterval (2688295882 / 1000000000000) (2688300329 / 1000000000000)
      | _ => orderedInterval (3244966840 / 1000000000000) (3244967126 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (3182725957 / 1000000000000) (3182738180 / 1000000000000)
      | 1 => orderedInterval (8717946788 / 1000000000000) (8717946899 / 1000000000000)
      | 2 => orderedInterval (2863246144 / 1000000000000) (2863249601 / 1000000000000)
      | 3 => orderedInterval (67195944298 / 1000000000000) (67196045480 / 1000000000000)
      | 4 => orderedInterval (13266724624 / 1000000000000) (13266724834 / 1000000000000)
      | 5 => orderedInterval (3111168045 / 1000000000000) (3111169297 / 1000000000000)
      | 6 => orderedInterval (-599600394 / 1000000000000) (-599600199 / 1000000000000)
      | 7 => orderedInterval (-2115784771 / 1000000000000) (-2115779963 / 1000000000000)
      | _ => orderedInterval (22270741569 / 1000000000000) (22270742031 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (14927410271 / 1000000000000) (14927422532 / 1000000000000)
      | 1 => orderedInterval (-4754148687 / 1000000000000) (-4754148518 / 1000000000000)
      | 2 => orderedInterval (-9761247336 / 1000000000000) (-9761242232 / 1000000000000)
      | 3 => orderedInterval (130285633846 / 1000000000000) (130285865800 / 1000000000000)
      | 4 => orderedInterval (-17865996543 / 1000000000000) (-17865996180 / 1000000000000)
      | 5 => orderedInterval (3786139072 / 1000000000000) (3786141357 / 1000000000000)
      | 6 => orderedInterval (5752043220 / 1000000000000) (5752043364 / 1000000000000)
      | 7 => orderedInterval (-3378738016 / 1000000000000) (-3378732804 / 1000000000000)
      | _ => orderedInterval (3289214575 / 1000000000000) (3289215348 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (17243105227 / 1000000000000) (17243131965 / 1000000000000)
    | 1 => orderedInterval (-35464203253 / 1000000000000) (-35464164912 / 1000000000000)
    | 2 => orderedInterval (-31434831319 / 1000000000000) (-31434766639 / 1000000000000)
    | 3 => orderedInterval (117893112260 / 1000000000000) (117893236160 / 1000000000000)
    | _ => orderedInterval (122280310402 / 1000000000000) (122280568667 / 1000000000000)

theorem compactCertificate513_stateChecks0 :
    compactCertificate513.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 122 12 (769 / 2)) (orderedInterval (36815137706 / 1000000000000) (36815168361 / 1000000000000), orderedInterval (-17378546737 / 1000000000000) (-17378516081 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (1132883838935869 / 4000000000000)) (orderedInterval (45176562682 / 1000000000000) (45176562684 / 1000000000000), orderedInterval (14302878560 / 1000000000000) (14302878562 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 146 12 (366351356944477 / 800000000000)) (orderedInterval (1930282782 / 1000000000000) (1930282783 / 1000000000000), orderedInterval (37233075998 / 1000000000000) (37233075999 / 1000000000000))) = true
  rfl'

theorem compactCertificate513_stateChecks1 :
    compactCertificate513.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (330572678748983 / 4000000000000)) (orderedInterval (86429052287 / 1000000000000) (86429052623 / 1000000000000), orderedInterval (-15791207966 / 1000000000000) (-15791207631 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (887964714013451 / 4000000000000)) (orderedInterval (14648134327 / 1000000000000) (14648134490 / 1000000000000), orderedInterval (-51542301685 / 1000000000000) (-51542301522 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 192 12 (2410996932283167 / 4000000000000)) (orderedInterval (11102176678 / 1000000000000) (11102176679 / 1000000000000), orderedInterval (30534781110 / 1000000000000) (30534781111 / 1000000000000))) = true
  rfl'

theorem compactCertificate513_stateChecks2 :
    compactCertificate513.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 141 12 (1775929428027671 / 4000000000000)) (orderedInterval (-36851178112 / 1000000000000) (-36851172717 / 1000000000000), orderedInterval (8752143423 / 1000000000000) (8752148819 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 242 12 (3043085344672883 / 4000000000000)) (orderedInterval (27803870373 / 1000000000000) (27803870446 / 1000000000000), orderedInterval (7966270448 / 1000000000000) (7966270521 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 178 12 (2241522891729497 / 4000000000000)) (orderedInterval (31153664437 / 1000000000000) (31153708710 / 1000000000000), orderedInterval (-12892348107 / 1000000000000) (-12892303833 / 1000000000000))) = true
  rfl'

theorem compactCertificate513_stateChecks3 :
    compactCertificate513.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 274 12 (3439072549394231 / 4000000000000)) (orderedInterval (-6547382981 / 1000000000000) (-6547382979 / 1000000000000), orderedInterval (26415681271 / 1000000000000) (26415681272 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 158 12 (1985549462155199 / 4000000000000)) (orderedInterval (25711778869 / 1000000000000) (25711778870 / 1000000000000), orderedInterval (24902205795 / 1000000000000) (24902205796 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 281 12 (3523392363658891 / 4000000000000)) (orderedInterval (24584250236 / 1000000000000) (24584308501 / 1000000000000), orderedInterval (-10892776209 / 1000000000000) (-10892717944 / 1000000000000))) = true
  rfl'

theorem compactCertificate513_stateChecks4 :
    compactCertificate513.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 262 12 (3292010188566679 / 4000000000000)) (orderedInterval (17714778812 / 1000000000000) (17714778813 / 1000000000000), orderedInterval (21430315404 / 1000000000000) (21430315405 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 187 12 (2349333806280007 / 4000000000000)) (orderedInterval (-19682786149 / 1000000000000) (-19682786148 / 1000000000000), orderedInterval (-26374595573 / 1000000000000) (-26374595572 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 212 12 (2663894142040353 / 4000000000000)) (orderedInterval (20872820000 / 1000000000000) (20872820001 / 1000000000000), orderedInterval (22793295280 / 1000000000000) (22793295281 / 1000000000000))) = true
  rfl'

theorem compactCertificate513_stateChecks5 :
    compactCertificate513.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 177 12 (2220877210707857 / 4000000000000)) (orderedInterval (1943400381 / 1000000000000) (1943400382 / 1000000000000), orderedInterval (-33807566756 / 1000000000000) (-33807566754 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 156 12 (1962212368108997 / 4000000000000)) (orderedInterval (34184132213 / 1000000000000) (34184132218 / 1000000000000), orderedInterval (11331939566 / 1000000000000) (11331939571 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 226 12 (568725625178703 / 800000000000)) (orderedInterval (29704285364 / 1000000000000) (29704292331 / 1000000000000), orderedInterval (-3648367712 / 1000000000000) (-3648360745 / 1000000000000))) = true
  rfl'

theorem compactCertificate513_stateChecks6 :
    compactCertificate513.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 125 12 (1573125009634141 / 4000000000000)) (orderedInterval (-39402963605 / 1000000000000) (-39402963591 / 1000000000000), orderedInterval (-8082828107 / 1000000000000) (-8082828093 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 106 12 (1333555492549301 / 4000000000000)) (orderedInterval (40150758081 / 1000000000000) (40150758082 / 1000000000000), orderedInterval (17186705424 / 1000000000000) (17186705425 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (834477108270503 / 4000000000000)) (orderedInterval (48788650234 / 1000000000000) (48788671235 / 1000000000000), orderedInterval (-26025398812 / 1000000000000) (-26025377811 / 1000000000000))) = true
  rfl'

theorem compactCertificate513_stateChecks7 :
    compactCertificate513.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (448784564173401 / 4000000000000)) (orderedInterval (-8786426972 / 1000000000000) (-8786426935 / 1000000000000), orderedInterval (74852401082 / 1000000000000) (74852401118 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 97 12 (1218537392763203 / 4000000000000)) (orderedInterval (-28916728889 / 1000000000000) (-28916728888 / 1000000000000), orderedInterval (-35358846796 / 1000000000000) (-35358846795 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 132 12 (1663808633852131 / 4000000000000)) (orderedInterval (34768632935 / 1000000000000) (34768681931 / 1000000000000), orderedInterval (-17976470770 / 1000000000000) (-17976421773 / 1000000000000))) = true
  rfl'

theorem compactCertificate513_stateChecks8 :
    compactCertificate513.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (703522891729497 / 4000000000000)) (orderedInterval (40399088548 / 1000000000000) (40399088549 / 1000000000000), orderedInterval (44466829987 / 1000000000000) (44466829988 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 228 12 (2859781496457337 / 4000000000000)) (orderedInterval (-15661408685 / 1000000000000) (-15661408454 / 1000000000000), orderedInterval (25411065213 / 1000000000000) (25411065444 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 152 12 (1910201505737783 / 4000000000000)) (orderedInterval (26531032859 / 1000000000000) (26531032860 / 1000000000000), orderedInterval (25056055968 / 1000000000000) (25056055969 / 1000000000000))) = true
  rfl'

theorem compactCertificate513_states : ∀ j,
    BesselStateValid (compactCertificate513.point j) (compactCertificate513.state j) :=
  compactCertificate513.statesValid_of_checks3 compactCertificate513_stateChecks0
    compactCertificate513_stateChecks1 compactCertificate513_stateChecks2
    compactCertificate513_stateChecks3 compactCertificate513_stateChecks4
    compactCertificate513_stateChecks5 compactCertificate513_stateChecks6
    compactCertificate513_stateChecks7 compactCertificate513_stateChecks8

theorem compactCertificate513_chunkChecks0_0 :
    compactCertificate513.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (769 / 2) 0 (IntervalRat.scale (769 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (36815137706 / 1000000000000) (36815168361 / 1000000000000), orderedInterval (-17378546737 / 1000000000000) (-17378516081 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1132883838935869 / 4000000000000) 0 (IntervalRat.scale (769 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (45176562682 / 1000000000000) (45176562684 / 1000000000000), orderedInterval (14302878560 / 1000000000000) (14302878562 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (366351356944477 / 800000000000) 0 (IntervalRat.scale (769 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (1930282782 / 1000000000000) (1930282783 / 1000000000000), orderedInterval (37233075998 / 1000000000000) (37233075999 / 1000000000000)))) (orderedInterval (15126460901 / 1000000000000) (15126473079 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (330572678748983 / 4000000000000) 0 (IntervalRat.scale (769 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (86429052287 / 1000000000000) (86429052623 / 1000000000000), orderedInterval (-15791207966 / 1000000000000) (-15791207631 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (887964714013451 / 4000000000000) 0 (IntervalRat.scale (769 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (14648134327 / 1000000000000) (14648134490 / 1000000000000), orderedInterval (-51542301685 / 1000000000000) (-51542301522 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2410996932283167 / 4000000000000) 0 (IntervalRat.scale (769 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (11102176678 / 1000000000000) (11102176679 / 1000000000000), orderedInterval (30534781110 / 1000000000000) (30534781111 / 1000000000000)))) (orderedInterval (-1192114761 / 1000000000000) (-1192114704 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1775929428027671 / 4000000000000) 0 (IntervalRat.scale (769 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-36851178112 / 1000000000000) (-36851172717 / 1000000000000), orderedInterval (8752143423 / 1000000000000) (8752148819 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3043085344672883 / 4000000000000) 0 (IntervalRat.scale (769 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (27803870373 / 1000000000000) (27803870446 / 1000000000000), orderedInterval (7966270448 / 1000000000000) (7966270521 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2241522891729497 / 4000000000000) 0 (IntervalRat.scale (769 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (31153664437 / 1000000000000) (31153708710 / 1000000000000), orderedInterval (-12892348107 / 1000000000000) (-12892303833 / 1000000000000)))) (orderedInterval (-104660016 / 1000000000000) (-104658921 / 1000000000000))) = true
  rfl'

theorem compactCertificate513_chunkChecks0_1 :
    compactCertificate513.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3439072549394231 / 4000000000000) 0 (IntervalRat.scale (769 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-6547382981 / 1000000000000) (-6547382979 / 1000000000000), orderedInterval (26415681271 / 1000000000000) (26415681272 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1985549462155199 / 4000000000000) 0 (IntervalRat.scale (769 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (25711778869 / 1000000000000) (25711778870 / 1000000000000), orderedInterval (24902205795 / 1000000000000) (24902205796 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3523392363658891 / 4000000000000) 0 (IntervalRat.scale (769 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (24584250236 / 1000000000000) (24584308501 / 1000000000000), orderedInterval (-10892776209 / 1000000000000) (-10892717944 / 1000000000000)))) (orderedInterval (6563218079 / 1000000000000) (6563226515 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3292010188566679 / 4000000000000) 0 (IntervalRat.scale (769 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (17714778812 / 1000000000000) (17714778813 / 1000000000000), orderedInterval (21430315404 / 1000000000000) (21430315405 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2349333806280007 / 4000000000000) 0 (IntervalRat.scale (769 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-19682786149 / 1000000000000) (-19682786148 / 1000000000000), orderedInterval (-26374595573 / 1000000000000) (-26374595572 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2663894142040353 / 4000000000000) 0 (IntervalRat.scale (769 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (20872820000 / 1000000000000) (20872820001 / 1000000000000), orderedInterval (22793295280 / 1000000000000) (22793295281 / 1000000000000)))) (orderedInterval (-2286695610 / 1000000000000) (-2286695563 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2220877210707857 / 4000000000000) 0 (IntervalRat.scale (769 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (1943400381 / 1000000000000) (1943400382 / 1000000000000), orderedInterval (-33807566756 / 1000000000000) (-33807566754 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1962212368108997 / 4000000000000) 0 (IntervalRat.scale (769 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (34184132213 / 1000000000000) (34184132218 / 1000000000000), orderedInterval (11331939566 / 1000000000000) (11331939571 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (568725625178703 / 800000000000) 0 (IntervalRat.scale (769 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (29704285364 / 1000000000000) (29704292331 / 1000000000000), orderedInterval (-3648367712 / 1000000000000) (-3648360745 / 1000000000000)))) (orderedInterval (-1173255528 / 1000000000000) (-1173255312 / 1000000000000))) = true
  rfl'

theorem compactCertificate513_chunkChecks0_2 :
    compactCertificate513.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1573125009634141 / 4000000000000) 0 (IntervalRat.scale (769 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-39402963605 / 1000000000000) (-39402963591 / 1000000000000), orderedInterval (-8082828107 / 1000000000000) (-8082828093 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1333555492549301 / 4000000000000) 0 (IntervalRat.scale (769 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (40150758081 / 1000000000000) (40150758082 / 1000000000000), orderedInterval (17186705424 / 1000000000000) (17186705425 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (834477108270503 / 4000000000000) 0 (IntervalRat.scale (769 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (48788650234 / 1000000000000) (48788671235 / 1000000000000), orderedInterval (-26025398812 / 1000000000000) (-26025377811 / 1000000000000)))) (orderedInterval (5616032612 / 1000000000000) (5616033394 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (448784564173401 / 4000000000000) 0 (IntervalRat.scale (769 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-8786426972 / 1000000000000) (-8786426935 / 1000000000000), orderedInterval (74852401082 / 1000000000000) (74852401118 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1218537392763203 / 4000000000000) 0 (IntervalRat.scale (769 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-28916728889 / 1000000000000) (-28916728888 / 1000000000000), orderedInterval (-35358846796 / 1000000000000) (-35358846795 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1663808633852131 / 4000000000000) 0 (IntervalRat.scale (769 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (34768632935 / 1000000000000) (34768681931 / 1000000000000), orderedInterval (-17976470770 / 1000000000000) (-17976421773 / 1000000000000)))) (orderedInterval (-1846360279 / 1000000000000) (-1846356477 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (703522891729497 / 4000000000000) 0 (IntervalRat.scale (769 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (40399088548 / 1000000000000) (40399088549 / 1000000000000), orderedInterval (44466829987 / 1000000000000) (44466829988 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2859781496457337 / 4000000000000) 0 (IntervalRat.scale (769 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-15661408685 / 1000000000000) (-15661408454 / 1000000000000), orderedInterval (25411065213 / 1000000000000) (25411065444 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1910201505737783 / 4000000000000) 0 (IntervalRat.scale (769 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (26531032859 / 1000000000000) (26531032860 / 1000000000000), orderedInterval (25056055968 / 1000000000000) (25056055969 / 1000000000000)))) (orderedInterval (-3459520171 / 1000000000000) (-3459520046 / 1000000000000))) = true
  rfl'

theorem compactCertificate513_chunkChecks0 :
    compactCertificate513.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate513.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate513_chunkChecks0_0
    compactCertificate513_chunkChecks0_1 compactCertificate513_chunkChecks0_2

theorem compactCertificate513_chunkChecks1_0 :
    compactCertificate513.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (769 / 2) 1 (IntervalRat.scale (769 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (36815137706 / 1000000000000) (36815168361 / 1000000000000), orderedInterval (-17378546737 / 1000000000000) (-17378516081 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1132883838935869 / 4000000000000) 1 (IntervalRat.scale (769 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (45176562682 / 1000000000000) (45176562684 / 1000000000000), orderedInterval (14302878560 / 1000000000000) (14302878562 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (366351356944477 / 800000000000) 1 (IntervalRat.scale (769 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (1930282782 / 1000000000000) (1930282783 / 1000000000000), orderedInterval (37233075998 / 1000000000000) (37233075999 / 1000000000000)))) (orderedInterval (-4187888176 / 1000000000000) (-4187875995 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (330572678748983 / 4000000000000) 1 (IntervalRat.scale (769 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (86429052287 / 1000000000000) (86429052623 / 1000000000000), orderedInterval (-15791207966 / 1000000000000) (-15791207631 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (887964714013451 / 4000000000000) 1 (IntervalRat.scale (769 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (14648134327 / 1000000000000) (14648134490 / 1000000000000), orderedInterval (-51542301685 / 1000000000000) (-51542301522 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2410996932283167 / 4000000000000) 1 (IntervalRat.scale (769 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (11102176678 / 1000000000000) (11102176679 / 1000000000000), orderedInterval (30534781110 / 1000000000000) (30534781111 / 1000000000000)))) (orderedInterval (-4452530890 / 1000000000000) (-4452530833 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1775929428027671 / 4000000000000) 1 (IntervalRat.scale (769 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-36851178112 / 1000000000000) (-36851172717 / 1000000000000), orderedInterval (8752143423 / 1000000000000) (8752148819 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3043085344672883 / 4000000000000) 1 (IntervalRat.scale (769 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (27803870373 / 1000000000000) (27803870446 / 1000000000000), orderedInterval (7966270448 / 1000000000000) (7966270521 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2241522891729497 / 4000000000000) 1 (IntervalRat.scale (769 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (31153664437 / 1000000000000) (31153708710 / 1000000000000), orderedInterval (-12892348107 / 1000000000000) (-12892303833 / 1000000000000)))) (orderedInterval (-940273821 / 1000000000000) (-940272219 / 1000000000000))) = true
  rfl'

theorem compactCertificate513_chunkChecks1_1 :
    compactCertificate513.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3439072549394231 / 4000000000000) 1 (IntervalRat.scale (769 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-6547382981 / 1000000000000) (-6547382979 / 1000000000000), orderedInterval (26415681271 / 1000000000000) (26415681272 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1985549462155199 / 4000000000000) 1 (IntervalRat.scale (769 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (25711778869 / 1000000000000) (25711778870 / 1000000000000), orderedInterval (24902205795 / 1000000000000) (24902205796 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3523392363658891 / 4000000000000) 1 (IntervalRat.scale (769 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (24584250236 / 1000000000000) (24584308501 / 1000000000000), orderedInterval (-10892776209 / 1000000000000) (-10892717944 / 1000000000000)))) (orderedInterval (-11660974812 / 1000000000000) (-11660955521 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3292010188566679 / 4000000000000) 1 (IntervalRat.scale (769 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (17714778812 / 1000000000000) (17714778813 / 1000000000000), orderedInterval (21430315404 / 1000000000000) (21430315405 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2349333806280007 / 4000000000000) 1 (IntervalRat.scale (769 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-19682786149 / 1000000000000) (-19682786148 / 1000000000000), orderedInterval (-26374595573 / 1000000000000) (-26374595572 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2663894142040353 / 4000000000000) 1 (IntervalRat.scale (769 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (20872820000 / 1000000000000) (20872820001 / 1000000000000), orderedInterval (22793295280 / 1000000000000) (22793295281 / 1000000000000)))) (orderedInterval (-4837626717 / 1000000000000) (-4837626642 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2220877210707857 / 4000000000000) 1 (IntervalRat.scale (769 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (1943400381 / 1000000000000) (1943400382 / 1000000000000), orderedInterval (-33807566756 / 1000000000000) (-33807566754 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1962212368108997 / 4000000000000) 1 (IntervalRat.scale (769 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (34184132213 / 1000000000000) (34184132218 / 1000000000000), orderedInterval (11331939566 / 1000000000000) (11331939571 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (568725625178703 / 800000000000) 1 (IntervalRat.scale (769 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (29704285364 / 1000000000000) (29704292331 / 1000000000000), orderedInterval (-3648367712 / 1000000000000) (-3648360745 / 1000000000000)))) (orderedInterval (-1563804833 / 1000000000000) (-1563804450 / 1000000000000))) = true
  rfl'

theorem compactCertificate513_chunkChecks1_2 :
    compactCertificate513.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1573125009634141 / 4000000000000) 1 (IntervalRat.scale (769 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-39402963605 / 1000000000000) (-39402963591 / 1000000000000), orderedInterval (-8082828107 / 1000000000000) (-8082828093 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1333555492549301 / 4000000000000) 1 (IntervalRat.scale (769 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (40150758081 / 1000000000000) (40150758082 / 1000000000000), orderedInterval (17186705424 / 1000000000000) (17186705425 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (834477108270503 / 4000000000000) 1 (IntervalRat.scale (769 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (48788650234 / 1000000000000) (48788671235 / 1000000000000), orderedInterval (-26025398812 / 1000000000000) (-26025377811 / 1000000000000)))) (orderedInterval (18738188 / 1000000000000) (18738651 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (448784564173401 / 4000000000000) 1 (IntervalRat.scale (769 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-8786426972 / 1000000000000) (-8786426935 / 1000000000000), orderedInterval (74852401082 / 1000000000000) (74852401118 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1218537392763203 / 4000000000000) 1 (IntervalRat.scale (769 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-28916728889 / 1000000000000) (-28916728888 / 1000000000000), orderedInterval (-35358846796 / 1000000000000) (-35358846795 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1663808633852131 / 4000000000000) 1 (IntervalRat.scale (769 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (34768632935 / 1000000000000) (34768681931 / 1000000000000), orderedInterval (-17976470770 / 1000000000000) (-17976421773 / 1000000000000)))) (orderedInterval (1722635532 / 1000000000000) (1722639636 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (703522891729497 / 4000000000000) 1 (IntervalRat.scale (769 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (40399088548 / 1000000000000) (40399088549 / 1000000000000), orderedInterval (44466829987 / 1000000000000) (44466829988 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2859781496457337 / 4000000000000) 1 (IntervalRat.scale (769 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-15661408685 / 1000000000000) (-15661408454 / 1000000000000), orderedInterval (25411065213 / 1000000000000) (25411065444 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1910201505737783 / 4000000000000) 1 (IntervalRat.scale (769 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (26531032859 / 1000000000000) (26531032860 / 1000000000000), orderedInterval (25056055968 / 1000000000000) (25056055969 / 1000000000000)))) (orderedInterval (-9562477724 / 1000000000000) (-9562477539 / 1000000000000))) = true
  rfl'

theorem compactCertificate513_chunkChecks1 :
    compactCertificate513.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate513.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate513_chunkChecks1_0
    compactCertificate513_chunkChecks1_1 compactCertificate513_chunkChecks1_2

theorem compactCertificate513_chunkChecks2_0 :
    compactCertificate513.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (769 / 2) 2 (IntervalRat.scale (769 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (36815137706 / 1000000000000) (36815168361 / 1000000000000), orderedInterval (-17378546737 / 1000000000000) (-17378516081 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1132883838935869 / 4000000000000) 2 (IntervalRat.scale (769 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (45176562682 / 1000000000000) (45176562684 / 1000000000000), orderedInterval (14302878560 / 1000000000000) (14302878562 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (366351356944477 / 800000000000) 2 (IntervalRat.scale (769 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (1930282782 / 1000000000000) (1930282783 / 1000000000000), orderedInterval (37233075998 / 1000000000000) (37233075999 / 1000000000000)))) (orderedInterval (-14970425403 / 1000000000000) (-14970413186 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (330572678748983 / 4000000000000) 2 (IntervalRat.scale (769 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (86429052287 / 1000000000000) (86429052623 / 1000000000000), orderedInterval (-15791207966 / 1000000000000) (-15791207631 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (887964714013451 / 4000000000000) 2 (IntervalRat.scale (769 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (14648134327 / 1000000000000) (14648134490 / 1000000000000), orderedInterval (-51542301685 / 1000000000000) (-51542301522 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2410996932283167 / 4000000000000) 2 (IntervalRat.scale (769 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (11102176678 / 1000000000000) (11102176679 / 1000000000000), orderedInterval (30534781110 / 1000000000000) (30534781111 / 1000000000000)))) (orderedInterval (1816146829 / 1000000000000) (1816146904 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1775929428027671 / 4000000000000) 2 (IntervalRat.scale (769 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-36851178112 / 1000000000000) (-36851172717 / 1000000000000), orderedInterval (8752143423 / 1000000000000) (8752148819 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3043085344672883 / 4000000000000) 2 (IntervalRat.scale (769 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (27803870373 / 1000000000000) (27803870446 / 1000000000000), orderedInterval (7966270448 / 1000000000000) (7966270521 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2241522891729497 / 4000000000000) 2 (IntervalRat.scale (769 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (31153664437 / 1000000000000) (31153708710 / 1000000000000), orderedInterval (-12892348107 / 1000000000000) (-12892303833 / 1000000000000)))) (orderedInterval (1760475800 / 1000000000000) (1760478152 / 1000000000000))) = true
  rfl'

theorem compactCertificate513_chunkChecks2_1 :
    compactCertificate513.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3439072549394231 / 4000000000000) 2 (IntervalRat.scale (769 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-6547382981 / 1000000000000) (-6547382979 / 1000000000000), orderedInterval (26415681271 / 1000000000000) (26415681272 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1985549462155199 / 4000000000000) 2 (IntervalRat.scale (769 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (25711778869 / 1000000000000) (25711778870 / 1000000000000), orderedInterval (24902205795 / 1000000000000) (24902205796 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3523392363658891 / 4000000000000) 2 (IntervalRat.scale (769 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (24584250236 / 1000000000000) (24584308501 / 1000000000000), orderedInterval (-10892776209 / 1000000000000) (-10892717944 / 1000000000000)))) (orderedInterval (-27303067757 / 1000000000000) (-27303023559 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3292010188566679 / 4000000000000) 2 (IntervalRat.scale (769 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (17714778812 / 1000000000000) (17714778813 / 1000000000000), orderedInterval (21430315404 / 1000000000000) (21430315405 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2349333806280007 / 4000000000000) 2 (IntervalRat.scale (769 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-19682786149 / 1000000000000) (-19682786148 / 1000000000000), orderedInterval (-26374595573 / 1000000000000) (-26374595572 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2663894142040353 / 4000000000000) 2 (IntervalRat.scale (769 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (20872820000 / 1000000000000) (20872820001 / 1000000000000), orderedInterval (22793295280 / 1000000000000) (22793295281 / 1000000000000)))) (orderedInterval (6137608395 / 1000000000000) (6137608519 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2220877210707857 / 4000000000000) 2 (IntervalRat.scale (769 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (1943400381 / 1000000000000) (1943400382 / 1000000000000), orderedInterval (-33807566756 / 1000000000000) (-33807566754 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1962212368108997 / 4000000000000) 2 (IntervalRat.scale (769 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (34184132213 / 1000000000000) (34184132218 / 1000000000000), orderedInterval (11331939566 / 1000000000000) (11331939571 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (568725625178703 / 800000000000) 2 (IntervalRat.scale (769 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (29704285364 / 1000000000000) (29704292331 / 1000000000000), orderedInterval (-3648367712 / 1000000000000) (-3648360745 / 1000000000000)))) (orderedInterval (541573356 / 1000000000000) (541574047 / 1000000000000))) = true
  rfl'

theorem compactCertificate513_chunkChecks2_2 :
    compactCertificate513.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1573125009634141 / 4000000000000) 2 (IntervalRat.scale (769 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-39402963605 / 1000000000000) (-39402963591 / 1000000000000), orderedInterval (-8082828107 / 1000000000000) (-8082828093 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1333555492549301 / 4000000000000) 2 (IntervalRat.scale (769 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (40150758081 / 1000000000000) (40150758082 / 1000000000000), orderedInterval (17186705424 / 1000000000000) (17186705425 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (834477108270503 / 4000000000000) 2 (IntervalRat.scale (769 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (48788650234 / 1000000000000) (48788671235 / 1000000000000), orderedInterval (-26025398812 / 1000000000000) (-26025377811 / 1000000000000)))) (orderedInterval (-5350405261 / 1000000000000) (-5350404971 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (448784564173401 / 4000000000000) 2 (IntervalRat.scale (769 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-8786426972 / 1000000000000) (-8786426935 / 1000000000000), orderedInterval (74852401082 / 1000000000000) (74852401118 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1218537392763203 / 4000000000000) 2 (IntervalRat.scale (769 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-28916728889 / 1000000000000) (-28916728888 / 1000000000000), orderedInterval (-35358846796 / 1000000000000) (-35358846795 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1663808633852131 / 4000000000000) 2 (IntervalRat.scale (769 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (34768632935 / 1000000000000) (34768681931 / 1000000000000), orderedInterval (-17976470770 / 1000000000000) (-17976421773 / 1000000000000)))) (orderedInterval (2688295882 / 1000000000000) (2688300329 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (703522891729497 / 4000000000000) 2 (IntervalRat.scale (769 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (40399088548 / 1000000000000) (40399088549 / 1000000000000), orderedInterval (44466829987 / 1000000000000) (44466829988 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2859781496457337 / 4000000000000) 2 (IntervalRat.scale (769 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-15661408685 / 1000000000000) (-15661408454 / 1000000000000), orderedInterval (25411065213 / 1000000000000) (25411065444 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1910201505737783 / 4000000000000) 2 (IntervalRat.scale (769 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (26531032859 / 1000000000000) (26531032860 / 1000000000000), orderedInterval (25056055968 / 1000000000000) (25056055969 / 1000000000000)))) (orderedInterval (3244966840 / 1000000000000) (3244967126 / 1000000000000))) = true
  rfl'

theorem compactCertificate513_chunkChecks2 :
    compactCertificate513.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate513.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate513_chunkChecks2_0
    compactCertificate513_chunkChecks2_1 compactCertificate513_chunkChecks2_2

theorem compactCertificate513_chunkChecks3_0 :
    compactCertificate513.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (769 / 2) 3 (IntervalRat.scale (769 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (36815137706 / 1000000000000) (36815168361 / 1000000000000), orderedInterval (-17378546737 / 1000000000000) (-17378516081 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1132883838935869 / 4000000000000) 3 (IntervalRat.scale (769 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (45176562682 / 1000000000000) (45176562684 / 1000000000000), orderedInterval (14302878560 / 1000000000000) (14302878562 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (366351356944477 / 800000000000) 3 (IntervalRat.scale (769 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (1930282782 / 1000000000000) (1930282783 / 1000000000000), orderedInterval (37233075998 / 1000000000000) (37233075999 / 1000000000000)))) (orderedInterval (3182725957 / 1000000000000) (3182738180 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (330572678748983 / 4000000000000) 3 (IntervalRat.scale (769 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (86429052287 / 1000000000000) (86429052623 / 1000000000000), orderedInterval (-15791207966 / 1000000000000) (-15791207631 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (887964714013451 / 4000000000000) 3 (IntervalRat.scale (769 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (14648134327 / 1000000000000) (14648134490 / 1000000000000), orderedInterval (-51542301685 / 1000000000000) (-51542301522 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2410996932283167 / 4000000000000) 3 (IntervalRat.scale (769 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (11102176678 / 1000000000000) (11102176679 / 1000000000000), orderedInterval (30534781110 / 1000000000000) (30534781111 / 1000000000000)))) (orderedInterval (8717946788 / 1000000000000) (8717946899 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1775929428027671 / 4000000000000) 3 (IntervalRat.scale (769 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-36851178112 / 1000000000000) (-36851172717 / 1000000000000), orderedInterval (8752143423 / 1000000000000) (8752148819 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3043085344672883 / 4000000000000) 3 (IntervalRat.scale (769 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (27803870373 / 1000000000000) (27803870446 / 1000000000000), orderedInterval (7966270448 / 1000000000000) (7966270521 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2241522891729497 / 4000000000000) 3 (IntervalRat.scale (769 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (31153664437 / 1000000000000) (31153708710 / 1000000000000), orderedInterval (-12892348107 / 1000000000000) (-12892303833 / 1000000000000)))) (orderedInterval (2863246144 / 1000000000000) (2863249601 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate513_chunkChecks3_1 :
    compactCertificate513.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3439072549394231 / 4000000000000) 3 (IntervalRat.scale (769 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-6547382981 / 1000000000000) (-6547382979 / 1000000000000), orderedInterval (26415681271 / 1000000000000) (26415681272 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1985549462155199 / 4000000000000) 3 (IntervalRat.scale (769 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (25711778869 / 1000000000000) (25711778870 / 1000000000000), orderedInterval (24902205795 / 1000000000000) (24902205796 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3523392363658891 / 4000000000000) 3 (IntervalRat.scale (769 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (24584250236 / 1000000000000) (24584308501 / 1000000000000), orderedInterval (-10892776209 / 1000000000000) (-10892717944 / 1000000000000)))) (orderedInterval (67195944298 / 1000000000000) (67196045480 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3292010188566679 / 4000000000000) 3 (IntervalRat.scale (769 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (17714778812 / 1000000000000) (17714778813 / 1000000000000), orderedInterval (21430315404 / 1000000000000) (21430315405 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2349333806280007 / 4000000000000) 3 (IntervalRat.scale (769 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-19682786149 / 1000000000000) (-19682786148 / 1000000000000), orderedInterval (-26374595573 / 1000000000000) (-26374595572 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2663894142040353 / 4000000000000) 3 (IntervalRat.scale (769 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (20872820000 / 1000000000000) (20872820001 / 1000000000000), orderedInterval (22793295280 / 1000000000000) (22793295281 / 1000000000000)))) (orderedInterval (13266724624 / 1000000000000) (13266724834 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2220877210707857 / 4000000000000) 3 (IntervalRat.scale (769 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (1943400381 / 1000000000000) (1943400382 / 1000000000000), orderedInterval (-33807566756 / 1000000000000) (-33807566754 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1962212368108997 / 4000000000000) 3 (IntervalRat.scale (769 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (34184132213 / 1000000000000) (34184132218 / 1000000000000), orderedInterval (11331939566 / 1000000000000) (11331939571 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (568725625178703 / 800000000000) 3 (IntervalRat.scale (769 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (29704285364 / 1000000000000) (29704292331 / 1000000000000), orderedInterval (-3648367712 / 1000000000000) (-3648360745 / 1000000000000)))) (orderedInterval (3111168045 / 1000000000000) (3111169297 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate513_chunkChecks3_2 :
    compactCertificate513.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1573125009634141 / 4000000000000) 3 (IntervalRat.scale (769 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-39402963605 / 1000000000000) (-39402963591 / 1000000000000), orderedInterval (-8082828107 / 1000000000000) (-8082828093 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1333555492549301 / 4000000000000) 3 (IntervalRat.scale (769 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (40150758081 / 1000000000000) (40150758082 / 1000000000000), orderedInterval (17186705424 / 1000000000000) (17186705425 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (834477108270503 / 4000000000000) 3 (IntervalRat.scale (769 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (48788650234 / 1000000000000) (48788671235 / 1000000000000), orderedInterval (-26025398812 / 1000000000000) (-26025377811 / 1000000000000)))) (orderedInterval (-599600394 / 1000000000000) (-599600199 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (448784564173401 / 4000000000000) 3 (IntervalRat.scale (769 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-8786426972 / 1000000000000) (-8786426935 / 1000000000000), orderedInterval (74852401082 / 1000000000000) (74852401118 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1218537392763203 / 4000000000000) 3 (IntervalRat.scale (769 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-28916728889 / 1000000000000) (-28916728888 / 1000000000000), orderedInterval (-35358846796 / 1000000000000) (-35358846795 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1663808633852131 / 4000000000000) 3 (IntervalRat.scale (769 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (34768632935 / 1000000000000) (34768681931 / 1000000000000), orderedInterval (-17976470770 / 1000000000000) (-17976421773 / 1000000000000)))) (orderedInterval (-2115784771 / 1000000000000) (-2115779963 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (703522891729497 / 4000000000000) 3 (IntervalRat.scale (769 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (40399088548 / 1000000000000) (40399088549 / 1000000000000), orderedInterval (44466829987 / 1000000000000) (44466829988 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2859781496457337 / 4000000000000) 3 (IntervalRat.scale (769 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-15661408685 / 1000000000000) (-15661408454 / 1000000000000), orderedInterval (25411065213 / 1000000000000) (25411065444 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1910201505737783 / 4000000000000) 3 (IntervalRat.scale (769 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (26531032859 / 1000000000000) (26531032860 / 1000000000000), orderedInterval (25056055968 / 1000000000000) (25056055969 / 1000000000000)))) (orderedInterval (22270741569 / 1000000000000) (22270742031 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate513_chunkChecks3 :
    compactCertificate513.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate513.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate513_chunkChecks3_0
    compactCertificate513_chunkChecks3_1 compactCertificate513_chunkChecks3_2

theorem compactCertificate513_chunkChecks4_0 :
    compactCertificate513.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (769 / 2) 4 (IntervalRat.scale (769 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (36815137706 / 1000000000000) (36815168361 / 1000000000000), orderedInterval (-17378546737 / 1000000000000) (-17378516081 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1132883838935869 / 4000000000000) 4 (IntervalRat.scale (769 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (45176562682 / 1000000000000) (45176562684 / 1000000000000), orderedInterval (14302878560 / 1000000000000) (14302878562 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (366351356944477 / 800000000000) 4 (IntervalRat.scale (769 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (1930282782 / 1000000000000) (1930282783 / 1000000000000), orderedInterval (37233075998 / 1000000000000) (37233075999 / 1000000000000)))) (orderedInterval (14927410271 / 1000000000000) (14927422532 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (330572678748983 / 4000000000000) 4 (IntervalRat.scale (769 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (86429052287 / 1000000000000) (86429052623 / 1000000000000), orderedInterval (-15791207966 / 1000000000000) (-15791207631 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (887964714013451 / 4000000000000) 4 (IntervalRat.scale (769 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (14648134327 / 1000000000000) (14648134490 / 1000000000000), orderedInterval (-51542301685 / 1000000000000) (-51542301522 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2410996932283167 / 4000000000000) 4 (IntervalRat.scale (769 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (11102176678 / 1000000000000) (11102176679 / 1000000000000), orderedInterval (30534781110 / 1000000000000) (30534781111 / 1000000000000)))) (orderedInterval (-4754148687 / 1000000000000) (-4754148518 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1775929428027671 / 4000000000000) 4 (IntervalRat.scale (769 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-36851178112 / 1000000000000) (-36851172717 / 1000000000000), orderedInterval (8752143423 / 1000000000000) (8752148819 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3043085344672883 / 4000000000000) 4 (IntervalRat.scale (769 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (27803870373 / 1000000000000) (27803870446 / 1000000000000), orderedInterval (7966270448 / 1000000000000) (7966270521 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2241522891729497 / 4000000000000) 4 (IntervalRat.scale (769 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (31153664437 / 1000000000000) (31153708710 / 1000000000000), orderedInterval (-12892348107 / 1000000000000) (-12892303833 / 1000000000000)))) (orderedInterval (-9761247336 / 1000000000000) (-9761242232 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate513_chunkChecks4_1 :
    compactCertificate513.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3439072549394231 / 4000000000000) 4 (IntervalRat.scale (769 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-6547382981 / 1000000000000) (-6547382979 / 1000000000000), orderedInterval (26415681271 / 1000000000000) (26415681272 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1985549462155199 / 4000000000000) 4 (IntervalRat.scale (769 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (25711778869 / 1000000000000) (25711778870 / 1000000000000), orderedInterval (24902205795 / 1000000000000) (24902205796 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3523392363658891 / 4000000000000) 4 (IntervalRat.scale (769 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (24584250236 / 1000000000000) (24584308501 / 1000000000000), orderedInterval (-10892776209 / 1000000000000) (-10892717944 / 1000000000000)))) (orderedInterval (130285633846 / 1000000000000) (130285865800 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3292010188566679 / 4000000000000) 4 (IntervalRat.scale (769 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (17714778812 / 1000000000000) (17714778813 / 1000000000000), orderedInterval (21430315404 / 1000000000000) (21430315405 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2349333806280007 / 4000000000000) 4 (IntervalRat.scale (769 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-19682786149 / 1000000000000) (-19682786148 / 1000000000000), orderedInterval (-26374595573 / 1000000000000) (-26374595572 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2663894142040353 / 4000000000000) 4 (IntervalRat.scale (769 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (20872820000 / 1000000000000) (20872820001 / 1000000000000), orderedInterval (22793295280 / 1000000000000) (22793295281 / 1000000000000)))) (orderedInterval (-17865996543 / 1000000000000) (-17865996180 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2220877210707857 / 4000000000000) 4 (IntervalRat.scale (769 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (1943400381 / 1000000000000) (1943400382 / 1000000000000), orderedInterval (-33807566756 / 1000000000000) (-33807566754 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1962212368108997 / 4000000000000) 4 (IntervalRat.scale (769 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (34184132213 / 1000000000000) (34184132218 / 1000000000000), orderedInterval (11331939566 / 1000000000000) (11331939571 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (568725625178703 / 800000000000) 4 (IntervalRat.scale (769 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (29704285364 / 1000000000000) (29704292331 / 1000000000000), orderedInterval (-3648367712 / 1000000000000) (-3648360745 / 1000000000000)))) (orderedInterval (3786139072 / 1000000000000) (3786141357 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate513_chunkChecks4_2 :
    compactCertificate513.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1573125009634141 / 4000000000000) 4 (IntervalRat.scale (769 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-39402963605 / 1000000000000) (-39402963591 / 1000000000000), orderedInterval (-8082828107 / 1000000000000) (-8082828093 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1333555492549301 / 4000000000000) 4 (IntervalRat.scale (769 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (40150758081 / 1000000000000) (40150758082 / 1000000000000), orderedInterval (17186705424 / 1000000000000) (17186705425 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (834477108270503 / 4000000000000) 4 (IntervalRat.scale (769 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (48788650234 / 1000000000000) (48788671235 / 1000000000000), orderedInterval (-26025398812 / 1000000000000) (-26025377811 / 1000000000000)))) (orderedInterval (5752043220 / 1000000000000) (5752043364 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (448784564173401 / 4000000000000) 4 (IntervalRat.scale (769 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-8786426972 / 1000000000000) (-8786426935 / 1000000000000), orderedInterval (74852401082 / 1000000000000) (74852401118 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1218537392763203 / 4000000000000) 4 (IntervalRat.scale (769 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-28916728889 / 1000000000000) (-28916728888 / 1000000000000), orderedInterval (-35358846796 / 1000000000000) (-35358846795 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1663808633852131 / 4000000000000) 4 (IntervalRat.scale (769 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (34768632935 / 1000000000000) (34768681931 / 1000000000000), orderedInterval (-17976470770 / 1000000000000) (-17976421773 / 1000000000000)))) (orderedInterval (-3378738016 / 1000000000000) (-3378732804 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (703522891729497 / 4000000000000) 4 (IntervalRat.scale (769 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (40399088548 / 1000000000000) (40399088549 / 1000000000000), orderedInterval (44466829987 / 1000000000000) (44466829988 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2859781496457337 / 4000000000000) 4 (IntervalRat.scale (769 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-15661408685 / 1000000000000) (-15661408454 / 1000000000000), orderedInterval (25411065213 / 1000000000000) (25411065444 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1910201505737783 / 4000000000000) 4 (IntervalRat.scale (769 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (26531032859 / 1000000000000) (26531032860 / 1000000000000), orderedInterval (25056055968 / 1000000000000) (25056055969 / 1000000000000)))) (orderedInterval (3289214575 / 1000000000000) (3289215348 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate513_chunkChecks4 :
    compactCertificate513.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate513.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate513_chunkChecks4_0
    compactCertificate513_chunkChecks4_1 compactCertificate513_chunkChecks4_2

theorem compactCertificate513_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate513.chunkCheck r b = true :=
  compactCertificate513.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate513_chunkChecks0
    · exact compactCertificate513_chunkChecks1
    · exact compactCertificate513_chunkChecks2
    · exact compactCertificate513_chunkChecks3
    · exact compactCertificate513_chunkChecks4)

theorem compactCertificate513_coefficient0 :
    compactCertificate513.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate513_coefficient1 :
    compactCertificate513.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate513_coefficient2 :
    compactCertificate513.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate513_coefficient3 :
    compactCertificate513.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate513_coefficient4 :
    compactCertificate513.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate513_coefficients : ∀ r : Fin 5,
    compactCertificate513.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate513_coefficient0
  · exact compactCertificate513_coefficient1
  · exact compactCertificate513_coefficient2
  · exact compactCertificate513_coefficient3
  · exact compactCertificate513_coefficient4

theorem compactCertificate513_lower : (1 : ℚ) ≤ compactCertificate513.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate513, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate513_proves {t : ℝ} (ht : t ∈ compactCertificate513.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate513.proves compactCertificate513_states compactCertificate513_chunks
    compactCertificate513_coefficients compactCertificate513_lower ht

end Erdos232
