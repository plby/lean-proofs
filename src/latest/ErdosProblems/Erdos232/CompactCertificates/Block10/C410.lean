/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate410 : CompactCertificate where
  left := 281
  right := 282
  center := 563 / 2
  grid := fun i =>
    match i.val with
    | 0 => 90
    | 1 => 66
    | 2 => 107
    | 3 => 19
    | 4 => 52
    | 5 => 141
    | 6 => 104
    | 7 => 177
    | 8 => 131
    | 9 => 200
    | 10 => 116
    | 11 => 205
    | 12 => 192
    | 13 => 137
    | 14 => 155
    | 15 => 129
    | 16 => 114
    | 17 => 166
    | 18 => 92
    | 19 => 78
    | 20 => 49
    | 21 => 26
    | 22 => 71
    | 23 => 97
    | 24 => 41
    | 25 => 167
    | _ => 111
  point := fun i =>
    match i.val with
    | 0 => 563 / 2
    | 1 => 829406503668263 / 4000000000000
    | 2 => 268213022054279 / 800000000000
    | 3 => 242018749201141 / 4000000000000
    | 4 => 650096403107377 / 4000000000000
    | 5 => 1765138196196909 / 4000000000000
    | 6 => 1300192806215317 / 4000000000000
    | 7 => 2227902534526441 / 4000000000000
    | 8 => 1641062923333819 / 4000000000000
    | 9 => 2517812542664437 / 4000000000000
    | 10 => 1453659749276173 / 4000000000000
    | 11 => 2579544734382257 / 4000000000000
    | 12 => 2410145300602133 / 4000000000000
    | 13 => 1719993410839589 / 4000000000000
    | 14 => 1950289209322131 / 4000000000000
    | 15 => 1625947814861539 / 4000000000000
    | 16 => 1436574204480319 / 4000000000000
    | 17 => 416375197627581 / 800000000000
    | 18 => 1151715709264007 / 4000000000000
    | 19 => 976322161645327 / 4000000000000
    | 20 => 610937076666181 / 4000000000000
    | 21 => 328563991716027 / 4000000000000
    | 22 => 892115152309081 / 4000000000000
    | 23 => 1218106971207737 / 4000000000000
    | 24 => 515062923333819 / 4000000000000
    | 25 => 2093702187913499 / 4000000000000
    | _ => 1398496030858741 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-21043304689 / 1000000000000) (-21043303579 / 1000000000000), orderedInterval (42683692109 / 1000000000000) (42683693219 / 1000000000000))
    | 1 => (orderedInterval (39411357964 / 1000000000000) (39411357965 / 1000000000000), orderedInterval (38853485960 / 1000000000000) (38853485961 / 1000000000000))
    | 2 => (orderedInterval (4311770806 / 1000000000000) (4311770811 / 1000000000000), orderedInterval (-43368382765 / 1000000000000) (-43368382760 / 1000000000000))
    | 3 => (orderedInterval (-102536916538 / 1000000000000) (-102536916501 / 1000000000000), orderedInterval (3612762311 / 1000000000000) (3612762348 / 1000000000000))
    | 4 => (orderedInterval (-3383533511 / 1000000000000) (-3383533502 / 1000000000000), orderedInterval (62505603556 / 1000000000000) (62505603565 / 1000000000000))
    | 5 => (orderedInterval (29631694805 / 1000000000000) (29631737045 / 1000000000000), orderedInterval (-23795172654 / 1000000000000) (-23795130414 / 1000000000000))
    | 6 => (orderedInterval (-34456957186 / 1000000000000) (-34456887974 / 1000000000000), orderedInterval (27824526423 / 1000000000000) (27824595634 / 1000000000000))
    | 7 => (orderedInterval (-33531128609 / 1000000000000) (-33531125331 / 1000000000000), orderedInterval (4349475800 / 1000000000000) (4349479079 / 1000000000000))
    | 8 => (orderedInterval (18809859199 / 1000000000000) (18809860015 / 1000000000000), orderedInterval (-34633836652 / 1000000000000) (-34633835836 / 1000000000000))
    | 9 => (orderedInterval (29884976052 / 1000000000000) (29885017427 / 1000000000000), orderedInterval (-10899060985 / 1000000000000) (-10899019609 / 1000000000000))
    | 10 => (orderedInterval (-9327982565 / 1000000000000) (-9327982537 / 1000000000000), orderedInterval (40814320262 / 1000000000000) (40814320289 / 1000000000000))
    | 11 => (orderedInterval (-31333228792 / 1000000000000) (-31333225835 / 1000000000000), orderedInterval (2350268622 / 1000000000000) (2350271579 / 1000000000000))
    | 12 => (orderedInterval (4398234452 / 1000000000000) (4398234453 / 1000000000000), orderedInterval (32202289293 / 1000000000000) (32202289294 / 1000000000000))
    | 13 => (orderedInterval (-14460073635 / 1000000000000) (-14460073634 / 1000000000000), orderedInterval (-35640215506 / 1000000000000) (-35640215505 / 1000000000000))
    | 14 => (orderedInterval (-35671601623 / 1000000000000) (-35671601567 / 1000000000000), orderedInterval (-5727900995 / 1000000000000) (-5727900939 / 1000000000000))
    | 15 => (orderedInterval (-35875757956 / 1000000000000) (-35875725290 / 1000000000000), orderedInterval (16749827706 / 1000000000000) (16749860371 / 1000000000000))
    | 16 => (orderedInterval (41121759639 / 1000000000000) (41121762512 / 1000000000000), orderedInterval (-9090773666 / 1000000000000) (-9090770793 / 1000000000000))
    | 17 => (orderedInterval (-8660290777 / 1000000000000) (-8660290766 / 1000000000000), orderedInterval (33892909954 / 1000000000000) (33892909966 / 1000000000000))
    | 18 => (orderedInterval (-14462181489 / 1000000000000) (-14462181320 / 1000000000000), orderedInterval (44767476144 / 1000000000000) (44767476313 / 1000000000000))
    | 19 => (orderedInterval (-9082916314 / 1000000000000) (-9082916280 / 1000000000000), orderedInterval (50275369515 / 1000000000000) (50275369549 / 1000000000000))
    | 20 => (orderedInterval (26277752606 / 1000000000000) (26277754105 / 1000000000000), orderedInterval (-59057605631 / 1000000000000) (-59057604133 / 1000000000000))
    | 21 => (orderedInterval (83360814374 / 1000000000000) (83360814375 / 1000000000000), orderedInterval (27797892217 / 1000000000000) (27797892218 / 1000000000000))
    | 22 => (orderedInterval (-36828050978 / 1000000000000) (-36828050977 / 1000000000000), orderedInterval (-38623040076 / 1000000000000) (-38623040075 / 1000000000000))
    | 23 => (orderedInterval (-24951323460 / 1000000000000) (-24951323459 / 1000000000000), orderedInterval (-38272924789 / 1000000000000) (-38272924788 / 1000000000000))
    | 24 => (orderedInterval (-47663258836 / 1000000000000) (-47663258835 / 1000000000000), orderedInterval (-51508564252 / 1000000000000) (-51508564251 / 1000000000000))
    | 25 => (orderedInterval (14705067877 / 1000000000000) (14705068053 / 1000000000000), orderedInterval (-31637107070 / 1000000000000) (-31637106893 / 1000000000000))
    | _ => (orderedInterval (-42357219643 / 1000000000000) (-42357218726 / 1000000000000), orderedInterval (5231058707 / 1000000000000) (5231059624 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-7720572301 / 1000000000000) (-7720571841 / 1000000000000)
      | 1 => orderedInterval (-1117595437 / 1000000000000) (-1117592399 / 1000000000000)
      | 2 => orderedInterval (1488831240 / 1000000000000) (1488831377 / 1000000000000)
      | 3 => orderedInterval (-10455536657 / 1000000000000) (-10455528771 / 1000000000000)
      | 4 => orderedInterval (-1266268877 / 1000000000000) (-1266268842 / 1000000000000)
      | 5 => orderedInterval (-2989280901 / 1000000000000) (-2989280331 / 1000000000000)
      | 6 => orderedInterval (3681965472 / 1000000000000) (3681965620 / 1000000000000)
      | 7 => orderedInterval (1208486937 / 1000000000000) (1208486972 / 1000000000000)
      | _ => orderedInterval (6462989375 / 1000000000000) (6462989640 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (14154016482 / 1000000000000) (14154016945 / 1000000000000)
      | 1 => orderedInterval (3960960772 / 1000000000000) (3960965518 / 1000000000000)
      | 2 => orderedInterval (-1485352034 / 1000000000000) (-1485351777 / 1000000000000)
      | 3 => orderedInterval (8999794738 / 1000000000000) (8999812375 / 1000000000000)
      | 4 => orderedInterval (-6342273401 / 1000000000000) (-6342273345 / 1000000000000)
      | 5 => orderedInterval (2547499937 / 1000000000000) (2547500731 / 1000000000000)
      | 6 => orderedInterval (-10831949908 / 1000000000000) (-10831949786 / 1000000000000)
      | 7 => orderedInterval (3717582304 / 1000000000000) (3717582335 / 1000000000000)
      | _ => orderedInterval (3427540043 / 1000000000000) (3427540393 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (7732392049 / 1000000000000) (7732392517 / 1000000000000)
      | 1 => orderedInterval (5152302040 / 1000000000000) (5152309490 / 1000000000000)
      | 2 => orderedInterval (-5009206535 / 1000000000000) (-5009206047 / 1000000000000)
      | 3 => orderedInterval (51047394796 / 1000000000000) (51047434322 / 1000000000000)
      | 4 => orderedInterval (3035321595 / 1000000000000) (3035321686 / 1000000000000)
      | 5 => orderedInterval (5443240074 / 1000000000000) (5443241190 / 1000000000000)
      | 6 => orderedInterval (-3019083496 / 1000000000000) (-3019083389 / 1000000000000)
      | 7 => orderedInterval (-2644491088 / 1000000000000) (-2644491057 / 1000000000000)
      | _ => orderedInterval (-8072798754 / 1000000000000) (-8072798276 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-12790919525 / 1000000000000) (-12790919053 / 1000000000000)
      | 1 => orderedInterval (-6973597572 / 1000000000000) (-6973585898 / 1000000000000)
      | 2 => orderedInterval (3648140814 / 1000000000000) (3648141750 / 1000000000000)
      | 3 => orderedInterval (-32357004699 / 1000000000000) (-32356916219 / 1000000000000)
      | 4 => orderedInterval (17551839661 / 1000000000000) (17551839816 / 1000000000000)
      | 5 => orderedInterval (-7166905155 / 1000000000000) (-7166903583 / 1000000000000)
      | 6 => orderedInterval (9832337900 / 1000000000000) (9832337999 / 1000000000000)
      | 7 => orderedInterval (-4127073678 / 1000000000000) (-4127073646 / 1000000000000)
      | _ => orderedInterval (-14617332576 / 1000000000000) (-14617331903 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-7632649723 / 1000000000000) (-7632649244 / 1000000000000)
      | 1 => orderedInterval (-12682843207 / 1000000000000) (-12682824869 / 1000000000000)
      | 2 => orderedInterval (17875815035 / 1000000000000) (17875816844 / 1000000000000)
      | 3 => orderedInterval (-257128654260 / 1000000000000) (-257128455850 / 1000000000000)
      | 4 => orderedInterval (-7611319537 / 1000000000000) (-7611319268 / 1000000000000)
      | 5 => orderedInterval (-10576356676 / 1000000000000) (-10576354445 / 1000000000000)
      | 6 => orderedInterval (2825803883 / 1000000000000) (2825803979 / 1000000000000)
      | 7 => orderedInterval (2966318698 / 1000000000000) (2966318731 / 1000000000000)
      | _ => orderedInterval (4693184648 / 1000000000000) (4693185633 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-10706981149 / 1000000000000) (-10706968575 / 1000000000000)
    | 1 => orderedInterval (18147818933 / 1000000000000) (18147843389 / 1000000000000)
    | 2 => orderedInterval (53665070681 / 1000000000000) (53665120436 / 1000000000000)
    | 3 => orderedInterval (-47000514830 / 1000000000000) (-47000410737 / 1000000000000)
    | _ => orderedInterval (-267270701139 / 1000000000000) (-267270478489 / 1000000000000)

theorem compactCertificate410_stateChecks0 :
    compactCertificate410.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (563 / 2)) (orderedInterval (-21043304689 / 1000000000000) (-21043303579 / 1000000000000), orderedInterval (42683692109 / 1000000000000) (42683693219 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (829406503668263 / 4000000000000)) (orderedInterval (39411357964 / 1000000000000) (39411357965 / 1000000000000), orderedInterval (38853485960 / 1000000000000) (38853485961 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 107 12 (268213022054279 / 800000000000)) (orderedInterval (4311770806 / 1000000000000) (4311770811 / 1000000000000), orderedInterval (-43368382765 / 1000000000000) (-43368382760 / 1000000000000))) = true
  rfl'

theorem compactCertificate410_stateChecks1 :
    compactCertificate410.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 19 12 (242018749201141 / 4000000000000)) (orderedInterval (-102536916538 / 1000000000000) (-102536916501 / 1000000000000), orderedInterval (3612762311 / 1000000000000) (3612762348 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (650096403107377 / 4000000000000)) (orderedInterval (-3383533511 / 1000000000000) (-3383533502 / 1000000000000), orderedInterval (62505603556 / 1000000000000) (62505603565 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 141 12 (1765138196196909 / 4000000000000)) (orderedInterval (29631694805 / 1000000000000) (29631737045 / 1000000000000), orderedInterval (-23795172654 / 1000000000000) (-23795130414 / 1000000000000))) = true
  rfl'

theorem compactCertificate410_stateChecks2 :
    compactCertificate410.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 104 12 (1300192806215317 / 4000000000000)) (orderedInterval (-34456957186 / 1000000000000) (-34456887974 / 1000000000000), orderedInterval (27824526423 / 1000000000000) (27824595634 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 177 12 (2227902534526441 / 4000000000000)) (orderedInterval (-33531128609 / 1000000000000) (-33531125331 / 1000000000000), orderedInterval (4349475800 / 1000000000000) (4349479079 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 131 12 (1641062923333819 / 4000000000000)) (orderedInterval (18809859199 / 1000000000000) (18809860015 / 1000000000000), orderedInterval (-34633836652 / 1000000000000) (-34633835836 / 1000000000000))) = true
  rfl'

theorem compactCertificate410_stateChecks3 :
    compactCertificate410.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 200 12 (2517812542664437 / 4000000000000)) (orderedInterval (29884976052 / 1000000000000) (29885017427 / 1000000000000), orderedInterval (-10899060985 / 1000000000000) (-10899019609 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 116 12 (1453659749276173 / 4000000000000)) (orderedInterval (-9327982565 / 1000000000000) (-9327982537 / 1000000000000), orderedInterval (40814320262 / 1000000000000) (40814320289 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 205 12 (2579544734382257 / 4000000000000)) (orderedInterval (-31333228792 / 1000000000000) (-31333225835 / 1000000000000), orderedInterval (2350268622 / 1000000000000) (2350271579 / 1000000000000))) = true
  rfl'

theorem compactCertificate410_stateChecks4 :
    compactCertificate410.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 192 12 (2410145300602133 / 4000000000000)) (orderedInterval (4398234452 / 1000000000000) (4398234453 / 1000000000000), orderedInterval (32202289293 / 1000000000000) (32202289294 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 137 12 (1719993410839589 / 4000000000000)) (orderedInterval (-14460073635 / 1000000000000) (-14460073634 / 1000000000000), orderedInterval (-35640215506 / 1000000000000) (-35640215505 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 155 12 (1950289209322131 / 4000000000000)) (orderedInterval (-35671601623 / 1000000000000) (-35671601567 / 1000000000000), orderedInterval (-5727900995 / 1000000000000) (-5727900939 / 1000000000000))) = true
  rfl'

theorem compactCertificate410_stateChecks5 :
    compactCertificate410.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 129 12 (1625947814861539 / 4000000000000)) (orderedInterval (-35875757956 / 1000000000000) (-35875725290 / 1000000000000), orderedInterval (16749827706 / 1000000000000) (16749860371 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 114 12 (1436574204480319 / 4000000000000)) (orderedInterval (41121759639 / 1000000000000) (41121762512 / 1000000000000), orderedInterval (-9090773666 / 1000000000000) (-9090770793 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 166 12 (416375197627581 / 800000000000)) (orderedInterval (-8660290777 / 1000000000000) (-8660290766 / 1000000000000), orderedInterval (33892909954 / 1000000000000) (33892909966 / 1000000000000))) = true
  rfl'

theorem compactCertificate410_stateChecks6 :
    compactCertificate410.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 92 12 (1151715709264007 / 4000000000000)) (orderedInterval (-14462181489 / 1000000000000) (-14462181320 / 1000000000000), orderedInterval (44767476144 / 1000000000000) (44767476313 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (976322161645327 / 4000000000000)) (orderedInterval (-9082916314 / 1000000000000) (-9082916280 / 1000000000000), orderedInterval (50275369515 / 1000000000000) (50275369549 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (610937076666181 / 4000000000000)) (orderedInterval (26277752606 / 1000000000000) (26277754105 / 1000000000000), orderedInterval (-59057605631 / 1000000000000) (-59057604133 / 1000000000000))) = true
  rfl'

theorem compactCertificate410_stateChecks7 :
    compactCertificate410.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (328563991716027 / 4000000000000)) (orderedInterval (83360814374 / 1000000000000) (83360814375 / 1000000000000), orderedInterval (27797892217 / 1000000000000) (27797892218 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (892115152309081 / 4000000000000)) (orderedInterval (-36828050978 / 1000000000000) (-36828050977 / 1000000000000), orderedInterval (-38623040076 / 1000000000000) (-38623040075 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 97 12 (1218106971207737 / 4000000000000)) (orderedInterval (-24951323460 / 1000000000000) (-24951323459 / 1000000000000), orderedInterval (-38272924789 / 1000000000000) (-38272924788 / 1000000000000))) = true
  rfl'

theorem compactCertificate410_stateChecks8 :
    compactCertificate410.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (515062923333819 / 4000000000000)) (orderedInterval (-47663258836 / 1000000000000) (-47663258835 / 1000000000000), orderedInterval (-51508564252 / 1000000000000) (-51508564251 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 167 12 (2093702187913499 / 4000000000000)) (orderedInterval (14705067877 / 1000000000000) (14705068053 / 1000000000000), orderedInterval (-31637107070 / 1000000000000) (-31637106893 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 111 12 (1398496030858741 / 4000000000000)) (orderedInterval (-42357219643 / 1000000000000) (-42357218726 / 1000000000000), orderedInterval (5231058707 / 1000000000000) (5231059624 / 1000000000000))) = true
  rfl'

theorem compactCertificate410_states : ∀ j,
    BesselStateValid (compactCertificate410.point j) (compactCertificate410.state j) :=
  compactCertificate410.statesValid_of_checks3 compactCertificate410_stateChecks0
    compactCertificate410_stateChecks1 compactCertificate410_stateChecks2
    compactCertificate410_stateChecks3 compactCertificate410_stateChecks4
    compactCertificate410_stateChecks5 compactCertificate410_stateChecks6
    compactCertificate410_stateChecks7 compactCertificate410_stateChecks8

theorem compactCertificate410_chunkChecks0_0 :
    compactCertificate410.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (563 / 2) 0 (IntervalRat.scale (563 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-21043304689 / 1000000000000) (-21043303579 / 1000000000000), orderedInterval (42683692109 / 1000000000000) (42683693219 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (829406503668263 / 4000000000000) 0 (IntervalRat.scale (563 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (39411357964 / 1000000000000) (39411357965 / 1000000000000), orderedInterval (38853485960 / 1000000000000) (38853485961 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (268213022054279 / 800000000000) 0 (IntervalRat.scale (563 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (4311770806 / 1000000000000) (4311770811 / 1000000000000), orderedInterval (-43368382765 / 1000000000000) (-43368382760 / 1000000000000)))) (orderedInterval (-7720572301 / 1000000000000) (-7720571841 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (242018749201141 / 4000000000000) 0 (IntervalRat.scale (563 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-102536916538 / 1000000000000) (-102536916501 / 1000000000000), orderedInterval (3612762311 / 1000000000000) (3612762348 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (650096403107377 / 4000000000000) 0 (IntervalRat.scale (563 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-3383533511 / 1000000000000) (-3383533502 / 1000000000000), orderedInterval (62505603556 / 1000000000000) (62505603565 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1765138196196909 / 4000000000000) 0 (IntervalRat.scale (563 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29631694805 / 1000000000000) (29631737045 / 1000000000000), orderedInterval (-23795172654 / 1000000000000) (-23795130414 / 1000000000000)))) (orderedInterval (-1117595437 / 1000000000000) (-1117592399 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1300192806215317 / 4000000000000) 0 (IntervalRat.scale (563 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-34456957186 / 1000000000000) (-34456887974 / 1000000000000), orderedInterval (27824526423 / 1000000000000) (27824595634 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2227902534526441 / 4000000000000) 0 (IntervalRat.scale (563 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-33531128609 / 1000000000000) (-33531125331 / 1000000000000), orderedInterval (4349475800 / 1000000000000) (4349479079 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1641062923333819 / 4000000000000) 0 (IntervalRat.scale (563 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (18809859199 / 1000000000000) (18809860015 / 1000000000000), orderedInterval (-34633836652 / 1000000000000) (-34633835836 / 1000000000000)))) (orderedInterval (1488831240 / 1000000000000) (1488831377 / 1000000000000))) = true
  rfl'

theorem compactCertificate410_chunkChecks0_1 :
    compactCertificate410.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2517812542664437 / 4000000000000) 0 (IntervalRat.scale (563 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (29884976052 / 1000000000000) (29885017427 / 1000000000000), orderedInterval (-10899060985 / 1000000000000) (-10899019609 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1453659749276173 / 4000000000000) 0 (IntervalRat.scale (563 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-9327982565 / 1000000000000) (-9327982537 / 1000000000000), orderedInterval (40814320262 / 1000000000000) (40814320289 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2579544734382257 / 4000000000000) 0 (IntervalRat.scale (563 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-31333228792 / 1000000000000) (-31333225835 / 1000000000000), orderedInterval (2350268622 / 1000000000000) (2350271579 / 1000000000000)))) (orderedInterval (-10455536657 / 1000000000000) (-10455528771 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2410145300602133 / 4000000000000) 0 (IntervalRat.scale (563 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (4398234452 / 1000000000000) (4398234453 / 1000000000000), orderedInterval (32202289293 / 1000000000000) (32202289294 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1719993410839589 / 4000000000000) 0 (IntervalRat.scale (563 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14460073635 / 1000000000000) (-14460073634 / 1000000000000), orderedInterval (-35640215506 / 1000000000000) (-35640215505 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1950289209322131 / 4000000000000) 0 (IntervalRat.scale (563 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-35671601623 / 1000000000000) (-35671601567 / 1000000000000), orderedInterval (-5727900995 / 1000000000000) (-5727900939 / 1000000000000)))) (orderedInterval (-1266268877 / 1000000000000) (-1266268842 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1625947814861539 / 4000000000000) 0 (IntervalRat.scale (563 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-35875757956 / 1000000000000) (-35875725290 / 1000000000000), orderedInterval (16749827706 / 1000000000000) (16749860371 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1436574204480319 / 4000000000000) 0 (IntervalRat.scale (563 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (41121759639 / 1000000000000) (41121762512 / 1000000000000), orderedInterval (-9090773666 / 1000000000000) (-9090770793 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (416375197627581 / 800000000000) 0 (IntervalRat.scale (563 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-8660290777 / 1000000000000) (-8660290766 / 1000000000000), orderedInterval (33892909954 / 1000000000000) (33892909966 / 1000000000000)))) (orderedInterval (-2989280901 / 1000000000000) (-2989280331 / 1000000000000))) = true
  rfl'

theorem compactCertificate410_chunkChecks0_2 :
    compactCertificate410.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1151715709264007 / 4000000000000) 0 (IntervalRat.scale (563 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-14462181489 / 1000000000000) (-14462181320 / 1000000000000), orderedInterval (44767476144 / 1000000000000) (44767476313 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (976322161645327 / 4000000000000) 0 (IntervalRat.scale (563 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-9082916314 / 1000000000000) (-9082916280 / 1000000000000), orderedInterval (50275369515 / 1000000000000) (50275369549 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (610937076666181 / 4000000000000) 0 (IntervalRat.scale (563 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (26277752606 / 1000000000000) (26277754105 / 1000000000000), orderedInterval (-59057605631 / 1000000000000) (-59057604133 / 1000000000000)))) (orderedInterval (3681965472 / 1000000000000) (3681965620 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (328563991716027 / 4000000000000) 0 (IntervalRat.scale (563 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (83360814374 / 1000000000000) (83360814375 / 1000000000000), orderedInterval (27797892217 / 1000000000000) (27797892218 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (892115152309081 / 4000000000000) 0 (IntervalRat.scale (563 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-36828050978 / 1000000000000) (-36828050977 / 1000000000000), orderedInterval (-38623040076 / 1000000000000) (-38623040075 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1218106971207737 / 4000000000000) 0 (IntervalRat.scale (563 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-24951323460 / 1000000000000) (-24951323459 / 1000000000000), orderedInterval (-38272924789 / 1000000000000) (-38272924788 / 1000000000000)))) (orderedInterval (1208486937 / 1000000000000) (1208486972 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (515062923333819 / 4000000000000) 0 (IntervalRat.scale (563 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-47663258836 / 1000000000000) (-47663258835 / 1000000000000), orderedInterval (-51508564252 / 1000000000000) (-51508564251 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2093702187913499 / 4000000000000) 0 (IntervalRat.scale (563 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (14705067877 / 1000000000000) (14705068053 / 1000000000000), orderedInterval (-31637107070 / 1000000000000) (-31637106893 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1398496030858741 / 4000000000000) 0 (IntervalRat.scale (563 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-42357219643 / 1000000000000) (-42357218726 / 1000000000000), orderedInterval (5231058707 / 1000000000000) (5231059624 / 1000000000000)))) (orderedInterval (6462989375 / 1000000000000) (6462989640 / 1000000000000))) = true
  rfl'

theorem compactCertificate410_chunkChecks0 :
    compactCertificate410.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate410.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate410_chunkChecks0_0
    compactCertificate410_chunkChecks0_1 compactCertificate410_chunkChecks0_2

theorem compactCertificate410_chunkChecks1_0 :
    compactCertificate410.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (563 / 2) 1 (IntervalRat.scale (563 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-21043304689 / 1000000000000) (-21043303579 / 1000000000000), orderedInterval (42683692109 / 1000000000000) (42683693219 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (829406503668263 / 4000000000000) 1 (IntervalRat.scale (563 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (39411357964 / 1000000000000) (39411357965 / 1000000000000), orderedInterval (38853485960 / 1000000000000) (38853485961 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (268213022054279 / 800000000000) 1 (IntervalRat.scale (563 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (4311770806 / 1000000000000) (4311770811 / 1000000000000), orderedInterval (-43368382765 / 1000000000000) (-43368382760 / 1000000000000)))) (orderedInterval (14154016482 / 1000000000000) (14154016945 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (242018749201141 / 4000000000000) 1 (IntervalRat.scale (563 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-102536916538 / 1000000000000) (-102536916501 / 1000000000000), orderedInterval (3612762311 / 1000000000000) (3612762348 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (650096403107377 / 4000000000000) 1 (IntervalRat.scale (563 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-3383533511 / 1000000000000) (-3383533502 / 1000000000000), orderedInterval (62505603556 / 1000000000000) (62505603565 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1765138196196909 / 4000000000000) 1 (IntervalRat.scale (563 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29631694805 / 1000000000000) (29631737045 / 1000000000000), orderedInterval (-23795172654 / 1000000000000) (-23795130414 / 1000000000000)))) (orderedInterval (3960960772 / 1000000000000) (3960965518 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1300192806215317 / 4000000000000) 1 (IntervalRat.scale (563 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-34456957186 / 1000000000000) (-34456887974 / 1000000000000), orderedInterval (27824526423 / 1000000000000) (27824595634 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2227902534526441 / 4000000000000) 1 (IntervalRat.scale (563 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-33531128609 / 1000000000000) (-33531125331 / 1000000000000), orderedInterval (4349475800 / 1000000000000) (4349479079 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1641062923333819 / 4000000000000) 1 (IntervalRat.scale (563 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (18809859199 / 1000000000000) (18809860015 / 1000000000000), orderedInterval (-34633836652 / 1000000000000) (-34633835836 / 1000000000000)))) (orderedInterval (-1485352034 / 1000000000000) (-1485351777 / 1000000000000))) = true
  rfl'

theorem compactCertificate410_chunkChecks1_1 :
    compactCertificate410.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2517812542664437 / 4000000000000) 1 (IntervalRat.scale (563 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (29884976052 / 1000000000000) (29885017427 / 1000000000000), orderedInterval (-10899060985 / 1000000000000) (-10899019609 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1453659749276173 / 4000000000000) 1 (IntervalRat.scale (563 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-9327982565 / 1000000000000) (-9327982537 / 1000000000000), orderedInterval (40814320262 / 1000000000000) (40814320289 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2579544734382257 / 4000000000000) 1 (IntervalRat.scale (563 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-31333228792 / 1000000000000) (-31333225835 / 1000000000000), orderedInterval (2350268622 / 1000000000000) (2350271579 / 1000000000000)))) (orderedInterval (8999794738 / 1000000000000) (8999812375 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2410145300602133 / 4000000000000) 1 (IntervalRat.scale (563 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (4398234452 / 1000000000000) (4398234453 / 1000000000000), orderedInterval (32202289293 / 1000000000000) (32202289294 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1719993410839589 / 4000000000000) 1 (IntervalRat.scale (563 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14460073635 / 1000000000000) (-14460073634 / 1000000000000), orderedInterval (-35640215506 / 1000000000000) (-35640215505 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1950289209322131 / 4000000000000) 1 (IntervalRat.scale (563 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-35671601623 / 1000000000000) (-35671601567 / 1000000000000), orderedInterval (-5727900995 / 1000000000000) (-5727900939 / 1000000000000)))) (orderedInterval (-6342273401 / 1000000000000) (-6342273345 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1625947814861539 / 4000000000000) 1 (IntervalRat.scale (563 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-35875757956 / 1000000000000) (-35875725290 / 1000000000000), orderedInterval (16749827706 / 1000000000000) (16749860371 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1436574204480319 / 4000000000000) 1 (IntervalRat.scale (563 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (41121759639 / 1000000000000) (41121762512 / 1000000000000), orderedInterval (-9090773666 / 1000000000000) (-9090770793 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (416375197627581 / 800000000000) 1 (IntervalRat.scale (563 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-8660290777 / 1000000000000) (-8660290766 / 1000000000000), orderedInterval (33892909954 / 1000000000000) (33892909966 / 1000000000000)))) (orderedInterval (2547499937 / 1000000000000) (2547500731 / 1000000000000))) = true
  rfl'

theorem compactCertificate410_chunkChecks1_2 :
    compactCertificate410.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1151715709264007 / 4000000000000) 1 (IntervalRat.scale (563 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-14462181489 / 1000000000000) (-14462181320 / 1000000000000), orderedInterval (44767476144 / 1000000000000) (44767476313 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (976322161645327 / 4000000000000) 1 (IntervalRat.scale (563 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-9082916314 / 1000000000000) (-9082916280 / 1000000000000), orderedInterval (50275369515 / 1000000000000) (50275369549 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (610937076666181 / 4000000000000) 1 (IntervalRat.scale (563 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (26277752606 / 1000000000000) (26277754105 / 1000000000000), orderedInterval (-59057605631 / 1000000000000) (-59057604133 / 1000000000000)))) (orderedInterval (-10831949908 / 1000000000000) (-10831949786 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (328563991716027 / 4000000000000) 1 (IntervalRat.scale (563 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (83360814374 / 1000000000000) (83360814375 / 1000000000000), orderedInterval (27797892217 / 1000000000000) (27797892218 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (892115152309081 / 4000000000000) 1 (IntervalRat.scale (563 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-36828050978 / 1000000000000) (-36828050977 / 1000000000000), orderedInterval (-38623040076 / 1000000000000) (-38623040075 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1218106971207737 / 4000000000000) 1 (IntervalRat.scale (563 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-24951323460 / 1000000000000) (-24951323459 / 1000000000000), orderedInterval (-38272924789 / 1000000000000) (-38272924788 / 1000000000000)))) (orderedInterval (3717582304 / 1000000000000) (3717582335 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (515062923333819 / 4000000000000) 1 (IntervalRat.scale (563 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-47663258836 / 1000000000000) (-47663258835 / 1000000000000), orderedInterval (-51508564252 / 1000000000000) (-51508564251 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2093702187913499 / 4000000000000) 1 (IntervalRat.scale (563 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (14705067877 / 1000000000000) (14705068053 / 1000000000000), orderedInterval (-31637107070 / 1000000000000) (-31637106893 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1398496030858741 / 4000000000000) 1 (IntervalRat.scale (563 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-42357219643 / 1000000000000) (-42357218726 / 1000000000000), orderedInterval (5231058707 / 1000000000000) (5231059624 / 1000000000000)))) (orderedInterval (3427540043 / 1000000000000) (3427540393 / 1000000000000))) = true
  rfl'

theorem compactCertificate410_chunkChecks1 :
    compactCertificate410.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate410.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate410_chunkChecks1_0
    compactCertificate410_chunkChecks1_1 compactCertificate410_chunkChecks1_2

theorem compactCertificate410_chunkChecks2_0 :
    compactCertificate410.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (563 / 2) 2 (IntervalRat.scale (563 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-21043304689 / 1000000000000) (-21043303579 / 1000000000000), orderedInterval (42683692109 / 1000000000000) (42683693219 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (829406503668263 / 4000000000000) 2 (IntervalRat.scale (563 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (39411357964 / 1000000000000) (39411357965 / 1000000000000), orderedInterval (38853485960 / 1000000000000) (38853485961 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (268213022054279 / 800000000000) 2 (IntervalRat.scale (563 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (4311770806 / 1000000000000) (4311770811 / 1000000000000), orderedInterval (-43368382765 / 1000000000000) (-43368382760 / 1000000000000)))) (orderedInterval (7732392049 / 1000000000000) (7732392517 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (242018749201141 / 4000000000000) 2 (IntervalRat.scale (563 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-102536916538 / 1000000000000) (-102536916501 / 1000000000000), orderedInterval (3612762311 / 1000000000000) (3612762348 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (650096403107377 / 4000000000000) 2 (IntervalRat.scale (563 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-3383533511 / 1000000000000) (-3383533502 / 1000000000000), orderedInterval (62505603556 / 1000000000000) (62505603565 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1765138196196909 / 4000000000000) 2 (IntervalRat.scale (563 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29631694805 / 1000000000000) (29631737045 / 1000000000000), orderedInterval (-23795172654 / 1000000000000) (-23795130414 / 1000000000000)))) (orderedInterval (5152302040 / 1000000000000) (5152309490 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1300192806215317 / 4000000000000) 2 (IntervalRat.scale (563 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-34456957186 / 1000000000000) (-34456887974 / 1000000000000), orderedInterval (27824526423 / 1000000000000) (27824595634 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2227902534526441 / 4000000000000) 2 (IntervalRat.scale (563 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-33531128609 / 1000000000000) (-33531125331 / 1000000000000), orderedInterval (4349475800 / 1000000000000) (4349479079 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1641062923333819 / 4000000000000) 2 (IntervalRat.scale (563 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (18809859199 / 1000000000000) (18809860015 / 1000000000000), orderedInterval (-34633836652 / 1000000000000) (-34633835836 / 1000000000000)))) (orderedInterval (-5009206535 / 1000000000000) (-5009206047 / 1000000000000))) = true
  rfl'

theorem compactCertificate410_chunkChecks2_1 :
    compactCertificate410.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2517812542664437 / 4000000000000) 2 (IntervalRat.scale (563 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (29884976052 / 1000000000000) (29885017427 / 1000000000000), orderedInterval (-10899060985 / 1000000000000) (-10899019609 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1453659749276173 / 4000000000000) 2 (IntervalRat.scale (563 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-9327982565 / 1000000000000) (-9327982537 / 1000000000000), orderedInterval (40814320262 / 1000000000000) (40814320289 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2579544734382257 / 4000000000000) 2 (IntervalRat.scale (563 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-31333228792 / 1000000000000) (-31333225835 / 1000000000000), orderedInterval (2350268622 / 1000000000000) (2350271579 / 1000000000000)))) (orderedInterval (51047394796 / 1000000000000) (51047434322 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2410145300602133 / 4000000000000) 2 (IntervalRat.scale (563 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (4398234452 / 1000000000000) (4398234453 / 1000000000000), orderedInterval (32202289293 / 1000000000000) (32202289294 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1719993410839589 / 4000000000000) 2 (IntervalRat.scale (563 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14460073635 / 1000000000000) (-14460073634 / 1000000000000), orderedInterval (-35640215506 / 1000000000000) (-35640215505 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1950289209322131 / 4000000000000) 2 (IntervalRat.scale (563 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-35671601623 / 1000000000000) (-35671601567 / 1000000000000), orderedInterval (-5727900995 / 1000000000000) (-5727900939 / 1000000000000)))) (orderedInterval (3035321595 / 1000000000000) (3035321686 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1625947814861539 / 4000000000000) 2 (IntervalRat.scale (563 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-35875757956 / 1000000000000) (-35875725290 / 1000000000000), orderedInterval (16749827706 / 1000000000000) (16749860371 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1436574204480319 / 4000000000000) 2 (IntervalRat.scale (563 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (41121759639 / 1000000000000) (41121762512 / 1000000000000), orderedInterval (-9090773666 / 1000000000000) (-9090770793 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (416375197627581 / 800000000000) 2 (IntervalRat.scale (563 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-8660290777 / 1000000000000) (-8660290766 / 1000000000000), orderedInterval (33892909954 / 1000000000000) (33892909966 / 1000000000000)))) (orderedInterval (5443240074 / 1000000000000) (5443241190 / 1000000000000))) = true
  rfl'

theorem compactCertificate410_chunkChecks2_2 :
    compactCertificate410.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1151715709264007 / 4000000000000) 2 (IntervalRat.scale (563 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-14462181489 / 1000000000000) (-14462181320 / 1000000000000), orderedInterval (44767476144 / 1000000000000) (44767476313 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (976322161645327 / 4000000000000) 2 (IntervalRat.scale (563 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-9082916314 / 1000000000000) (-9082916280 / 1000000000000), orderedInterval (50275369515 / 1000000000000) (50275369549 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (610937076666181 / 4000000000000) 2 (IntervalRat.scale (563 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (26277752606 / 1000000000000) (26277754105 / 1000000000000), orderedInterval (-59057605631 / 1000000000000) (-59057604133 / 1000000000000)))) (orderedInterval (-3019083496 / 1000000000000) (-3019083389 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (328563991716027 / 4000000000000) 2 (IntervalRat.scale (563 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (83360814374 / 1000000000000) (83360814375 / 1000000000000), orderedInterval (27797892217 / 1000000000000) (27797892218 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (892115152309081 / 4000000000000) 2 (IntervalRat.scale (563 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-36828050978 / 1000000000000) (-36828050977 / 1000000000000), orderedInterval (-38623040076 / 1000000000000) (-38623040075 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1218106971207737 / 4000000000000) 2 (IntervalRat.scale (563 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-24951323460 / 1000000000000) (-24951323459 / 1000000000000), orderedInterval (-38272924789 / 1000000000000) (-38272924788 / 1000000000000)))) (orderedInterval (-2644491088 / 1000000000000) (-2644491057 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (515062923333819 / 4000000000000) 2 (IntervalRat.scale (563 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-47663258836 / 1000000000000) (-47663258835 / 1000000000000), orderedInterval (-51508564252 / 1000000000000) (-51508564251 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2093702187913499 / 4000000000000) 2 (IntervalRat.scale (563 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (14705067877 / 1000000000000) (14705068053 / 1000000000000), orderedInterval (-31637107070 / 1000000000000) (-31637106893 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1398496030858741 / 4000000000000) 2 (IntervalRat.scale (563 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-42357219643 / 1000000000000) (-42357218726 / 1000000000000), orderedInterval (5231058707 / 1000000000000) (5231059624 / 1000000000000)))) (orderedInterval (-8072798754 / 1000000000000) (-8072798276 / 1000000000000))) = true
  rfl'

theorem compactCertificate410_chunkChecks2 :
    compactCertificate410.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate410.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate410_chunkChecks2_0
    compactCertificate410_chunkChecks2_1 compactCertificate410_chunkChecks2_2

theorem compactCertificate410_chunkChecks3_0 :
    compactCertificate410.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (563 / 2) 3 (IntervalRat.scale (563 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-21043304689 / 1000000000000) (-21043303579 / 1000000000000), orderedInterval (42683692109 / 1000000000000) (42683693219 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (829406503668263 / 4000000000000) 3 (IntervalRat.scale (563 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (39411357964 / 1000000000000) (39411357965 / 1000000000000), orderedInterval (38853485960 / 1000000000000) (38853485961 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (268213022054279 / 800000000000) 3 (IntervalRat.scale (563 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (4311770806 / 1000000000000) (4311770811 / 1000000000000), orderedInterval (-43368382765 / 1000000000000) (-43368382760 / 1000000000000)))) (orderedInterval (-12790919525 / 1000000000000) (-12790919053 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (242018749201141 / 4000000000000) 3 (IntervalRat.scale (563 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-102536916538 / 1000000000000) (-102536916501 / 1000000000000), orderedInterval (3612762311 / 1000000000000) (3612762348 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (650096403107377 / 4000000000000) 3 (IntervalRat.scale (563 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-3383533511 / 1000000000000) (-3383533502 / 1000000000000), orderedInterval (62505603556 / 1000000000000) (62505603565 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1765138196196909 / 4000000000000) 3 (IntervalRat.scale (563 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29631694805 / 1000000000000) (29631737045 / 1000000000000), orderedInterval (-23795172654 / 1000000000000) (-23795130414 / 1000000000000)))) (orderedInterval (-6973597572 / 1000000000000) (-6973585898 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1300192806215317 / 4000000000000) 3 (IntervalRat.scale (563 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-34456957186 / 1000000000000) (-34456887974 / 1000000000000), orderedInterval (27824526423 / 1000000000000) (27824595634 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2227902534526441 / 4000000000000) 3 (IntervalRat.scale (563 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-33531128609 / 1000000000000) (-33531125331 / 1000000000000), orderedInterval (4349475800 / 1000000000000) (4349479079 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1641062923333819 / 4000000000000) 3 (IntervalRat.scale (563 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (18809859199 / 1000000000000) (18809860015 / 1000000000000), orderedInterval (-34633836652 / 1000000000000) (-34633835836 / 1000000000000)))) (orderedInterval (3648140814 / 1000000000000) (3648141750 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate410_chunkChecks3_1 :
    compactCertificate410.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2517812542664437 / 4000000000000) 3 (IntervalRat.scale (563 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (29884976052 / 1000000000000) (29885017427 / 1000000000000), orderedInterval (-10899060985 / 1000000000000) (-10899019609 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1453659749276173 / 4000000000000) 3 (IntervalRat.scale (563 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-9327982565 / 1000000000000) (-9327982537 / 1000000000000), orderedInterval (40814320262 / 1000000000000) (40814320289 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2579544734382257 / 4000000000000) 3 (IntervalRat.scale (563 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-31333228792 / 1000000000000) (-31333225835 / 1000000000000), orderedInterval (2350268622 / 1000000000000) (2350271579 / 1000000000000)))) (orderedInterval (-32357004699 / 1000000000000) (-32356916219 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2410145300602133 / 4000000000000) 3 (IntervalRat.scale (563 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (4398234452 / 1000000000000) (4398234453 / 1000000000000), orderedInterval (32202289293 / 1000000000000) (32202289294 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1719993410839589 / 4000000000000) 3 (IntervalRat.scale (563 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14460073635 / 1000000000000) (-14460073634 / 1000000000000), orderedInterval (-35640215506 / 1000000000000) (-35640215505 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1950289209322131 / 4000000000000) 3 (IntervalRat.scale (563 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-35671601623 / 1000000000000) (-35671601567 / 1000000000000), orderedInterval (-5727900995 / 1000000000000) (-5727900939 / 1000000000000)))) (orderedInterval (17551839661 / 1000000000000) (17551839816 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1625947814861539 / 4000000000000) 3 (IntervalRat.scale (563 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-35875757956 / 1000000000000) (-35875725290 / 1000000000000), orderedInterval (16749827706 / 1000000000000) (16749860371 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1436574204480319 / 4000000000000) 3 (IntervalRat.scale (563 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (41121759639 / 1000000000000) (41121762512 / 1000000000000), orderedInterval (-9090773666 / 1000000000000) (-9090770793 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (416375197627581 / 800000000000) 3 (IntervalRat.scale (563 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-8660290777 / 1000000000000) (-8660290766 / 1000000000000), orderedInterval (33892909954 / 1000000000000) (33892909966 / 1000000000000)))) (orderedInterval (-7166905155 / 1000000000000) (-7166903583 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate410_chunkChecks3_2 :
    compactCertificate410.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1151715709264007 / 4000000000000) 3 (IntervalRat.scale (563 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-14462181489 / 1000000000000) (-14462181320 / 1000000000000), orderedInterval (44767476144 / 1000000000000) (44767476313 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (976322161645327 / 4000000000000) 3 (IntervalRat.scale (563 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-9082916314 / 1000000000000) (-9082916280 / 1000000000000), orderedInterval (50275369515 / 1000000000000) (50275369549 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (610937076666181 / 4000000000000) 3 (IntervalRat.scale (563 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (26277752606 / 1000000000000) (26277754105 / 1000000000000), orderedInterval (-59057605631 / 1000000000000) (-59057604133 / 1000000000000)))) (orderedInterval (9832337900 / 1000000000000) (9832337999 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (328563991716027 / 4000000000000) 3 (IntervalRat.scale (563 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (83360814374 / 1000000000000) (83360814375 / 1000000000000), orderedInterval (27797892217 / 1000000000000) (27797892218 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (892115152309081 / 4000000000000) 3 (IntervalRat.scale (563 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-36828050978 / 1000000000000) (-36828050977 / 1000000000000), orderedInterval (-38623040076 / 1000000000000) (-38623040075 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1218106971207737 / 4000000000000) 3 (IntervalRat.scale (563 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-24951323460 / 1000000000000) (-24951323459 / 1000000000000), orderedInterval (-38272924789 / 1000000000000) (-38272924788 / 1000000000000)))) (orderedInterval (-4127073678 / 1000000000000) (-4127073646 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (515062923333819 / 4000000000000) 3 (IntervalRat.scale (563 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-47663258836 / 1000000000000) (-47663258835 / 1000000000000), orderedInterval (-51508564252 / 1000000000000) (-51508564251 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2093702187913499 / 4000000000000) 3 (IntervalRat.scale (563 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (14705067877 / 1000000000000) (14705068053 / 1000000000000), orderedInterval (-31637107070 / 1000000000000) (-31637106893 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1398496030858741 / 4000000000000) 3 (IntervalRat.scale (563 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-42357219643 / 1000000000000) (-42357218726 / 1000000000000), orderedInterval (5231058707 / 1000000000000) (5231059624 / 1000000000000)))) (orderedInterval (-14617332576 / 1000000000000) (-14617331903 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate410_chunkChecks3 :
    compactCertificate410.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate410.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate410_chunkChecks3_0
    compactCertificate410_chunkChecks3_1 compactCertificate410_chunkChecks3_2

theorem compactCertificate410_chunkChecks4_0 :
    compactCertificate410.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (563 / 2) 4 (IntervalRat.scale (563 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-21043304689 / 1000000000000) (-21043303579 / 1000000000000), orderedInterval (42683692109 / 1000000000000) (42683693219 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (829406503668263 / 4000000000000) 4 (IntervalRat.scale (563 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (39411357964 / 1000000000000) (39411357965 / 1000000000000), orderedInterval (38853485960 / 1000000000000) (38853485961 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (268213022054279 / 800000000000) 4 (IntervalRat.scale (563 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (4311770806 / 1000000000000) (4311770811 / 1000000000000), orderedInterval (-43368382765 / 1000000000000) (-43368382760 / 1000000000000)))) (orderedInterval (-7632649723 / 1000000000000) (-7632649244 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (242018749201141 / 4000000000000) 4 (IntervalRat.scale (563 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-102536916538 / 1000000000000) (-102536916501 / 1000000000000), orderedInterval (3612762311 / 1000000000000) (3612762348 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (650096403107377 / 4000000000000) 4 (IntervalRat.scale (563 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-3383533511 / 1000000000000) (-3383533502 / 1000000000000), orderedInterval (62505603556 / 1000000000000) (62505603565 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1765138196196909 / 4000000000000) 4 (IntervalRat.scale (563 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29631694805 / 1000000000000) (29631737045 / 1000000000000), orderedInterval (-23795172654 / 1000000000000) (-23795130414 / 1000000000000)))) (orderedInterval (-12682843207 / 1000000000000) (-12682824869 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1300192806215317 / 4000000000000) 4 (IntervalRat.scale (563 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-34456957186 / 1000000000000) (-34456887974 / 1000000000000), orderedInterval (27824526423 / 1000000000000) (27824595634 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2227902534526441 / 4000000000000) 4 (IntervalRat.scale (563 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-33531128609 / 1000000000000) (-33531125331 / 1000000000000), orderedInterval (4349475800 / 1000000000000) (4349479079 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1641062923333819 / 4000000000000) 4 (IntervalRat.scale (563 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (18809859199 / 1000000000000) (18809860015 / 1000000000000), orderedInterval (-34633836652 / 1000000000000) (-34633835836 / 1000000000000)))) (orderedInterval (17875815035 / 1000000000000) (17875816844 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate410_chunkChecks4_1 :
    compactCertificate410.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2517812542664437 / 4000000000000) 4 (IntervalRat.scale (563 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (29884976052 / 1000000000000) (29885017427 / 1000000000000), orderedInterval (-10899060985 / 1000000000000) (-10899019609 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1453659749276173 / 4000000000000) 4 (IntervalRat.scale (563 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-9327982565 / 1000000000000) (-9327982537 / 1000000000000), orderedInterval (40814320262 / 1000000000000) (40814320289 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2579544734382257 / 4000000000000) 4 (IntervalRat.scale (563 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-31333228792 / 1000000000000) (-31333225835 / 1000000000000), orderedInterval (2350268622 / 1000000000000) (2350271579 / 1000000000000)))) (orderedInterval (-257128654260 / 1000000000000) (-257128455850 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2410145300602133 / 4000000000000) 4 (IntervalRat.scale (563 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (4398234452 / 1000000000000) (4398234453 / 1000000000000), orderedInterval (32202289293 / 1000000000000) (32202289294 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1719993410839589 / 4000000000000) 4 (IntervalRat.scale (563 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14460073635 / 1000000000000) (-14460073634 / 1000000000000), orderedInterval (-35640215506 / 1000000000000) (-35640215505 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1950289209322131 / 4000000000000) 4 (IntervalRat.scale (563 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-35671601623 / 1000000000000) (-35671601567 / 1000000000000), orderedInterval (-5727900995 / 1000000000000) (-5727900939 / 1000000000000)))) (orderedInterval (-7611319537 / 1000000000000) (-7611319268 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1625947814861539 / 4000000000000) 4 (IntervalRat.scale (563 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-35875757956 / 1000000000000) (-35875725290 / 1000000000000), orderedInterval (16749827706 / 1000000000000) (16749860371 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1436574204480319 / 4000000000000) 4 (IntervalRat.scale (563 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (41121759639 / 1000000000000) (41121762512 / 1000000000000), orderedInterval (-9090773666 / 1000000000000) (-9090770793 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (416375197627581 / 800000000000) 4 (IntervalRat.scale (563 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-8660290777 / 1000000000000) (-8660290766 / 1000000000000), orderedInterval (33892909954 / 1000000000000) (33892909966 / 1000000000000)))) (orderedInterval (-10576356676 / 1000000000000) (-10576354445 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate410_chunkChecks4_2 :
    compactCertificate410.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1151715709264007 / 4000000000000) 4 (IntervalRat.scale (563 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-14462181489 / 1000000000000) (-14462181320 / 1000000000000), orderedInterval (44767476144 / 1000000000000) (44767476313 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (976322161645327 / 4000000000000) 4 (IntervalRat.scale (563 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-9082916314 / 1000000000000) (-9082916280 / 1000000000000), orderedInterval (50275369515 / 1000000000000) (50275369549 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (610937076666181 / 4000000000000) 4 (IntervalRat.scale (563 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (26277752606 / 1000000000000) (26277754105 / 1000000000000), orderedInterval (-59057605631 / 1000000000000) (-59057604133 / 1000000000000)))) (orderedInterval (2825803883 / 1000000000000) (2825803979 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (328563991716027 / 4000000000000) 4 (IntervalRat.scale (563 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (83360814374 / 1000000000000) (83360814375 / 1000000000000), orderedInterval (27797892217 / 1000000000000) (27797892218 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (892115152309081 / 4000000000000) 4 (IntervalRat.scale (563 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-36828050978 / 1000000000000) (-36828050977 / 1000000000000), orderedInterval (-38623040076 / 1000000000000) (-38623040075 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1218106971207737 / 4000000000000) 4 (IntervalRat.scale (563 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-24951323460 / 1000000000000) (-24951323459 / 1000000000000), orderedInterval (-38272924789 / 1000000000000) (-38272924788 / 1000000000000)))) (orderedInterval (2966318698 / 1000000000000) (2966318731 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (515062923333819 / 4000000000000) 4 (IntervalRat.scale (563 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-47663258836 / 1000000000000) (-47663258835 / 1000000000000), orderedInterval (-51508564252 / 1000000000000) (-51508564251 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2093702187913499 / 4000000000000) 4 (IntervalRat.scale (563 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (14705067877 / 1000000000000) (14705068053 / 1000000000000), orderedInterval (-31637107070 / 1000000000000) (-31637106893 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1398496030858741 / 4000000000000) 4 (IntervalRat.scale (563 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-42357219643 / 1000000000000) (-42357218726 / 1000000000000), orderedInterval (5231058707 / 1000000000000) (5231059624 / 1000000000000)))) (orderedInterval (4693184648 / 1000000000000) (4693185633 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate410_chunkChecks4 :
    compactCertificate410.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate410.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate410_chunkChecks4_0
    compactCertificate410_chunkChecks4_1 compactCertificate410_chunkChecks4_2

theorem compactCertificate410_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate410.chunkCheck r b = true :=
  compactCertificate410.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate410_chunkChecks0
    · exact compactCertificate410_chunkChecks1
    · exact compactCertificate410_chunkChecks2
    · exact compactCertificate410_chunkChecks3
    · exact compactCertificate410_chunkChecks4)

theorem compactCertificate410_coefficient0 :
    compactCertificate410.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate410_coefficient1 :
    compactCertificate410.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate410_coefficient2 :
    compactCertificate410.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate410_coefficient3 :
    compactCertificate410.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate410_coefficient4 :
    compactCertificate410.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate410_coefficients : ∀ r : Fin 5,
    compactCertificate410.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate410_coefficient0
  · exact compactCertificate410_coefficient1
  · exact compactCertificate410_coefficient2
  · exact compactCertificate410_coefficient3
  · exact compactCertificate410_coefficient4

theorem compactCertificate410_lower : (1 : ℚ) ≤ compactCertificate410.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate410, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate410_proves {t : ℝ} (ht : t ∈ compactCertificate410.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate410.proves compactCertificate410_states compactCertificate410_chunks
    compactCertificate410_coefficients compactCertificate410_lower ht

end Erdos232
