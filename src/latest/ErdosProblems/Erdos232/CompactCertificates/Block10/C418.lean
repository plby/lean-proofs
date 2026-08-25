/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate418 : CompactCertificate where
  left := 289
  right := 290
  center := 579 / 2
  grid := fun i =>
    match i.val with
    | 0 => 92
    | 1 => 68
    | 2 => 110
    | 3 => 20
    | 4 => 53
    | 5 => 145
    | 6 => 106
    | 7 => 182
    | 8 => 134
    | 9 => 206
    | 10 => 119
    | 11 => 211
    | 12 => 197
    | 13 => 141
    | 14 => 160
    | 15 => 133
    | 16 => 118
    | 17 => 170
    | 18 => 94
    | 19 => 80
    | 20 => 50
    | 21 => 27
    | 22 => 73
    | 23 => 100
    | 24 => 42
    | 25 => 171
    | _ => 115
  point := fun i =>
    match i.val with
    | 0 => 579 / 2
    | 1 => 852977558834679 / 4000000000000
    | 2 => 275835416997207 / 800000000000
    | 3 => 248896724311653 / 4000000000000
    | 4 => 668571611721441 / 4000000000000
    | 5 => 1815301981523997 / 4000000000000
    | 6 => 1337143223443461 / 4000000000000
    | 7 => 2291217704246553 / 4000000000000
    | 8 => 1687700590782027 / 4000000000000
    | 9 => 2589366717944421 / 4000000000000
    | 10 => 1494971571635709 / 4000000000000
    | 11 => 2652853288112481 / 4000000000000
    | 12 => 2478639660832389 / 4000000000000
    | 13 => 1768874218252437 / 4000000000000
    | 14 => 2005714835164323 / 4000000000000
    | 15 => 1672155923276787 / 4000000000000
    | 16 => 1477400469616527 / 4000000000000
    | 17 => 428208240544173 / 800000000000
    | 18 => 1184446528710231 / 4000000000000
    | 19 => 1004068439773791 / 4000000000000
    | 20 => 628299409217973 / 4000000000000
    | 21 => 337901511906891 / 4000000000000
    | 22 => 917468336033673 / 4000000000000
    | 23 => 1252724576073321 / 4000000000000
    | 24 => 529700590782027 / 4000000000000
    | 25 => 2153203493431467 / 4000000000000
    | _ => 1438240145412453 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (44624743182 / 1000000000000) (44624743183 / 1000000000000), orderedInterval (14333398789 / 1000000000000) (14333398791 / 1000000000000))
    | 1 => (orderedInterval (21322674116 / 1000000000000) (21322674117 / 1000000000000), orderedInterval (50256556081 / 1000000000000) (50256556082 / 1000000000000))
    | 2 => (orderedInterval (176818003 / 1000000000000) (176818005 / 1000000000000), orderedInterval (42968876710 / 1000000000000) (42968876711 / 1000000000000))
    | 3 => (orderedInterval (17682001615 / 1000000000000) (17682001616 / 1000000000000), orderedInterval (99450716614 / 1000000000000) (99450716616 / 1000000000000))
    | 4 => (orderedInterval (-61044094340 / 1000000000000) (-61044094334 / 1000000000000), orderedInterval (-8896897994 / 1000000000000) (-8896897989 / 1000000000000))
    | 5 => (orderedInterval (29805434130 / 1000000000000) (29805484151 / 1000000000000), orderedInterval (-22713685178 / 1000000000000) (-22713635157 / 1000000000000))
    | 6 => (orderedInterval (38479710658 / 1000000000000) (38479749400 / 1000000000000), orderedInterval (-20642197864 / 1000000000000) (-20642159121 / 1000000000000))
    | 7 => (orderedInterval (32310061131 / 1000000000000) (32310073523 / 1000000000000), orderedInterval (-8242086668 / 1000000000000) (-8242074276 / 1000000000000))
    | 8 => (orderedInterval (38309638403 / 1000000000000) (38309640747 / 1000000000000), orderedInterval (-6465353174 / 1000000000000) (-6465350831 / 1000000000000))
    | 9 => (orderedInterval (25668040787 / 1000000000000) (25668040788 / 1000000000000), orderedInterval (17996516938 / 1000000000000) (17996516939 / 1000000000000))
    | 10 => (orderedInterval (-25901029981 / 1000000000000) (-25901029980 / 1000000000000), orderedInterval (-32097884961 / 1000000000000) (-32097884960 / 1000000000000))
    | 11 => (orderedInterval (-27920578830 / 1000000000000) (-27920578827 / 1000000000000), orderedInterval (-13408137956 / 1000000000000) (-13408137953 / 1000000000000))
    | 12 => (orderedInterval (-32046547528 / 1000000000000) (-32046546655 / 1000000000000), orderedInterval (-597123650 / 1000000000000) (-597122777 / 1000000000000))
    | 13 => (orderedInterval (-1483382292 / 1000000000000) (-1483382291 / 1000000000000), orderedInterval (-37911445646 / 1000000000000) (-37911445645 / 1000000000000))
    | 14 => (orderedInterval (-15208069661 / 1000000000000) (-15208069440 / 1000000000000), orderedInterval (32238242606 / 1000000000000) (32238242827 / 1000000000000))
    | 15 => (orderedInterval (-32673302490 / 1000000000000) (-32673302489 / 1000000000000), orderedInterval (-21299305460 / 1000000000000) (-21299305459 / 1000000000000))
    | 16 => (orderedInterval (-22499879772 / 1000000000000) (-22499877302 / 1000000000000), orderedInterval (34921395093 / 1000000000000) (34921397563 / 1000000000000))
    | 17 => (orderedInterval (31711896054 / 1000000000000) (31711940161 / 1000000000000), orderedInterval (-13583930689 / 1000000000000) (-13583886582 / 1000000000000))
    | 18 => (orderedInterval (46361311255 / 1000000000000) (46361311425 / 1000000000000), orderedInterval (-824879241 / 1000000000000) (-824879072 / 1000000000000))
    | 19 => (orderedInterval (23013671183 / 1000000000000) (23013671184 / 1000000000000), orderedInterval (44748519924 / 1000000000000) (44748519925 / 1000000000000))
    | 20 => (orderedInterval (44764669772 / 1000000000000) (44764669773 / 1000000000000), orderedInterval (45124440124 / 1000000000000) (45124440125 / 1000000000000))
    | 21 => (orderedInterval (-36684667023 / 1000000000000) (-36684667022 / 1000000000000), orderedInterval (-78462464606 / 1000000000000) (-78462464605 / 1000000000000))
    | 22 => (orderedInterval (-38363403819 / 1000000000000) (-38363403818 / 1000000000000), orderedInterval (-36024524164 / 1000000000000) (-36024524163 / 1000000000000))
    | 23 => (orderedInterval (-8653094846 / 1000000000000) (-8653094821 / 1000000000000), orderedInterval (44261740279 / 1000000000000) (44261740304 / 1000000000000))
    | 24 => (orderedInterval (66070530113 / 1000000000000) (66070530114 / 1000000000000), orderedInterval (20775535056 / 1000000000000) (20775535057 / 1000000000000))
    | 25 => (orderedInterval (-32824068786 / 1000000000000) (-32824051150 / 1000000000000), orderedInterval (10288519847 / 1000000000000) (10288537483 / 1000000000000))
    | _ => (orderedInterval (33932307514 / 1000000000000) (33932395495 / 1000000000000), orderedInterval (-24929893259 / 1000000000000) (-24929805277 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (17896747847 / 1000000000000) (17896747869 / 1000000000000)
      | 1 => orderedInterval (-4539524834 / 1000000000000) (-4539521243 / 1000000000000)
      | 2 => orderedInterval (-70703573 / 1000000000000) (-70703117 / 1000000000000)
      | 3 => orderedInterval (-10449028960 / 1000000000000) (-10449028845 / 1000000000000)
      | 4 => orderedInterval (515227756 / 1000000000000) (515227808 / 1000000000000)
      | 5 => orderedInterval (1722242483 / 1000000000000) (1722243782 / 1000000000000)
      | 6 => orderedInterval (-7258070155 / 1000000000000) (-7258070055 / 1000000000000)
      | 7 => orderedInterval (2210895308 / 1000000000000) (2210895346 / 1000000000000)
      | _ => orderedInterval (-3296386641 / 1000000000000) (-3296368617 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (9029260496 / 1000000000000) (9029260520 / 1000000000000)
      | 1 => orderedInterval (2111782346 / 1000000000000) (2111787960 / 1000000000000)
      | 2 => orderedInterval (275266537 / 1000000000000) (275267405 / 1000000000000)
      | 3 => orderedInterval (-14587191946 / 1000000000000) (-14587191706 / 1000000000000)
      | 4 => orderedInterval (-5735700817 / 1000000000000) (-5735700724 / 1000000000000)
      | 5 => orderedInterval (-3547865012 / 1000000000000) (-3547862703 / 1000000000000)
      | 6 => orderedInterval (-1264122465 / 1000000000000) (-1264122370 / 1000000000000)
      | 7 => orderedInterval (-2599365116 / 1000000000000) (-2599365082 / 1000000000000)
      | _ => orderedInterval (4309481229 / 1000000000000) (4309504514 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-17841394774 / 1000000000000) (-17841394747 / 1000000000000)
      | 1 => orderedInterval (5951448112 / 1000000000000) (5951456925 / 1000000000000)
      | 2 => orderedInterval (1933850129 / 1000000000000) (1933851800 / 1000000000000)
      | 3 => orderedInterval (46883762795 / 1000000000000) (46883763309 / 1000000000000)
      | 4 => orderedInterval (-2534357867 / 1000000000000) (-2534357698 / 1000000000000)
      | 5 => orderedInterval (-4072495360 / 1000000000000) (-4072491202 / 1000000000000)
      | 6 => orderedInterval (8309920926 / 1000000000000) (8309921019 / 1000000000000)
      | 7 => orderedInterval (-1371124343 / 1000000000000) (-1371124309 / 1000000000000)
      | _ => orderedInterval (484691756 / 1000000000000) (484722430 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-10066456147 / 1000000000000) (-10066456115 / 1000000000000)
      | 1 => orderedInterval (-6167654056 / 1000000000000) (-6167640245 / 1000000000000)
      | 2 => orderedInterval (-1492118210 / 1000000000000) (-1492114977 / 1000000000000)
      | 3 => orderedInterval (63623462816 / 1000000000000) (63623463941 / 1000000000000)
      | 4 => orderedInterval (13528495651 / 1000000000000) (13528495969 / 1000000000000)
      | 5 => orderedInterval (7102964432 / 1000000000000) (7102971969 / 1000000000000)
      | 6 => orderedInterval (1246546697 / 1000000000000) (1246546788 / 1000000000000)
      | 7 => orderedInterval (3856806665 / 1000000000000) (3856806700 / 1000000000000)
      | _ => orderedInterval (-3591021720 / 1000000000000) (-3590980502 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (17836383858 / 1000000000000) (17836383895 / 1000000000000)
      | 1 => orderedInterval (-13001069428 / 1000000000000) (-13001047733 / 1000000000000)
      | 2 => orderedInterval (-11085904398 / 1000000000000) (-11085898093 / 1000000000000)
      | 3 => orderedInterval (-229114310639 / 1000000000000) (-229114308142 / 1000000000000)
      | 4 => orderedInterval (11979183087 / 1000000000000) (11979183703 / 1000000000000)
      | 5 => orderedInterval (11210323333 / 1000000000000) (11210337102 / 1000000000000)
      | 6 => orderedInterval (-8732015632 / 1000000000000) (-8732015541 / 1000000000000)
      | 7 => orderedInterval (1229449730 / 1000000000000) (1229449766 / 1000000000000)
      | _ => orderedInterval (16832482361 / 1000000000000) (16832539496 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-3268600769 / 1000000000000) (-3268577072 / 1000000000000)
    | 1 => orderedInterval (-12008454748 / 1000000000000) (-12008422186 / 1000000000000)
    | 2 => orderedInterval (37744301374 / 1000000000000) (37744347527 / 1000000000000)
    | 3 => orderedInterval (68041026128 / 1000000000000) (68041093528 / 1000000000000)
    | _ => orderedInterval (-202845477728 / 1000000000000) (-202845375547 / 1000000000000)

theorem compactCertificate418_stateChecks0 :
    compactCertificate418.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 92 12 (579 / 2)) (orderedInterval (44624743182 / 1000000000000) (44624743183 / 1000000000000), orderedInterval (14333398789 / 1000000000000) (14333398791 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (852977558834679 / 4000000000000)) (orderedInterval (21322674116 / 1000000000000) (21322674117 / 1000000000000), orderedInterval (50256556081 / 1000000000000) (50256556082 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 110 12 (275835416997207 / 800000000000)) (orderedInterval (176818003 / 1000000000000) (176818005 / 1000000000000), orderedInterval (42968876710 / 1000000000000) (42968876711 / 1000000000000))) = true
  rfl'

theorem compactCertificate418_stateChecks1 :
    compactCertificate418.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 20 12 (248896724311653 / 4000000000000)) (orderedInterval (17682001615 / 1000000000000) (17682001616 / 1000000000000), orderedInterval (99450716614 / 1000000000000) (99450716616 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (668571611721441 / 4000000000000)) (orderedInterval (-61044094340 / 1000000000000) (-61044094334 / 1000000000000), orderedInterval (-8896897994 / 1000000000000) (-8896897989 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 145 12 (1815301981523997 / 4000000000000)) (orderedInterval (29805434130 / 1000000000000) (29805484151 / 1000000000000), orderedInterval (-22713685178 / 1000000000000) (-22713635157 / 1000000000000))) = true
  rfl'

theorem compactCertificate418_stateChecks2 :
    compactCertificate418.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 106 12 (1337143223443461 / 4000000000000)) (orderedInterval (38479710658 / 1000000000000) (38479749400 / 1000000000000), orderedInterval (-20642197864 / 1000000000000) (-20642159121 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 182 12 (2291217704246553 / 4000000000000)) (orderedInterval (32310061131 / 1000000000000) (32310073523 / 1000000000000), orderedInterval (-8242086668 / 1000000000000) (-8242074276 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 134 12 (1687700590782027 / 4000000000000)) (orderedInterval (38309638403 / 1000000000000) (38309640747 / 1000000000000), orderedInterval (-6465353174 / 1000000000000) (-6465350831 / 1000000000000))) = true
  rfl'

theorem compactCertificate418_stateChecks3 :
    compactCertificate418.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 206 12 (2589366717944421 / 4000000000000)) (orderedInterval (25668040787 / 1000000000000) (25668040788 / 1000000000000), orderedInterval (17996516938 / 1000000000000) (17996516939 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 119 12 (1494971571635709 / 4000000000000)) (orderedInterval (-25901029981 / 1000000000000) (-25901029980 / 1000000000000), orderedInterval (-32097884961 / 1000000000000) (-32097884960 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 211 12 (2652853288112481 / 4000000000000)) (orderedInterval (-27920578830 / 1000000000000) (-27920578827 / 1000000000000), orderedInterval (-13408137956 / 1000000000000) (-13408137953 / 1000000000000))) = true
  rfl'

theorem compactCertificate418_stateChecks4 :
    compactCertificate418.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 197 12 (2478639660832389 / 4000000000000)) (orderedInterval (-32046547528 / 1000000000000) (-32046546655 / 1000000000000), orderedInterval (-597123650 / 1000000000000) (-597122777 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 141 12 (1768874218252437 / 4000000000000)) (orderedInterval (-1483382292 / 1000000000000) (-1483382291 / 1000000000000), orderedInterval (-37911445646 / 1000000000000) (-37911445645 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 160 12 (2005714835164323 / 4000000000000)) (orderedInterval (-15208069661 / 1000000000000) (-15208069440 / 1000000000000), orderedInterval (32238242606 / 1000000000000) (32238242827 / 1000000000000))) = true
  rfl'

theorem compactCertificate418_stateChecks5 :
    compactCertificate418.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 133 12 (1672155923276787 / 4000000000000)) (orderedInterval (-32673302490 / 1000000000000) (-32673302489 / 1000000000000), orderedInterval (-21299305460 / 1000000000000) (-21299305459 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 118 12 (1477400469616527 / 4000000000000)) (orderedInterval (-22499879772 / 1000000000000) (-22499877302 / 1000000000000), orderedInterval (34921395093 / 1000000000000) (34921397563 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 170 12 (428208240544173 / 800000000000)) (orderedInterval (31711896054 / 1000000000000) (31711940161 / 1000000000000), orderedInterval (-13583930689 / 1000000000000) (-13583886582 / 1000000000000))) = true
  rfl'

theorem compactCertificate418_stateChecks6 :
    compactCertificate418.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 94 12 (1184446528710231 / 4000000000000)) (orderedInterval (46361311255 / 1000000000000) (46361311425 / 1000000000000), orderedInterval (-824879241 / 1000000000000) (-824879072 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (1004068439773791 / 4000000000000)) (orderedInterval (23013671183 / 1000000000000) (23013671184 / 1000000000000), orderedInterval (44748519924 / 1000000000000) (44748519925 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (628299409217973 / 4000000000000)) (orderedInterval (44764669772 / 1000000000000) (44764669773 / 1000000000000), orderedInterval (45124440124 / 1000000000000) (45124440125 / 1000000000000))) = true
  rfl'

theorem compactCertificate418_stateChecks7 :
    compactCertificate418.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (337901511906891 / 4000000000000)) (orderedInterval (-36684667023 / 1000000000000) (-36684667022 / 1000000000000), orderedInterval (-78462464606 / 1000000000000) (-78462464605 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (917468336033673 / 4000000000000)) (orderedInterval (-38363403819 / 1000000000000) (-38363403818 / 1000000000000), orderedInterval (-36024524164 / 1000000000000) (-36024524163 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 100 12 (1252724576073321 / 4000000000000)) (orderedInterval (-8653094846 / 1000000000000) (-8653094821 / 1000000000000), orderedInterval (44261740279 / 1000000000000) (44261740304 / 1000000000000))) = true
  rfl'

theorem compactCertificate418_stateChecks8 :
    compactCertificate418.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (529700590782027 / 4000000000000)) (orderedInterval (66070530113 / 1000000000000) (66070530114 / 1000000000000), orderedInterval (20775535056 / 1000000000000) (20775535057 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 171 12 (2153203493431467 / 4000000000000)) (orderedInterval (-32824068786 / 1000000000000) (-32824051150 / 1000000000000), orderedInterval (10288519847 / 1000000000000) (10288537483 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 115 12 (1438240145412453 / 4000000000000)) (orderedInterval (33932307514 / 1000000000000) (33932395495 / 1000000000000), orderedInterval (-24929893259 / 1000000000000) (-24929805277 / 1000000000000))) = true
  rfl'

theorem compactCertificate418_states : ∀ j,
    BesselStateValid (compactCertificate418.point j) (compactCertificate418.state j) :=
  compactCertificate418.statesValid_of_checks3 compactCertificate418_stateChecks0
    compactCertificate418_stateChecks1 compactCertificate418_stateChecks2
    compactCertificate418_stateChecks3 compactCertificate418_stateChecks4
    compactCertificate418_stateChecks5 compactCertificate418_stateChecks6
    compactCertificate418_stateChecks7 compactCertificate418_stateChecks8

theorem compactCertificate418_chunkChecks0_0 :
    compactCertificate418.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (579 / 2) 0 (IntervalRat.scale (579 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (44624743182 / 1000000000000) (44624743183 / 1000000000000), orderedInterval (14333398789 / 1000000000000) (14333398791 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (852977558834679 / 4000000000000) 0 (IntervalRat.scale (579 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (21322674116 / 1000000000000) (21322674117 / 1000000000000), orderedInterval (50256556081 / 1000000000000) (50256556082 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (275835416997207 / 800000000000) 0 (IntervalRat.scale (579 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (176818003 / 1000000000000) (176818005 / 1000000000000), orderedInterval (42968876710 / 1000000000000) (42968876711 / 1000000000000)))) (orderedInterval (17896747847 / 1000000000000) (17896747869 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (248896724311653 / 4000000000000) 0 (IntervalRat.scale (579 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (17682001615 / 1000000000000) (17682001616 / 1000000000000), orderedInterval (99450716614 / 1000000000000) (99450716616 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (668571611721441 / 4000000000000) 0 (IntervalRat.scale (579 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-61044094340 / 1000000000000) (-61044094334 / 1000000000000), orderedInterval (-8896897994 / 1000000000000) (-8896897989 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1815301981523997 / 4000000000000) 0 (IntervalRat.scale (579 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29805434130 / 1000000000000) (29805484151 / 1000000000000), orderedInterval (-22713685178 / 1000000000000) (-22713635157 / 1000000000000)))) (orderedInterval (-4539524834 / 1000000000000) (-4539521243 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1337143223443461 / 4000000000000) 0 (IntervalRat.scale (579 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (38479710658 / 1000000000000) (38479749400 / 1000000000000), orderedInterval (-20642197864 / 1000000000000) (-20642159121 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2291217704246553 / 4000000000000) 0 (IntervalRat.scale (579 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (32310061131 / 1000000000000) (32310073523 / 1000000000000), orderedInterval (-8242086668 / 1000000000000) (-8242074276 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1687700590782027 / 4000000000000) 0 (IntervalRat.scale (579 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (38309638403 / 1000000000000) (38309640747 / 1000000000000), orderedInterval (-6465353174 / 1000000000000) (-6465350831 / 1000000000000)))) (orderedInterval (-70703573 / 1000000000000) (-70703117 / 1000000000000))) = true
  rfl'

theorem compactCertificate418_chunkChecks0_1 :
    compactCertificate418.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2589366717944421 / 4000000000000) 0 (IntervalRat.scale (579 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (25668040787 / 1000000000000) (25668040788 / 1000000000000), orderedInterval (17996516938 / 1000000000000) (17996516939 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1494971571635709 / 4000000000000) 0 (IntervalRat.scale (579 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-25901029981 / 1000000000000) (-25901029980 / 1000000000000), orderedInterval (-32097884961 / 1000000000000) (-32097884960 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2652853288112481 / 4000000000000) 0 (IntervalRat.scale (579 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-27920578830 / 1000000000000) (-27920578827 / 1000000000000), orderedInterval (-13408137956 / 1000000000000) (-13408137953 / 1000000000000)))) (orderedInterval (-10449028960 / 1000000000000) (-10449028845 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2478639660832389 / 4000000000000) 0 (IntervalRat.scale (579 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-32046547528 / 1000000000000) (-32046546655 / 1000000000000), orderedInterval (-597123650 / 1000000000000) (-597122777 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1768874218252437 / 4000000000000) 0 (IntervalRat.scale (579 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-1483382292 / 1000000000000) (-1483382291 / 1000000000000), orderedInterval (-37911445646 / 1000000000000) (-37911445645 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2005714835164323 / 4000000000000) 0 (IntervalRat.scale (579 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-15208069661 / 1000000000000) (-15208069440 / 1000000000000), orderedInterval (32238242606 / 1000000000000) (32238242827 / 1000000000000)))) (orderedInterval (515227756 / 1000000000000) (515227808 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1672155923276787 / 4000000000000) 0 (IntervalRat.scale (579 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-32673302490 / 1000000000000) (-32673302489 / 1000000000000), orderedInterval (-21299305460 / 1000000000000) (-21299305459 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1477400469616527 / 4000000000000) 0 (IntervalRat.scale (579 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-22499879772 / 1000000000000) (-22499877302 / 1000000000000), orderedInterval (34921395093 / 1000000000000) (34921397563 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (428208240544173 / 800000000000) 0 (IntervalRat.scale (579 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (31711896054 / 1000000000000) (31711940161 / 1000000000000), orderedInterval (-13583930689 / 1000000000000) (-13583886582 / 1000000000000)))) (orderedInterval (1722242483 / 1000000000000) (1722243782 / 1000000000000))) = true
  rfl'

theorem compactCertificate418_chunkChecks0_2 :
    compactCertificate418.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1184446528710231 / 4000000000000) 0 (IntervalRat.scale (579 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (46361311255 / 1000000000000) (46361311425 / 1000000000000), orderedInterval (-824879241 / 1000000000000) (-824879072 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1004068439773791 / 4000000000000) 0 (IntervalRat.scale (579 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (23013671183 / 1000000000000) (23013671184 / 1000000000000), orderedInterval (44748519924 / 1000000000000) (44748519925 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (628299409217973 / 4000000000000) 0 (IntervalRat.scale (579 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (44764669772 / 1000000000000) (44764669773 / 1000000000000), orderedInterval (45124440124 / 1000000000000) (45124440125 / 1000000000000)))) (orderedInterval (-7258070155 / 1000000000000) (-7258070055 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (337901511906891 / 4000000000000) 0 (IntervalRat.scale (579 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-36684667023 / 1000000000000) (-36684667022 / 1000000000000), orderedInterval (-78462464606 / 1000000000000) (-78462464605 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (917468336033673 / 4000000000000) 0 (IntervalRat.scale (579 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-38363403819 / 1000000000000) (-38363403818 / 1000000000000), orderedInterval (-36024524164 / 1000000000000) (-36024524163 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1252724576073321 / 4000000000000) 0 (IntervalRat.scale (579 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-8653094846 / 1000000000000) (-8653094821 / 1000000000000), orderedInterval (44261740279 / 1000000000000) (44261740304 / 1000000000000)))) (orderedInterval (2210895308 / 1000000000000) (2210895346 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (529700590782027 / 4000000000000) 0 (IntervalRat.scale (579 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (66070530113 / 1000000000000) (66070530114 / 1000000000000), orderedInterval (20775535056 / 1000000000000) (20775535057 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2153203493431467 / 4000000000000) 0 (IntervalRat.scale (579 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-32824068786 / 1000000000000) (-32824051150 / 1000000000000), orderedInterval (10288519847 / 1000000000000) (10288537483 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1438240145412453 / 4000000000000) 0 (IntervalRat.scale (579 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (33932307514 / 1000000000000) (33932395495 / 1000000000000), orderedInterval (-24929893259 / 1000000000000) (-24929805277 / 1000000000000)))) (orderedInterval (-3296386641 / 1000000000000) (-3296368617 / 1000000000000))) = true
  rfl'

theorem compactCertificate418_chunkChecks0 :
    compactCertificate418.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate418.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate418_chunkChecks0_0
    compactCertificate418_chunkChecks0_1 compactCertificate418_chunkChecks0_2

theorem compactCertificate418_chunkChecks1_0 :
    compactCertificate418.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (579 / 2) 1 (IntervalRat.scale (579 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (44624743182 / 1000000000000) (44624743183 / 1000000000000), orderedInterval (14333398789 / 1000000000000) (14333398791 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (852977558834679 / 4000000000000) 1 (IntervalRat.scale (579 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (21322674116 / 1000000000000) (21322674117 / 1000000000000), orderedInterval (50256556081 / 1000000000000) (50256556082 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (275835416997207 / 800000000000) 1 (IntervalRat.scale (579 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (176818003 / 1000000000000) (176818005 / 1000000000000), orderedInterval (42968876710 / 1000000000000) (42968876711 / 1000000000000)))) (orderedInterval (9029260496 / 1000000000000) (9029260520 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (248896724311653 / 4000000000000) 1 (IntervalRat.scale (579 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (17682001615 / 1000000000000) (17682001616 / 1000000000000), orderedInterval (99450716614 / 1000000000000) (99450716616 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (668571611721441 / 4000000000000) 1 (IntervalRat.scale (579 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-61044094340 / 1000000000000) (-61044094334 / 1000000000000), orderedInterval (-8896897994 / 1000000000000) (-8896897989 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1815301981523997 / 4000000000000) 1 (IntervalRat.scale (579 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29805434130 / 1000000000000) (29805484151 / 1000000000000), orderedInterval (-22713685178 / 1000000000000) (-22713635157 / 1000000000000)))) (orderedInterval (2111782346 / 1000000000000) (2111787960 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1337143223443461 / 4000000000000) 1 (IntervalRat.scale (579 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (38479710658 / 1000000000000) (38479749400 / 1000000000000), orderedInterval (-20642197864 / 1000000000000) (-20642159121 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2291217704246553 / 4000000000000) 1 (IntervalRat.scale (579 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (32310061131 / 1000000000000) (32310073523 / 1000000000000), orderedInterval (-8242086668 / 1000000000000) (-8242074276 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1687700590782027 / 4000000000000) 1 (IntervalRat.scale (579 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (38309638403 / 1000000000000) (38309640747 / 1000000000000), orderedInterval (-6465353174 / 1000000000000) (-6465350831 / 1000000000000)))) (orderedInterval (275266537 / 1000000000000) (275267405 / 1000000000000))) = true
  rfl'

theorem compactCertificate418_chunkChecks1_1 :
    compactCertificate418.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2589366717944421 / 4000000000000) 1 (IntervalRat.scale (579 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (25668040787 / 1000000000000) (25668040788 / 1000000000000), orderedInterval (17996516938 / 1000000000000) (17996516939 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1494971571635709 / 4000000000000) 1 (IntervalRat.scale (579 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-25901029981 / 1000000000000) (-25901029980 / 1000000000000), orderedInterval (-32097884961 / 1000000000000) (-32097884960 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2652853288112481 / 4000000000000) 1 (IntervalRat.scale (579 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-27920578830 / 1000000000000) (-27920578827 / 1000000000000), orderedInterval (-13408137956 / 1000000000000) (-13408137953 / 1000000000000)))) (orderedInterval (-14587191946 / 1000000000000) (-14587191706 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2478639660832389 / 4000000000000) 1 (IntervalRat.scale (579 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-32046547528 / 1000000000000) (-32046546655 / 1000000000000), orderedInterval (-597123650 / 1000000000000) (-597122777 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1768874218252437 / 4000000000000) 1 (IntervalRat.scale (579 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-1483382292 / 1000000000000) (-1483382291 / 1000000000000), orderedInterval (-37911445646 / 1000000000000) (-37911445645 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2005714835164323 / 4000000000000) 1 (IntervalRat.scale (579 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-15208069661 / 1000000000000) (-15208069440 / 1000000000000), orderedInterval (32238242606 / 1000000000000) (32238242827 / 1000000000000)))) (orderedInterval (-5735700817 / 1000000000000) (-5735700724 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1672155923276787 / 4000000000000) 1 (IntervalRat.scale (579 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-32673302490 / 1000000000000) (-32673302489 / 1000000000000), orderedInterval (-21299305460 / 1000000000000) (-21299305459 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1477400469616527 / 4000000000000) 1 (IntervalRat.scale (579 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-22499879772 / 1000000000000) (-22499877302 / 1000000000000), orderedInterval (34921395093 / 1000000000000) (34921397563 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (428208240544173 / 800000000000) 1 (IntervalRat.scale (579 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (31711896054 / 1000000000000) (31711940161 / 1000000000000), orderedInterval (-13583930689 / 1000000000000) (-13583886582 / 1000000000000)))) (orderedInterval (-3547865012 / 1000000000000) (-3547862703 / 1000000000000))) = true
  rfl'

theorem compactCertificate418_chunkChecks1_2 :
    compactCertificate418.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1184446528710231 / 4000000000000) 1 (IntervalRat.scale (579 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (46361311255 / 1000000000000) (46361311425 / 1000000000000), orderedInterval (-824879241 / 1000000000000) (-824879072 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1004068439773791 / 4000000000000) 1 (IntervalRat.scale (579 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (23013671183 / 1000000000000) (23013671184 / 1000000000000), orderedInterval (44748519924 / 1000000000000) (44748519925 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (628299409217973 / 4000000000000) 1 (IntervalRat.scale (579 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (44764669772 / 1000000000000) (44764669773 / 1000000000000), orderedInterval (45124440124 / 1000000000000) (45124440125 / 1000000000000)))) (orderedInterval (-1264122465 / 1000000000000) (-1264122370 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (337901511906891 / 4000000000000) 1 (IntervalRat.scale (579 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-36684667023 / 1000000000000) (-36684667022 / 1000000000000), orderedInterval (-78462464606 / 1000000000000) (-78462464605 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (917468336033673 / 4000000000000) 1 (IntervalRat.scale (579 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-38363403819 / 1000000000000) (-38363403818 / 1000000000000), orderedInterval (-36024524164 / 1000000000000) (-36024524163 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1252724576073321 / 4000000000000) 1 (IntervalRat.scale (579 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-8653094846 / 1000000000000) (-8653094821 / 1000000000000), orderedInterval (44261740279 / 1000000000000) (44261740304 / 1000000000000)))) (orderedInterval (-2599365116 / 1000000000000) (-2599365082 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (529700590782027 / 4000000000000) 1 (IntervalRat.scale (579 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (66070530113 / 1000000000000) (66070530114 / 1000000000000), orderedInterval (20775535056 / 1000000000000) (20775535057 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2153203493431467 / 4000000000000) 1 (IntervalRat.scale (579 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-32824068786 / 1000000000000) (-32824051150 / 1000000000000), orderedInterval (10288519847 / 1000000000000) (10288537483 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1438240145412453 / 4000000000000) 1 (IntervalRat.scale (579 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (33932307514 / 1000000000000) (33932395495 / 1000000000000), orderedInterval (-24929893259 / 1000000000000) (-24929805277 / 1000000000000)))) (orderedInterval (4309481229 / 1000000000000) (4309504514 / 1000000000000))) = true
  rfl'

theorem compactCertificate418_chunkChecks1 :
    compactCertificate418.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate418.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate418_chunkChecks1_0
    compactCertificate418_chunkChecks1_1 compactCertificate418_chunkChecks1_2

theorem compactCertificate418_chunkChecks2_0 :
    compactCertificate418.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (579 / 2) 2 (IntervalRat.scale (579 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (44624743182 / 1000000000000) (44624743183 / 1000000000000), orderedInterval (14333398789 / 1000000000000) (14333398791 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (852977558834679 / 4000000000000) 2 (IntervalRat.scale (579 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (21322674116 / 1000000000000) (21322674117 / 1000000000000), orderedInterval (50256556081 / 1000000000000) (50256556082 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (275835416997207 / 800000000000) 2 (IntervalRat.scale (579 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (176818003 / 1000000000000) (176818005 / 1000000000000), orderedInterval (42968876710 / 1000000000000) (42968876711 / 1000000000000)))) (orderedInterval (-17841394774 / 1000000000000) (-17841394747 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (248896724311653 / 4000000000000) 2 (IntervalRat.scale (579 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (17682001615 / 1000000000000) (17682001616 / 1000000000000), orderedInterval (99450716614 / 1000000000000) (99450716616 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (668571611721441 / 4000000000000) 2 (IntervalRat.scale (579 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-61044094340 / 1000000000000) (-61044094334 / 1000000000000), orderedInterval (-8896897994 / 1000000000000) (-8896897989 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1815301981523997 / 4000000000000) 2 (IntervalRat.scale (579 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29805434130 / 1000000000000) (29805484151 / 1000000000000), orderedInterval (-22713685178 / 1000000000000) (-22713635157 / 1000000000000)))) (orderedInterval (5951448112 / 1000000000000) (5951456925 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1337143223443461 / 4000000000000) 2 (IntervalRat.scale (579 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (38479710658 / 1000000000000) (38479749400 / 1000000000000), orderedInterval (-20642197864 / 1000000000000) (-20642159121 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2291217704246553 / 4000000000000) 2 (IntervalRat.scale (579 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (32310061131 / 1000000000000) (32310073523 / 1000000000000), orderedInterval (-8242086668 / 1000000000000) (-8242074276 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1687700590782027 / 4000000000000) 2 (IntervalRat.scale (579 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (38309638403 / 1000000000000) (38309640747 / 1000000000000), orderedInterval (-6465353174 / 1000000000000) (-6465350831 / 1000000000000)))) (orderedInterval (1933850129 / 1000000000000) (1933851800 / 1000000000000))) = true
  rfl'

theorem compactCertificate418_chunkChecks2_1 :
    compactCertificate418.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2589366717944421 / 4000000000000) 2 (IntervalRat.scale (579 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (25668040787 / 1000000000000) (25668040788 / 1000000000000), orderedInterval (17996516938 / 1000000000000) (17996516939 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1494971571635709 / 4000000000000) 2 (IntervalRat.scale (579 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-25901029981 / 1000000000000) (-25901029980 / 1000000000000), orderedInterval (-32097884961 / 1000000000000) (-32097884960 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2652853288112481 / 4000000000000) 2 (IntervalRat.scale (579 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-27920578830 / 1000000000000) (-27920578827 / 1000000000000), orderedInterval (-13408137956 / 1000000000000) (-13408137953 / 1000000000000)))) (orderedInterval (46883762795 / 1000000000000) (46883763309 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2478639660832389 / 4000000000000) 2 (IntervalRat.scale (579 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-32046547528 / 1000000000000) (-32046546655 / 1000000000000), orderedInterval (-597123650 / 1000000000000) (-597122777 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1768874218252437 / 4000000000000) 2 (IntervalRat.scale (579 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-1483382292 / 1000000000000) (-1483382291 / 1000000000000), orderedInterval (-37911445646 / 1000000000000) (-37911445645 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2005714835164323 / 4000000000000) 2 (IntervalRat.scale (579 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-15208069661 / 1000000000000) (-15208069440 / 1000000000000), orderedInterval (32238242606 / 1000000000000) (32238242827 / 1000000000000)))) (orderedInterval (-2534357867 / 1000000000000) (-2534357698 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1672155923276787 / 4000000000000) 2 (IntervalRat.scale (579 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-32673302490 / 1000000000000) (-32673302489 / 1000000000000), orderedInterval (-21299305460 / 1000000000000) (-21299305459 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1477400469616527 / 4000000000000) 2 (IntervalRat.scale (579 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-22499879772 / 1000000000000) (-22499877302 / 1000000000000), orderedInterval (34921395093 / 1000000000000) (34921397563 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (428208240544173 / 800000000000) 2 (IntervalRat.scale (579 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (31711896054 / 1000000000000) (31711940161 / 1000000000000), orderedInterval (-13583930689 / 1000000000000) (-13583886582 / 1000000000000)))) (orderedInterval (-4072495360 / 1000000000000) (-4072491202 / 1000000000000))) = true
  rfl'

theorem compactCertificate418_chunkChecks2_2 :
    compactCertificate418.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1184446528710231 / 4000000000000) 2 (IntervalRat.scale (579 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (46361311255 / 1000000000000) (46361311425 / 1000000000000), orderedInterval (-824879241 / 1000000000000) (-824879072 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1004068439773791 / 4000000000000) 2 (IntervalRat.scale (579 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (23013671183 / 1000000000000) (23013671184 / 1000000000000), orderedInterval (44748519924 / 1000000000000) (44748519925 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (628299409217973 / 4000000000000) 2 (IntervalRat.scale (579 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (44764669772 / 1000000000000) (44764669773 / 1000000000000), orderedInterval (45124440124 / 1000000000000) (45124440125 / 1000000000000)))) (orderedInterval (8309920926 / 1000000000000) (8309921019 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (337901511906891 / 4000000000000) 2 (IntervalRat.scale (579 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-36684667023 / 1000000000000) (-36684667022 / 1000000000000), orderedInterval (-78462464606 / 1000000000000) (-78462464605 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (917468336033673 / 4000000000000) 2 (IntervalRat.scale (579 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-38363403819 / 1000000000000) (-38363403818 / 1000000000000), orderedInterval (-36024524164 / 1000000000000) (-36024524163 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1252724576073321 / 4000000000000) 2 (IntervalRat.scale (579 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-8653094846 / 1000000000000) (-8653094821 / 1000000000000), orderedInterval (44261740279 / 1000000000000) (44261740304 / 1000000000000)))) (orderedInterval (-1371124343 / 1000000000000) (-1371124309 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (529700590782027 / 4000000000000) 2 (IntervalRat.scale (579 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (66070530113 / 1000000000000) (66070530114 / 1000000000000), orderedInterval (20775535056 / 1000000000000) (20775535057 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2153203493431467 / 4000000000000) 2 (IntervalRat.scale (579 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-32824068786 / 1000000000000) (-32824051150 / 1000000000000), orderedInterval (10288519847 / 1000000000000) (10288537483 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1438240145412453 / 4000000000000) 2 (IntervalRat.scale (579 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (33932307514 / 1000000000000) (33932395495 / 1000000000000), orderedInterval (-24929893259 / 1000000000000) (-24929805277 / 1000000000000)))) (orderedInterval (484691756 / 1000000000000) (484722430 / 1000000000000))) = true
  rfl'

theorem compactCertificate418_chunkChecks2 :
    compactCertificate418.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate418.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate418_chunkChecks2_0
    compactCertificate418_chunkChecks2_1 compactCertificate418_chunkChecks2_2

theorem compactCertificate418_chunkChecks3_0 :
    compactCertificate418.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (579 / 2) 3 (IntervalRat.scale (579 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (44624743182 / 1000000000000) (44624743183 / 1000000000000), orderedInterval (14333398789 / 1000000000000) (14333398791 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (852977558834679 / 4000000000000) 3 (IntervalRat.scale (579 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (21322674116 / 1000000000000) (21322674117 / 1000000000000), orderedInterval (50256556081 / 1000000000000) (50256556082 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (275835416997207 / 800000000000) 3 (IntervalRat.scale (579 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (176818003 / 1000000000000) (176818005 / 1000000000000), orderedInterval (42968876710 / 1000000000000) (42968876711 / 1000000000000)))) (orderedInterval (-10066456147 / 1000000000000) (-10066456115 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (248896724311653 / 4000000000000) 3 (IntervalRat.scale (579 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (17682001615 / 1000000000000) (17682001616 / 1000000000000), orderedInterval (99450716614 / 1000000000000) (99450716616 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (668571611721441 / 4000000000000) 3 (IntervalRat.scale (579 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-61044094340 / 1000000000000) (-61044094334 / 1000000000000), orderedInterval (-8896897994 / 1000000000000) (-8896897989 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1815301981523997 / 4000000000000) 3 (IntervalRat.scale (579 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29805434130 / 1000000000000) (29805484151 / 1000000000000), orderedInterval (-22713685178 / 1000000000000) (-22713635157 / 1000000000000)))) (orderedInterval (-6167654056 / 1000000000000) (-6167640245 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1337143223443461 / 4000000000000) 3 (IntervalRat.scale (579 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (38479710658 / 1000000000000) (38479749400 / 1000000000000), orderedInterval (-20642197864 / 1000000000000) (-20642159121 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2291217704246553 / 4000000000000) 3 (IntervalRat.scale (579 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (32310061131 / 1000000000000) (32310073523 / 1000000000000), orderedInterval (-8242086668 / 1000000000000) (-8242074276 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1687700590782027 / 4000000000000) 3 (IntervalRat.scale (579 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (38309638403 / 1000000000000) (38309640747 / 1000000000000), orderedInterval (-6465353174 / 1000000000000) (-6465350831 / 1000000000000)))) (orderedInterval (-1492118210 / 1000000000000) (-1492114977 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate418_chunkChecks3_1 :
    compactCertificate418.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2589366717944421 / 4000000000000) 3 (IntervalRat.scale (579 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (25668040787 / 1000000000000) (25668040788 / 1000000000000), orderedInterval (17996516938 / 1000000000000) (17996516939 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1494971571635709 / 4000000000000) 3 (IntervalRat.scale (579 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-25901029981 / 1000000000000) (-25901029980 / 1000000000000), orderedInterval (-32097884961 / 1000000000000) (-32097884960 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2652853288112481 / 4000000000000) 3 (IntervalRat.scale (579 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-27920578830 / 1000000000000) (-27920578827 / 1000000000000), orderedInterval (-13408137956 / 1000000000000) (-13408137953 / 1000000000000)))) (orderedInterval (63623462816 / 1000000000000) (63623463941 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2478639660832389 / 4000000000000) 3 (IntervalRat.scale (579 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-32046547528 / 1000000000000) (-32046546655 / 1000000000000), orderedInterval (-597123650 / 1000000000000) (-597122777 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1768874218252437 / 4000000000000) 3 (IntervalRat.scale (579 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-1483382292 / 1000000000000) (-1483382291 / 1000000000000), orderedInterval (-37911445646 / 1000000000000) (-37911445645 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2005714835164323 / 4000000000000) 3 (IntervalRat.scale (579 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-15208069661 / 1000000000000) (-15208069440 / 1000000000000), orderedInterval (32238242606 / 1000000000000) (32238242827 / 1000000000000)))) (orderedInterval (13528495651 / 1000000000000) (13528495969 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1672155923276787 / 4000000000000) 3 (IntervalRat.scale (579 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-32673302490 / 1000000000000) (-32673302489 / 1000000000000), orderedInterval (-21299305460 / 1000000000000) (-21299305459 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1477400469616527 / 4000000000000) 3 (IntervalRat.scale (579 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-22499879772 / 1000000000000) (-22499877302 / 1000000000000), orderedInterval (34921395093 / 1000000000000) (34921397563 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (428208240544173 / 800000000000) 3 (IntervalRat.scale (579 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (31711896054 / 1000000000000) (31711940161 / 1000000000000), orderedInterval (-13583930689 / 1000000000000) (-13583886582 / 1000000000000)))) (orderedInterval (7102964432 / 1000000000000) (7102971969 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate418_chunkChecks3_2 :
    compactCertificate418.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1184446528710231 / 4000000000000) 3 (IntervalRat.scale (579 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (46361311255 / 1000000000000) (46361311425 / 1000000000000), orderedInterval (-824879241 / 1000000000000) (-824879072 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1004068439773791 / 4000000000000) 3 (IntervalRat.scale (579 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (23013671183 / 1000000000000) (23013671184 / 1000000000000), orderedInterval (44748519924 / 1000000000000) (44748519925 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (628299409217973 / 4000000000000) 3 (IntervalRat.scale (579 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (44764669772 / 1000000000000) (44764669773 / 1000000000000), orderedInterval (45124440124 / 1000000000000) (45124440125 / 1000000000000)))) (orderedInterval (1246546697 / 1000000000000) (1246546788 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (337901511906891 / 4000000000000) 3 (IntervalRat.scale (579 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-36684667023 / 1000000000000) (-36684667022 / 1000000000000), orderedInterval (-78462464606 / 1000000000000) (-78462464605 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (917468336033673 / 4000000000000) 3 (IntervalRat.scale (579 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-38363403819 / 1000000000000) (-38363403818 / 1000000000000), orderedInterval (-36024524164 / 1000000000000) (-36024524163 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1252724576073321 / 4000000000000) 3 (IntervalRat.scale (579 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-8653094846 / 1000000000000) (-8653094821 / 1000000000000), orderedInterval (44261740279 / 1000000000000) (44261740304 / 1000000000000)))) (orderedInterval (3856806665 / 1000000000000) (3856806700 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (529700590782027 / 4000000000000) 3 (IntervalRat.scale (579 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (66070530113 / 1000000000000) (66070530114 / 1000000000000), orderedInterval (20775535056 / 1000000000000) (20775535057 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2153203493431467 / 4000000000000) 3 (IntervalRat.scale (579 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-32824068786 / 1000000000000) (-32824051150 / 1000000000000), orderedInterval (10288519847 / 1000000000000) (10288537483 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1438240145412453 / 4000000000000) 3 (IntervalRat.scale (579 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (33932307514 / 1000000000000) (33932395495 / 1000000000000), orderedInterval (-24929893259 / 1000000000000) (-24929805277 / 1000000000000)))) (orderedInterval (-3591021720 / 1000000000000) (-3590980502 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate418_chunkChecks3 :
    compactCertificate418.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate418.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate418_chunkChecks3_0
    compactCertificate418_chunkChecks3_1 compactCertificate418_chunkChecks3_2

theorem compactCertificate418_chunkChecks4_0 :
    compactCertificate418.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (579 / 2) 4 (IntervalRat.scale (579 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (44624743182 / 1000000000000) (44624743183 / 1000000000000), orderedInterval (14333398789 / 1000000000000) (14333398791 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (852977558834679 / 4000000000000) 4 (IntervalRat.scale (579 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (21322674116 / 1000000000000) (21322674117 / 1000000000000), orderedInterval (50256556081 / 1000000000000) (50256556082 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (275835416997207 / 800000000000) 4 (IntervalRat.scale (579 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (176818003 / 1000000000000) (176818005 / 1000000000000), orderedInterval (42968876710 / 1000000000000) (42968876711 / 1000000000000)))) (orderedInterval (17836383858 / 1000000000000) (17836383895 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (248896724311653 / 4000000000000) 4 (IntervalRat.scale (579 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (17682001615 / 1000000000000) (17682001616 / 1000000000000), orderedInterval (99450716614 / 1000000000000) (99450716616 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (668571611721441 / 4000000000000) 4 (IntervalRat.scale (579 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-61044094340 / 1000000000000) (-61044094334 / 1000000000000), orderedInterval (-8896897994 / 1000000000000) (-8896897989 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1815301981523997 / 4000000000000) 4 (IntervalRat.scale (579 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29805434130 / 1000000000000) (29805484151 / 1000000000000), orderedInterval (-22713685178 / 1000000000000) (-22713635157 / 1000000000000)))) (orderedInterval (-13001069428 / 1000000000000) (-13001047733 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1337143223443461 / 4000000000000) 4 (IntervalRat.scale (579 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (38479710658 / 1000000000000) (38479749400 / 1000000000000), orderedInterval (-20642197864 / 1000000000000) (-20642159121 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2291217704246553 / 4000000000000) 4 (IntervalRat.scale (579 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (32310061131 / 1000000000000) (32310073523 / 1000000000000), orderedInterval (-8242086668 / 1000000000000) (-8242074276 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1687700590782027 / 4000000000000) 4 (IntervalRat.scale (579 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (38309638403 / 1000000000000) (38309640747 / 1000000000000), orderedInterval (-6465353174 / 1000000000000) (-6465350831 / 1000000000000)))) (orderedInterval (-11085904398 / 1000000000000) (-11085898093 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate418_chunkChecks4_1 :
    compactCertificate418.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2589366717944421 / 4000000000000) 4 (IntervalRat.scale (579 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (25668040787 / 1000000000000) (25668040788 / 1000000000000), orderedInterval (17996516938 / 1000000000000) (17996516939 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1494971571635709 / 4000000000000) 4 (IntervalRat.scale (579 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-25901029981 / 1000000000000) (-25901029980 / 1000000000000), orderedInterval (-32097884961 / 1000000000000) (-32097884960 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2652853288112481 / 4000000000000) 4 (IntervalRat.scale (579 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-27920578830 / 1000000000000) (-27920578827 / 1000000000000), orderedInterval (-13408137956 / 1000000000000) (-13408137953 / 1000000000000)))) (orderedInterval (-229114310639 / 1000000000000) (-229114308142 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2478639660832389 / 4000000000000) 4 (IntervalRat.scale (579 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-32046547528 / 1000000000000) (-32046546655 / 1000000000000), orderedInterval (-597123650 / 1000000000000) (-597122777 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1768874218252437 / 4000000000000) 4 (IntervalRat.scale (579 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-1483382292 / 1000000000000) (-1483382291 / 1000000000000), orderedInterval (-37911445646 / 1000000000000) (-37911445645 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2005714835164323 / 4000000000000) 4 (IntervalRat.scale (579 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-15208069661 / 1000000000000) (-15208069440 / 1000000000000), orderedInterval (32238242606 / 1000000000000) (32238242827 / 1000000000000)))) (orderedInterval (11979183087 / 1000000000000) (11979183703 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1672155923276787 / 4000000000000) 4 (IntervalRat.scale (579 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-32673302490 / 1000000000000) (-32673302489 / 1000000000000), orderedInterval (-21299305460 / 1000000000000) (-21299305459 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1477400469616527 / 4000000000000) 4 (IntervalRat.scale (579 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-22499879772 / 1000000000000) (-22499877302 / 1000000000000), orderedInterval (34921395093 / 1000000000000) (34921397563 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (428208240544173 / 800000000000) 4 (IntervalRat.scale (579 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (31711896054 / 1000000000000) (31711940161 / 1000000000000), orderedInterval (-13583930689 / 1000000000000) (-13583886582 / 1000000000000)))) (orderedInterval (11210323333 / 1000000000000) (11210337102 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate418_chunkChecks4_2 :
    compactCertificate418.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1184446528710231 / 4000000000000) 4 (IntervalRat.scale (579 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (46361311255 / 1000000000000) (46361311425 / 1000000000000), orderedInterval (-824879241 / 1000000000000) (-824879072 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1004068439773791 / 4000000000000) 4 (IntervalRat.scale (579 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (23013671183 / 1000000000000) (23013671184 / 1000000000000), orderedInterval (44748519924 / 1000000000000) (44748519925 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (628299409217973 / 4000000000000) 4 (IntervalRat.scale (579 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (44764669772 / 1000000000000) (44764669773 / 1000000000000), orderedInterval (45124440124 / 1000000000000) (45124440125 / 1000000000000)))) (orderedInterval (-8732015632 / 1000000000000) (-8732015541 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (337901511906891 / 4000000000000) 4 (IntervalRat.scale (579 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-36684667023 / 1000000000000) (-36684667022 / 1000000000000), orderedInterval (-78462464606 / 1000000000000) (-78462464605 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (917468336033673 / 4000000000000) 4 (IntervalRat.scale (579 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-38363403819 / 1000000000000) (-38363403818 / 1000000000000), orderedInterval (-36024524164 / 1000000000000) (-36024524163 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1252724576073321 / 4000000000000) 4 (IntervalRat.scale (579 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-8653094846 / 1000000000000) (-8653094821 / 1000000000000), orderedInterval (44261740279 / 1000000000000) (44261740304 / 1000000000000)))) (orderedInterval (1229449730 / 1000000000000) (1229449766 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (529700590782027 / 4000000000000) 4 (IntervalRat.scale (579 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (66070530113 / 1000000000000) (66070530114 / 1000000000000), orderedInterval (20775535056 / 1000000000000) (20775535057 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2153203493431467 / 4000000000000) 4 (IntervalRat.scale (579 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-32824068786 / 1000000000000) (-32824051150 / 1000000000000), orderedInterval (10288519847 / 1000000000000) (10288537483 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1438240145412453 / 4000000000000) 4 (IntervalRat.scale (579 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (33932307514 / 1000000000000) (33932395495 / 1000000000000), orderedInterval (-24929893259 / 1000000000000) (-24929805277 / 1000000000000)))) (orderedInterval (16832482361 / 1000000000000) (16832539496 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate418_chunkChecks4 :
    compactCertificate418.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate418.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate418_chunkChecks4_0
    compactCertificate418_chunkChecks4_1 compactCertificate418_chunkChecks4_2

theorem compactCertificate418_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate418.chunkCheck r b = true :=
  compactCertificate418.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate418_chunkChecks0
    · exact compactCertificate418_chunkChecks1
    · exact compactCertificate418_chunkChecks2
    · exact compactCertificate418_chunkChecks3
    · exact compactCertificate418_chunkChecks4)

theorem compactCertificate418_coefficient0 :
    compactCertificate418.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate418_coefficient1 :
    compactCertificate418.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate418_coefficient2 :
    compactCertificate418.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate418_coefficient3 :
    compactCertificate418.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate418_coefficient4 :
    compactCertificate418.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate418_coefficients : ∀ r : Fin 5,
    compactCertificate418.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate418_coefficient0
  · exact compactCertificate418_coefficient1
  · exact compactCertificate418_coefficient2
  · exact compactCertificate418_coefficient3
  · exact compactCertificate418_coefficient4

theorem compactCertificate418_lower : (1 : ℚ) ≤ compactCertificate418.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate418, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate418_proves {t : ℝ} (ht : t ∈ compactCertificate418.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate418.proves compactCertificate418_states compactCertificate418_chunks
    compactCertificate418_coefficients compactCertificate418_lower ht

end Erdos232
