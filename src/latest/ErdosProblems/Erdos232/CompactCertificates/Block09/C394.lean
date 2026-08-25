/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate394 : CompactCertificate where
  left := 265
  right := 266
  center := 531 / 2
  grid := fun i =>
    match i.val with
    | 0 => 85
    | 1 => 62
    | 2 => 101
    | 3 => 18
    | 4 => 49
    | 5 => 133
    | 6 => 98
    | 7 => 167
    | 8 => 123
    | 9 => 189
    | 10 => 109
    | 11 => 194
    | 12 => 181
    | 13 => 129
    | 14 => 146
    | 15 => 122
    | 16 => 108
    | 17 => 156
    | 18 => 86
    | 19 => 73
    | 20 => 46
    | 21 => 25
    | 22 => 67
    | 23 => 91
    | 24 => 39
    | 25 => 157
    | _ => 105
  point := fun i =>
    match i.val with
    | 0 => 531 / 2
    | 1 => 782264393335431 / 4000000000000
    | 2 => 252968232168423 / 800000000000
    | 3 => 228262798980117 / 4000000000000
    | 4 => 613145985879249 / 4000000000000
    | 5 => 1664810625542733 / 4000000000000
    | 6 => 1226291971759029 / 4000000000000
    | 7 => 2101272195086217 / 4000000000000
    | 8 => 1547787588437403 / 4000000000000
    | 9 => 2374704192104469 / 4000000000000
    | 10 => 1371036104557101 / 4000000000000
    | 11 => 2432927626921809 / 4000000000000
    | 12 => 2273156580141621 / 4000000000000
    | 13 => 1622231796013893 / 4000000000000
    | 14 => 1839437957637747 / 4000000000000
    | 15 => 1533531598031043 / 4000000000000
    | 16 => 1354921674207903 / 4000000000000
    | 17 => 392709111794397 / 800000000000
    | 18 => 1086254070371559 / 4000000000000
    | 19 => 920829605388399 / 4000000000000
    | 20 => 576212411562597 / 4000000000000
    | 21 => 309888951334299 / 4000000000000
    | 22 => 841408784859897 / 4000000000000
    | 23 => 1148871761476569 / 4000000000000
    | 24 => 485787588437403 / 4000000000000
    | 25 => 1974699576877563 / 4000000000000
    | _ => 1319007801751317 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (33394147986 / 1000000000000) (33394173480 / 1000000000000), orderedInterval (-35876933215 / 1000000000000) (-35876907721 / 1000000000000))
    | 1 => (orderedInterval (57054800285 / 1000000000000) (57054800352 / 1000000000000), orderedInterval (-220982130 / 1000000000000) (-220982062 / 1000000000000))
    | 2 => (orderedInterval (13498198628 / 1000000000000) (13498198754 / 1000000000000), orderedInterval (-42812469407 / 1000000000000) (-42812469281 / 1000000000000))
    | 3 => (orderedInterval (101777324256 / 1000000000000) (101777324257 / 1000000000000), orderedInterval (27338062087 / 1000000000000) (27338062088 / 1000000000000))
    | 4 => (orderedInterval (-8548394666 / 1000000000000) (-8548394664 / 1000000000000), orderedInterval (-63847643604 / 1000000000000) (-63847643603 / 1000000000000))
    | 5 => (orderedInterval (29228924624 / 1000000000000) (29228954542 / 1000000000000), orderedInterval (-26020889480 / 1000000000000) (-26020859561 / 1000000000000))
    | 6 => (orderedInterval (-22567195820 / 1000000000000) (-22567193909 / 1000000000000), orderedInterval (39625836644 / 1000000000000) (39625838556 / 1000000000000))
    | 7 => (orderedInterval (-34587759897 / 1000000000000) (-34587759756 / 1000000000000), orderedInterval (-3911855981 / 1000000000000) (-3911855840 / 1000000000000))
    | 8 => (orderedInterval (-39252750131 / 1000000000000) (-39252750125 / 1000000000000), orderedInterval (-10169772817 / 1000000000000) (-10169772811 / 1000000000000))
    | 9 => (orderedInterval (-21101503104 / 1000000000000) (-21101503103 / 1000000000000), orderedInterval (-25023432421 / 1000000000000) (-25023432420 / 1000000000000))
    | 10 => (orderedInterval (-38610597071 / 1000000000000) (-38610597070 / 1000000000000), orderedInterval (-19089428078 / 1000000000000) (-19089428077 / 1000000000000))
    | 11 => (orderedInterval (-14126751881 / 1000000000000) (-14126751759 / 1000000000000), orderedInterval (29116730453 / 1000000000000) (29116730576 / 1000000000000))
    | 12 => (orderedInterval (-14439213202 / 1000000000000) (-14439213201 / 1000000000000), orderedInterval (-30182470779 / 1000000000000) (-30182470778 / 1000000000000))
    | 13 => (orderedInterval (-34897916318 / 1000000000000) (-34897916317 / 1000000000000), orderedInterval (-18715250956 / 1000000000000) (-18715250955 / 1000000000000))
    | 14 => (orderedInterval (34251365331 / 1000000000000) (34251395844 / 1000000000000), orderedInterval (-14570707930 / 1000000000000) (-14570677417 / 1000000000000))
    | 15 => (orderedInterval (31759236309 / 1000000000000) (31759236310 / 1000000000000), orderedInterval (25490582331 / 1000000000000) (25490582332 / 1000000000000))
    | 16 => (orderedInterval (9606296839 / 1000000000000) (9606296840 / 1000000000000), orderedInterval (42260516024 / 1000000000000) (42260516025 / 1000000000000))
    | 17 => (orderedInterval (36009466536 / 1000000000000) (36009467116 / 1000000000000), orderedInterval (-479004241 / 1000000000000) (-479003661 / 1000000000000))
    | 18 => (orderedInterval (39941898018 / 1000000000000) (39941974537 / 1000000000000), orderedInterval (-27439906159 / 1000000000000) (-27439829639 / 1000000000000))
    | 19 => (orderedInterval (-52396448169 / 1000000000000) (-52396447896 / 1000000000000), orderedInterval (4588637948 / 1000000000000) (4588638221 / 1000000000000))
    | 20 => (orderedInterval (21187372503 / 1000000000000) (21187372504 / 1000000000000), orderedInterval (62938026172 / 1000000000000) (62938026173 / 1000000000000))
    | 21 => (orderedInterval (25381651913 / 1000000000000) (25381652373 / 1000000000000), orderedInterval (-87188561633 / 1000000000000) (-87188561174 / 1000000000000))
    | 22 => (orderedInterval (-33305967469 / 1000000000000) (-33305967468 / 1000000000000), orderedInterval (-43706239649 / 1000000000000) (-43706239648 / 1000000000000))
    | 23 => (orderedInterval (-40205992520 / 1000000000000) (-40205940962 / 1000000000000), orderedInterval (24564512250 / 1000000000000) (24564563808 / 1000000000000))
    | 24 => (orderedInterval (20762034033 / 1000000000000) (20762034415 / 1000000000000), orderedInterval (-69446380630 / 1000000000000) (-69446380249 / 1000000000000))
    | 25 => (orderedInterval (-33844997260 / 1000000000000) (-33844997256 / 1000000000000), orderedInterval (-11968567140 / 1000000000000) (-11968567136 / 1000000000000))
    | _ => (orderedInterval (-27276325045 / 1000000000000) (-27276325044 / 1000000000000), orderedInterval (-34405768740 / 1000000000000) (-34405768739 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (14560000959 / 1000000000000) (14560011091 / 1000000000000)
      | 1 => orderedInterval (-3494204524 / 1000000000000) (-3494202365 / 1000000000000)
      | 2 => orderedInterval (118163364 / 1000000000000) (118163384 / 1000000000000)
      | 3 => orderedInterval (-1119446262 / 1000000000000) (-1119446139 / 1000000000000)
      | 4 => orderedInterval (-3212706435 / 1000000000000) (-3212706248 / 1000000000000)
      | 5 => orderedInterval (738993302 / 1000000000000) (738993343 / 1000000000000)
      | 6 => orderedInterval (-2731022582 / 1000000000000) (-2731010264 / 1000000000000)
      | 7 => orderedInterval (3368270573 / 1000000000000) (3368274566 / 1000000000000)
      | _ => orderedInterval (7997965371 / 1000000000000) (7997965447 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-17214006003 / 1000000000000) (-17213995867 / 1000000000000)
      | 1 => orderedInterval (1490139067 / 1000000000000) (1490142438 / 1000000000000)
      | 2 => orderedInterval (-119478931 / 1000000000000) (-119478895 / 1000000000000)
      | 3 => orderedInterval (17598690147 / 1000000000000) (17598690406 / 1000000000000)
      | 4 => orderedInterval (-1409348266 / 1000000000000) (-1409347946 / 1000000000000)
      | 5 => orderedInterval (-2683105423 / 1000000000000) (-2683105358 / 1000000000000)
      | 6 => orderedInterval (5374141447 / 1000000000000) (5374154036 / 1000000000000)
      | 7 => orderedInterval (-781220861 / 1000000000000) (-781216555 / 1000000000000)
      | _ => orderedInterval (9637732702 / 1000000000000) (9637732808 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-14583461374 / 1000000000000) (-14583451196 / 1000000000000)
      | 1 => orderedInterval (5255661774 / 1000000000000) (5255667064 / 1000000000000)
      | 2 => orderedInterval (-2160967930 / 1000000000000) (-2160967866 / 1000000000000)
      | 3 => orderedInterval (-3506402266 / 1000000000000) (-3506401706 / 1000000000000)
      | 4 => orderedInterval (7031136928 / 1000000000000) (7031137478 / 1000000000000)
      | 5 => orderedInterval (-3011580142 / 1000000000000) (-3011580036 / 1000000000000)
      | 6 => orderedInterval (4228545901 / 1000000000000) (4228558819 / 1000000000000)
      | 7 => orderedInterval (-4037529417 / 1000000000000) (-4037524747 / 1000000000000)
      | _ => orderedInterval (-17482370101 / 1000000000000) (-17482369946 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (18520129560 / 1000000000000) (18520139743 / 1000000000000)
      | 1 => orderedInterval (-6694250829 / 1000000000000) (-6694242540 / 1000000000000)
      | 2 => orderedInterval (-165590629 / 1000000000000) (-165590511 / 1000000000000)
      | 3 => orderedInterval (-96419853356 / 1000000000000) (-96419852119 / 1000000000000)
      | 4 => orderedInterval (554766743 / 1000000000000) (554767692 / 1000000000000)
      | 5 => orderedInterval (4224822144 / 1000000000000) (4224822323 / 1000000000000)
      | 6 => orderedInterval (-4868772743 / 1000000000000) (-4868759535 / 1000000000000)
      | 7 => orderedInterval (1865469701 / 1000000000000) (1865474751 / 1000000000000)
      | _ => orderedInterval (-18525126842 / 1000000000000) (-18525126604 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (14846811072 / 1000000000000) (14846821301 / 1000000000000)
      | 1 => orderedInterval (-12534718835 / 1000000000000) (-12534705813 / 1000000000000)
      | 2 => orderedInterval (12071317386 / 1000000000000) (12071317609 / 1000000000000)
      | 3 => orderedInterval (31204037957 / 1000000000000) (31204040715 / 1000000000000)
      | 4 => orderedInterval (-14059388194 / 1000000000000) (-14059386547 / 1000000000000)
      | 5 => orderedInterval (10880480883 / 1000000000000) (10880481192 / 1000000000000)
      | 6 => orderedInterval (-5217371668 / 1000000000000) (-5217358113 / 1000000000000)
      | 7 => orderedInterval (4500371136 / 1000000000000) (4500376616 / 1000000000000)
      | _ => orderedInterval (45255892366 / 1000000000000) (45255892749 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (16226013766 / 1000000000000) (16226042815 / 1000000000000)
    | 1 => orderedInterval (11893543879 / 1000000000000) (11893575067 / 1000000000000)
    | 2 => orderedInterval (-28266966627 / 1000000000000) (-28266932136 / 1000000000000)
    | 3 => orderedInterval (-101508406251 / 1000000000000) (-101508366800 / 1000000000000)
    | _ => orderedInterval (86947432103 / 1000000000000) (86947479709 / 1000000000000)

theorem compactCertificate394_stateChecks0 :
    compactCertificate394.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (531 / 2)) (orderedInterval (33394147986 / 1000000000000) (33394173480 / 1000000000000), orderedInterval (-35876933215 / 1000000000000) (-35876907721 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (782264393335431 / 4000000000000)) (orderedInterval (57054800285 / 1000000000000) (57054800352 / 1000000000000), orderedInterval (-220982130 / 1000000000000) (-220982062 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 101 12 (252968232168423 / 800000000000)) (orderedInterval (13498198628 / 1000000000000) (13498198754 / 1000000000000), orderedInterval (-42812469407 / 1000000000000) (-42812469281 / 1000000000000))) = true
  rfl'

theorem compactCertificate394_stateChecks1 :
    compactCertificate394.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 18 12 (228262798980117 / 4000000000000)) (orderedInterval (101777324256 / 1000000000000) (101777324257 / 1000000000000), orderedInterval (27338062087 / 1000000000000) (27338062088 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (613145985879249 / 4000000000000)) (orderedInterval (-8548394666 / 1000000000000) (-8548394664 / 1000000000000), orderedInterval (-63847643604 / 1000000000000) (-63847643603 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 133 12 (1664810625542733 / 4000000000000)) (orderedInterval (29228924624 / 1000000000000) (29228954542 / 1000000000000), orderedInterval (-26020889480 / 1000000000000) (-26020859561 / 1000000000000))) = true
  rfl'

theorem compactCertificate394_stateChecks2 :
    compactCertificate394.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 98 12 (1226291971759029 / 4000000000000)) (orderedInterval (-22567195820 / 1000000000000) (-22567193909 / 1000000000000), orderedInterval (39625836644 / 1000000000000) (39625838556 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 167 12 (2101272195086217 / 4000000000000)) (orderedInterval (-34587759897 / 1000000000000) (-34587759756 / 1000000000000), orderedInterval (-3911855981 / 1000000000000) (-3911855840 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 123 12 (1547787588437403 / 4000000000000)) (orderedInterval (-39252750131 / 1000000000000) (-39252750125 / 1000000000000), orderedInterval (-10169772817 / 1000000000000) (-10169772811 / 1000000000000))) = true
  rfl'

theorem compactCertificate394_stateChecks3 :
    compactCertificate394.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 189 12 (2374704192104469 / 4000000000000)) (orderedInterval (-21101503104 / 1000000000000) (-21101503103 / 1000000000000), orderedInterval (-25023432421 / 1000000000000) (-25023432420 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 109 12 (1371036104557101 / 4000000000000)) (orderedInterval (-38610597071 / 1000000000000) (-38610597070 / 1000000000000), orderedInterval (-19089428078 / 1000000000000) (-19089428077 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 194 12 (2432927626921809 / 4000000000000)) (orderedInterval (-14126751881 / 1000000000000) (-14126751759 / 1000000000000), orderedInterval (29116730453 / 1000000000000) (29116730576 / 1000000000000))) = true
  rfl'

theorem compactCertificate394_stateChecks4 :
    compactCertificate394.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 181 12 (2273156580141621 / 4000000000000)) (orderedInterval (-14439213202 / 1000000000000) (-14439213201 / 1000000000000), orderedInterval (-30182470779 / 1000000000000) (-30182470778 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 129 12 (1622231796013893 / 4000000000000)) (orderedInterval (-34897916318 / 1000000000000) (-34897916317 / 1000000000000), orderedInterval (-18715250956 / 1000000000000) (-18715250955 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 146 12 (1839437957637747 / 4000000000000)) (orderedInterval (34251365331 / 1000000000000) (34251395844 / 1000000000000), orderedInterval (-14570707930 / 1000000000000) (-14570677417 / 1000000000000))) = true
  rfl'

theorem compactCertificate394_stateChecks5 :
    compactCertificate394.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 122 12 (1533531598031043 / 4000000000000)) (orderedInterval (31759236309 / 1000000000000) (31759236310 / 1000000000000), orderedInterval (25490582331 / 1000000000000) (25490582332 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 108 12 (1354921674207903 / 4000000000000)) (orderedInterval (9606296839 / 1000000000000) (9606296840 / 1000000000000), orderedInterval (42260516024 / 1000000000000) (42260516025 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 156 12 (392709111794397 / 800000000000)) (orderedInterval (36009466536 / 1000000000000) (36009467116 / 1000000000000), orderedInterval (-479004241 / 1000000000000) (-479003661 / 1000000000000))) = true
  rfl'

theorem compactCertificate394_stateChecks6 :
    compactCertificate394.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (1086254070371559 / 4000000000000)) (orderedInterval (39941898018 / 1000000000000) (39941974537 / 1000000000000), orderedInterval (-27439906159 / 1000000000000) (-27439829639 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (920829605388399 / 4000000000000)) (orderedInterval (-52396448169 / 1000000000000) (-52396447896 / 1000000000000), orderedInterval (4588637948 / 1000000000000) (4588638221 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (576212411562597 / 4000000000000)) (orderedInterval (21187372503 / 1000000000000) (21187372504 / 1000000000000), orderedInterval (62938026172 / 1000000000000) (62938026173 / 1000000000000))) = true
  rfl'

theorem compactCertificate394_stateChecks7 :
    compactCertificate394.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (309888951334299 / 4000000000000)) (orderedInterval (25381651913 / 1000000000000) (25381652373 / 1000000000000), orderedInterval (-87188561633 / 1000000000000) (-87188561174 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (841408784859897 / 4000000000000)) (orderedInterval (-33305967469 / 1000000000000) (-33305967468 / 1000000000000), orderedInterval (-43706239649 / 1000000000000) (-43706239648 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 91 12 (1148871761476569 / 4000000000000)) (orderedInterval (-40205992520 / 1000000000000) (-40205940962 / 1000000000000), orderedInterval (24564512250 / 1000000000000) (24564563808 / 1000000000000))) = true
  rfl'

theorem compactCertificate394_stateChecks8 :
    compactCertificate394.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (485787588437403 / 4000000000000)) (orderedInterval (20762034033 / 1000000000000) (20762034415 / 1000000000000), orderedInterval (-69446380630 / 1000000000000) (-69446380249 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 157 12 (1974699576877563 / 4000000000000)) (orderedInterval (-33844997260 / 1000000000000) (-33844997256 / 1000000000000), orderedInterval (-11968567140 / 1000000000000) (-11968567136 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 105 12 (1319007801751317 / 4000000000000)) (orderedInterval (-27276325045 / 1000000000000) (-27276325044 / 1000000000000), orderedInterval (-34405768740 / 1000000000000) (-34405768739 / 1000000000000))) = true
  rfl'

theorem compactCertificate394_states : ∀ j,
    BesselStateValid (compactCertificate394.point j) (compactCertificate394.state j) :=
  compactCertificate394.statesValid_of_checks3 compactCertificate394_stateChecks0
    compactCertificate394_stateChecks1 compactCertificate394_stateChecks2
    compactCertificate394_stateChecks3 compactCertificate394_stateChecks4
    compactCertificate394_stateChecks5 compactCertificate394_stateChecks6
    compactCertificate394_stateChecks7 compactCertificate394_stateChecks8

theorem compactCertificate394_chunkChecks0_0 :
    compactCertificate394.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (531 / 2) 0 (IntervalRat.scale (531 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (33394147986 / 1000000000000) (33394173480 / 1000000000000), orderedInterval (-35876933215 / 1000000000000) (-35876907721 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (782264393335431 / 4000000000000) 0 (IntervalRat.scale (531 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (57054800285 / 1000000000000) (57054800352 / 1000000000000), orderedInterval (-220982130 / 1000000000000) (-220982062 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (252968232168423 / 800000000000) 0 (IntervalRat.scale (531 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (13498198628 / 1000000000000) (13498198754 / 1000000000000), orderedInterval (-42812469407 / 1000000000000) (-42812469281 / 1000000000000)))) (orderedInterval (14560000959 / 1000000000000) (14560011091 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (228262798980117 / 4000000000000) 0 (IntervalRat.scale (531 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (101777324256 / 1000000000000) (101777324257 / 1000000000000), orderedInterval (27338062087 / 1000000000000) (27338062088 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (613145985879249 / 4000000000000) 0 (IntervalRat.scale (531 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-8548394666 / 1000000000000) (-8548394664 / 1000000000000), orderedInterval (-63847643604 / 1000000000000) (-63847643603 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1664810625542733 / 4000000000000) 0 (IntervalRat.scale (531 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29228924624 / 1000000000000) (29228954542 / 1000000000000), orderedInterval (-26020889480 / 1000000000000) (-26020859561 / 1000000000000)))) (orderedInterval (-3494204524 / 1000000000000) (-3494202365 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1226291971759029 / 4000000000000) 0 (IntervalRat.scale (531 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-22567195820 / 1000000000000) (-22567193909 / 1000000000000), orderedInterval (39625836644 / 1000000000000) (39625838556 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2101272195086217 / 4000000000000) 0 (IntervalRat.scale (531 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-34587759897 / 1000000000000) (-34587759756 / 1000000000000), orderedInterval (-3911855981 / 1000000000000) (-3911855840 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1547787588437403 / 4000000000000) 0 (IntervalRat.scale (531 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-39252750131 / 1000000000000) (-39252750125 / 1000000000000), orderedInterval (-10169772817 / 1000000000000) (-10169772811 / 1000000000000)))) (orderedInterval (118163364 / 1000000000000) (118163384 / 1000000000000))) = true
  rfl'

theorem compactCertificate394_chunkChecks0_1 :
    compactCertificate394.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2374704192104469 / 4000000000000) 0 (IntervalRat.scale (531 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-21101503104 / 1000000000000) (-21101503103 / 1000000000000), orderedInterval (-25023432421 / 1000000000000) (-25023432420 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1371036104557101 / 4000000000000) 0 (IntervalRat.scale (531 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-38610597071 / 1000000000000) (-38610597070 / 1000000000000), orderedInterval (-19089428078 / 1000000000000) (-19089428077 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2432927626921809 / 4000000000000) 0 (IntervalRat.scale (531 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-14126751881 / 1000000000000) (-14126751759 / 1000000000000), orderedInterval (29116730453 / 1000000000000) (29116730576 / 1000000000000)))) (orderedInterval (-1119446262 / 1000000000000) (-1119446139 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2273156580141621 / 4000000000000) 0 (IntervalRat.scale (531 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-14439213202 / 1000000000000) (-14439213201 / 1000000000000), orderedInterval (-30182470779 / 1000000000000) (-30182470778 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1622231796013893 / 4000000000000) 0 (IntervalRat.scale (531 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-34897916318 / 1000000000000) (-34897916317 / 1000000000000), orderedInterval (-18715250956 / 1000000000000) (-18715250955 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1839437957637747 / 4000000000000) 0 (IntervalRat.scale (531 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (34251365331 / 1000000000000) (34251395844 / 1000000000000), orderedInterval (-14570707930 / 1000000000000) (-14570677417 / 1000000000000)))) (orderedInterval (-3212706435 / 1000000000000) (-3212706248 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1533531598031043 / 4000000000000) 0 (IntervalRat.scale (531 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (31759236309 / 1000000000000) (31759236310 / 1000000000000), orderedInterval (25490582331 / 1000000000000) (25490582332 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1354921674207903 / 4000000000000) 0 (IntervalRat.scale (531 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (9606296839 / 1000000000000) (9606296840 / 1000000000000), orderedInterval (42260516024 / 1000000000000) (42260516025 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (392709111794397 / 800000000000) 0 (IntervalRat.scale (531 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (36009466536 / 1000000000000) (36009467116 / 1000000000000), orderedInterval (-479004241 / 1000000000000) (-479003661 / 1000000000000)))) (orderedInterval (738993302 / 1000000000000) (738993343 / 1000000000000))) = true
  rfl'

theorem compactCertificate394_chunkChecks0_2 :
    compactCertificate394.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1086254070371559 / 4000000000000) 0 (IntervalRat.scale (531 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (39941898018 / 1000000000000) (39941974537 / 1000000000000), orderedInterval (-27439906159 / 1000000000000) (-27439829639 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (920829605388399 / 4000000000000) 0 (IntervalRat.scale (531 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-52396448169 / 1000000000000) (-52396447896 / 1000000000000), orderedInterval (4588637948 / 1000000000000) (4588638221 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (576212411562597 / 4000000000000) 0 (IntervalRat.scale (531 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (21187372503 / 1000000000000) (21187372504 / 1000000000000), orderedInterval (62938026172 / 1000000000000) (62938026173 / 1000000000000)))) (orderedInterval (-2731022582 / 1000000000000) (-2731010264 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (309888951334299 / 4000000000000) 0 (IntervalRat.scale (531 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (25381651913 / 1000000000000) (25381652373 / 1000000000000), orderedInterval (-87188561633 / 1000000000000) (-87188561174 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (841408784859897 / 4000000000000) 0 (IntervalRat.scale (531 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-33305967469 / 1000000000000) (-33305967468 / 1000000000000), orderedInterval (-43706239649 / 1000000000000) (-43706239648 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1148871761476569 / 4000000000000) 0 (IntervalRat.scale (531 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-40205992520 / 1000000000000) (-40205940962 / 1000000000000), orderedInterval (24564512250 / 1000000000000) (24564563808 / 1000000000000)))) (orderedInterval (3368270573 / 1000000000000) (3368274566 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (485787588437403 / 4000000000000) 0 (IntervalRat.scale (531 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (20762034033 / 1000000000000) (20762034415 / 1000000000000), orderedInterval (-69446380630 / 1000000000000) (-69446380249 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1974699576877563 / 4000000000000) 0 (IntervalRat.scale (531 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-33844997260 / 1000000000000) (-33844997256 / 1000000000000), orderedInterval (-11968567140 / 1000000000000) (-11968567136 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1319007801751317 / 4000000000000) 0 (IntervalRat.scale (531 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-27276325045 / 1000000000000) (-27276325044 / 1000000000000), orderedInterval (-34405768740 / 1000000000000) (-34405768739 / 1000000000000)))) (orderedInterval (7997965371 / 1000000000000) (7997965447 / 1000000000000))) = true
  rfl'

theorem compactCertificate394_chunkChecks0 :
    compactCertificate394.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate394.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate394_chunkChecks0_0
    compactCertificate394_chunkChecks0_1 compactCertificate394_chunkChecks0_2

theorem compactCertificate394_chunkChecks1_0 :
    compactCertificate394.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (531 / 2) 1 (IntervalRat.scale (531 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (33394147986 / 1000000000000) (33394173480 / 1000000000000), orderedInterval (-35876933215 / 1000000000000) (-35876907721 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (782264393335431 / 4000000000000) 1 (IntervalRat.scale (531 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (57054800285 / 1000000000000) (57054800352 / 1000000000000), orderedInterval (-220982130 / 1000000000000) (-220982062 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (252968232168423 / 800000000000) 1 (IntervalRat.scale (531 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (13498198628 / 1000000000000) (13498198754 / 1000000000000), orderedInterval (-42812469407 / 1000000000000) (-42812469281 / 1000000000000)))) (orderedInterval (-17214006003 / 1000000000000) (-17213995867 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (228262798980117 / 4000000000000) 1 (IntervalRat.scale (531 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (101777324256 / 1000000000000) (101777324257 / 1000000000000), orderedInterval (27338062087 / 1000000000000) (27338062088 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (613145985879249 / 4000000000000) 1 (IntervalRat.scale (531 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-8548394666 / 1000000000000) (-8548394664 / 1000000000000), orderedInterval (-63847643604 / 1000000000000) (-63847643603 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1664810625542733 / 4000000000000) 1 (IntervalRat.scale (531 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29228924624 / 1000000000000) (29228954542 / 1000000000000), orderedInterval (-26020889480 / 1000000000000) (-26020859561 / 1000000000000)))) (orderedInterval (1490139067 / 1000000000000) (1490142438 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1226291971759029 / 4000000000000) 1 (IntervalRat.scale (531 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-22567195820 / 1000000000000) (-22567193909 / 1000000000000), orderedInterval (39625836644 / 1000000000000) (39625838556 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2101272195086217 / 4000000000000) 1 (IntervalRat.scale (531 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-34587759897 / 1000000000000) (-34587759756 / 1000000000000), orderedInterval (-3911855981 / 1000000000000) (-3911855840 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1547787588437403 / 4000000000000) 1 (IntervalRat.scale (531 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-39252750131 / 1000000000000) (-39252750125 / 1000000000000), orderedInterval (-10169772817 / 1000000000000) (-10169772811 / 1000000000000)))) (orderedInterval (-119478931 / 1000000000000) (-119478895 / 1000000000000))) = true
  rfl'

theorem compactCertificate394_chunkChecks1_1 :
    compactCertificate394.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2374704192104469 / 4000000000000) 1 (IntervalRat.scale (531 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-21101503104 / 1000000000000) (-21101503103 / 1000000000000), orderedInterval (-25023432421 / 1000000000000) (-25023432420 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1371036104557101 / 4000000000000) 1 (IntervalRat.scale (531 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-38610597071 / 1000000000000) (-38610597070 / 1000000000000), orderedInterval (-19089428078 / 1000000000000) (-19089428077 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2432927626921809 / 4000000000000) 1 (IntervalRat.scale (531 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-14126751881 / 1000000000000) (-14126751759 / 1000000000000), orderedInterval (29116730453 / 1000000000000) (29116730576 / 1000000000000)))) (orderedInterval (17598690147 / 1000000000000) (17598690406 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2273156580141621 / 4000000000000) 1 (IntervalRat.scale (531 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-14439213202 / 1000000000000) (-14439213201 / 1000000000000), orderedInterval (-30182470779 / 1000000000000) (-30182470778 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1622231796013893 / 4000000000000) 1 (IntervalRat.scale (531 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-34897916318 / 1000000000000) (-34897916317 / 1000000000000), orderedInterval (-18715250956 / 1000000000000) (-18715250955 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1839437957637747 / 4000000000000) 1 (IntervalRat.scale (531 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (34251365331 / 1000000000000) (34251395844 / 1000000000000), orderedInterval (-14570707930 / 1000000000000) (-14570677417 / 1000000000000)))) (orderedInterval (-1409348266 / 1000000000000) (-1409347946 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1533531598031043 / 4000000000000) 1 (IntervalRat.scale (531 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (31759236309 / 1000000000000) (31759236310 / 1000000000000), orderedInterval (25490582331 / 1000000000000) (25490582332 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1354921674207903 / 4000000000000) 1 (IntervalRat.scale (531 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (9606296839 / 1000000000000) (9606296840 / 1000000000000), orderedInterval (42260516024 / 1000000000000) (42260516025 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (392709111794397 / 800000000000) 1 (IntervalRat.scale (531 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (36009466536 / 1000000000000) (36009467116 / 1000000000000), orderedInterval (-479004241 / 1000000000000) (-479003661 / 1000000000000)))) (orderedInterval (-2683105423 / 1000000000000) (-2683105358 / 1000000000000))) = true
  rfl'

theorem compactCertificate394_chunkChecks1_2 :
    compactCertificate394.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1086254070371559 / 4000000000000) 1 (IntervalRat.scale (531 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (39941898018 / 1000000000000) (39941974537 / 1000000000000), orderedInterval (-27439906159 / 1000000000000) (-27439829639 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (920829605388399 / 4000000000000) 1 (IntervalRat.scale (531 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-52396448169 / 1000000000000) (-52396447896 / 1000000000000), orderedInterval (4588637948 / 1000000000000) (4588638221 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (576212411562597 / 4000000000000) 1 (IntervalRat.scale (531 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (21187372503 / 1000000000000) (21187372504 / 1000000000000), orderedInterval (62938026172 / 1000000000000) (62938026173 / 1000000000000)))) (orderedInterval (5374141447 / 1000000000000) (5374154036 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (309888951334299 / 4000000000000) 1 (IntervalRat.scale (531 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (25381651913 / 1000000000000) (25381652373 / 1000000000000), orderedInterval (-87188561633 / 1000000000000) (-87188561174 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (841408784859897 / 4000000000000) 1 (IntervalRat.scale (531 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-33305967469 / 1000000000000) (-33305967468 / 1000000000000), orderedInterval (-43706239649 / 1000000000000) (-43706239648 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1148871761476569 / 4000000000000) 1 (IntervalRat.scale (531 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-40205992520 / 1000000000000) (-40205940962 / 1000000000000), orderedInterval (24564512250 / 1000000000000) (24564563808 / 1000000000000)))) (orderedInterval (-781220861 / 1000000000000) (-781216555 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (485787588437403 / 4000000000000) 1 (IntervalRat.scale (531 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (20762034033 / 1000000000000) (20762034415 / 1000000000000), orderedInterval (-69446380630 / 1000000000000) (-69446380249 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1974699576877563 / 4000000000000) 1 (IntervalRat.scale (531 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-33844997260 / 1000000000000) (-33844997256 / 1000000000000), orderedInterval (-11968567140 / 1000000000000) (-11968567136 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1319007801751317 / 4000000000000) 1 (IntervalRat.scale (531 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-27276325045 / 1000000000000) (-27276325044 / 1000000000000), orderedInterval (-34405768740 / 1000000000000) (-34405768739 / 1000000000000)))) (orderedInterval (9637732702 / 1000000000000) (9637732808 / 1000000000000))) = true
  rfl'

theorem compactCertificate394_chunkChecks1 :
    compactCertificate394.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate394.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate394_chunkChecks1_0
    compactCertificate394_chunkChecks1_1 compactCertificate394_chunkChecks1_2

theorem compactCertificate394_chunkChecks2_0 :
    compactCertificate394.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (531 / 2) 2 (IntervalRat.scale (531 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (33394147986 / 1000000000000) (33394173480 / 1000000000000), orderedInterval (-35876933215 / 1000000000000) (-35876907721 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (782264393335431 / 4000000000000) 2 (IntervalRat.scale (531 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (57054800285 / 1000000000000) (57054800352 / 1000000000000), orderedInterval (-220982130 / 1000000000000) (-220982062 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (252968232168423 / 800000000000) 2 (IntervalRat.scale (531 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (13498198628 / 1000000000000) (13498198754 / 1000000000000), orderedInterval (-42812469407 / 1000000000000) (-42812469281 / 1000000000000)))) (orderedInterval (-14583461374 / 1000000000000) (-14583451196 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (228262798980117 / 4000000000000) 2 (IntervalRat.scale (531 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (101777324256 / 1000000000000) (101777324257 / 1000000000000), orderedInterval (27338062087 / 1000000000000) (27338062088 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (613145985879249 / 4000000000000) 2 (IntervalRat.scale (531 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-8548394666 / 1000000000000) (-8548394664 / 1000000000000), orderedInterval (-63847643604 / 1000000000000) (-63847643603 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1664810625542733 / 4000000000000) 2 (IntervalRat.scale (531 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29228924624 / 1000000000000) (29228954542 / 1000000000000), orderedInterval (-26020889480 / 1000000000000) (-26020859561 / 1000000000000)))) (orderedInterval (5255661774 / 1000000000000) (5255667064 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1226291971759029 / 4000000000000) 2 (IntervalRat.scale (531 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-22567195820 / 1000000000000) (-22567193909 / 1000000000000), orderedInterval (39625836644 / 1000000000000) (39625838556 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2101272195086217 / 4000000000000) 2 (IntervalRat.scale (531 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-34587759897 / 1000000000000) (-34587759756 / 1000000000000), orderedInterval (-3911855981 / 1000000000000) (-3911855840 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1547787588437403 / 4000000000000) 2 (IntervalRat.scale (531 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-39252750131 / 1000000000000) (-39252750125 / 1000000000000), orderedInterval (-10169772817 / 1000000000000) (-10169772811 / 1000000000000)))) (orderedInterval (-2160967930 / 1000000000000) (-2160967866 / 1000000000000))) = true
  rfl'

theorem compactCertificate394_chunkChecks2_1 :
    compactCertificate394.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2374704192104469 / 4000000000000) 2 (IntervalRat.scale (531 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-21101503104 / 1000000000000) (-21101503103 / 1000000000000), orderedInterval (-25023432421 / 1000000000000) (-25023432420 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1371036104557101 / 4000000000000) 2 (IntervalRat.scale (531 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-38610597071 / 1000000000000) (-38610597070 / 1000000000000), orderedInterval (-19089428078 / 1000000000000) (-19089428077 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2432927626921809 / 4000000000000) 2 (IntervalRat.scale (531 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-14126751881 / 1000000000000) (-14126751759 / 1000000000000), orderedInterval (29116730453 / 1000000000000) (29116730576 / 1000000000000)))) (orderedInterval (-3506402266 / 1000000000000) (-3506401706 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2273156580141621 / 4000000000000) 2 (IntervalRat.scale (531 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-14439213202 / 1000000000000) (-14439213201 / 1000000000000), orderedInterval (-30182470779 / 1000000000000) (-30182470778 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1622231796013893 / 4000000000000) 2 (IntervalRat.scale (531 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-34897916318 / 1000000000000) (-34897916317 / 1000000000000), orderedInterval (-18715250956 / 1000000000000) (-18715250955 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1839437957637747 / 4000000000000) 2 (IntervalRat.scale (531 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (34251365331 / 1000000000000) (34251395844 / 1000000000000), orderedInterval (-14570707930 / 1000000000000) (-14570677417 / 1000000000000)))) (orderedInterval (7031136928 / 1000000000000) (7031137478 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1533531598031043 / 4000000000000) 2 (IntervalRat.scale (531 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (31759236309 / 1000000000000) (31759236310 / 1000000000000), orderedInterval (25490582331 / 1000000000000) (25490582332 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1354921674207903 / 4000000000000) 2 (IntervalRat.scale (531 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (9606296839 / 1000000000000) (9606296840 / 1000000000000), orderedInterval (42260516024 / 1000000000000) (42260516025 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (392709111794397 / 800000000000) 2 (IntervalRat.scale (531 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (36009466536 / 1000000000000) (36009467116 / 1000000000000), orderedInterval (-479004241 / 1000000000000) (-479003661 / 1000000000000)))) (orderedInterval (-3011580142 / 1000000000000) (-3011580036 / 1000000000000))) = true
  rfl'

theorem compactCertificate394_chunkChecks2_2 :
    compactCertificate394.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1086254070371559 / 4000000000000) 2 (IntervalRat.scale (531 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (39941898018 / 1000000000000) (39941974537 / 1000000000000), orderedInterval (-27439906159 / 1000000000000) (-27439829639 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (920829605388399 / 4000000000000) 2 (IntervalRat.scale (531 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-52396448169 / 1000000000000) (-52396447896 / 1000000000000), orderedInterval (4588637948 / 1000000000000) (4588638221 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (576212411562597 / 4000000000000) 2 (IntervalRat.scale (531 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (21187372503 / 1000000000000) (21187372504 / 1000000000000), orderedInterval (62938026172 / 1000000000000) (62938026173 / 1000000000000)))) (orderedInterval (4228545901 / 1000000000000) (4228558819 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (309888951334299 / 4000000000000) 2 (IntervalRat.scale (531 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (25381651913 / 1000000000000) (25381652373 / 1000000000000), orderedInterval (-87188561633 / 1000000000000) (-87188561174 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (841408784859897 / 4000000000000) 2 (IntervalRat.scale (531 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-33305967469 / 1000000000000) (-33305967468 / 1000000000000), orderedInterval (-43706239649 / 1000000000000) (-43706239648 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1148871761476569 / 4000000000000) 2 (IntervalRat.scale (531 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-40205992520 / 1000000000000) (-40205940962 / 1000000000000), orderedInterval (24564512250 / 1000000000000) (24564563808 / 1000000000000)))) (orderedInterval (-4037529417 / 1000000000000) (-4037524747 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (485787588437403 / 4000000000000) 2 (IntervalRat.scale (531 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (20762034033 / 1000000000000) (20762034415 / 1000000000000), orderedInterval (-69446380630 / 1000000000000) (-69446380249 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1974699576877563 / 4000000000000) 2 (IntervalRat.scale (531 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-33844997260 / 1000000000000) (-33844997256 / 1000000000000), orderedInterval (-11968567140 / 1000000000000) (-11968567136 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1319007801751317 / 4000000000000) 2 (IntervalRat.scale (531 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-27276325045 / 1000000000000) (-27276325044 / 1000000000000), orderedInterval (-34405768740 / 1000000000000) (-34405768739 / 1000000000000)))) (orderedInterval (-17482370101 / 1000000000000) (-17482369946 / 1000000000000))) = true
  rfl'

theorem compactCertificate394_chunkChecks2 :
    compactCertificate394.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate394.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate394_chunkChecks2_0
    compactCertificate394_chunkChecks2_1 compactCertificate394_chunkChecks2_2

theorem compactCertificate394_chunkChecks3_0 :
    compactCertificate394.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (531 / 2) 3 (IntervalRat.scale (531 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (33394147986 / 1000000000000) (33394173480 / 1000000000000), orderedInterval (-35876933215 / 1000000000000) (-35876907721 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (782264393335431 / 4000000000000) 3 (IntervalRat.scale (531 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (57054800285 / 1000000000000) (57054800352 / 1000000000000), orderedInterval (-220982130 / 1000000000000) (-220982062 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (252968232168423 / 800000000000) 3 (IntervalRat.scale (531 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (13498198628 / 1000000000000) (13498198754 / 1000000000000), orderedInterval (-42812469407 / 1000000000000) (-42812469281 / 1000000000000)))) (orderedInterval (18520129560 / 1000000000000) (18520139743 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (228262798980117 / 4000000000000) 3 (IntervalRat.scale (531 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (101777324256 / 1000000000000) (101777324257 / 1000000000000), orderedInterval (27338062087 / 1000000000000) (27338062088 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (613145985879249 / 4000000000000) 3 (IntervalRat.scale (531 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-8548394666 / 1000000000000) (-8548394664 / 1000000000000), orderedInterval (-63847643604 / 1000000000000) (-63847643603 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1664810625542733 / 4000000000000) 3 (IntervalRat.scale (531 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29228924624 / 1000000000000) (29228954542 / 1000000000000), orderedInterval (-26020889480 / 1000000000000) (-26020859561 / 1000000000000)))) (orderedInterval (-6694250829 / 1000000000000) (-6694242540 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1226291971759029 / 4000000000000) 3 (IntervalRat.scale (531 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-22567195820 / 1000000000000) (-22567193909 / 1000000000000), orderedInterval (39625836644 / 1000000000000) (39625838556 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2101272195086217 / 4000000000000) 3 (IntervalRat.scale (531 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-34587759897 / 1000000000000) (-34587759756 / 1000000000000), orderedInterval (-3911855981 / 1000000000000) (-3911855840 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1547787588437403 / 4000000000000) 3 (IntervalRat.scale (531 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-39252750131 / 1000000000000) (-39252750125 / 1000000000000), orderedInterval (-10169772817 / 1000000000000) (-10169772811 / 1000000000000)))) (orderedInterval (-165590629 / 1000000000000) (-165590511 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate394_chunkChecks3_1 :
    compactCertificate394.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2374704192104469 / 4000000000000) 3 (IntervalRat.scale (531 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-21101503104 / 1000000000000) (-21101503103 / 1000000000000), orderedInterval (-25023432421 / 1000000000000) (-25023432420 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1371036104557101 / 4000000000000) 3 (IntervalRat.scale (531 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-38610597071 / 1000000000000) (-38610597070 / 1000000000000), orderedInterval (-19089428078 / 1000000000000) (-19089428077 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2432927626921809 / 4000000000000) 3 (IntervalRat.scale (531 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-14126751881 / 1000000000000) (-14126751759 / 1000000000000), orderedInterval (29116730453 / 1000000000000) (29116730576 / 1000000000000)))) (orderedInterval (-96419853356 / 1000000000000) (-96419852119 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2273156580141621 / 4000000000000) 3 (IntervalRat.scale (531 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-14439213202 / 1000000000000) (-14439213201 / 1000000000000), orderedInterval (-30182470779 / 1000000000000) (-30182470778 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1622231796013893 / 4000000000000) 3 (IntervalRat.scale (531 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-34897916318 / 1000000000000) (-34897916317 / 1000000000000), orderedInterval (-18715250956 / 1000000000000) (-18715250955 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1839437957637747 / 4000000000000) 3 (IntervalRat.scale (531 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (34251365331 / 1000000000000) (34251395844 / 1000000000000), orderedInterval (-14570707930 / 1000000000000) (-14570677417 / 1000000000000)))) (orderedInterval (554766743 / 1000000000000) (554767692 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1533531598031043 / 4000000000000) 3 (IntervalRat.scale (531 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (31759236309 / 1000000000000) (31759236310 / 1000000000000), orderedInterval (25490582331 / 1000000000000) (25490582332 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1354921674207903 / 4000000000000) 3 (IntervalRat.scale (531 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (9606296839 / 1000000000000) (9606296840 / 1000000000000), orderedInterval (42260516024 / 1000000000000) (42260516025 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (392709111794397 / 800000000000) 3 (IntervalRat.scale (531 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (36009466536 / 1000000000000) (36009467116 / 1000000000000), orderedInterval (-479004241 / 1000000000000) (-479003661 / 1000000000000)))) (orderedInterval (4224822144 / 1000000000000) (4224822323 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate394_chunkChecks3_2 :
    compactCertificate394.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1086254070371559 / 4000000000000) 3 (IntervalRat.scale (531 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (39941898018 / 1000000000000) (39941974537 / 1000000000000), orderedInterval (-27439906159 / 1000000000000) (-27439829639 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (920829605388399 / 4000000000000) 3 (IntervalRat.scale (531 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-52396448169 / 1000000000000) (-52396447896 / 1000000000000), orderedInterval (4588637948 / 1000000000000) (4588638221 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (576212411562597 / 4000000000000) 3 (IntervalRat.scale (531 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (21187372503 / 1000000000000) (21187372504 / 1000000000000), orderedInterval (62938026172 / 1000000000000) (62938026173 / 1000000000000)))) (orderedInterval (-4868772743 / 1000000000000) (-4868759535 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (309888951334299 / 4000000000000) 3 (IntervalRat.scale (531 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (25381651913 / 1000000000000) (25381652373 / 1000000000000), orderedInterval (-87188561633 / 1000000000000) (-87188561174 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (841408784859897 / 4000000000000) 3 (IntervalRat.scale (531 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-33305967469 / 1000000000000) (-33305967468 / 1000000000000), orderedInterval (-43706239649 / 1000000000000) (-43706239648 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1148871761476569 / 4000000000000) 3 (IntervalRat.scale (531 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-40205992520 / 1000000000000) (-40205940962 / 1000000000000), orderedInterval (24564512250 / 1000000000000) (24564563808 / 1000000000000)))) (orderedInterval (1865469701 / 1000000000000) (1865474751 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (485787588437403 / 4000000000000) 3 (IntervalRat.scale (531 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (20762034033 / 1000000000000) (20762034415 / 1000000000000), orderedInterval (-69446380630 / 1000000000000) (-69446380249 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1974699576877563 / 4000000000000) 3 (IntervalRat.scale (531 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-33844997260 / 1000000000000) (-33844997256 / 1000000000000), orderedInterval (-11968567140 / 1000000000000) (-11968567136 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1319007801751317 / 4000000000000) 3 (IntervalRat.scale (531 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-27276325045 / 1000000000000) (-27276325044 / 1000000000000), orderedInterval (-34405768740 / 1000000000000) (-34405768739 / 1000000000000)))) (orderedInterval (-18525126842 / 1000000000000) (-18525126604 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate394_chunkChecks3 :
    compactCertificate394.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate394.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate394_chunkChecks3_0
    compactCertificate394_chunkChecks3_1 compactCertificate394_chunkChecks3_2

theorem compactCertificate394_chunkChecks4_0 :
    compactCertificate394.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (531 / 2) 4 (IntervalRat.scale (531 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (33394147986 / 1000000000000) (33394173480 / 1000000000000), orderedInterval (-35876933215 / 1000000000000) (-35876907721 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (782264393335431 / 4000000000000) 4 (IntervalRat.scale (531 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (57054800285 / 1000000000000) (57054800352 / 1000000000000), orderedInterval (-220982130 / 1000000000000) (-220982062 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (252968232168423 / 800000000000) 4 (IntervalRat.scale (531 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (13498198628 / 1000000000000) (13498198754 / 1000000000000), orderedInterval (-42812469407 / 1000000000000) (-42812469281 / 1000000000000)))) (orderedInterval (14846811072 / 1000000000000) (14846821301 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (228262798980117 / 4000000000000) 4 (IntervalRat.scale (531 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (101777324256 / 1000000000000) (101777324257 / 1000000000000), orderedInterval (27338062087 / 1000000000000) (27338062088 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (613145985879249 / 4000000000000) 4 (IntervalRat.scale (531 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-8548394666 / 1000000000000) (-8548394664 / 1000000000000), orderedInterval (-63847643604 / 1000000000000) (-63847643603 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1664810625542733 / 4000000000000) 4 (IntervalRat.scale (531 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29228924624 / 1000000000000) (29228954542 / 1000000000000), orderedInterval (-26020889480 / 1000000000000) (-26020859561 / 1000000000000)))) (orderedInterval (-12534718835 / 1000000000000) (-12534705813 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1226291971759029 / 4000000000000) 4 (IntervalRat.scale (531 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-22567195820 / 1000000000000) (-22567193909 / 1000000000000), orderedInterval (39625836644 / 1000000000000) (39625838556 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2101272195086217 / 4000000000000) 4 (IntervalRat.scale (531 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-34587759897 / 1000000000000) (-34587759756 / 1000000000000), orderedInterval (-3911855981 / 1000000000000) (-3911855840 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1547787588437403 / 4000000000000) 4 (IntervalRat.scale (531 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-39252750131 / 1000000000000) (-39252750125 / 1000000000000), orderedInterval (-10169772817 / 1000000000000) (-10169772811 / 1000000000000)))) (orderedInterval (12071317386 / 1000000000000) (12071317609 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate394_chunkChecks4_1 :
    compactCertificate394.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2374704192104469 / 4000000000000) 4 (IntervalRat.scale (531 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-21101503104 / 1000000000000) (-21101503103 / 1000000000000), orderedInterval (-25023432421 / 1000000000000) (-25023432420 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1371036104557101 / 4000000000000) 4 (IntervalRat.scale (531 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-38610597071 / 1000000000000) (-38610597070 / 1000000000000), orderedInterval (-19089428078 / 1000000000000) (-19089428077 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2432927626921809 / 4000000000000) 4 (IntervalRat.scale (531 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-14126751881 / 1000000000000) (-14126751759 / 1000000000000), orderedInterval (29116730453 / 1000000000000) (29116730576 / 1000000000000)))) (orderedInterval (31204037957 / 1000000000000) (31204040715 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2273156580141621 / 4000000000000) 4 (IntervalRat.scale (531 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-14439213202 / 1000000000000) (-14439213201 / 1000000000000), orderedInterval (-30182470779 / 1000000000000) (-30182470778 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1622231796013893 / 4000000000000) 4 (IntervalRat.scale (531 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-34897916318 / 1000000000000) (-34897916317 / 1000000000000), orderedInterval (-18715250956 / 1000000000000) (-18715250955 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1839437957637747 / 4000000000000) 4 (IntervalRat.scale (531 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (34251365331 / 1000000000000) (34251395844 / 1000000000000), orderedInterval (-14570707930 / 1000000000000) (-14570677417 / 1000000000000)))) (orderedInterval (-14059388194 / 1000000000000) (-14059386547 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1533531598031043 / 4000000000000) 4 (IntervalRat.scale (531 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (31759236309 / 1000000000000) (31759236310 / 1000000000000), orderedInterval (25490582331 / 1000000000000) (25490582332 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1354921674207903 / 4000000000000) 4 (IntervalRat.scale (531 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (9606296839 / 1000000000000) (9606296840 / 1000000000000), orderedInterval (42260516024 / 1000000000000) (42260516025 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (392709111794397 / 800000000000) 4 (IntervalRat.scale (531 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (36009466536 / 1000000000000) (36009467116 / 1000000000000), orderedInterval (-479004241 / 1000000000000) (-479003661 / 1000000000000)))) (orderedInterval (10880480883 / 1000000000000) (10880481192 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate394_chunkChecks4_2 :
    compactCertificate394.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1086254070371559 / 4000000000000) 4 (IntervalRat.scale (531 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (39941898018 / 1000000000000) (39941974537 / 1000000000000), orderedInterval (-27439906159 / 1000000000000) (-27439829639 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (920829605388399 / 4000000000000) 4 (IntervalRat.scale (531 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-52396448169 / 1000000000000) (-52396447896 / 1000000000000), orderedInterval (4588637948 / 1000000000000) (4588638221 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (576212411562597 / 4000000000000) 4 (IntervalRat.scale (531 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (21187372503 / 1000000000000) (21187372504 / 1000000000000), orderedInterval (62938026172 / 1000000000000) (62938026173 / 1000000000000)))) (orderedInterval (-5217371668 / 1000000000000) (-5217358113 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (309888951334299 / 4000000000000) 4 (IntervalRat.scale (531 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (25381651913 / 1000000000000) (25381652373 / 1000000000000), orderedInterval (-87188561633 / 1000000000000) (-87188561174 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (841408784859897 / 4000000000000) 4 (IntervalRat.scale (531 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-33305967469 / 1000000000000) (-33305967468 / 1000000000000), orderedInterval (-43706239649 / 1000000000000) (-43706239648 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1148871761476569 / 4000000000000) 4 (IntervalRat.scale (531 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-40205992520 / 1000000000000) (-40205940962 / 1000000000000), orderedInterval (24564512250 / 1000000000000) (24564563808 / 1000000000000)))) (orderedInterval (4500371136 / 1000000000000) (4500376616 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (485787588437403 / 4000000000000) 4 (IntervalRat.scale (531 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (20762034033 / 1000000000000) (20762034415 / 1000000000000), orderedInterval (-69446380630 / 1000000000000) (-69446380249 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1974699576877563 / 4000000000000) 4 (IntervalRat.scale (531 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-33844997260 / 1000000000000) (-33844997256 / 1000000000000), orderedInterval (-11968567140 / 1000000000000) (-11968567136 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1319007801751317 / 4000000000000) 4 (IntervalRat.scale (531 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-27276325045 / 1000000000000) (-27276325044 / 1000000000000), orderedInterval (-34405768740 / 1000000000000) (-34405768739 / 1000000000000)))) (orderedInterval (45255892366 / 1000000000000) (45255892749 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate394_chunkChecks4 :
    compactCertificate394.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate394.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate394_chunkChecks4_0
    compactCertificate394_chunkChecks4_1 compactCertificate394_chunkChecks4_2

theorem compactCertificate394_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate394.chunkCheck r b = true :=
  compactCertificate394.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate394_chunkChecks0
    · exact compactCertificate394_chunkChecks1
    · exact compactCertificate394_chunkChecks2
    · exact compactCertificate394_chunkChecks3
    · exact compactCertificate394_chunkChecks4)

theorem compactCertificate394_coefficient0 :
    compactCertificate394.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate394_coefficient1 :
    compactCertificate394.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate394_coefficient2 :
    compactCertificate394.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate394_coefficient3 :
    compactCertificate394.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate394_coefficient4 :
    compactCertificate394.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate394_coefficients : ∀ r : Fin 5,
    compactCertificate394.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate394_coefficient0
  · exact compactCertificate394_coefficient1
  · exact compactCertificate394_coefficient2
  · exact compactCertificate394_coefficient3
  · exact compactCertificate394_coefficient4

theorem compactCertificate394_lower : (1 : ℚ) ≤ compactCertificate394.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate394, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate394_proves {t : ℝ} (ht : t ∈ compactCertificate394.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate394.proves compactCertificate394_states compactCertificate394_chunks
    compactCertificate394_coefficients compactCertificate394_lower ht

end Erdos232
