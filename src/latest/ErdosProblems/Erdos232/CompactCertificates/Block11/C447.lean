/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate447 : CompactCertificate where
  left := 318
  right := 319
  center := 637 / 2
  grid := fun i =>
    match i.val with
    | 0 => 101
    | 1 => 75
    | 2 => 121
    | 3 => 22
    | 4 => 59
    | 5 => 159
    | 6 => 117
    | 7 => 201
    | 8 => 148
    | 9 => 227
    | 10 => 131
    | 11 => 232
    | 12 => 217
    | 13 => 155
    | 14 => 176
    | 15 => 146
    | 16 => 129
    | 17 => 188
    | 18 => 104
    | 19 => 88
    | 20 => 55
    | 21 => 30
    | 22 => 80
    | 23 => 110
    | 24 => 46
    | 25 => 189
    | _ => 126
  point := fun i =>
    match i.val with
    | 0 => 637 / 2
    | 1 => 938422633812937 / 4000000000000
    | 2 => 303466598665321 / 800000000000
    | 3 => 273829384087259 / 4000000000000
    | 4 => 735544242947423 / 4000000000000
    | 5 => 1997145703334691 / 4000000000000
    | 6 => 1471088485895483 / 4000000000000
    | 7 => 2520735194481959 / 4000000000000
    | 8 => 1856762135281781 / 4000000000000
    | 9 => 2848750603334363 / 4000000000000
    | 10 => 1644726927689027 / 4000000000000
    | 11 => 2918596795384543 / 4000000000000
    | 12 => 2726931716667067 / 4000000000000
    | 13 => 1946067145124011 / 4000000000000
    | 14 => 2206632728842269 / 4000000000000
    | 15 => 1839660316282061 / 4000000000000
    | 16 => 1625395680735281 / 4000000000000
    | 17 => 471103021116819 / 800000000000
    | 18 => 1303095749202793 / 4000000000000
    | 19 => 1104648697989473 / 4000000000000
    | 20 => 691237864718219 / 4000000000000
    | 21 => 371750022598773 / 4000000000000
    | 22 => 1009373627035319 / 4000000000000
    | 23 => 1378213393711063 / 4000000000000
    | 24 => 582762135281781 / 4000000000000
    | 25 => 2368895725934101 / 4000000000000
    | _ => 1582312560669659 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-40942675641 / 1000000000000) (-40942658152 / 1000000000000), orderedInterval (18022620427 / 1000000000000) (18022637917 / 1000000000000))
    | 1 => (orderedInterval (11821265310 / 1000000000000) (11821265386 / 1000000000000), orderedInterval (-50758191290 / 1000000000000) (-50758191214 / 1000000000000))
    | 2 => (orderedInterval (589656851 / 1000000000000) (589656852 / 1000000000000), orderedInterval (-40963121441 / 1000000000000) (-40963121440 / 1000000000000))
    | 3 => (orderedInterval (12106918026 / 1000000000000) (12106918028 / 1000000000000), orderedInterval (95583792651 / 1000000000000) (95583792652 / 1000000000000))
    | 4 => (orderedInterval (37143146975 / 1000000000000) (37143166944 / 1000000000000), orderedInterval (-45734569799 / 1000000000000) (-45734549830 / 1000000000000))
    | 5 => (orderedInterval (-18917381705 / 1000000000000) (-18917381704 / 1000000000000), orderedInterval (-30266236685 / 1000000000000) (-30266236684 / 1000000000000))
    | 6 => (orderedInterval (-34802403194 / 1000000000000) (-34802403193 / 1000000000000), orderedInterval (-22752005807 / 1000000000000) (-22752005806 / 1000000000000))
    | 7 => (orderedInterval (14989836524 / 1000000000000) (14989836704 / 1000000000000), orderedInterval (-28038984247 / 1000000000000) (-28038984067 / 1000000000000))
    | 8 => (orderedInterval (738763063 / 1000000000000) (738763064 / 1000000000000), orderedInterval (37025103663 / 1000000000000) (37025103664 / 1000000000000))
    | 9 => (orderedInterval (5018698153 / 1000000000000) (5018698154 / 1000000000000), orderedInterval (-29477345396 / 1000000000000) (-29477345394 / 1000000000000))
    | 10 => (orderedInterval (-15979458997 / 1000000000000) (-15979458996 / 1000000000000), orderedInterval (-35937852945 / 1000000000000) (-35937852944 / 1000000000000))
    | 11 => (orderedInterval (29535175630 / 1000000000000) (29535178082 / 1000000000000), orderedInterval (-437710754 / 1000000000000) (-437708302 / 1000000000000))
    | 12 => (orderedInterval (-21761893901 / 1000000000000) (-21761893900 / 1000000000000), orderedInterval (-21437377790 / 1000000000000) (-21437377789 / 1000000000000))
    | 13 => (orderedInterval (-12575820263 / 1000000000000) (-12575820262 / 1000000000000), orderedInterval (-33904255385 / 1000000000000) (-33904255384 / 1000000000000))
    | 14 => (orderedInterval (-15595100980 / 1000000000000) (-15595100726 / 1000000000000), orderedInterval (30193670671 / 1000000000000) (30193670925 / 1000000000000))
    | 15 => (orderedInterval (33388935080 / 1000000000000) (33388985356 / 1000000000000), orderedInterval (-16449377954 / 1000000000000) (-16449327678 / 1000000000000))
    | 16 => (orderedInterval (-37839571776 / 1000000000000) (-37839563072 / 1000000000000), orderedInterval (11658994050 / 1000000000000) (11659002754 / 1000000000000))
    | 17 => (orderedInterval (-26848787024 / 1000000000000) (-26848749847 / 1000000000000), orderedInterval (19002094876 / 1000000000000) (19002132053 / 1000000000000))
    | 18 => (orderedInterval (-7334376239 / 1000000000000) (-7334376224 / 1000000000000), orderedInterval (43604669156 / 1000000000000) (43604669171 / 1000000000000))
    | 19 => (orderedInterval (22467484288 / 1000000000000) (22467484289 / 1000000000000), orderedInterval (42391068665 / 1000000000000) (42391068666 / 1000000000000))
    | 20 => (orderedInterval (-43816011606 / 1000000000000) (-43816011605 / 1000000000000), orderedInterval (-41874378715 / 1000000000000) (-41874378714 / 1000000000000))
    | 21 => (orderedInterval (-41569783628 / 1000000000000) (-41569776979 / 1000000000000), orderedInterval (71791639279 / 1000000000000) (71791645929 / 1000000000000))
    | 22 => (orderedInterval (48903907201 / 1000000000000) (48903909036 / 1000000000000), orderedInterval (-11552655910 / 1000000000000) (-11552654075 / 1000000000000))
    | 23 => (orderedInterval (-10084200026 / 1000000000000) (-10084199988 / 1000000000000), orderedInterval (41799528215 / 1000000000000) (41799528253 / 1000000000000))
    | 24 => (orderedInterval (61113978381 / 1000000000000) (61113984256 / 1000000000000), orderedInterval (-25403677277 / 1000000000000) (-25403671401 / 1000000000000))
    | 25 => (orderedInterval (22394018040 / 1000000000000) (22394023091 / 1000000000000), orderedInterval (-23966194707 / 1000000000000) (-23966189656 / 1000000000000))
    | _ => (orderedInterval (20021765255 / 1000000000000) (20021765256 / 1000000000000), orderedInterval (34737743619 / 1000000000000) (34737743620 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-16083490360 / 1000000000000) (-16083483404 / 1000000000000)
      | 1 => orderedInterval (2569639526 / 1000000000000) (2569640294 / 1000000000000)
      | 2 => orderedInterval (-444492102 / 1000000000000) (-444492078 / 1000000000000)
      | 3 => orderedInterval (2122890691 / 1000000000000) (2122891166 / 1000000000000)
      | 4 => orderedInterval (-717416091 / 1000000000000) (-717416051 / 1000000000000)
      | 5 => orderedInterval (1863561842 / 1000000000000) (1863563903 / 1000000000000)
      | 6 => orderedInterval (-1525389469 / 1000000000000) (-1525389387 / 1000000000000)
      | 7 => orderedInterval (430956233 / 1000000000000) (430956439 / 1000000000000)
      | _ => orderedInterval (-5211112490 / 1000000000000) (-5211111955 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (3932270379 / 1000000000000) (3932277338 / 1000000000000)
      | 1 => orderedInterval (2185931750 / 1000000000000) (2185932215 / 1000000000000)
      | 2 => orderedInterval (3015300938 / 1000000000000) (3015300981 / 1000000000000)
      | 3 => orderedInterval (8131929576 / 1000000000000) (8131930637 / 1000000000000)
      | 4 => orderedInterval (-4333649525 / 1000000000000) (-4333649460 / 1000000000000)
      | 5 => orderedInterval (-225977408 / 1000000000000) (-225974129 / 1000000000000)
      | 6 => orderedInterval (-9951330450 / 1000000000000) (-9951330373 / 1000000000000)
      | 7 => orderedInterval (-3644678382 / 1000000000000) (-3644678275 / 1000000000000)
      | _ => orderedInterval (-4537569043 / 1000000000000) (-4537568138 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (16107043229 / 1000000000000) (16107050213 / 1000000000000)
      | 1 => orderedInterval (-3757670438 / 1000000000000) (-3757670133 / 1000000000000)
      | 2 => orderedInterval (1762627535 / 1000000000000) (1762627613 / 1000000000000)
      | 3 => orderedInterval (-15628515954 / 1000000000000) (-15628513561 / 1000000000000)
      | 4 => orderedInterval (751719789 / 1000000000000) (751719895 / 1000000000000)
      | 5 => orderedInterval (-1977986459 / 1000000000000) (-1977981107 / 1000000000000)
      | 6 => orderedInterval (180328768 / 1000000000000) (180328842 / 1000000000000)
      | 7 => orderedInterval (-261925080 / 1000000000000) (-261925005 / 1000000000000)
      | _ => orderedInterval (12034599268 / 1000000000000) (12034600883 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-2944116102 / 1000000000000) (-2944109114 / 1000000000000)
      | 1 => orderedInterval (-7945207331 / 1000000000000) (-7945207099 / 1000000000000)
      | 2 => orderedInterval (-9474565270 / 1000000000000) (-9474565126 / 1000000000000)
      | 3 => orderedInterval (-52033558606 / 1000000000000) (-52033553177 / 1000000000000)
      | 4 => orderedInterval (8423534523 / 1000000000000) (8423534703 / 1000000000000)
      | 5 => orderedInterval (-1111381991 / 1000000000000) (-1111373075 / 1000000000000)
      | 6 => orderedInterval (9241878615 / 1000000000000) (9241878686 / 1000000000000)
      | 7 => orderedInterval (3959035013 / 1000000000000) (3959035076 / 1000000000000)
      | _ => orderedInterval (-77868628 / 1000000000000) (-77865694 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-16107548881 / 1000000000000) (-16107541866 / 1000000000000)
      | 1 => orderedInterval (8321616132 / 1000000000000) (8321616354 / 1000000000000)
      | 2 => orderedInterval (-6945894331 / 1000000000000) (-6945894059 / 1000000000000)
      | 3 => orderedInterval (90387796756 / 1000000000000) (90387809116 / 1000000000000)
      | 4 => orderedInterval (2429288782 / 1000000000000) (2429289095 / 1000000000000)
      | 5 => orderedInterval (-612792029 / 1000000000000) (-612776846 / 1000000000000)
      | 6 => orderedInterval (383147048 / 1000000000000) (383147118 / 1000000000000)
      | 7 => orderedInterval (602004499 / 1000000000000) (602004558 / 1000000000000)
      | _ => orderedInterval (-30712988171 / 1000000000000) (-30712982784 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-16994852220 / 1000000000000) (-16994841073 / 1000000000000)
    | 1 => orderedInterval (-5427772165 / 1000000000000) (-5427759204 / 1000000000000)
    | 2 => orderedInterval (9210220658 / 1000000000000) (9210237640 / 1000000000000)
    | 3 => orderedInterval (-51962249777 / 1000000000000) (-51962224820 / 1000000000000)
    | _ => orderedInterval (47744629805 / 1000000000000) (47744670686 / 1000000000000)

theorem compactCertificate447_stateChecks0 :
    compactCertificate447.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 101 12 (637 / 2)) (orderedInterval (-40942675641 / 1000000000000) (-40942658152 / 1000000000000), orderedInterval (18022620427 / 1000000000000) (18022637917 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (938422633812937 / 4000000000000)) (orderedInterval (11821265310 / 1000000000000) (11821265386 / 1000000000000), orderedInterval (-50758191290 / 1000000000000) (-50758191214 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 121 12 (303466598665321 / 800000000000)) (orderedInterval (589656851 / 1000000000000) (589656852 / 1000000000000), orderedInterval (-40963121441 / 1000000000000) (-40963121440 / 1000000000000))) = true
  rfl'

theorem compactCertificate447_stateChecks1 :
    compactCertificate447.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 22 12 (273829384087259 / 4000000000000)) (orderedInterval (12106918026 / 1000000000000) (12106918028 / 1000000000000), orderedInterval (95583792651 / 1000000000000) (95583792652 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (735544242947423 / 4000000000000)) (orderedInterval (37143146975 / 1000000000000) (37143166944 / 1000000000000), orderedInterval (-45734569799 / 1000000000000) (-45734549830 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 159 12 (1997145703334691 / 4000000000000)) (orderedInterval (-18917381705 / 1000000000000) (-18917381704 / 1000000000000), orderedInterval (-30266236685 / 1000000000000) (-30266236684 / 1000000000000))) = true
  rfl'

theorem compactCertificate447_stateChecks2 :
    compactCertificate447.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 117 12 (1471088485895483 / 4000000000000)) (orderedInterval (-34802403194 / 1000000000000) (-34802403193 / 1000000000000), orderedInterval (-22752005807 / 1000000000000) (-22752005806 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 201 12 (2520735194481959 / 4000000000000)) (orderedInterval (14989836524 / 1000000000000) (14989836704 / 1000000000000), orderedInterval (-28038984247 / 1000000000000) (-28038984067 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 148 12 (1856762135281781 / 4000000000000)) (orderedInterval (738763063 / 1000000000000) (738763064 / 1000000000000), orderedInterval (37025103663 / 1000000000000) (37025103664 / 1000000000000))) = true
  rfl'

theorem compactCertificate447_stateChecks3 :
    compactCertificate447.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 227 12 (2848750603334363 / 4000000000000)) (orderedInterval (5018698153 / 1000000000000) (5018698154 / 1000000000000), orderedInterval (-29477345396 / 1000000000000) (-29477345394 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 131 12 (1644726927689027 / 4000000000000)) (orderedInterval (-15979458997 / 1000000000000) (-15979458996 / 1000000000000), orderedInterval (-35937852945 / 1000000000000) (-35937852944 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 232 12 (2918596795384543 / 4000000000000)) (orderedInterval (29535175630 / 1000000000000) (29535178082 / 1000000000000), orderedInterval (-437710754 / 1000000000000) (-437708302 / 1000000000000))) = true
  rfl'

theorem compactCertificate447_stateChecks4 :
    compactCertificate447.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 217 12 (2726931716667067 / 4000000000000)) (orderedInterval (-21761893901 / 1000000000000) (-21761893900 / 1000000000000), orderedInterval (-21437377790 / 1000000000000) (-21437377789 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 155 12 (1946067145124011 / 4000000000000)) (orderedInterval (-12575820263 / 1000000000000) (-12575820262 / 1000000000000), orderedInterval (-33904255385 / 1000000000000) (-33904255384 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 176 12 (2206632728842269 / 4000000000000)) (orderedInterval (-15595100980 / 1000000000000) (-15595100726 / 1000000000000), orderedInterval (30193670671 / 1000000000000) (30193670925 / 1000000000000))) = true
  rfl'

theorem compactCertificate447_stateChecks5 :
    compactCertificate447.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 146 12 (1839660316282061 / 4000000000000)) (orderedInterval (33388935080 / 1000000000000) (33388985356 / 1000000000000), orderedInterval (-16449377954 / 1000000000000) (-16449327678 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 129 12 (1625395680735281 / 4000000000000)) (orderedInterval (-37839571776 / 1000000000000) (-37839563072 / 1000000000000), orderedInterval (11658994050 / 1000000000000) (11659002754 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 188 12 (471103021116819 / 800000000000)) (orderedInterval (-26848787024 / 1000000000000) (-26848749847 / 1000000000000), orderedInterval (19002094876 / 1000000000000) (19002132053 / 1000000000000))) = true
  rfl'

theorem compactCertificate447_stateChecks6 :
    compactCertificate447.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 104 12 (1303095749202793 / 4000000000000)) (orderedInterval (-7334376239 / 1000000000000) (-7334376224 / 1000000000000), orderedInterval (43604669156 / 1000000000000) (43604669171 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 88 12 (1104648697989473 / 4000000000000)) (orderedInterval (22467484288 / 1000000000000) (22467484289 / 1000000000000), orderedInterval (42391068665 / 1000000000000) (42391068666 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (691237864718219 / 4000000000000)) (orderedInterval (-43816011606 / 1000000000000) (-43816011605 / 1000000000000), orderedInterval (-41874378715 / 1000000000000) (-41874378714 / 1000000000000))) = true
  rfl'

theorem compactCertificate447_stateChecks7 :
    compactCertificate447.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (371750022598773 / 4000000000000)) (orderedInterval (-41569783628 / 1000000000000) (-41569776979 / 1000000000000), orderedInterval (71791639279 / 1000000000000) (71791645929 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (1009373627035319 / 4000000000000)) (orderedInterval (48903907201 / 1000000000000) (48903909036 / 1000000000000), orderedInterval (-11552655910 / 1000000000000) (-11552654075 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 110 12 (1378213393711063 / 4000000000000)) (orderedInterval (-10084200026 / 1000000000000) (-10084199988 / 1000000000000), orderedInterval (41799528215 / 1000000000000) (41799528253 / 1000000000000))) = true
  rfl'

theorem compactCertificate447_stateChecks8 :
    compactCertificate447.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (582762135281781 / 4000000000000)) (orderedInterval (61113978381 / 1000000000000) (61113984256 / 1000000000000), orderedInterval (-25403677277 / 1000000000000) (-25403671401 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 189 12 (2368895725934101 / 4000000000000)) (orderedInterval (22394018040 / 1000000000000) (22394023091 / 1000000000000), orderedInterval (-23966194707 / 1000000000000) (-23966189656 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 126 12 (1582312560669659 / 4000000000000)) (orderedInterval (20021765255 / 1000000000000) (20021765256 / 1000000000000), orderedInterval (34737743619 / 1000000000000) (34737743620 / 1000000000000))) = true
  rfl'

theorem compactCertificate447_states : ∀ j,
    BesselStateValid (compactCertificate447.point j) (compactCertificate447.state j) :=
  compactCertificate447.statesValid_of_checks3 compactCertificate447_stateChecks0
    compactCertificate447_stateChecks1 compactCertificate447_stateChecks2
    compactCertificate447_stateChecks3 compactCertificate447_stateChecks4
    compactCertificate447_stateChecks5 compactCertificate447_stateChecks6
    compactCertificate447_stateChecks7 compactCertificate447_stateChecks8

theorem compactCertificate447_chunkChecks0_0 :
    compactCertificate447.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (637 / 2) 0 (IntervalRat.scale (637 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-40942675641 / 1000000000000) (-40942658152 / 1000000000000), orderedInterval (18022620427 / 1000000000000) (18022637917 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (938422633812937 / 4000000000000) 0 (IntervalRat.scale (637 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (11821265310 / 1000000000000) (11821265386 / 1000000000000), orderedInterval (-50758191290 / 1000000000000) (-50758191214 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (303466598665321 / 800000000000) 0 (IntervalRat.scale (637 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (589656851 / 1000000000000) (589656852 / 1000000000000), orderedInterval (-40963121441 / 1000000000000) (-40963121440 / 1000000000000)))) (orderedInterval (-16083490360 / 1000000000000) (-16083483404 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (273829384087259 / 4000000000000) 0 (IntervalRat.scale (637 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (12106918026 / 1000000000000) (12106918028 / 1000000000000), orderedInterval (95583792651 / 1000000000000) (95583792652 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (735544242947423 / 4000000000000) 0 (IntervalRat.scale (637 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (37143146975 / 1000000000000) (37143166944 / 1000000000000), orderedInterval (-45734569799 / 1000000000000) (-45734549830 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1997145703334691 / 4000000000000) 0 (IntervalRat.scale (637 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-18917381705 / 1000000000000) (-18917381704 / 1000000000000), orderedInterval (-30266236685 / 1000000000000) (-30266236684 / 1000000000000)))) (orderedInterval (2569639526 / 1000000000000) (2569640294 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1471088485895483 / 4000000000000) 0 (IntervalRat.scale (637 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-34802403194 / 1000000000000) (-34802403193 / 1000000000000), orderedInterval (-22752005807 / 1000000000000) (-22752005806 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2520735194481959 / 4000000000000) 0 (IntervalRat.scale (637 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (14989836524 / 1000000000000) (14989836704 / 1000000000000), orderedInterval (-28038984247 / 1000000000000) (-28038984067 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1856762135281781 / 4000000000000) 0 (IntervalRat.scale (637 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (738763063 / 1000000000000) (738763064 / 1000000000000), orderedInterval (37025103663 / 1000000000000) (37025103664 / 1000000000000)))) (orderedInterval (-444492102 / 1000000000000) (-444492078 / 1000000000000))) = true
  rfl'

theorem compactCertificate447_chunkChecks0_1 :
    compactCertificate447.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2848750603334363 / 4000000000000) 0 (IntervalRat.scale (637 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (5018698153 / 1000000000000) (5018698154 / 1000000000000), orderedInterval (-29477345396 / 1000000000000) (-29477345394 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1644726927689027 / 4000000000000) 0 (IntervalRat.scale (637 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-15979458997 / 1000000000000) (-15979458996 / 1000000000000), orderedInterval (-35937852945 / 1000000000000) (-35937852944 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2918596795384543 / 4000000000000) 0 (IntervalRat.scale (637 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (29535175630 / 1000000000000) (29535178082 / 1000000000000), orderedInterval (-437710754 / 1000000000000) (-437708302 / 1000000000000)))) (orderedInterval (2122890691 / 1000000000000) (2122891166 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2726931716667067 / 4000000000000) 0 (IntervalRat.scale (637 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21761893901 / 1000000000000) (-21761893900 / 1000000000000), orderedInterval (-21437377790 / 1000000000000) (-21437377789 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1946067145124011 / 4000000000000) 0 (IntervalRat.scale (637 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-12575820263 / 1000000000000) (-12575820262 / 1000000000000), orderedInterval (-33904255385 / 1000000000000) (-33904255384 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2206632728842269 / 4000000000000) 0 (IntervalRat.scale (637 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-15595100980 / 1000000000000) (-15595100726 / 1000000000000), orderedInterval (30193670671 / 1000000000000) (30193670925 / 1000000000000)))) (orderedInterval (-717416091 / 1000000000000) (-717416051 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1839660316282061 / 4000000000000) 0 (IntervalRat.scale (637 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (33388935080 / 1000000000000) (33388985356 / 1000000000000), orderedInterval (-16449377954 / 1000000000000) (-16449327678 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1625395680735281 / 4000000000000) 0 (IntervalRat.scale (637 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-37839571776 / 1000000000000) (-37839563072 / 1000000000000), orderedInterval (11658994050 / 1000000000000) (11659002754 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (471103021116819 / 800000000000) 0 (IntervalRat.scale (637 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-26848787024 / 1000000000000) (-26848749847 / 1000000000000), orderedInterval (19002094876 / 1000000000000) (19002132053 / 1000000000000)))) (orderedInterval (1863561842 / 1000000000000) (1863563903 / 1000000000000))) = true
  rfl'

theorem compactCertificate447_chunkChecks0_2 :
    compactCertificate447.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1303095749202793 / 4000000000000) 0 (IntervalRat.scale (637 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-7334376239 / 1000000000000) (-7334376224 / 1000000000000), orderedInterval (43604669156 / 1000000000000) (43604669171 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1104648697989473 / 4000000000000) 0 (IntervalRat.scale (637 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (22467484288 / 1000000000000) (22467484289 / 1000000000000), orderedInterval (42391068665 / 1000000000000) (42391068666 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (691237864718219 / 4000000000000) 0 (IntervalRat.scale (637 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-43816011606 / 1000000000000) (-43816011605 / 1000000000000), orderedInterval (-41874378715 / 1000000000000) (-41874378714 / 1000000000000)))) (orderedInterval (-1525389469 / 1000000000000) (-1525389387 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (371750022598773 / 4000000000000) 0 (IntervalRat.scale (637 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-41569783628 / 1000000000000) (-41569776979 / 1000000000000), orderedInterval (71791639279 / 1000000000000) (71791645929 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1009373627035319 / 4000000000000) 0 (IntervalRat.scale (637 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (48903907201 / 1000000000000) (48903909036 / 1000000000000), orderedInterval (-11552655910 / 1000000000000) (-11552654075 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1378213393711063 / 4000000000000) 0 (IntervalRat.scale (637 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-10084200026 / 1000000000000) (-10084199988 / 1000000000000), orderedInterval (41799528215 / 1000000000000) (41799528253 / 1000000000000)))) (orderedInterval (430956233 / 1000000000000) (430956439 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (582762135281781 / 4000000000000) 0 (IntervalRat.scale (637 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (61113978381 / 1000000000000) (61113984256 / 1000000000000), orderedInterval (-25403677277 / 1000000000000) (-25403671401 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2368895725934101 / 4000000000000) 0 (IntervalRat.scale (637 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (22394018040 / 1000000000000) (22394023091 / 1000000000000), orderedInterval (-23966194707 / 1000000000000) (-23966189656 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1582312560669659 / 4000000000000) 0 (IntervalRat.scale (637 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (20021765255 / 1000000000000) (20021765256 / 1000000000000), orderedInterval (34737743619 / 1000000000000) (34737743620 / 1000000000000)))) (orderedInterval (-5211112490 / 1000000000000) (-5211111955 / 1000000000000))) = true
  rfl'

theorem compactCertificate447_chunkChecks0 :
    compactCertificate447.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate447.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate447_chunkChecks0_0
    compactCertificate447_chunkChecks0_1 compactCertificate447_chunkChecks0_2

theorem compactCertificate447_chunkChecks1_0 :
    compactCertificate447.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (637 / 2) 1 (IntervalRat.scale (637 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-40942675641 / 1000000000000) (-40942658152 / 1000000000000), orderedInterval (18022620427 / 1000000000000) (18022637917 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (938422633812937 / 4000000000000) 1 (IntervalRat.scale (637 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (11821265310 / 1000000000000) (11821265386 / 1000000000000), orderedInterval (-50758191290 / 1000000000000) (-50758191214 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (303466598665321 / 800000000000) 1 (IntervalRat.scale (637 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (589656851 / 1000000000000) (589656852 / 1000000000000), orderedInterval (-40963121441 / 1000000000000) (-40963121440 / 1000000000000)))) (orderedInterval (3932270379 / 1000000000000) (3932277338 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (273829384087259 / 4000000000000) 1 (IntervalRat.scale (637 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (12106918026 / 1000000000000) (12106918028 / 1000000000000), orderedInterval (95583792651 / 1000000000000) (95583792652 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (735544242947423 / 4000000000000) 1 (IntervalRat.scale (637 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (37143146975 / 1000000000000) (37143166944 / 1000000000000), orderedInterval (-45734569799 / 1000000000000) (-45734549830 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1997145703334691 / 4000000000000) 1 (IntervalRat.scale (637 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-18917381705 / 1000000000000) (-18917381704 / 1000000000000), orderedInterval (-30266236685 / 1000000000000) (-30266236684 / 1000000000000)))) (orderedInterval (2185931750 / 1000000000000) (2185932215 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1471088485895483 / 4000000000000) 1 (IntervalRat.scale (637 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-34802403194 / 1000000000000) (-34802403193 / 1000000000000), orderedInterval (-22752005807 / 1000000000000) (-22752005806 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2520735194481959 / 4000000000000) 1 (IntervalRat.scale (637 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (14989836524 / 1000000000000) (14989836704 / 1000000000000), orderedInterval (-28038984247 / 1000000000000) (-28038984067 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1856762135281781 / 4000000000000) 1 (IntervalRat.scale (637 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (738763063 / 1000000000000) (738763064 / 1000000000000), orderedInterval (37025103663 / 1000000000000) (37025103664 / 1000000000000)))) (orderedInterval (3015300938 / 1000000000000) (3015300981 / 1000000000000))) = true
  rfl'

theorem compactCertificate447_chunkChecks1_1 :
    compactCertificate447.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2848750603334363 / 4000000000000) 1 (IntervalRat.scale (637 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (5018698153 / 1000000000000) (5018698154 / 1000000000000), orderedInterval (-29477345396 / 1000000000000) (-29477345394 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1644726927689027 / 4000000000000) 1 (IntervalRat.scale (637 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-15979458997 / 1000000000000) (-15979458996 / 1000000000000), orderedInterval (-35937852945 / 1000000000000) (-35937852944 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2918596795384543 / 4000000000000) 1 (IntervalRat.scale (637 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (29535175630 / 1000000000000) (29535178082 / 1000000000000), orderedInterval (-437710754 / 1000000000000) (-437708302 / 1000000000000)))) (orderedInterval (8131929576 / 1000000000000) (8131930637 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2726931716667067 / 4000000000000) 1 (IntervalRat.scale (637 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21761893901 / 1000000000000) (-21761893900 / 1000000000000), orderedInterval (-21437377790 / 1000000000000) (-21437377789 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1946067145124011 / 4000000000000) 1 (IntervalRat.scale (637 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-12575820263 / 1000000000000) (-12575820262 / 1000000000000), orderedInterval (-33904255385 / 1000000000000) (-33904255384 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2206632728842269 / 4000000000000) 1 (IntervalRat.scale (637 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-15595100980 / 1000000000000) (-15595100726 / 1000000000000), orderedInterval (30193670671 / 1000000000000) (30193670925 / 1000000000000)))) (orderedInterval (-4333649525 / 1000000000000) (-4333649460 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1839660316282061 / 4000000000000) 1 (IntervalRat.scale (637 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (33388935080 / 1000000000000) (33388985356 / 1000000000000), orderedInterval (-16449377954 / 1000000000000) (-16449327678 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1625395680735281 / 4000000000000) 1 (IntervalRat.scale (637 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-37839571776 / 1000000000000) (-37839563072 / 1000000000000), orderedInterval (11658994050 / 1000000000000) (11659002754 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (471103021116819 / 800000000000) 1 (IntervalRat.scale (637 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-26848787024 / 1000000000000) (-26848749847 / 1000000000000), orderedInterval (19002094876 / 1000000000000) (19002132053 / 1000000000000)))) (orderedInterval (-225977408 / 1000000000000) (-225974129 / 1000000000000))) = true
  rfl'

theorem compactCertificate447_chunkChecks1_2 :
    compactCertificate447.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1303095749202793 / 4000000000000) 1 (IntervalRat.scale (637 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-7334376239 / 1000000000000) (-7334376224 / 1000000000000), orderedInterval (43604669156 / 1000000000000) (43604669171 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1104648697989473 / 4000000000000) 1 (IntervalRat.scale (637 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (22467484288 / 1000000000000) (22467484289 / 1000000000000), orderedInterval (42391068665 / 1000000000000) (42391068666 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (691237864718219 / 4000000000000) 1 (IntervalRat.scale (637 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-43816011606 / 1000000000000) (-43816011605 / 1000000000000), orderedInterval (-41874378715 / 1000000000000) (-41874378714 / 1000000000000)))) (orderedInterval (-9951330450 / 1000000000000) (-9951330373 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (371750022598773 / 4000000000000) 1 (IntervalRat.scale (637 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-41569783628 / 1000000000000) (-41569776979 / 1000000000000), orderedInterval (71791639279 / 1000000000000) (71791645929 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1009373627035319 / 4000000000000) 1 (IntervalRat.scale (637 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (48903907201 / 1000000000000) (48903909036 / 1000000000000), orderedInterval (-11552655910 / 1000000000000) (-11552654075 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1378213393711063 / 4000000000000) 1 (IntervalRat.scale (637 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-10084200026 / 1000000000000) (-10084199988 / 1000000000000), orderedInterval (41799528215 / 1000000000000) (41799528253 / 1000000000000)))) (orderedInterval (-3644678382 / 1000000000000) (-3644678275 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (582762135281781 / 4000000000000) 1 (IntervalRat.scale (637 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (61113978381 / 1000000000000) (61113984256 / 1000000000000), orderedInterval (-25403677277 / 1000000000000) (-25403671401 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2368895725934101 / 4000000000000) 1 (IntervalRat.scale (637 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (22394018040 / 1000000000000) (22394023091 / 1000000000000), orderedInterval (-23966194707 / 1000000000000) (-23966189656 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1582312560669659 / 4000000000000) 1 (IntervalRat.scale (637 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (20021765255 / 1000000000000) (20021765256 / 1000000000000), orderedInterval (34737743619 / 1000000000000) (34737743620 / 1000000000000)))) (orderedInterval (-4537569043 / 1000000000000) (-4537568138 / 1000000000000))) = true
  rfl'

theorem compactCertificate447_chunkChecks1 :
    compactCertificate447.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate447.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate447_chunkChecks1_0
    compactCertificate447_chunkChecks1_1 compactCertificate447_chunkChecks1_2

theorem compactCertificate447_chunkChecks2_0 :
    compactCertificate447.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (637 / 2) 2 (IntervalRat.scale (637 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-40942675641 / 1000000000000) (-40942658152 / 1000000000000), orderedInterval (18022620427 / 1000000000000) (18022637917 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (938422633812937 / 4000000000000) 2 (IntervalRat.scale (637 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (11821265310 / 1000000000000) (11821265386 / 1000000000000), orderedInterval (-50758191290 / 1000000000000) (-50758191214 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (303466598665321 / 800000000000) 2 (IntervalRat.scale (637 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (589656851 / 1000000000000) (589656852 / 1000000000000), orderedInterval (-40963121441 / 1000000000000) (-40963121440 / 1000000000000)))) (orderedInterval (16107043229 / 1000000000000) (16107050213 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (273829384087259 / 4000000000000) 2 (IntervalRat.scale (637 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (12106918026 / 1000000000000) (12106918028 / 1000000000000), orderedInterval (95583792651 / 1000000000000) (95583792652 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (735544242947423 / 4000000000000) 2 (IntervalRat.scale (637 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (37143146975 / 1000000000000) (37143166944 / 1000000000000), orderedInterval (-45734569799 / 1000000000000) (-45734549830 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1997145703334691 / 4000000000000) 2 (IntervalRat.scale (637 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-18917381705 / 1000000000000) (-18917381704 / 1000000000000), orderedInterval (-30266236685 / 1000000000000) (-30266236684 / 1000000000000)))) (orderedInterval (-3757670438 / 1000000000000) (-3757670133 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1471088485895483 / 4000000000000) 2 (IntervalRat.scale (637 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-34802403194 / 1000000000000) (-34802403193 / 1000000000000), orderedInterval (-22752005807 / 1000000000000) (-22752005806 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2520735194481959 / 4000000000000) 2 (IntervalRat.scale (637 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (14989836524 / 1000000000000) (14989836704 / 1000000000000), orderedInterval (-28038984247 / 1000000000000) (-28038984067 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1856762135281781 / 4000000000000) 2 (IntervalRat.scale (637 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (738763063 / 1000000000000) (738763064 / 1000000000000), orderedInterval (37025103663 / 1000000000000) (37025103664 / 1000000000000)))) (orderedInterval (1762627535 / 1000000000000) (1762627613 / 1000000000000))) = true
  rfl'

theorem compactCertificate447_chunkChecks2_1 :
    compactCertificate447.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2848750603334363 / 4000000000000) 2 (IntervalRat.scale (637 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (5018698153 / 1000000000000) (5018698154 / 1000000000000), orderedInterval (-29477345396 / 1000000000000) (-29477345394 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1644726927689027 / 4000000000000) 2 (IntervalRat.scale (637 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-15979458997 / 1000000000000) (-15979458996 / 1000000000000), orderedInterval (-35937852945 / 1000000000000) (-35937852944 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2918596795384543 / 4000000000000) 2 (IntervalRat.scale (637 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (29535175630 / 1000000000000) (29535178082 / 1000000000000), orderedInterval (-437710754 / 1000000000000) (-437708302 / 1000000000000)))) (orderedInterval (-15628515954 / 1000000000000) (-15628513561 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2726931716667067 / 4000000000000) 2 (IntervalRat.scale (637 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21761893901 / 1000000000000) (-21761893900 / 1000000000000), orderedInterval (-21437377790 / 1000000000000) (-21437377789 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1946067145124011 / 4000000000000) 2 (IntervalRat.scale (637 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-12575820263 / 1000000000000) (-12575820262 / 1000000000000), orderedInterval (-33904255385 / 1000000000000) (-33904255384 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2206632728842269 / 4000000000000) 2 (IntervalRat.scale (637 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-15595100980 / 1000000000000) (-15595100726 / 1000000000000), orderedInterval (30193670671 / 1000000000000) (30193670925 / 1000000000000)))) (orderedInterval (751719789 / 1000000000000) (751719895 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1839660316282061 / 4000000000000) 2 (IntervalRat.scale (637 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (33388935080 / 1000000000000) (33388985356 / 1000000000000), orderedInterval (-16449377954 / 1000000000000) (-16449327678 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1625395680735281 / 4000000000000) 2 (IntervalRat.scale (637 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-37839571776 / 1000000000000) (-37839563072 / 1000000000000), orderedInterval (11658994050 / 1000000000000) (11659002754 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (471103021116819 / 800000000000) 2 (IntervalRat.scale (637 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-26848787024 / 1000000000000) (-26848749847 / 1000000000000), orderedInterval (19002094876 / 1000000000000) (19002132053 / 1000000000000)))) (orderedInterval (-1977986459 / 1000000000000) (-1977981107 / 1000000000000))) = true
  rfl'

theorem compactCertificate447_chunkChecks2_2 :
    compactCertificate447.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1303095749202793 / 4000000000000) 2 (IntervalRat.scale (637 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-7334376239 / 1000000000000) (-7334376224 / 1000000000000), orderedInterval (43604669156 / 1000000000000) (43604669171 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1104648697989473 / 4000000000000) 2 (IntervalRat.scale (637 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (22467484288 / 1000000000000) (22467484289 / 1000000000000), orderedInterval (42391068665 / 1000000000000) (42391068666 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (691237864718219 / 4000000000000) 2 (IntervalRat.scale (637 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-43816011606 / 1000000000000) (-43816011605 / 1000000000000), orderedInterval (-41874378715 / 1000000000000) (-41874378714 / 1000000000000)))) (orderedInterval (180328768 / 1000000000000) (180328842 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (371750022598773 / 4000000000000) 2 (IntervalRat.scale (637 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-41569783628 / 1000000000000) (-41569776979 / 1000000000000), orderedInterval (71791639279 / 1000000000000) (71791645929 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1009373627035319 / 4000000000000) 2 (IntervalRat.scale (637 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (48903907201 / 1000000000000) (48903909036 / 1000000000000), orderedInterval (-11552655910 / 1000000000000) (-11552654075 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1378213393711063 / 4000000000000) 2 (IntervalRat.scale (637 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-10084200026 / 1000000000000) (-10084199988 / 1000000000000), orderedInterval (41799528215 / 1000000000000) (41799528253 / 1000000000000)))) (orderedInterval (-261925080 / 1000000000000) (-261925005 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (582762135281781 / 4000000000000) 2 (IntervalRat.scale (637 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (61113978381 / 1000000000000) (61113984256 / 1000000000000), orderedInterval (-25403677277 / 1000000000000) (-25403671401 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2368895725934101 / 4000000000000) 2 (IntervalRat.scale (637 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (22394018040 / 1000000000000) (22394023091 / 1000000000000), orderedInterval (-23966194707 / 1000000000000) (-23966189656 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1582312560669659 / 4000000000000) 2 (IntervalRat.scale (637 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (20021765255 / 1000000000000) (20021765256 / 1000000000000), orderedInterval (34737743619 / 1000000000000) (34737743620 / 1000000000000)))) (orderedInterval (12034599268 / 1000000000000) (12034600883 / 1000000000000))) = true
  rfl'

theorem compactCertificate447_chunkChecks2 :
    compactCertificate447.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate447.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate447_chunkChecks2_0
    compactCertificate447_chunkChecks2_1 compactCertificate447_chunkChecks2_2

theorem compactCertificate447_chunkChecks3_0 :
    compactCertificate447.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (637 / 2) 3 (IntervalRat.scale (637 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-40942675641 / 1000000000000) (-40942658152 / 1000000000000), orderedInterval (18022620427 / 1000000000000) (18022637917 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (938422633812937 / 4000000000000) 3 (IntervalRat.scale (637 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (11821265310 / 1000000000000) (11821265386 / 1000000000000), orderedInterval (-50758191290 / 1000000000000) (-50758191214 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (303466598665321 / 800000000000) 3 (IntervalRat.scale (637 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (589656851 / 1000000000000) (589656852 / 1000000000000), orderedInterval (-40963121441 / 1000000000000) (-40963121440 / 1000000000000)))) (orderedInterval (-2944116102 / 1000000000000) (-2944109114 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (273829384087259 / 4000000000000) 3 (IntervalRat.scale (637 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (12106918026 / 1000000000000) (12106918028 / 1000000000000), orderedInterval (95583792651 / 1000000000000) (95583792652 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (735544242947423 / 4000000000000) 3 (IntervalRat.scale (637 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (37143146975 / 1000000000000) (37143166944 / 1000000000000), orderedInterval (-45734569799 / 1000000000000) (-45734549830 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1997145703334691 / 4000000000000) 3 (IntervalRat.scale (637 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-18917381705 / 1000000000000) (-18917381704 / 1000000000000), orderedInterval (-30266236685 / 1000000000000) (-30266236684 / 1000000000000)))) (orderedInterval (-7945207331 / 1000000000000) (-7945207099 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1471088485895483 / 4000000000000) 3 (IntervalRat.scale (637 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-34802403194 / 1000000000000) (-34802403193 / 1000000000000), orderedInterval (-22752005807 / 1000000000000) (-22752005806 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2520735194481959 / 4000000000000) 3 (IntervalRat.scale (637 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (14989836524 / 1000000000000) (14989836704 / 1000000000000), orderedInterval (-28038984247 / 1000000000000) (-28038984067 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1856762135281781 / 4000000000000) 3 (IntervalRat.scale (637 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (738763063 / 1000000000000) (738763064 / 1000000000000), orderedInterval (37025103663 / 1000000000000) (37025103664 / 1000000000000)))) (orderedInterval (-9474565270 / 1000000000000) (-9474565126 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate447_chunkChecks3_1 :
    compactCertificate447.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2848750603334363 / 4000000000000) 3 (IntervalRat.scale (637 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (5018698153 / 1000000000000) (5018698154 / 1000000000000), orderedInterval (-29477345396 / 1000000000000) (-29477345394 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1644726927689027 / 4000000000000) 3 (IntervalRat.scale (637 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-15979458997 / 1000000000000) (-15979458996 / 1000000000000), orderedInterval (-35937852945 / 1000000000000) (-35937852944 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2918596795384543 / 4000000000000) 3 (IntervalRat.scale (637 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (29535175630 / 1000000000000) (29535178082 / 1000000000000), orderedInterval (-437710754 / 1000000000000) (-437708302 / 1000000000000)))) (orderedInterval (-52033558606 / 1000000000000) (-52033553177 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2726931716667067 / 4000000000000) 3 (IntervalRat.scale (637 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21761893901 / 1000000000000) (-21761893900 / 1000000000000), orderedInterval (-21437377790 / 1000000000000) (-21437377789 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1946067145124011 / 4000000000000) 3 (IntervalRat.scale (637 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-12575820263 / 1000000000000) (-12575820262 / 1000000000000), orderedInterval (-33904255385 / 1000000000000) (-33904255384 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2206632728842269 / 4000000000000) 3 (IntervalRat.scale (637 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-15595100980 / 1000000000000) (-15595100726 / 1000000000000), orderedInterval (30193670671 / 1000000000000) (30193670925 / 1000000000000)))) (orderedInterval (8423534523 / 1000000000000) (8423534703 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1839660316282061 / 4000000000000) 3 (IntervalRat.scale (637 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (33388935080 / 1000000000000) (33388985356 / 1000000000000), orderedInterval (-16449377954 / 1000000000000) (-16449327678 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1625395680735281 / 4000000000000) 3 (IntervalRat.scale (637 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-37839571776 / 1000000000000) (-37839563072 / 1000000000000), orderedInterval (11658994050 / 1000000000000) (11659002754 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (471103021116819 / 800000000000) 3 (IntervalRat.scale (637 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-26848787024 / 1000000000000) (-26848749847 / 1000000000000), orderedInterval (19002094876 / 1000000000000) (19002132053 / 1000000000000)))) (orderedInterval (-1111381991 / 1000000000000) (-1111373075 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate447_chunkChecks3_2 :
    compactCertificate447.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1303095749202793 / 4000000000000) 3 (IntervalRat.scale (637 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-7334376239 / 1000000000000) (-7334376224 / 1000000000000), orderedInterval (43604669156 / 1000000000000) (43604669171 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1104648697989473 / 4000000000000) 3 (IntervalRat.scale (637 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (22467484288 / 1000000000000) (22467484289 / 1000000000000), orderedInterval (42391068665 / 1000000000000) (42391068666 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (691237864718219 / 4000000000000) 3 (IntervalRat.scale (637 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-43816011606 / 1000000000000) (-43816011605 / 1000000000000), orderedInterval (-41874378715 / 1000000000000) (-41874378714 / 1000000000000)))) (orderedInterval (9241878615 / 1000000000000) (9241878686 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (371750022598773 / 4000000000000) 3 (IntervalRat.scale (637 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-41569783628 / 1000000000000) (-41569776979 / 1000000000000), orderedInterval (71791639279 / 1000000000000) (71791645929 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1009373627035319 / 4000000000000) 3 (IntervalRat.scale (637 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (48903907201 / 1000000000000) (48903909036 / 1000000000000), orderedInterval (-11552655910 / 1000000000000) (-11552654075 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1378213393711063 / 4000000000000) 3 (IntervalRat.scale (637 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-10084200026 / 1000000000000) (-10084199988 / 1000000000000), orderedInterval (41799528215 / 1000000000000) (41799528253 / 1000000000000)))) (orderedInterval (3959035013 / 1000000000000) (3959035076 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (582762135281781 / 4000000000000) 3 (IntervalRat.scale (637 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (61113978381 / 1000000000000) (61113984256 / 1000000000000), orderedInterval (-25403677277 / 1000000000000) (-25403671401 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2368895725934101 / 4000000000000) 3 (IntervalRat.scale (637 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (22394018040 / 1000000000000) (22394023091 / 1000000000000), orderedInterval (-23966194707 / 1000000000000) (-23966189656 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1582312560669659 / 4000000000000) 3 (IntervalRat.scale (637 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (20021765255 / 1000000000000) (20021765256 / 1000000000000), orderedInterval (34737743619 / 1000000000000) (34737743620 / 1000000000000)))) (orderedInterval (-77868628 / 1000000000000) (-77865694 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate447_chunkChecks3 :
    compactCertificate447.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate447.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate447_chunkChecks3_0
    compactCertificate447_chunkChecks3_1 compactCertificate447_chunkChecks3_2

theorem compactCertificate447_chunkChecks4_0 :
    compactCertificate447.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (637 / 2) 4 (IntervalRat.scale (637 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-40942675641 / 1000000000000) (-40942658152 / 1000000000000), orderedInterval (18022620427 / 1000000000000) (18022637917 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (938422633812937 / 4000000000000) 4 (IntervalRat.scale (637 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (11821265310 / 1000000000000) (11821265386 / 1000000000000), orderedInterval (-50758191290 / 1000000000000) (-50758191214 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (303466598665321 / 800000000000) 4 (IntervalRat.scale (637 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (589656851 / 1000000000000) (589656852 / 1000000000000), orderedInterval (-40963121441 / 1000000000000) (-40963121440 / 1000000000000)))) (orderedInterval (-16107548881 / 1000000000000) (-16107541866 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (273829384087259 / 4000000000000) 4 (IntervalRat.scale (637 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (12106918026 / 1000000000000) (12106918028 / 1000000000000), orderedInterval (95583792651 / 1000000000000) (95583792652 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (735544242947423 / 4000000000000) 4 (IntervalRat.scale (637 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (37143146975 / 1000000000000) (37143166944 / 1000000000000), orderedInterval (-45734569799 / 1000000000000) (-45734549830 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1997145703334691 / 4000000000000) 4 (IntervalRat.scale (637 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-18917381705 / 1000000000000) (-18917381704 / 1000000000000), orderedInterval (-30266236685 / 1000000000000) (-30266236684 / 1000000000000)))) (orderedInterval (8321616132 / 1000000000000) (8321616354 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1471088485895483 / 4000000000000) 4 (IntervalRat.scale (637 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-34802403194 / 1000000000000) (-34802403193 / 1000000000000), orderedInterval (-22752005807 / 1000000000000) (-22752005806 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2520735194481959 / 4000000000000) 4 (IntervalRat.scale (637 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (14989836524 / 1000000000000) (14989836704 / 1000000000000), orderedInterval (-28038984247 / 1000000000000) (-28038984067 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1856762135281781 / 4000000000000) 4 (IntervalRat.scale (637 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (738763063 / 1000000000000) (738763064 / 1000000000000), orderedInterval (37025103663 / 1000000000000) (37025103664 / 1000000000000)))) (orderedInterval (-6945894331 / 1000000000000) (-6945894059 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate447_chunkChecks4_1 :
    compactCertificate447.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2848750603334363 / 4000000000000) 4 (IntervalRat.scale (637 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (5018698153 / 1000000000000) (5018698154 / 1000000000000), orderedInterval (-29477345396 / 1000000000000) (-29477345394 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1644726927689027 / 4000000000000) 4 (IntervalRat.scale (637 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-15979458997 / 1000000000000) (-15979458996 / 1000000000000), orderedInterval (-35937852945 / 1000000000000) (-35937852944 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2918596795384543 / 4000000000000) 4 (IntervalRat.scale (637 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (29535175630 / 1000000000000) (29535178082 / 1000000000000), orderedInterval (-437710754 / 1000000000000) (-437708302 / 1000000000000)))) (orderedInterval (90387796756 / 1000000000000) (90387809116 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2726931716667067 / 4000000000000) 4 (IntervalRat.scale (637 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21761893901 / 1000000000000) (-21761893900 / 1000000000000), orderedInterval (-21437377790 / 1000000000000) (-21437377789 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1946067145124011 / 4000000000000) 4 (IntervalRat.scale (637 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-12575820263 / 1000000000000) (-12575820262 / 1000000000000), orderedInterval (-33904255385 / 1000000000000) (-33904255384 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2206632728842269 / 4000000000000) 4 (IntervalRat.scale (637 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-15595100980 / 1000000000000) (-15595100726 / 1000000000000), orderedInterval (30193670671 / 1000000000000) (30193670925 / 1000000000000)))) (orderedInterval (2429288782 / 1000000000000) (2429289095 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1839660316282061 / 4000000000000) 4 (IntervalRat.scale (637 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (33388935080 / 1000000000000) (33388985356 / 1000000000000), orderedInterval (-16449377954 / 1000000000000) (-16449327678 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1625395680735281 / 4000000000000) 4 (IntervalRat.scale (637 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-37839571776 / 1000000000000) (-37839563072 / 1000000000000), orderedInterval (11658994050 / 1000000000000) (11659002754 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (471103021116819 / 800000000000) 4 (IntervalRat.scale (637 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-26848787024 / 1000000000000) (-26848749847 / 1000000000000), orderedInterval (19002094876 / 1000000000000) (19002132053 / 1000000000000)))) (orderedInterval (-612792029 / 1000000000000) (-612776846 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate447_chunkChecks4_2 :
    compactCertificate447.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1303095749202793 / 4000000000000) 4 (IntervalRat.scale (637 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-7334376239 / 1000000000000) (-7334376224 / 1000000000000), orderedInterval (43604669156 / 1000000000000) (43604669171 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1104648697989473 / 4000000000000) 4 (IntervalRat.scale (637 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (22467484288 / 1000000000000) (22467484289 / 1000000000000), orderedInterval (42391068665 / 1000000000000) (42391068666 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (691237864718219 / 4000000000000) 4 (IntervalRat.scale (637 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-43816011606 / 1000000000000) (-43816011605 / 1000000000000), orderedInterval (-41874378715 / 1000000000000) (-41874378714 / 1000000000000)))) (orderedInterval (383147048 / 1000000000000) (383147118 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (371750022598773 / 4000000000000) 4 (IntervalRat.scale (637 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-41569783628 / 1000000000000) (-41569776979 / 1000000000000), orderedInterval (71791639279 / 1000000000000) (71791645929 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1009373627035319 / 4000000000000) 4 (IntervalRat.scale (637 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (48903907201 / 1000000000000) (48903909036 / 1000000000000), orderedInterval (-11552655910 / 1000000000000) (-11552654075 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1378213393711063 / 4000000000000) 4 (IntervalRat.scale (637 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-10084200026 / 1000000000000) (-10084199988 / 1000000000000), orderedInterval (41799528215 / 1000000000000) (41799528253 / 1000000000000)))) (orderedInterval (602004499 / 1000000000000) (602004558 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (582762135281781 / 4000000000000) 4 (IntervalRat.scale (637 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (61113978381 / 1000000000000) (61113984256 / 1000000000000), orderedInterval (-25403677277 / 1000000000000) (-25403671401 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2368895725934101 / 4000000000000) 4 (IntervalRat.scale (637 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (22394018040 / 1000000000000) (22394023091 / 1000000000000), orderedInterval (-23966194707 / 1000000000000) (-23966189656 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1582312560669659 / 4000000000000) 4 (IntervalRat.scale (637 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (20021765255 / 1000000000000) (20021765256 / 1000000000000), orderedInterval (34737743619 / 1000000000000) (34737743620 / 1000000000000)))) (orderedInterval (-30712988171 / 1000000000000) (-30712982784 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate447_chunkChecks4 :
    compactCertificate447.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate447.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate447_chunkChecks4_0
    compactCertificate447_chunkChecks4_1 compactCertificate447_chunkChecks4_2

theorem compactCertificate447_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate447.chunkCheck r b = true :=
  compactCertificate447.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate447_chunkChecks0
    · exact compactCertificate447_chunkChecks1
    · exact compactCertificate447_chunkChecks2
    · exact compactCertificate447_chunkChecks3
    · exact compactCertificate447_chunkChecks4)

theorem compactCertificate447_coefficient0 :
    compactCertificate447.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate447_coefficient1 :
    compactCertificate447.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate447_coefficient2 :
    compactCertificate447.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate447_coefficient3 :
    compactCertificate447.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate447_coefficient4 :
    compactCertificate447.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate447_coefficients : ∀ r : Fin 5,
    compactCertificate447.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate447_coefficient0
  · exact compactCertificate447_coefficient1
  · exact compactCertificate447_coefficient2
  · exact compactCertificate447_coefficient3
  · exact compactCertificate447_coefficient4

theorem compactCertificate447_lower : (1 : ℚ) ≤ compactCertificate447.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate447, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate447_proves {t : ℝ} (ht : t ∈ compactCertificate447.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate447.proves compactCertificate447_states compactCertificate447_chunks
    compactCertificate447_coefficients compactCertificate447_lower ht

end Erdos232
