/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate316 : CompactCertificate where
  left := 189
  right := 190
  center := 379 / 2
  grid := fun i =>
    match i.val with
    | 0 => 60
    | 1 => 44
    | 2 => 72
    | 3 => 13
    | 4 => 35
    | 5 => 95
    | 6 => 70
    | 7 => 119
    | 8 => 88
    | 9 => 135
    | 10 => 78
    | 11 => 138
    | 12 => 129
    | 13 => 92
    | 14 => 105
    | 15 => 87
    | 16 => 77
    | 17 => 112
    | 18 => 62
    | 19 => 52
    | 20 => 33
    | 21 => 18
    | 22 => 48
    | 23 => 65
    | 24 => 28
    | 25 => 112
    | _ => 75
  point := fun i =>
    match i.val with
    | 0 => 379 / 2
    | 1 => 558339369254479 / 4000000000000
    | 2 => 180555480210607 / 800000000000
    | 3 => 162922035430253 / 4000000000000
    | 4 => 437631504045641 / 4000000000000
    | 5 => 1188254664935397 / 4000000000000
    | 6 => 875263008091661 / 4000000000000
    | 7 => 1499778082745153 / 4000000000000
    | 8 => 1104729747679427 / 4000000000000
    | 9 => 1694939526944621 / 4000000000000
    | 10 => 978573792141509 / 4000000000000
    | 11 => 1736496366484681 / 4000000000000
    | 12 => 1622460157954189 / 4000000000000
    | 13 => 1157864125591837 / 4000000000000
    | 14 => 1312894512136923 / 4000000000000
    | 15 => 1094554568086187 / 4000000000000
    | 16 => 967072155413927 / 4000000000000
    | 17 => 280295204086773 / 800000000000
    | 18 => 775311285632431 / 4000000000000
    | 19 => 657239963167991 / 4000000000000
    | 20 => 411270252320573 / 4000000000000
    | 21 => 221182509521091 / 4000000000000
    | 22 => 600553539476273 / 4000000000000
    | 23 => 820004515253521 / 4000000000000
    | 24 => 346729747679427 / 4000000000000
    | 25 => 1409437174456867 / 4000000000000
    | _ => 941438713491053 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (56584218044 / 1000000000000) (56584219154 / 1000000000000), orderedInterval (-12706634787 / 1000000000000) (-12706633677 / 1000000000000))
    | 1 => (orderedInterval (56912161891 / 1000000000000) (56912193934 / 1000000000000), orderedInterval (-36560447786 / 1000000000000) (-36560415743 / 1000000000000))
    | 2 => (orderedInterval (14908084846 / 1000000000000) (14908084847 / 1000000000000), orderedInterval (50942175932 / 1000000000000) (50942175933 / 1000000000000))
    | 3 => (orderedInterval (-77841847755 / 1000000000000) (-77841847754 / 1000000000000), orderedInterval (-96875845797 / 1000000000000) (-96875845796 / 1000000000000))
    | 4 => (orderedInterval (-17864390125 / 1000000000000) (-17864390124 / 1000000000000), orderedInterval (-74078270647 / 1000000000000) (-74078270646 / 1000000000000))
    | 5 => (orderedInterval (26240451443 / 1000000000000) (26240456508 / 1000000000000), orderedInterval (-38181829641 / 1000000000000) (-38181824576 / 1000000000000))
    | 6 => (orderedInterval (-16501030273 / 1000000000000) (-16501030011 / 1000000000000), orderedInterval (51390499335 / 1000000000000) (51390499597 / 1000000000000))
    | 7 => (orderedInterval (-39250740016 / 1000000000000) (-39250731690 / 1000000000000), orderedInterval (12593566388 / 1000000000000) (12593574714 / 1000000000000))
    | 8 => (orderedInterval (23321727829 / 1000000000000) (23321727830 / 1000000000000), orderedInterval (41924059351 / 1000000000000) (41924059352 / 1000000000000))
    | 9 => (orderedInterval (-15271653691 / 1000000000000) (-15271653690 / 1000000000000), orderedInterval (-35607510771 / 1000000000000) (-35607510770 / 1000000000000))
    | 10 => (orderedInterval (19115876618 / 1000000000000) (19115876619 / 1000000000000), orderedInterval (47255986969 / 1000000000000) (47255986970 / 1000000000000))
    | 11 => (orderedInterval (37520323394 / 1000000000000) (37520323414 / 1000000000000), orderedInterval (7616484490 / 1000000000000) (7616484509 / 1000000000000))
    | 12 => (orderedInterval (-35908869915 / 1000000000000) (-35908869914 / 1000000000000), orderedInterval (-16691011660 / 1000000000000) (-16691011659 / 1000000000000))
    | 13 => (orderedInterval (44112178713 / 1000000000000) (44112178714 / 1000000000000), orderedInterval (15842449110 / 1000000000000) (15842449112 / 1000000000000))
    | 14 => (orderedInterval (33335200771 / 1000000000000) (33335251622 / 1000000000000), orderedInterval (-28831942945 / 1000000000000) (-28831892093 / 1000000000000))
    | 15 => (orderedInterval (-43095612059 / 1000000000000) (-43095612058 / 1000000000000), orderedInterval (-21583756341 / 1000000000000) (-21583756340 / 1000000000000))
    | 16 => (orderedInterval (-31066510077 / 1000000000000) (-31066510076 / 1000000000000), orderedInterval (-40777612852 / 1000000000000) (-40777612851 / 1000000000000))
    | 17 => (orderedInterval (-27601514242 / 1000000000000) (-27601503387 / 1000000000000), orderedInterval (32522532632 / 1000000000000) (32522543487 / 1000000000000))
    | 18 => (orderedInterval (-9479446932 / 1000000000000) (-9479446891 / 1000000000000), orderedInterval (56545339961 / 1000000000000) (56545340003 / 1000000000000))
    | 19 => (orderedInterval (61440243539 / 1000000000000) (61440244011 / 1000000000000), orderedInterval (-10166129584 / 1000000000000) (-10166129112 / 1000000000000))
    | 20 => (orderedInterval (5567340139 / 1000000000000) (5567340158 / 1000000000000), orderedInterval (-78517956119 / 1000000000000) (-78517956099 / 1000000000000))
    | 21 => (orderedInterval (-48583806421 / 1000000000000) (-48583801957 / 1000000000000), orderedInterval (96110131335 / 1000000000000) (96110135799 / 1000000000000))
    | 22 => (orderedInterval (8215523596 / 1000000000000) (8215523597 / 1000000000000), orderedInterval (64569450520 / 1000000000000) (64569450521 / 1000000000000))
    | 23 => (orderedInterval (-55722690508 / 1000000000000) (-55722690424 / 1000000000000), orderedInterval (782233554 / 1000000000000) (782233638 / 1000000000000))
    | 24 => (orderedInterval (-40950480053 / 1000000000000) (-40950474921 / 1000000000000), orderedInterval (75518342581 / 1000000000000) (75518347712 / 1000000000000))
    | 25 => (orderedInterval (40793025370 / 1000000000000) (40793025373 / 1000000000000), orderedInterval (11886246046 / 1000000000000) (11886246049 / 1000000000000))
    | _ => (orderedInterval (-26071628444 / 1000000000000) (-26071628443 / 1000000000000), orderedInterval (-44946319992 / 1000000000000) (-44946319991 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (23833137535 / 1000000000000) (23833138288 / 1000000000000)
      | 1 => orderedInterval (-1673155861 / 1000000000000) (-1673155477 / 1000000000000)
      | 2 => orderedInterval (1774289750 / 1000000000000) (1774290018 / 1000000000000)
      | 3 => orderedInterval (9463652626 / 1000000000000) (9463652705 / 1000000000000)
      | 4 => orderedInterval (4650944375 / 1000000000000) (4650944656 / 1000000000000)
      | 5 => orderedInterval (573471431 / 1000000000000) (573471728 / 1000000000000)
      | 6 => orderedInterval (-1780576953 / 1000000000000) (-1780576870 / 1000000000000)
      | 7 => orderedInterval (4981245153 / 1000000000000) (4981245265 / 1000000000000)
      | _ => orderedInterval (1324241391 / 1000000000000) (1324241476 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-1727095515 / 1000000000000) (-1727094840 / 1000000000000)
      | 1 => orderedInterval (2919367788 / 1000000000000) (2919368379 / 1000000000000)
      | 2 => orderedInterval (708137346 / 1000000000000) (708137874 / 1000000000000)
      | 3 => orderedInterval (21148203651 / 1000000000000) (21148203814 / 1000000000000)
      | 4 => orderedInterval (3186082552 / 1000000000000) (3186083036 / 1000000000000)
      | 5 => orderedInterval (4156906812 / 1000000000000) (4156907353 / 1000000000000)
      | 6 => orderedInterval (-10135651255 / 1000000000000) (-10135651180 / 1000000000000)
      | 7 => orderedInterval (-1743305972 / 1000000000000) (-1743305920 / 1000000000000)
      | _ => orderedInterval (8883111735 / 1000000000000) (8883111824 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-23947540927 / 1000000000000) (-23947540304 / 1000000000000)
      | 1 => orderedInterval (4747143173 / 1000000000000) (4747144098 / 1000000000000)
      | 2 => orderedInterval (-5940479146 / 1000000000000) (-5940478104 / 1000000000000)
      | 3 => orderedInterval (-44032532971 / 1000000000000) (-44032532621 / 1000000000000)
      | 4 => orderedInterval (-12213977122 / 1000000000000) (-12213976286 / 1000000000000)
      | 5 => orderedInterval (537797411 / 1000000000000) (537798404 / 1000000000000)
      | 6 => orderedInterval (1028855614 / 1000000000000) (1028855684 / 1000000000000)
      | 7 => orderedInterval (-4947946545 / 1000000000000) (-4947946509 / 1000000000000)
      | _ => orderedInterval (3939746186 / 1000000000000) (3939746303 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (248719009 / 1000000000000) (248719592 / 1000000000000)
      | 1 => orderedInterval (-9971325207 / 1000000000000) (-9971323761 / 1000000000000)
      | 2 => orderedInterval (-96478224 / 1000000000000) (-96476169 / 1000000000000)
      | 3 => orderedInterval (-91056567112 / 1000000000000) (-91056566346 / 1000000000000)
      | 4 => orderedInterval (-8988140974 / 1000000000000) (-8988139528 / 1000000000000)
      | 5 => orderedInterval (-9361422023 / 1000000000000) (-9361420200 / 1000000000000)
      | 6 => orderedInterval (9702361108 / 1000000000000) (9702361175 / 1000000000000)
      | 7 => orderedInterval (874584738 / 1000000000000) (874584770 / 1000000000000)
      | _ => orderedInterval (-10000719757 / 1000000000000) (-10000719583 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (24341044644 / 1000000000000) (24341045202 / 1000000000000)
      | 1 => orderedInterval (-11230503284 / 1000000000000) (-11230501012 / 1000000000000)
      | 2 => orderedInterval (21098386810 / 1000000000000) (21098390879 / 1000000000000)
      | 3 => orderedInterval (219643333144 / 1000000000000) (219643334852 / 1000000000000)
      | 4 => orderedInterval (34894392872 / 1000000000000) (34894395382 / 1000000000000)
      | 5 => orderedInterval (-5613175166 / 1000000000000) (-5613171804 / 1000000000000)
      | 6 => orderedInterval (-393260081 / 1000000000000) (-393260018 / 1000000000000)
      | 7 => orderedInterval (5772529011 / 1000000000000) (5772529043 / 1000000000000)
      | _ => orderedInterval (-27959221047 / 1000000000000) (-27959220772 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (43147249447 / 1000000000000) (43147251789 / 1000000000000)
    | 1 => orderedInterval (27395757142 / 1000000000000) (27395760340 / 1000000000000)
    | 2 => orderedInterval (-80828934327 / 1000000000000) (-80828929335 / 1000000000000)
    | 3 => orderedInterval (-118648988442 / 1000000000000) (-118648980050 / 1000000000000)
    | _ => orderedInterval (260553526903 / 1000000000000) (260553541752 / 1000000000000)

theorem compactCertificate316_stateChecks0 :
    compactCertificate316.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (379 / 2)) (orderedInterval (56584218044 / 1000000000000) (56584219154 / 1000000000000), orderedInterval (-12706634787 / 1000000000000) (-12706633677 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (558339369254479 / 4000000000000)) (orderedInterval (56912161891 / 1000000000000) (56912193934 / 1000000000000), orderedInterval (-36560447786 / 1000000000000) (-36560415743 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (180555480210607 / 800000000000)) (orderedInterval (14908084846 / 1000000000000) (14908084847 / 1000000000000), orderedInterval (50942175932 / 1000000000000) (50942175933 / 1000000000000))) = true
  rfl'

theorem compactCertificate316_stateChecks1 :
    compactCertificate316.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 13 12 (162922035430253 / 4000000000000)) (orderedInterval (-77841847755 / 1000000000000) (-77841847754 / 1000000000000), orderedInterval (-96875845797 / 1000000000000) (-96875845796 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (437631504045641 / 4000000000000)) (orderedInterval (-17864390125 / 1000000000000) (-17864390124 / 1000000000000), orderedInterval (-74078270647 / 1000000000000) (-74078270646 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 95 12 (1188254664935397 / 4000000000000)) (orderedInterval (26240451443 / 1000000000000) (26240456508 / 1000000000000), orderedInterval (-38181829641 / 1000000000000) (-38181824576 / 1000000000000))) = true
  rfl'

theorem compactCertificate316_stateChecks2 :
    compactCertificate316.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (875263008091661 / 4000000000000)) (orderedInterval (-16501030273 / 1000000000000) (-16501030011 / 1000000000000), orderedInterval (51390499335 / 1000000000000) (51390499597 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 119 12 (1499778082745153 / 4000000000000)) (orderedInterval (-39250740016 / 1000000000000) (-39250731690 / 1000000000000), orderedInterval (12593566388 / 1000000000000) (12593574714 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 88 12 (1104729747679427 / 4000000000000)) (orderedInterval (23321727829 / 1000000000000) (23321727830 / 1000000000000), orderedInterval (41924059351 / 1000000000000) (41924059352 / 1000000000000))) = true
  rfl'

theorem compactCertificate316_stateChecks3 :
    compactCertificate316.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 135 12 (1694939526944621 / 4000000000000)) (orderedInterval (-15271653691 / 1000000000000) (-15271653690 / 1000000000000), orderedInterval (-35607510771 / 1000000000000) (-35607510770 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (978573792141509 / 4000000000000)) (orderedInterval (19115876618 / 1000000000000) (19115876619 / 1000000000000), orderedInterval (47255986969 / 1000000000000) (47255986970 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 138 12 (1736496366484681 / 4000000000000)) (orderedInterval (37520323394 / 1000000000000) (37520323414 / 1000000000000), orderedInterval (7616484490 / 1000000000000) (7616484509 / 1000000000000))) = true
  rfl'

theorem compactCertificate316_stateChecks4 :
    compactCertificate316.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 129 12 (1622460157954189 / 4000000000000)) (orderedInterval (-35908869915 / 1000000000000) (-35908869914 / 1000000000000), orderedInterval (-16691011660 / 1000000000000) (-16691011659 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 92 12 (1157864125591837 / 4000000000000)) (orderedInterval (44112178713 / 1000000000000) (44112178714 / 1000000000000), orderedInterval (15842449110 / 1000000000000) (15842449112 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 105 12 (1312894512136923 / 4000000000000)) (orderedInterval (33335200771 / 1000000000000) (33335251622 / 1000000000000), orderedInterval (-28831942945 / 1000000000000) (-28831892093 / 1000000000000))) = true
  rfl'

theorem compactCertificate316_stateChecks5 :
    compactCertificate316.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (1094554568086187 / 4000000000000)) (orderedInterval (-43095612059 / 1000000000000) (-43095612058 / 1000000000000), orderedInterval (-21583756341 / 1000000000000) (-21583756340 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (967072155413927 / 4000000000000)) (orderedInterval (-31066510077 / 1000000000000) (-31066510076 / 1000000000000), orderedInterval (-40777612852 / 1000000000000) (-40777612851 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 112 12 (280295204086773 / 800000000000)) (orderedInterval (-27601514242 / 1000000000000) (-27601503387 / 1000000000000), orderedInterval (32522532632 / 1000000000000) (32522543487 / 1000000000000))) = true
  rfl'

theorem compactCertificate316_stateChecks6 :
    compactCertificate316.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (775311285632431 / 4000000000000)) (orderedInterval (-9479446932 / 1000000000000) (-9479446891 / 1000000000000), orderedInterval (56545339961 / 1000000000000) (56545340003 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (657239963167991 / 4000000000000)) (orderedInterval (61440243539 / 1000000000000) (61440244011 / 1000000000000), orderedInterval (-10166129584 / 1000000000000) (-10166129112 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (411270252320573 / 4000000000000)) (orderedInterval (5567340139 / 1000000000000) (5567340158 / 1000000000000), orderedInterval (-78517956119 / 1000000000000) (-78517956099 / 1000000000000))) = true
  rfl'

theorem compactCertificate316_stateChecks7 :
    compactCertificate316.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 18 12 (221182509521091 / 4000000000000)) (orderedInterval (-48583806421 / 1000000000000) (-48583801957 / 1000000000000), orderedInterval (96110131335 / 1000000000000) (96110135799 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (600553539476273 / 4000000000000)) (orderedInterval (8215523596 / 1000000000000) (8215523597 / 1000000000000), orderedInterval (64569450520 / 1000000000000) (64569450521 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (820004515253521 / 4000000000000)) (orderedInterval (-55722690508 / 1000000000000) (-55722690424 / 1000000000000), orderedInterval (782233554 / 1000000000000) (782233638 / 1000000000000))) = true
  rfl'

theorem compactCertificate316_stateChecks8 :
    compactCertificate316.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 28 12 (346729747679427 / 4000000000000)) (orderedInterval (-40950480053 / 1000000000000) (-40950474921 / 1000000000000), orderedInterval (75518342581 / 1000000000000) (75518347712 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 112 12 (1409437174456867 / 4000000000000)) (orderedInterval (40793025370 / 1000000000000) (40793025373 / 1000000000000), orderedInterval (11886246046 / 1000000000000) (11886246049 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (941438713491053 / 4000000000000)) (orderedInterval (-26071628444 / 1000000000000) (-26071628443 / 1000000000000), orderedInterval (-44946319992 / 1000000000000) (-44946319991 / 1000000000000))) = true
  rfl'

theorem compactCertificate316_states : ∀ j,
    BesselStateValid (compactCertificate316.point j) (compactCertificate316.state j) :=
  compactCertificate316.statesValid_of_checks3 compactCertificate316_stateChecks0
    compactCertificate316_stateChecks1 compactCertificate316_stateChecks2
    compactCertificate316_stateChecks3 compactCertificate316_stateChecks4
    compactCertificate316_stateChecks5 compactCertificate316_stateChecks6
    compactCertificate316_stateChecks7 compactCertificate316_stateChecks8

theorem compactCertificate316_chunkChecks0_0 :
    compactCertificate316.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (379 / 2) 0 (IntervalRat.scale (379 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (56584218044 / 1000000000000) (56584219154 / 1000000000000), orderedInterval (-12706634787 / 1000000000000) (-12706633677 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (558339369254479 / 4000000000000) 0 (IntervalRat.scale (379 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (56912161891 / 1000000000000) (56912193934 / 1000000000000), orderedInterval (-36560447786 / 1000000000000) (-36560415743 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (180555480210607 / 800000000000) 0 (IntervalRat.scale (379 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (14908084846 / 1000000000000) (14908084847 / 1000000000000), orderedInterval (50942175932 / 1000000000000) (50942175933 / 1000000000000)))) (orderedInterval (23833137535 / 1000000000000) (23833138288 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (162922035430253 / 4000000000000) 0 (IntervalRat.scale (379 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-77841847755 / 1000000000000) (-77841847754 / 1000000000000), orderedInterval (-96875845797 / 1000000000000) (-96875845796 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (437631504045641 / 4000000000000) 0 (IntervalRat.scale (379 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-17864390125 / 1000000000000) (-17864390124 / 1000000000000), orderedInterval (-74078270647 / 1000000000000) (-74078270646 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1188254664935397 / 4000000000000) 0 (IntervalRat.scale (379 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (26240451443 / 1000000000000) (26240456508 / 1000000000000), orderedInterval (-38181829641 / 1000000000000) (-38181824576 / 1000000000000)))) (orderedInterval (-1673155861 / 1000000000000) (-1673155477 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (875263008091661 / 4000000000000) 0 (IntervalRat.scale (379 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-16501030273 / 1000000000000) (-16501030011 / 1000000000000), orderedInterval (51390499335 / 1000000000000) (51390499597 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1499778082745153 / 4000000000000) 0 (IntervalRat.scale (379 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-39250740016 / 1000000000000) (-39250731690 / 1000000000000), orderedInterval (12593566388 / 1000000000000) (12593574714 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1104729747679427 / 4000000000000) 0 (IntervalRat.scale (379 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (23321727829 / 1000000000000) (23321727830 / 1000000000000), orderedInterval (41924059351 / 1000000000000) (41924059352 / 1000000000000)))) (orderedInterval (1774289750 / 1000000000000) (1774290018 / 1000000000000))) = true
  rfl'

theorem compactCertificate316_chunkChecks0_1 :
    compactCertificate316.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1694939526944621 / 4000000000000) 0 (IntervalRat.scale (379 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-15271653691 / 1000000000000) (-15271653690 / 1000000000000), orderedInterval (-35607510771 / 1000000000000) (-35607510770 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (978573792141509 / 4000000000000) 0 (IntervalRat.scale (379 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (19115876618 / 1000000000000) (19115876619 / 1000000000000), orderedInterval (47255986969 / 1000000000000) (47255986970 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1736496366484681 / 4000000000000) 0 (IntervalRat.scale (379 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (37520323394 / 1000000000000) (37520323414 / 1000000000000), orderedInterval (7616484490 / 1000000000000) (7616484509 / 1000000000000)))) (orderedInterval (9463652626 / 1000000000000) (9463652705 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1622460157954189 / 4000000000000) 0 (IntervalRat.scale (379 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-35908869915 / 1000000000000) (-35908869914 / 1000000000000), orderedInterval (-16691011660 / 1000000000000) (-16691011659 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1157864125591837 / 4000000000000) 0 (IntervalRat.scale (379 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (44112178713 / 1000000000000) (44112178714 / 1000000000000), orderedInterval (15842449110 / 1000000000000) (15842449112 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1312894512136923 / 4000000000000) 0 (IntervalRat.scale (379 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (33335200771 / 1000000000000) (33335251622 / 1000000000000), orderedInterval (-28831942945 / 1000000000000) (-28831892093 / 1000000000000)))) (orderedInterval (4650944375 / 1000000000000) (4650944656 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1094554568086187 / 4000000000000) 0 (IntervalRat.scale (379 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-43095612059 / 1000000000000) (-43095612058 / 1000000000000), orderedInterval (-21583756341 / 1000000000000) (-21583756340 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (967072155413927 / 4000000000000) 0 (IntervalRat.scale (379 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-31066510077 / 1000000000000) (-31066510076 / 1000000000000), orderedInterval (-40777612852 / 1000000000000) (-40777612851 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (280295204086773 / 800000000000) 0 (IntervalRat.scale (379 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-27601514242 / 1000000000000) (-27601503387 / 1000000000000), orderedInterval (32522532632 / 1000000000000) (32522543487 / 1000000000000)))) (orderedInterval (573471431 / 1000000000000) (573471728 / 1000000000000))) = true
  rfl'

theorem compactCertificate316_chunkChecks0_2 :
    compactCertificate316.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (775311285632431 / 4000000000000) 0 (IntervalRat.scale (379 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-9479446932 / 1000000000000) (-9479446891 / 1000000000000), orderedInterval (56545339961 / 1000000000000) (56545340003 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (657239963167991 / 4000000000000) 0 (IntervalRat.scale (379 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (61440243539 / 1000000000000) (61440244011 / 1000000000000), orderedInterval (-10166129584 / 1000000000000) (-10166129112 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (411270252320573 / 4000000000000) 0 (IntervalRat.scale (379 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (5567340139 / 1000000000000) (5567340158 / 1000000000000), orderedInterval (-78517956119 / 1000000000000) (-78517956099 / 1000000000000)))) (orderedInterval (-1780576953 / 1000000000000) (-1780576870 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (221182509521091 / 4000000000000) 0 (IntervalRat.scale (379 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-48583806421 / 1000000000000) (-48583801957 / 1000000000000), orderedInterval (96110131335 / 1000000000000) (96110135799 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (600553539476273 / 4000000000000) 0 (IntervalRat.scale (379 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (8215523596 / 1000000000000) (8215523597 / 1000000000000), orderedInterval (64569450520 / 1000000000000) (64569450521 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (820004515253521 / 4000000000000) 0 (IntervalRat.scale (379 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-55722690508 / 1000000000000) (-55722690424 / 1000000000000), orderedInterval (782233554 / 1000000000000) (782233638 / 1000000000000)))) (orderedInterval (4981245153 / 1000000000000) (4981245265 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (346729747679427 / 4000000000000) 0 (IntervalRat.scale (379 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-40950480053 / 1000000000000) (-40950474921 / 1000000000000), orderedInterval (75518342581 / 1000000000000) (75518347712 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1409437174456867 / 4000000000000) 0 (IntervalRat.scale (379 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (40793025370 / 1000000000000) (40793025373 / 1000000000000), orderedInterval (11886246046 / 1000000000000) (11886246049 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (941438713491053 / 4000000000000) 0 (IntervalRat.scale (379 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-26071628444 / 1000000000000) (-26071628443 / 1000000000000), orderedInterval (-44946319992 / 1000000000000) (-44946319991 / 1000000000000)))) (orderedInterval (1324241391 / 1000000000000) (1324241476 / 1000000000000))) = true
  rfl'

theorem compactCertificate316_chunkChecks0 :
    compactCertificate316.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate316.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate316_chunkChecks0_0
    compactCertificate316_chunkChecks0_1 compactCertificate316_chunkChecks0_2

theorem compactCertificate316_chunkChecks1_0 :
    compactCertificate316.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (379 / 2) 1 (IntervalRat.scale (379 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (56584218044 / 1000000000000) (56584219154 / 1000000000000), orderedInterval (-12706634787 / 1000000000000) (-12706633677 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (558339369254479 / 4000000000000) 1 (IntervalRat.scale (379 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (56912161891 / 1000000000000) (56912193934 / 1000000000000), orderedInterval (-36560447786 / 1000000000000) (-36560415743 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (180555480210607 / 800000000000) 1 (IntervalRat.scale (379 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (14908084846 / 1000000000000) (14908084847 / 1000000000000), orderedInterval (50942175932 / 1000000000000) (50942175933 / 1000000000000)))) (orderedInterval (-1727095515 / 1000000000000) (-1727094840 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (162922035430253 / 4000000000000) 1 (IntervalRat.scale (379 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-77841847755 / 1000000000000) (-77841847754 / 1000000000000), orderedInterval (-96875845797 / 1000000000000) (-96875845796 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (437631504045641 / 4000000000000) 1 (IntervalRat.scale (379 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-17864390125 / 1000000000000) (-17864390124 / 1000000000000), orderedInterval (-74078270647 / 1000000000000) (-74078270646 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1188254664935397 / 4000000000000) 1 (IntervalRat.scale (379 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (26240451443 / 1000000000000) (26240456508 / 1000000000000), orderedInterval (-38181829641 / 1000000000000) (-38181824576 / 1000000000000)))) (orderedInterval (2919367788 / 1000000000000) (2919368379 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (875263008091661 / 4000000000000) 1 (IntervalRat.scale (379 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-16501030273 / 1000000000000) (-16501030011 / 1000000000000), orderedInterval (51390499335 / 1000000000000) (51390499597 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1499778082745153 / 4000000000000) 1 (IntervalRat.scale (379 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-39250740016 / 1000000000000) (-39250731690 / 1000000000000), orderedInterval (12593566388 / 1000000000000) (12593574714 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1104729747679427 / 4000000000000) 1 (IntervalRat.scale (379 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (23321727829 / 1000000000000) (23321727830 / 1000000000000), orderedInterval (41924059351 / 1000000000000) (41924059352 / 1000000000000)))) (orderedInterval (708137346 / 1000000000000) (708137874 / 1000000000000))) = true
  rfl'

theorem compactCertificate316_chunkChecks1_1 :
    compactCertificate316.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1694939526944621 / 4000000000000) 1 (IntervalRat.scale (379 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-15271653691 / 1000000000000) (-15271653690 / 1000000000000), orderedInterval (-35607510771 / 1000000000000) (-35607510770 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (978573792141509 / 4000000000000) 1 (IntervalRat.scale (379 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (19115876618 / 1000000000000) (19115876619 / 1000000000000), orderedInterval (47255986969 / 1000000000000) (47255986970 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1736496366484681 / 4000000000000) 1 (IntervalRat.scale (379 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (37520323394 / 1000000000000) (37520323414 / 1000000000000), orderedInterval (7616484490 / 1000000000000) (7616484509 / 1000000000000)))) (orderedInterval (21148203651 / 1000000000000) (21148203814 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1622460157954189 / 4000000000000) 1 (IntervalRat.scale (379 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-35908869915 / 1000000000000) (-35908869914 / 1000000000000), orderedInterval (-16691011660 / 1000000000000) (-16691011659 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1157864125591837 / 4000000000000) 1 (IntervalRat.scale (379 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (44112178713 / 1000000000000) (44112178714 / 1000000000000), orderedInterval (15842449110 / 1000000000000) (15842449112 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1312894512136923 / 4000000000000) 1 (IntervalRat.scale (379 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (33335200771 / 1000000000000) (33335251622 / 1000000000000), orderedInterval (-28831942945 / 1000000000000) (-28831892093 / 1000000000000)))) (orderedInterval (3186082552 / 1000000000000) (3186083036 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1094554568086187 / 4000000000000) 1 (IntervalRat.scale (379 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-43095612059 / 1000000000000) (-43095612058 / 1000000000000), orderedInterval (-21583756341 / 1000000000000) (-21583756340 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (967072155413927 / 4000000000000) 1 (IntervalRat.scale (379 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-31066510077 / 1000000000000) (-31066510076 / 1000000000000), orderedInterval (-40777612852 / 1000000000000) (-40777612851 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (280295204086773 / 800000000000) 1 (IntervalRat.scale (379 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-27601514242 / 1000000000000) (-27601503387 / 1000000000000), orderedInterval (32522532632 / 1000000000000) (32522543487 / 1000000000000)))) (orderedInterval (4156906812 / 1000000000000) (4156907353 / 1000000000000))) = true
  rfl'

theorem compactCertificate316_chunkChecks1_2 :
    compactCertificate316.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (775311285632431 / 4000000000000) 1 (IntervalRat.scale (379 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-9479446932 / 1000000000000) (-9479446891 / 1000000000000), orderedInterval (56545339961 / 1000000000000) (56545340003 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (657239963167991 / 4000000000000) 1 (IntervalRat.scale (379 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (61440243539 / 1000000000000) (61440244011 / 1000000000000), orderedInterval (-10166129584 / 1000000000000) (-10166129112 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (411270252320573 / 4000000000000) 1 (IntervalRat.scale (379 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (5567340139 / 1000000000000) (5567340158 / 1000000000000), orderedInterval (-78517956119 / 1000000000000) (-78517956099 / 1000000000000)))) (orderedInterval (-10135651255 / 1000000000000) (-10135651180 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (221182509521091 / 4000000000000) 1 (IntervalRat.scale (379 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-48583806421 / 1000000000000) (-48583801957 / 1000000000000), orderedInterval (96110131335 / 1000000000000) (96110135799 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (600553539476273 / 4000000000000) 1 (IntervalRat.scale (379 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (8215523596 / 1000000000000) (8215523597 / 1000000000000), orderedInterval (64569450520 / 1000000000000) (64569450521 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (820004515253521 / 4000000000000) 1 (IntervalRat.scale (379 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-55722690508 / 1000000000000) (-55722690424 / 1000000000000), orderedInterval (782233554 / 1000000000000) (782233638 / 1000000000000)))) (orderedInterval (-1743305972 / 1000000000000) (-1743305920 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (346729747679427 / 4000000000000) 1 (IntervalRat.scale (379 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-40950480053 / 1000000000000) (-40950474921 / 1000000000000), orderedInterval (75518342581 / 1000000000000) (75518347712 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1409437174456867 / 4000000000000) 1 (IntervalRat.scale (379 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (40793025370 / 1000000000000) (40793025373 / 1000000000000), orderedInterval (11886246046 / 1000000000000) (11886246049 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (941438713491053 / 4000000000000) 1 (IntervalRat.scale (379 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-26071628444 / 1000000000000) (-26071628443 / 1000000000000), orderedInterval (-44946319992 / 1000000000000) (-44946319991 / 1000000000000)))) (orderedInterval (8883111735 / 1000000000000) (8883111824 / 1000000000000))) = true
  rfl'

theorem compactCertificate316_chunkChecks1 :
    compactCertificate316.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate316.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate316_chunkChecks1_0
    compactCertificate316_chunkChecks1_1 compactCertificate316_chunkChecks1_2

theorem compactCertificate316_chunkChecks2_0 :
    compactCertificate316.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (379 / 2) 2 (IntervalRat.scale (379 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (56584218044 / 1000000000000) (56584219154 / 1000000000000), orderedInterval (-12706634787 / 1000000000000) (-12706633677 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (558339369254479 / 4000000000000) 2 (IntervalRat.scale (379 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (56912161891 / 1000000000000) (56912193934 / 1000000000000), orderedInterval (-36560447786 / 1000000000000) (-36560415743 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (180555480210607 / 800000000000) 2 (IntervalRat.scale (379 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (14908084846 / 1000000000000) (14908084847 / 1000000000000), orderedInterval (50942175932 / 1000000000000) (50942175933 / 1000000000000)))) (orderedInterval (-23947540927 / 1000000000000) (-23947540304 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (162922035430253 / 4000000000000) 2 (IntervalRat.scale (379 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-77841847755 / 1000000000000) (-77841847754 / 1000000000000), orderedInterval (-96875845797 / 1000000000000) (-96875845796 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (437631504045641 / 4000000000000) 2 (IntervalRat.scale (379 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-17864390125 / 1000000000000) (-17864390124 / 1000000000000), orderedInterval (-74078270647 / 1000000000000) (-74078270646 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1188254664935397 / 4000000000000) 2 (IntervalRat.scale (379 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (26240451443 / 1000000000000) (26240456508 / 1000000000000), orderedInterval (-38181829641 / 1000000000000) (-38181824576 / 1000000000000)))) (orderedInterval (4747143173 / 1000000000000) (4747144098 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (875263008091661 / 4000000000000) 2 (IntervalRat.scale (379 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-16501030273 / 1000000000000) (-16501030011 / 1000000000000), orderedInterval (51390499335 / 1000000000000) (51390499597 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1499778082745153 / 4000000000000) 2 (IntervalRat.scale (379 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-39250740016 / 1000000000000) (-39250731690 / 1000000000000), orderedInterval (12593566388 / 1000000000000) (12593574714 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1104729747679427 / 4000000000000) 2 (IntervalRat.scale (379 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (23321727829 / 1000000000000) (23321727830 / 1000000000000), orderedInterval (41924059351 / 1000000000000) (41924059352 / 1000000000000)))) (orderedInterval (-5940479146 / 1000000000000) (-5940478104 / 1000000000000))) = true
  rfl'

theorem compactCertificate316_chunkChecks2_1 :
    compactCertificate316.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1694939526944621 / 4000000000000) 2 (IntervalRat.scale (379 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-15271653691 / 1000000000000) (-15271653690 / 1000000000000), orderedInterval (-35607510771 / 1000000000000) (-35607510770 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (978573792141509 / 4000000000000) 2 (IntervalRat.scale (379 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (19115876618 / 1000000000000) (19115876619 / 1000000000000), orderedInterval (47255986969 / 1000000000000) (47255986970 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1736496366484681 / 4000000000000) 2 (IntervalRat.scale (379 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (37520323394 / 1000000000000) (37520323414 / 1000000000000), orderedInterval (7616484490 / 1000000000000) (7616484509 / 1000000000000)))) (orderedInterval (-44032532971 / 1000000000000) (-44032532621 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1622460157954189 / 4000000000000) 2 (IntervalRat.scale (379 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-35908869915 / 1000000000000) (-35908869914 / 1000000000000), orderedInterval (-16691011660 / 1000000000000) (-16691011659 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1157864125591837 / 4000000000000) 2 (IntervalRat.scale (379 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (44112178713 / 1000000000000) (44112178714 / 1000000000000), orderedInterval (15842449110 / 1000000000000) (15842449112 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1312894512136923 / 4000000000000) 2 (IntervalRat.scale (379 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (33335200771 / 1000000000000) (33335251622 / 1000000000000), orderedInterval (-28831942945 / 1000000000000) (-28831892093 / 1000000000000)))) (orderedInterval (-12213977122 / 1000000000000) (-12213976286 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1094554568086187 / 4000000000000) 2 (IntervalRat.scale (379 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-43095612059 / 1000000000000) (-43095612058 / 1000000000000), orderedInterval (-21583756341 / 1000000000000) (-21583756340 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (967072155413927 / 4000000000000) 2 (IntervalRat.scale (379 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-31066510077 / 1000000000000) (-31066510076 / 1000000000000), orderedInterval (-40777612852 / 1000000000000) (-40777612851 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (280295204086773 / 800000000000) 2 (IntervalRat.scale (379 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-27601514242 / 1000000000000) (-27601503387 / 1000000000000), orderedInterval (32522532632 / 1000000000000) (32522543487 / 1000000000000)))) (orderedInterval (537797411 / 1000000000000) (537798404 / 1000000000000))) = true
  rfl'

theorem compactCertificate316_chunkChecks2_2 :
    compactCertificate316.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (775311285632431 / 4000000000000) 2 (IntervalRat.scale (379 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-9479446932 / 1000000000000) (-9479446891 / 1000000000000), orderedInterval (56545339961 / 1000000000000) (56545340003 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (657239963167991 / 4000000000000) 2 (IntervalRat.scale (379 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (61440243539 / 1000000000000) (61440244011 / 1000000000000), orderedInterval (-10166129584 / 1000000000000) (-10166129112 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (411270252320573 / 4000000000000) 2 (IntervalRat.scale (379 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (5567340139 / 1000000000000) (5567340158 / 1000000000000), orderedInterval (-78517956119 / 1000000000000) (-78517956099 / 1000000000000)))) (orderedInterval (1028855614 / 1000000000000) (1028855684 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (221182509521091 / 4000000000000) 2 (IntervalRat.scale (379 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-48583806421 / 1000000000000) (-48583801957 / 1000000000000), orderedInterval (96110131335 / 1000000000000) (96110135799 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (600553539476273 / 4000000000000) 2 (IntervalRat.scale (379 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (8215523596 / 1000000000000) (8215523597 / 1000000000000), orderedInterval (64569450520 / 1000000000000) (64569450521 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (820004515253521 / 4000000000000) 2 (IntervalRat.scale (379 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-55722690508 / 1000000000000) (-55722690424 / 1000000000000), orderedInterval (782233554 / 1000000000000) (782233638 / 1000000000000)))) (orderedInterval (-4947946545 / 1000000000000) (-4947946509 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (346729747679427 / 4000000000000) 2 (IntervalRat.scale (379 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-40950480053 / 1000000000000) (-40950474921 / 1000000000000), orderedInterval (75518342581 / 1000000000000) (75518347712 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1409437174456867 / 4000000000000) 2 (IntervalRat.scale (379 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (40793025370 / 1000000000000) (40793025373 / 1000000000000), orderedInterval (11886246046 / 1000000000000) (11886246049 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (941438713491053 / 4000000000000) 2 (IntervalRat.scale (379 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-26071628444 / 1000000000000) (-26071628443 / 1000000000000), orderedInterval (-44946319992 / 1000000000000) (-44946319991 / 1000000000000)))) (orderedInterval (3939746186 / 1000000000000) (3939746303 / 1000000000000))) = true
  rfl'

theorem compactCertificate316_chunkChecks2 :
    compactCertificate316.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate316.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate316_chunkChecks2_0
    compactCertificate316_chunkChecks2_1 compactCertificate316_chunkChecks2_2

theorem compactCertificate316_chunkChecks3_0 :
    compactCertificate316.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (379 / 2) 3 (IntervalRat.scale (379 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (56584218044 / 1000000000000) (56584219154 / 1000000000000), orderedInterval (-12706634787 / 1000000000000) (-12706633677 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (558339369254479 / 4000000000000) 3 (IntervalRat.scale (379 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (56912161891 / 1000000000000) (56912193934 / 1000000000000), orderedInterval (-36560447786 / 1000000000000) (-36560415743 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (180555480210607 / 800000000000) 3 (IntervalRat.scale (379 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (14908084846 / 1000000000000) (14908084847 / 1000000000000), orderedInterval (50942175932 / 1000000000000) (50942175933 / 1000000000000)))) (orderedInterval (248719009 / 1000000000000) (248719592 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (162922035430253 / 4000000000000) 3 (IntervalRat.scale (379 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-77841847755 / 1000000000000) (-77841847754 / 1000000000000), orderedInterval (-96875845797 / 1000000000000) (-96875845796 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (437631504045641 / 4000000000000) 3 (IntervalRat.scale (379 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-17864390125 / 1000000000000) (-17864390124 / 1000000000000), orderedInterval (-74078270647 / 1000000000000) (-74078270646 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1188254664935397 / 4000000000000) 3 (IntervalRat.scale (379 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (26240451443 / 1000000000000) (26240456508 / 1000000000000), orderedInterval (-38181829641 / 1000000000000) (-38181824576 / 1000000000000)))) (orderedInterval (-9971325207 / 1000000000000) (-9971323761 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (875263008091661 / 4000000000000) 3 (IntervalRat.scale (379 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-16501030273 / 1000000000000) (-16501030011 / 1000000000000), orderedInterval (51390499335 / 1000000000000) (51390499597 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1499778082745153 / 4000000000000) 3 (IntervalRat.scale (379 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-39250740016 / 1000000000000) (-39250731690 / 1000000000000), orderedInterval (12593566388 / 1000000000000) (12593574714 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1104729747679427 / 4000000000000) 3 (IntervalRat.scale (379 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (23321727829 / 1000000000000) (23321727830 / 1000000000000), orderedInterval (41924059351 / 1000000000000) (41924059352 / 1000000000000)))) (orderedInterval (-96478224 / 1000000000000) (-96476169 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate316_chunkChecks3_1 :
    compactCertificate316.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1694939526944621 / 4000000000000) 3 (IntervalRat.scale (379 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-15271653691 / 1000000000000) (-15271653690 / 1000000000000), orderedInterval (-35607510771 / 1000000000000) (-35607510770 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (978573792141509 / 4000000000000) 3 (IntervalRat.scale (379 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (19115876618 / 1000000000000) (19115876619 / 1000000000000), orderedInterval (47255986969 / 1000000000000) (47255986970 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1736496366484681 / 4000000000000) 3 (IntervalRat.scale (379 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (37520323394 / 1000000000000) (37520323414 / 1000000000000), orderedInterval (7616484490 / 1000000000000) (7616484509 / 1000000000000)))) (orderedInterval (-91056567112 / 1000000000000) (-91056566346 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1622460157954189 / 4000000000000) 3 (IntervalRat.scale (379 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-35908869915 / 1000000000000) (-35908869914 / 1000000000000), orderedInterval (-16691011660 / 1000000000000) (-16691011659 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1157864125591837 / 4000000000000) 3 (IntervalRat.scale (379 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (44112178713 / 1000000000000) (44112178714 / 1000000000000), orderedInterval (15842449110 / 1000000000000) (15842449112 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1312894512136923 / 4000000000000) 3 (IntervalRat.scale (379 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (33335200771 / 1000000000000) (33335251622 / 1000000000000), orderedInterval (-28831942945 / 1000000000000) (-28831892093 / 1000000000000)))) (orderedInterval (-8988140974 / 1000000000000) (-8988139528 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1094554568086187 / 4000000000000) 3 (IntervalRat.scale (379 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-43095612059 / 1000000000000) (-43095612058 / 1000000000000), orderedInterval (-21583756341 / 1000000000000) (-21583756340 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (967072155413927 / 4000000000000) 3 (IntervalRat.scale (379 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-31066510077 / 1000000000000) (-31066510076 / 1000000000000), orderedInterval (-40777612852 / 1000000000000) (-40777612851 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (280295204086773 / 800000000000) 3 (IntervalRat.scale (379 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-27601514242 / 1000000000000) (-27601503387 / 1000000000000), orderedInterval (32522532632 / 1000000000000) (32522543487 / 1000000000000)))) (orderedInterval (-9361422023 / 1000000000000) (-9361420200 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate316_chunkChecks3_2 :
    compactCertificate316.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (775311285632431 / 4000000000000) 3 (IntervalRat.scale (379 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-9479446932 / 1000000000000) (-9479446891 / 1000000000000), orderedInterval (56545339961 / 1000000000000) (56545340003 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (657239963167991 / 4000000000000) 3 (IntervalRat.scale (379 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (61440243539 / 1000000000000) (61440244011 / 1000000000000), orderedInterval (-10166129584 / 1000000000000) (-10166129112 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (411270252320573 / 4000000000000) 3 (IntervalRat.scale (379 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (5567340139 / 1000000000000) (5567340158 / 1000000000000), orderedInterval (-78517956119 / 1000000000000) (-78517956099 / 1000000000000)))) (orderedInterval (9702361108 / 1000000000000) (9702361175 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (221182509521091 / 4000000000000) 3 (IntervalRat.scale (379 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-48583806421 / 1000000000000) (-48583801957 / 1000000000000), orderedInterval (96110131335 / 1000000000000) (96110135799 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (600553539476273 / 4000000000000) 3 (IntervalRat.scale (379 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (8215523596 / 1000000000000) (8215523597 / 1000000000000), orderedInterval (64569450520 / 1000000000000) (64569450521 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (820004515253521 / 4000000000000) 3 (IntervalRat.scale (379 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-55722690508 / 1000000000000) (-55722690424 / 1000000000000), orderedInterval (782233554 / 1000000000000) (782233638 / 1000000000000)))) (orderedInterval (874584738 / 1000000000000) (874584770 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (346729747679427 / 4000000000000) 3 (IntervalRat.scale (379 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-40950480053 / 1000000000000) (-40950474921 / 1000000000000), orderedInterval (75518342581 / 1000000000000) (75518347712 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1409437174456867 / 4000000000000) 3 (IntervalRat.scale (379 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (40793025370 / 1000000000000) (40793025373 / 1000000000000), orderedInterval (11886246046 / 1000000000000) (11886246049 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (941438713491053 / 4000000000000) 3 (IntervalRat.scale (379 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-26071628444 / 1000000000000) (-26071628443 / 1000000000000), orderedInterval (-44946319992 / 1000000000000) (-44946319991 / 1000000000000)))) (orderedInterval (-10000719757 / 1000000000000) (-10000719583 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate316_chunkChecks3 :
    compactCertificate316.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate316.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate316_chunkChecks3_0
    compactCertificate316_chunkChecks3_1 compactCertificate316_chunkChecks3_2

theorem compactCertificate316_chunkChecks4_0 :
    compactCertificate316.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (379 / 2) 4 (IntervalRat.scale (379 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (56584218044 / 1000000000000) (56584219154 / 1000000000000), orderedInterval (-12706634787 / 1000000000000) (-12706633677 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (558339369254479 / 4000000000000) 4 (IntervalRat.scale (379 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (56912161891 / 1000000000000) (56912193934 / 1000000000000), orderedInterval (-36560447786 / 1000000000000) (-36560415743 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (180555480210607 / 800000000000) 4 (IntervalRat.scale (379 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (14908084846 / 1000000000000) (14908084847 / 1000000000000), orderedInterval (50942175932 / 1000000000000) (50942175933 / 1000000000000)))) (orderedInterval (24341044644 / 1000000000000) (24341045202 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (162922035430253 / 4000000000000) 4 (IntervalRat.scale (379 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-77841847755 / 1000000000000) (-77841847754 / 1000000000000), orderedInterval (-96875845797 / 1000000000000) (-96875845796 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (437631504045641 / 4000000000000) 4 (IntervalRat.scale (379 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-17864390125 / 1000000000000) (-17864390124 / 1000000000000), orderedInterval (-74078270647 / 1000000000000) (-74078270646 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1188254664935397 / 4000000000000) 4 (IntervalRat.scale (379 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (26240451443 / 1000000000000) (26240456508 / 1000000000000), orderedInterval (-38181829641 / 1000000000000) (-38181824576 / 1000000000000)))) (orderedInterval (-11230503284 / 1000000000000) (-11230501012 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (875263008091661 / 4000000000000) 4 (IntervalRat.scale (379 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-16501030273 / 1000000000000) (-16501030011 / 1000000000000), orderedInterval (51390499335 / 1000000000000) (51390499597 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1499778082745153 / 4000000000000) 4 (IntervalRat.scale (379 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-39250740016 / 1000000000000) (-39250731690 / 1000000000000), orderedInterval (12593566388 / 1000000000000) (12593574714 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1104729747679427 / 4000000000000) 4 (IntervalRat.scale (379 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (23321727829 / 1000000000000) (23321727830 / 1000000000000), orderedInterval (41924059351 / 1000000000000) (41924059352 / 1000000000000)))) (orderedInterval (21098386810 / 1000000000000) (21098390879 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate316_chunkChecks4_1 :
    compactCertificate316.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1694939526944621 / 4000000000000) 4 (IntervalRat.scale (379 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-15271653691 / 1000000000000) (-15271653690 / 1000000000000), orderedInterval (-35607510771 / 1000000000000) (-35607510770 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (978573792141509 / 4000000000000) 4 (IntervalRat.scale (379 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (19115876618 / 1000000000000) (19115876619 / 1000000000000), orderedInterval (47255986969 / 1000000000000) (47255986970 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1736496366484681 / 4000000000000) 4 (IntervalRat.scale (379 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (37520323394 / 1000000000000) (37520323414 / 1000000000000), orderedInterval (7616484490 / 1000000000000) (7616484509 / 1000000000000)))) (orderedInterval (219643333144 / 1000000000000) (219643334852 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1622460157954189 / 4000000000000) 4 (IntervalRat.scale (379 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-35908869915 / 1000000000000) (-35908869914 / 1000000000000), orderedInterval (-16691011660 / 1000000000000) (-16691011659 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1157864125591837 / 4000000000000) 4 (IntervalRat.scale (379 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (44112178713 / 1000000000000) (44112178714 / 1000000000000), orderedInterval (15842449110 / 1000000000000) (15842449112 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1312894512136923 / 4000000000000) 4 (IntervalRat.scale (379 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (33335200771 / 1000000000000) (33335251622 / 1000000000000), orderedInterval (-28831942945 / 1000000000000) (-28831892093 / 1000000000000)))) (orderedInterval (34894392872 / 1000000000000) (34894395382 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1094554568086187 / 4000000000000) 4 (IntervalRat.scale (379 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-43095612059 / 1000000000000) (-43095612058 / 1000000000000), orderedInterval (-21583756341 / 1000000000000) (-21583756340 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (967072155413927 / 4000000000000) 4 (IntervalRat.scale (379 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-31066510077 / 1000000000000) (-31066510076 / 1000000000000), orderedInterval (-40777612852 / 1000000000000) (-40777612851 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (280295204086773 / 800000000000) 4 (IntervalRat.scale (379 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-27601514242 / 1000000000000) (-27601503387 / 1000000000000), orderedInterval (32522532632 / 1000000000000) (32522543487 / 1000000000000)))) (orderedInterval (-5613175166 / 1000000000000) (-5613171804 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate316_chunkChecks4_2 :
    compactCertificate316.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (775311285632431 / 4000000000000) 4 (IntervalRat.scale (379 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-9479446932 / 1000000000000) (-9479446891 / 1000000000000), orderedInterval (56545339961 / 1000000000000) (56545340003 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (657239963167991 / 4000000000000) 4 (IntervalRat.scale (379 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (61440243539 / 1000000000000) (61440244011 / 1000000000000), orderedInterval (-10166129584 / 1000000000000) (-10166129112 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (411270252320573 / 4000000000000) 4 (IntervalRat.scale (379 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (5567340139 / 1000000000000) (5567340158 / 1000000000000), orderedInterval (-78517956119 / 1000000000000) (-78517956099 / 1000000000000)))) (orderedInterval (-393260081 / 1000000000000) (-393260018 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (221182509521091 / 4000000000000) 4 (IntervalRat.scale (379 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-48583806421 / 1000000000000) (-48583801957 / 1000000000000), orderedInterval (96110131335 / 1000000000000) (96110135799 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (600553539476273 / 4000000000000) 4 (IntervalRat.scale (379 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (8215523596 / 1000000000000) (8215523597 / 1000000000000), orderedInterval (64569450520 / 1000000000000) (64569450521 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (820004515253521 / 4000000000000) 4 (IntervalRat.scale (379 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-55722690508 / 1000000000000) (-55722690424 / 1000000000000), orderedInterval (782233554 / 1000000000000) (782233638 / 1000000000000)))) (orderedInterval (5772529011 / 1000000000000) (5772529043 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (346729747679427 / 4000000000000) 4 (IntervalRat.scale (379 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-40950480053 / 1000000000000) (-40950474921 / 1000000000000), orderedInterval (75518342581 / 1000000000000) (75518347712 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1409437174456867 / 4000000000000) 4 (IntervalRat.scale (379 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (40793025370 / 1000000000000) (40793025373 / 1000000000000), orderedInterval (11886246046 / 1000000000000) (11886246049 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (941438713491053 / 4000000000000) 4 (IntervalRat.scale (379 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-26071628444 / 1000000000000) (-26071628443 / 1000000000000), orderedInterval (-44946319992 / 1000000000000) (-44946319991 / 1000000000000)))) (orderedInterval (-27959221047 / 1000000000000) (-27959220772 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate316_chunkChecks4 :
    compactCertificate316.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate316.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate316_chunkChecks4_0
    compactCertificate316_chunkChecks4_1 compactCertificate316_chunkChecks4_2

theorem compactCertificate316_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate316.chunkCheck r b = true :=
  compactCertificate316.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate316_chunkChecks0
    · exact compactCertificate316_chunkChecks1
    · exact compactCertificate316_chunkChecks2
    · exact compactCertificate316_chunkChecks3
    · exact compactCertificate316_chunkChecks4)

theorem compactCertificate316_coefficient0 :
    compactCertificate316.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate316_coefficient1 :
    compactCertificate316.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate316_coefficient2 :
    compactCertificate316.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate316_coefficient3 :
    compactCertificate316.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate316_coefficient4 :
    compactCertificate316.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate316_coefficients : ∀ r : Fin 5,
    compactCertificate316.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate316_coefficient0
  · exact compactCertificate316_coefficient1
  · exact compactCertificate316_coefficient2
  · exact compactCertificate316_coefficient3
  · exact compactCertificate316_coefficient4

theorem compactCertificate316_lower : (1 : ℚ) ≤ compactCertificate316.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate316, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate316_proves {t : ℝ} (ht : t ∈ compactCertificate316.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate316.proves compactCertificate316_states compactCertificate316_chunks
    compactCertificate316_coefficients compactCertificate316_lower ht

end Erdos232
