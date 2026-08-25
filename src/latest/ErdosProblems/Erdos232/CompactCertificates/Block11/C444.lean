/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate444 : CompactCertificate where
  left := 315
  right := 316
  center := 631 / 2
  grid := fun i =>
    match i.val with
    | 0 => 100
    | 1 => 74
    | 2 => 120
    | 3 => 22
    | 4 => 58
    | 5 => 158
    | 6 => 116
    | 7 => 199
    | 8 => 146
    | 9 => 225
    | 10 => 130
    | 11 => 230
    | 12 => 215
    | 13 => 153
    | 14 => 174
    | 15 => 145
    | 16 => 128
    | 17 => 186
    | 18 => 103
    | 19 => 87
    | 20 => 55
    | 21 => 29
    | 22 => 80
    | 23 => 109
    | 24 => 46
    | 25 => 187
    | _ => 125
  point := fun i =>
    match i.val with
    | 0 => 631 / 2
    | 1 => 929583488125531 / 4000000000000
    | 2 => 300608200561723 / 800000000000
    | 3 => 271250143420817 / 4000000000000
    | 4 => 728616039717149 / 4000000000000
    | 5 => 1978334283837033 / 4000000000000
    | 6 => 1457232079434929 / 4000000000000
    | 7 => 2496992005836917 / 4000000000000
    | 8 => 1839273009988703 / 4000000000000
    | 9 => 2821917787604369 / 4000000000000
    | 10 => 1629234994304201 / 4000000000000
    | 11 => 2891106087735709 / 4000000000000
    | 12 => 2701246331580721 / 4000000000000
    | 13 => 1927736842344193 / 4000000000000
    | 14 => 2185848119151447 / 4000000000000
    | 15 => 1822332275626343 / 4000000000000
    | 16 => 1610085831309203 / 4000000000000
    | 17 => 466665630023097 / 800000000000
    | 18 => 1290821691910459 / 4000000000000
    | 19 => 1094243843691299 / 4000000000000
    | 20 => 684726990011297 / 4000000000000
    | 21 => 368248452527199 / 4000000000000
    | 22 => 999866183138597 / 4000000000000
    | 23 => 1365231791886469 / 4000000000000
    | 24 => 577273009988703 / 4000000000000
    | 25 => 2346582736364863 / 4000000000000
    | _ => 1567408517712017 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (38178940545 / 1000000000000) (38179003054 / 1000000000000), orderedInterval (-23728598119 / 1000000000000) (-23728535610 / 1000000000000))
    | 1 => (orderedInterval (33832692481 / 1000000000000) (33832692482 / 1000000000000), orderedInterval (39861234636 / 1000000000000) (39861234637 / 1000000000000))
    | 2 => (orderedInterval (-17747815905 / 1000000000000) (-17747815371 / 1000000000000), orderedInterval (37161654828 / 1000000000000) (37161655362 / 1000000000000))
    | 3 => (orderedInterval (-48054216685 / 1000000000000) (-48054209687 / 1000000000000), orderedInterval (84490246418 / 1000000000000) (84490253416 / 1000000000000))
    | 4 => (orderedInterval (39262865386 / 1000000000000) (39262865387 / 1000000000000), orderedInterval (44089312095 / 1000000000000) (44089312096 / 1000000000000))
    | 5 => (orderedInterval (-30246302857 / 1000000000000) (-30246217465 / 1000000000000), orderedInterval (19326824078 / 1000000000000) (19326909470 / 1000000000000))
    | 6 => (orderedInterval (25904109359 / 1000000000000) (25904109360 / 1000000000000), orderedInterval (32773808889 / 1000000000000) (32773808890 / 1000000000000))
    | 7 => (orderedInterval (4574446582 / 1000000000000) (4574446583 / 1000000000000), orderedInterval (-31608939337 / 1000000000000) (-31608939336 / 1000000000000))
    | 8 => (orderedInterval (34822958690 / 1000000000000) (34822979489 / 1000000000000), orderedInterval (-13147538062 / 1000000000000) (-13147517262 / 1000000000000))
    | 9 => (orderedInterval (16804727800 / 1000000000000) (16804728220 / 1000000000000), orderedInterval (-24911594746 / 1000000000000) (-24911594327 / 1000000000000))
    | 10 => (orderedInterval (-12181001239 / 1000000000000) (-12181001166 / 1000000000000), orderedInterval (37626318676 / 1000000000000) (37626318749 / 1000000000000))
    | 11 => (orderedInterval (24899937928 / 1000000000000) (24899937929 / 1000000000000), orderedInterval (16131785033 / 1000000000000) (16131785035 / 1000000000000))
    | 12 => (orderedInterval (-18688110240 / 1000000000000) (-18688110239 / 1000000000000), orderedInterval (-24347194719 / 1000000000000) (-24347194718 / 1000000000000))
    | 13 => (orderedInterval (-32155731531 / 1000000000000) (-32155660871 / 1000000000000), orderedInterval (16973777899 / 1000000000000) (16973848560 / 1000000000000))
    | 14 => (orderedInterval (19555200436 / 1000000000000) (19555200437 / 1000000000000), orderedInterval (27956716715 / 1000000000000) (27956716716 / 1000000000000))
    | 15 => (orderedInterval (-27767318230 / 1000000000000) (-27767318229 / 1000000000000), orderedInterval (-24996502867 / 1000000000000) (-24996502866 / 1000000000000))
    | 16 => (orderedInterval (36811270603 / 1000000000000) (36811270604 / 1000000000000), orderedInterval (15004496825 / 1000000000000) (15004496826 / 1000000000000))
    | 17 => (orderedInterval (-7177493561 / 1000000000000) (-7177493557 / 1000000000000), orderedInterval (32252617916 / 1000000000000) (32252617921 / 1000000000000))
    | 18 => (orderedInterval (4151664643 / 1000000000000) (4151664648 / 1000000000000), orderedInterval (-44227742109 / 1000000000000) (-44227742104 / 1000000000000))
    | 19 => (orderedInterval (-41290436104 / 1000000000000) (-41290436103 / 1000000000000), orderedInterval (-24869607201 / 1000000000000) (-24869607200 / 1000000000000))
    | 20 => (orderedInterval (44636676250 / 1000000000000) (44636749402 / 1000000000000), orderedInterval (-41681976762 / 1000000000000) (-41681903610 / 1000000000000))
    | 21 => (orderedInterval (-81969459568 / 1000000000000) (-81969459237 / 1000000000000), orderedInterval (14445993180 / 1000000000000) (14445993511 / 1000000000000))
    | 22 => (orderedInterval (-27486155801 / 1000000000000) (-27486150887 / 1000000000000), orderedInterval (42379122956 / 1000000000000) (42379127870 / 1000000000000))
    | 23 => (orderedInterval (14427972087 / 1000000000000) (14427972258 / 1000000000000), orderedInterval (-40728271861 / 1000000000000) (-40728271690 / 1000000000000))
    | 24 => (orderedInterval (36925376105 / 1000000000000) (36925376106 / 1000000000000), orderedInterval (55078485336 / 1000000000000) (55078485337 / 1000000000000))
    | 25 => (orderedInterval (1546297889 / 1000000000000) (1546297890 / 1000000000000), orderedInterval (-32907176162 / 1000000000000) (-32907176161 / 1000000000000))
    | _ => (orderedInterval (2492318540 / 1000000000000) (2492318542 / 1000000000000), orderedInterval (-40232927146 / 1000000000000) (-40232927143 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (14406588479 / 1000000000000) (14406613310 / 1000000000000)
      | 1 => orderedInterval (4105102595 / 1000000000000) (4105108780 / 1000000000000)
      | 2 => orderedInterval (700507962 / 1000000000000) (700508483 / 1000000000000)
      | 3 => orderedInterval (-348836435 / 1000000000000) (-348836229 / 1000000000000)
      | 4 => orderedInterval (-2802320668 / 1000000000000) (-2802313948 / 1000000000000)
      | 5 => orderedInterval (-2611006722 / 1000000000000) (-2611006691 / 1000000000000)
      | 6 => orderedInterval (3126376120 / 1000000000000) (3126378582 / 1000000000000)
      | 7 => orderedInterval (1031406658 / 1000000000000) (1031406827 / 1000000000000)
      | _ => orderedInterval (-370898233 / 1000000000000) (-370898145 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-6534394437 / 1000000000000) (-6534369598 / 1000000000000)
      | 1 => orderedInterval (-1421436417 / 1000000000000) (-1421426841 / 1000000000000)
      | 2 => orderedInterval (1465929984 / 1000000000000) (1465930748 / 1000000000000)
      | 3 => orderedInterval (18750505485 / 1000000000000) (18750505918 / 1000000000000)
      | 4 => orderedInterval (3147585666 / 1000000000000) (3147595934 / 1000000000000)
      | 5 => orderedInterval (14515345 / 1000000000000) (14515389 / 1000000000000)
      | 6 => orderedInterval (7717437001 / 1000000000000) (7717438368 / 1000000000000)
      | 7 => orderedInterval (2537117167 / 1000000000000) (2537117306 / 1000000000000)
      | _ => orderedInterval (14508294355 / 1000000000000) (14508294479 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-13805865832 / 1000000000000) (-13805840904 / 1000000000000)
      | 1 => orderedInterval (-5781388898 / 1000000000000) (-5781373886 / 1000000000000)
      | 2 => orderedInterval (-1239926114 / 1000000000000) (-1239924989 / 1000000000000)
      | 3 => orderedInterval (-2202125800 / 1000000000000) (-2202124861 / 1000000000000)
      | 4 => orderedInterval (5836240568 / 1000000000000) (5836256293 / 1000000000000)
      | 5 => orderedInterval (4725703311 / 1000000000000) (4725703377 / 1000000000000)
      | 6 => orderedInterval (-1514777058 / 1000000000000) (-1514776282 / 1000000000000)
      | 7 => orderedInterval (765696651 / 1000000000000) (765696771 / 1000000000000)
      | _ => orderedInterval (1063975394 / 1000000000000) (1063975577 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (5616338356 / 1000000000000) (5616363297 / 1000000000000)
      | 1 => orderedInterval (5010438350 / 1000000000000) (5010461873 / 1000000000000)
      | 2 => orderedInterval (-6564255846 / 1000000000000) (-6564254186 / 1000000000000)
      | 3 => orderedInterval (-83052440734 / 1000000000000) (-83052438667 / 1000000000000)
      | 4 => orderedInterval (-9314627022 / 1000000000000) (-9314602986 / 1000000000000)
      | 5 => orderedInterval (-2582115910 / 1000000000000) (-2582115808 / 1000000000000)
      | 6 => orderedInterval (-8263313324 / 1000000000000) (-8263312873 / 1000000000000)
      | 7 => orderedInterval (-3469333473 / 1000000000000) (-3469333365 / 1000000000000)
      | _ => orderedInterval (-31718369595 / 1000000000000) (-31718369314 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (13094352393 / 1000000000000) (13094377428 / 1000000000000)
      | 1 => orderedInterval (13113478655 / 1000000000000) (13113515600 / 1000000000000)
      | 2 => orderedInterval (1676296384 / 1000000000000) (1676298847 / 1000000000000)
      | 3 => orderedInterval (20864430046 / 1000000000000) (20864434639 / 1000000000000)
      | 4 => orderedInterval (-10304991981 / 1000000000000) (-10304955154 / 1000000000000)
      | 5 => orderedInterval (-9106603284 / 1000000000000) (-9106603123 / 1000000000000)
      | 6 => orderedInterval (772675564 / 1000000000000) (772675840 / 1000000000000)
      | 7 => orderedInterval (-1235725925 / 1000000000000) (-1235725825 / 1000000000000)
      | _ => orderedInterval (-2406547248 / 1000000000000) (-2406546797 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (17236919756 / 1000000000000) (17236960969 / 1000000000000)
    | 1 => orderedInterval (40185554149 / 1000000000000) (40185601703 / 1000000000000)
    | 2 => orderedInterval (-12152467778 / 1000000000000) (-12152408904 / 1000000000000)
    | 3 => orderedInterval (-134337679198 / 1000000000000) (-134337602029 / 1000000000000)
    | _ => orderedInterval (26467364604 / 1000000000000) (26467471455 / 1000000000000)

theorem compactCertificate444_stateChecks0 :
    compactCertificate444.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 100 12 (631 / 2)) (orderedInterval (38178940545 / 1000000000000) (38179003054 / 1000000000000), orderedInterval (-23728598119 / 1000000000000) (-23728535610 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (929583488125531 / 4000000000000)) (orderedInterval (33832692481 / 1000000000000) (33832692482 / 1000000000000), orderedInterval (39861234636 / 1000000000000) (39861234637 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 120 12 (300608200561723 / 800000000000)) (orderedInterval (-17747815905 / 1000000000000) (-17747815371 / 1000000000000), orderedInterval (37161654828 / 1000000000000) (37161655362 / 1000000000000))) = true
  rfl'

theorem compactCertificate444_stateChecks1 :
    compactCertificate444.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 22 12 (271250143420817 / 4000000000000)) (orderedInterval (-48054216685 / 1000000000000) (-48054209687 / 1000000000000), orderedInterval (84490246418 / 1000000000000) (84490253416 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (728616039717149 / 4000000000000)) (orderedInterval (39262865386 / 1000000000000) (39262865387 / 1000000000000), orderedInterval (44089312095 / 1000000000000) (44089312096 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 158 12 (1978334283837033 / 4000000000000)) (orderedInterval (-30246302857 / 1000000000000) (-30246217465 / 1000000000000), orderedInterval (19326824078 / 1000000000000) (19326909470 / 1000000000000))) = true
  rfl'

theorem compactCertificate444_stateChecks2 :
    compactCertificate444.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 116 12 (1457232079434929 / 4000000000000)) (orderedInterval (25904109359 / 1000000000000) (25904109360 / 1000000000000), orderedInterval (32773808889 / 1000000000000) (32773808890 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 199 12 (2496992005836917 / 4000000000000)) (orderedInterval (4574446582 / 1000000000000) (4574446583 / 1000000000000), orderedInterval (-31608939337 / 1000000000000) (-31608939336 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 146 12 (1839273009988703 / 4000000000000)) (orderedInterval (34822958690 / 1000000000000) (34822979489 / 1000000000000), orderedInterval (-13147538062 / 1000000000000) (-13147517262 / 1000000000000))) = true
  rfl'

theorem compactCertificate444_stateChecks3 :
    compactCertificate444.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 225 12 (2821917787604369 / 4000000000000)) (orderedInterval (16804727800 / 1000000000000) (16804728220 / 1000000000000), orderedInterval (-24911594746 / 1000000000000) (-24911594327 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 130 12 (1629234994304201 / 4000000000000)) (orderedInterval (-12181001239 / 1000000000000) (-12181001166 / 1000000000000), orderedInterval (37626318676 / 1000000000000) (37626318749 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 230 12 (2891106087735709 / 4000000000000)) (orderedInterval (24899937928 / 1000000000000) (24899937929 / 1000000000000), orderedInterval (16131785033 / 1000000000000) (16131785035 / 1000000000000))) = true
  rfl'

theorem compactCertificate444_stateChecks4 :
    compactCertificate444.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 215 12 (2701246331580721 / 4000000000000)) (orderedInterval (-18688110240 / 1000000000000) (-18688110239 / 1000000000000), orderedInterval (-24347194719 / 1000000000000) (-24347194718 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 153 12 (1927736842344193 / 4000000000000)) (orderedInterval (-32155731531 / 1000000000000) (-32155660871 / 1000000000000), orderedInterval (16973777899 / 1000000000000) (16973848560 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 174 12 (2185848119151447 / 4000000000000)) (orderedInterval (19555200436 / 1000000000000) (19555200437 / 1000000000000), orderedInterval (27956716715 / 1000000000000) (27956716716 / 1000000000000))) = true
  rfl'

theorem compactCertificate444_stateChecks5 :
    compactCertificate444.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 145 12 (1822332275626343 / 4000000000000)) (orderedInterval (-27767318230 / 1000000000000) (-27767318229 / 1000000000000), orderedInterval (-24996502867 / 1000000000000) (-24996502866 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 128 12 (1610085831309203 / 4000000000000)) (orderedInterval (36811270603 / 1000000000000) (36811270604 / 1000000000000), orderedInterval (15004496825 / 1000000000000) (15004496826 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 186 12 (466665630023097 / 800000000000)) (orderedInterval (-7177493561 / 1000000000000) (-7177493557 / 1000000000000), orderedInterval (32252617916 / 1000000000000) (32252617921 / 1000000000000))) = true
  rfl'

theorem compactCertificate444_stateChecks6 :
    compactCertificate444.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 103 12 (1290821691910459 / 4000000000000)) (orderedInterval (4151664643 / 1000000000000) (4151664648 / 1000000000000), orderedInterval (-44227742109 / 1000000000000) (-44227742104 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (1094243843691299 / 4000000000000)) (orderedInterval (-41290436104 / 1000000000000) (-41290436103 / 1000000000000), orderedInterval (-24869607201 / 1000000000000) (-24869607200 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (684726990011297 / 4000000000000)) (orderedInterval (44636676250 / 1000000000000) (44636749402 / 1000000000000), orderedInterval (-41681976762 / 1000000000000) (-41681903610 / 1000000000000))) = true
  rfl'

theorem compactCertificate444_stateChecks7 :
    compactCertificate444.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (368248452527199 / 4000000000000)) (orderedInterval (-81969459568 / 1000000000000) (-81969459237 / 1000000000000), orderedInterval (14445993180 / 1000000000000) (14445993511 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (999866183138597 / 4000000000000)) (orderedInterval (-27486155801 / 1000000000000) (-27486150887 / 1000000000000), orderedInterval (42379122956 / 1000000000000) (42379127870 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 109 12 (1365231791886469 / 4000000000000)) (orderedInterval (14427972087 / 1000000000000) (14427972258 / 1000000000000), orderedInterval (-40728271861 / 1000000000000) (-40728271690 / 1000000000000))) = true
  rfl'

theorem compactCertificate444_stateChecks8 :
    compactCertificate444.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (577273009988703 / 4000000000000)) (orderedInterval (36925376105 / 1000000000000) (36925376106 / 1000000000000), orderedInterval (55078485336 / 1000000000000) (55078485337 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 187 12 (2346582736364863 / 4000000000000)) (orderedInterval (1546297889 / 1000000000000) (1546297890 / 1000000000000), orderedInterval (-32907176162 / 1000000000000) (-32907176161 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 125 12 (1567408517712017 / 4000000000000)) (orderedInterval (2492318540 / 1000000000000) (2492318542 / 1000000000000), orderedInterval (-40232927146 / 1000000000000) (-40232927143 / 1000000000000))) = true
  rfl'

theorem compactCertificate444_states : ∀ j,
    BesselStateValid (compactCertificate444.point j) (compactCertificate444.state j) :=
  compactCertificate444.statesValid_of_checks3 compactCertificate444_stateChecks0
    compactCertificate444_stateChecks1 compactCertificate444_stateChecks2
    compactCertificate444_stateChecks3 compactCertificate444_stateChecks4
    compactCertificate444_stateChecks5 compactCertificate444_stateChecks6
    compactCertificate444_stateChecks7 compactCertificate444_stateChecks8

theorem compactCertificate444_chunkChecks0_0 :
    compactCertificate444.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (631 / 2) 0 (IntervalRat.scale (631 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (38178940545 / 1000000000000) (38179003054 / 1000000000000), orderedInterval (-23728598119 / 1000000000000) (-23728535610 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (929583488125531 / 4000000000000) 0 (IntervalRat.scale (631 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (33832692481 / 1000000000000) (33832692482 / 1000000000000), orderedInterval (39861234636 / 1000000000000) (39861234637 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (300608200561723 / 800000000000) 0 (IntervalRat.scale (631 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-17747815905 / 1000000000000) (-17747815371 / 1000000000000), orderedInterval (37161654828 / 1000000000000) (37161655362 / 1000000000000)))) (orderedInterval (14406588479 / 1000000000000) (14406613310 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (271250143420817 / 4000000000000) 0 (IntervalRat.scale (631 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-48054216685 / 1000000000000) (-48054209687 / 1000000000000), orderedInterval (84490246418 / 1000000000000) (84490253416 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (728616039717149 / 4000000000000) 0 (IntervalRat.scale (631 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (39262865386 / 1000000000000) (39262865387 / 1000000000000), orderedInterval (44089312095 / 1000000000000) (44089312096 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1978334283837033 / 4000000000000) 0 (IntervalRat.scale (631 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30246302857 / 1000000000000) (-30246217465 / 1000000000000), orderedInterval (19326824078 / 1000000000000) (19326909470 / 1000000000000)))) (orderedInterval (4105102595 / 1000000000000) (4105108780 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1457232079434929 / 4000000000000) 0 (IntervalRat.scale (631 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (25904109359 / 1000000000000) (25904109360 / 1000000000000), orderedInterval (32773808889 / 1000000000000) (32773808890 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2496992005836917 / 4000000000000) 0 (IntervalRat.scale (631 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (4574446582 / 1000000000000) (4574446583 / 1000000000000), orderedInterval (-31608939337 / 1000000000000) (-31608939336 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1839273009988703 / 4000000000000) 0 (IntervalRat.scale (631 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (34822958690 / 1000000000000) (34822979489 / 1000000000000), orderedInterval (-13147538062 / 1000000000000) (-13147517262 / 1000000000000)))) (orderedInterval (700507962 / 1000000000000) (700508483 / 1000000000000))) = true
  rfl'

theorem compactCertificate444_chunkChecks0_1 :
    compactCertificate444.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2821917787604369 / 4000000000000) 0 (IntervalRat.scale (631 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (16804727800 / 1000000000000) (16804728220 / 1000000000000), orderedInterval (-24911594746 / 1000000000000) (-24911594327 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1629234994304201 / 4000000000000) 0 (IntervalRat.scale (631 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-12181001239 / 1000000000000) (-12181001166 / 1000000000000), orderedInterval (37626318676 / 1000000000000) (37626318749 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2891106087735709 / 4000000000000) 0 (IntervalRat.scale (631 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (24899937928 / 1000000000000) (24899937929 / 1000000000000), orderedInterval (16131785033 / 1000000000000) (16131785035 / 1000000000000)))) (orderedInterval (-348836435 / 1000000000000) (-348836229 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2701246331580721 / 4000000000000) 0 (IntervalRat.scale (631 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-18688110240 / 1000000000000) (-18688110239 / 1000000000000), orderedInterval (-24347194719 / 1000000000000) (-24347194718 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1927736842344193 / 4000000000000) 0 (IntervalRat.scale (631 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-32155731531 / 1000000000000) (-32155660871 / 1000000000000), orderedInterval (16973777899 / 1000000000000) (16973848560 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2185848119151447 / 4000000000000) 0 (IntervalRat.scale (631 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (19555200436 / 1000000000000) (19555200437 / 1000000000000), orderedInterval (27956716715 / 1000000000000) (27956716716 / 1000000000000)))) (orderedInterval (-2802320668 / 1000000000000) (-2802313948 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1822332275626343 / 4000000000000) 0 (IntervalRat.scale (631 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-27767318230 / 1000000000000) (-27767318229 / 1000000000000), orderedInterval (-24996502867 / 1000000000000) (-24996502866 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1610085831309203 / 4000000000000) 0 (IntervalRat.scale (631 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (36811270603 / 1000000000000) (36811270604 / 1000000000000), orderedInterval (15004496825 / 1000000000000) (15004496826 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (466665630023097 / 800000000000) 0 (IntervalRat.scale (631 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-7177493561 / 1000000000000) (-7177493557 / 1000000000000), orderedInterval (32252617916 / 1000000000000) (32252617921 / 1000000000000)))) (orderedInterval (-2611006722 / 1000000000000) (-2611006691 / 1000000000000))) = true
  rfl'

theorem compactCertificate444_chunkChecks0_2 :
    compactCertificate444.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1290821691910459 / 4000000000000) 0 (IntervalRat.scale (631 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (4151664643 / 1000000000000) (4151664648 / 1000000000000), orderedInterval (-44227742109 / 1000000000000) (-44227742104 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1094243843691299 / 4000000000000) 0 (IntervalRat.scale (631 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-41290436104 / 1000000000000) (-41290436103 / 1000000000000), orderedInterval (-24869607201 / 1000000000000) (-24869607200 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (684726990011297 / 4000000000000) 0 (IntervalRat.scale (631 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (44636676250 / 1000000000000) (44636749402 / 1000000000000), orderedInterval (-41681976762 / 1000000000000) (-41681903610 / 1000000000000)))) (orderedInterval (3126376120 / 1000000000000) (3126378582 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (368248452527199 / 4000000000000) 0 (IntervalRat.scale (631 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-81969459568 / 1000000000000) (-81969459237 / 1000000000000), orderedInterval (14445993180 / 1000000000000) (14445993511 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (999866183138597 / 4000000000000) 0 (IntervalRat.scale (631 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-27486155801 / 1000000000000) (-27486150887 / 1000000000000), orderedInterval (42379122956 / 1000000000000) (42379127870 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1365231791886469 / 4000000000000) 0 (IntervalRat.scale (631 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (14427972087 / 1000000000000) (14427972258 / 1000000000000), orderedInterval (-40728271861 / 1000000000000) (-40728271690 / 1000000000000)))) (orderedInterval (1031406658 / 1000000000000) (1031406827 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (577273009988703 / 4000000000000) 0 (IntervalRat.scale (631 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (36925376105 / 1000000000000) (36925376106 / 1000000000000), orderedInterval (55078485336 / 1000000000000) (55078485337 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2346582736364863 / 4000000000000) 0 (IntervalRat.scale (631 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (1546297889 / 1000000000000) (1546297890 / 1000000000000), orderedInterval (-32907176162 / 1000000000000) (-32907176161 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1567408517712017 / 4000000000000) 0 (IntervalRat.scale (631 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (2492318540 / 1000000000000) (2492318542 / 1000000000000), orderedInterval (-40232927146 / 1000000000000) (-40232927143 / 1000000000000)))) (orderedInterval (-370898233 / 1000000000000) (-370898145 / 1000000000000))) = true
  rfl'

theorem compactCertificate444_chunkChecks0 :
    compactCertificate444.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate444.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate444_chunkChecks0_0
    compactCertificate444_chunkChecks0_1 compactCertificate444_chunkChecks0_2

theorem compactCertificate444_chunkChecks1_0 :
    compactCertificate444.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (631 / 2) 1 (IntervalRat.scale (631 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (38178940545 / 1000000000000) (38179003054 / 1000000000000), orderedInterval (-23728598119 / 1000000000000) (-23728535610 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (929583488125531 / 4000000000000) 1 (IntervalRat.scale (631 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (33832692481 / 1000000000000) (33832692482 / 1000000000000), orderedInterval (39861234636 / 1000000000000) (39861234637 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (300608200561723 / 800000000000) 1 (IntervalRat.scale (631 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-17747815905 / 1000000000000) (-17747815371 / 1000000000000), orderedInterval (37161654828 / 1000000000000) (37161655362 / 1000000000000)))) (orderedInterval (-6534394437 / 1000000000000) (-6534369598 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (271250143420817 / 4000000000000) 1 (IntervalRat.scale (631 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-48054216685 / 1000000000000) (-48054209687 / 1000000000000), orderedInterval (84490246418 / 1000000000000) (84490253416 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (728616039717149 / 4000000000000) 1 (IntervalRat.scale (631 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (39262865386 / 1000000000000) (39262865387 / 1000000000000), orderedInterval (44089312095 / 1000000000000) (44089312096 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1978334283837033 / 4000000000000) 1 (IntervalRat.scale (631 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30246302857 / 1000000000000) (-30246217465 / 1000000000000), orderedInterval (19326824078 / 1000000000000) (19326909470 / 1000000000000)))) (orderedInterval (-1421436417 / 1000000000000) (-1421426841 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1457232079434929 / 4000000000000) 1 (IntervalRat.scale (631 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (25904109359 / 1000000000000) (25904109360 / 1000000000000), orderedInterval (32773808889 / 1000000000000) (32773808890 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2496992005836917 / 4000000000000) 1 (IntervalRat.scale (631 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (4574446582 / 1000000000000) (4574446583 / 1000000000000), orderedInterval (-31608939337 / 1000000000000) (-31608939336 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1839273009988703 / 4000000000000) 1 (IntervalRat.scale (631 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (34822958690 / 1000000000000) (34822979489 / 1000000000000), orderedInterval (-13147538062 / 1000000000000) (-13147517262 / 1000000000000)))) (orderedInterval (1465929984 / 1000000000000) (1465930748 / 1000000000000))) = true
  rfl'

theorem compactCertificate444_chunkChecks1_1 :
    compactCertificate444.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2821917787604369 / 4000000000000) 1 (IntervalRat.scale (631 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (16804727800 / 1000000000000) (16804728220 / 1000000000000), orderedInterval (-24911594746 / 1000000000000) (-24911594327 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1629234994304201 / 4000000000000) 1 (IntervalRat.scale (631 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-12181001239 / 1000000000000) (-12181001166 / 1000000000000), orderedInterval (37626318676 / 1000000000000) (37626318749 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2891106087735709 / 4000000000000) 1 (IntervalRat.scale (631 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (24899937928 / 1000000000000) (24899937929 / 1000000000000), orderedInterval (16131785033 / 1000000000000) (16131785035 / 1000000000000)))) (orderedInterval (18750505485 / 1000000000000) (18750505918 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2701246331580721 / 4000000000000) 1 (IntervalRat.scale (631 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-18688110240 / 1000000000000) (-18688110239 / 1000000000000), orderedInterval (-24347194719 / 1000000000000) (-24347194718 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1927736842344193 / 4000000000000) 1 (IntervalRat.scale (631 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-32155731531 / 1000000000000) (-32155660871 / 1000000000000), orderedInterval (16973777899 / 1000000000000) (16973848560 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2185848119151447 / 4000000000000) 1 (IntervalRat.scale (631 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (19555200436 / 1000000000000) (19555200437 / 1000000000000), orderedInterval (27956716715 / 1000000000000) (27956716716 / 1000000000000)))) (orderedInterval (3147585666 / 1000000000000) (3147595934 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1822332275626343 / 4000000000000) 1 (IntervalRat.scale (631 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-27767318230 / 1000000000000) (-27767318229 / 1000000000000), orderedInterval (-24996502867 / 1000000000000) (-24996502866 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1610085831309203 / 4000000000000) 1 (IntervalRat.scale (631 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (36811270603 / 1000000000000) (36811270604 / 1000000000000), orderedInterval (15004496825 / 1000000000000) (15004496826 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (466665630023097 / 800000000000) 1 (IntervalRat.scale (631 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-7177493561 / 1000000000000) (-7177493557 / 1000000000000), orderedInterval (32252617916 / 1000000000000) (32252617921 / 1000000000000)))) (orderedInterval (14515345 / 1000000000000) (14515389 / 1000000000000))) = true
  rfl'

theorem compactCertificate444_chunkChecks1_2 :
    compactCertificate444.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1290821691910459 / 4000000000000) 1 (IntervalRat.scale (631 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (4151664643 / 1000000000000) (4151664648 / 1000000000000), orderedInterval (-44227742109 / 1000000000000) (-44227742104 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1094243843691299 / 4000000000000) 1 (IntervalRat.scale (631 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-41290436104 / 1000000000000) (-41290436103 / 1000000000000), orderedInterval (-24869607201 / 1000000000000) (-24869607200 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (684726990011297 / 4000000000000) 1 (IntervalRat.scale (631 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (44636676250 / 1000000000000) (44636749402 / 1000000000000), orderedInterval (-41681976762 / 1000000000000) (-41681903610 / 1000000000000)))) (orderedInterval (7717437001 / 1000000000000) (7717438368 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (368248452527199 / 4000000000000) 1 (IntervalRat.scale (631 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-81969459568 / 1000000000000) (-81969459237 / 1000000000000), orderedInterval (14445993180 / 1000000000000) (14445993511 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (999866183138597 / 4000000000000) 1 (IntervalRat.scale (631 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-27486155801 / 1000000000000) (-27486150887 / 1000000000000), orderedInterval (42379122956 / 1000000000000) (42379127870 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1365231791886469 / 4000000000000) 1 (IntervalRat.scale (631 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (14427972087 / 1000000000000) (14427972258 / 1000000000000), orderedInterval (-40728271861 / 1000000000000) (-40728271690 / 1000000000000)))) (orderedInterval (2537117167 / 1000000000000) (2537117306 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (577273009988703 / 4000000000000) 1 (IntervalRat.scale (631 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (36925376105 / 1000000000000) (36925376106 / 1000000000000), orderedInterval (55078485336 / 1000000000000) (55078485337 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2346582736364863 / 4000000000000) 1 (IntervalRat.scale (631 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (1546297889 / 1000000000000) (1546297890 / 1000000000000), orderedInterval (-32907176162 / 1000000000000) (-32907176161 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1567408517712017 / 4000000000000) 1 (IntervalRat.scale (631 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (2492318540 / 1000000000000) (2492318542 / 1000000000000), orderedInterval (-40232927146 / 1000000000000) (-40232927143 / 1000000000000)))) (orderedInterval (14508294355 / 1000000000000) (14508294479 / 1000000000000))) = true
  rfl'

theorem compactCertificate444_chunkChecks1 :
    compactCertificate444.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate444.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate444_chunkChecks1_0
    compactCertificate444_chunkChecks1_1 compactCertificate444_chunkChecks1_2

theorem compactCertificate444_chunkChecks2_0 :
    compactCertificate444.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (631 / 2) 2 (IntervalRat.scale (631 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (38178940545 / 1000000000000) (38179003054 / 1000000000000), orderedInterval (-23728598119 / 1000000000000) (-23728535610 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (929583488125531 / 4000000000000) 2 (IntervalRat.scale (631 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (33832692481 / 1000000000000) (33832692482 / 1000000000000), orderedInterval (39861234636 / 1000000000000) (39861234637 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (300608200561723 / 800000000000) 2 (IntervalRat.scale (631 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-17747815905 / 1000000000000) (-17747815371 / 1000000000000), orderedInterval (37161654828 / 1000000000000) (37161655362 / 1000000000000)))) (orderedInterval (-13805865832 / 1000000000000) (-13805840904 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (271250143420817 / 4000000000000) 2 (IntervalRat.scale (631 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-48054216685 / 1000000000000) (-48054209687 / 1000000000000), orderedInterval (84490246418 / 1000000000000) (84490253416 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (728616039717149 / 4000000000000) 2 (IntervalRat.scale (631 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (39262865386 / 1000000000000) (39262865387 / 1000000000000), orderedInterval (44089312095 / 1000000000000) (44089312096 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1978334283837033 / 4000000000000) 2 (IntervalRat.scale (631 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30246302857 / 1000000000000) (-30246217465 / 1000000000000), orderedInterval (19326824078 / 1000000000000) (19326909470 / 1000000000000)))) (orderedInterval (-5781388898 / 1000000000000) (-5781373886 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1457232079434929 / 4000000000000) 2 (IntervalRat.scale (631 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (25904109359 / 1000000000000) (25904109360 / 1000000000000), orderedInterval (32773808889 / 1000000000000) (32773808890 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2496992005836917 / 4000000000000) 2 (IntervalRat.scale (631 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (4574446582 / 1000000000000) (4574446583 / 1000000000000), orderedInterval (-31608939337 / 1000000000000) (-31608939336 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1839273009988703 / 4000000000000) 2 (IntervalRat.scale (631 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (34822958690 / 1000000000000) (34822979489 / 1000000000000), orderedInterval (-13147538062 / 1000000000000) (-13147517262 / 1000000000000)))) (orderedInterval (-1239926114 / 1000000000000) (-1239924989 / 1000000000000))) = true
  rfl'

theorem compactCertificate444_chunkChecks2_1 :
    compactCertificate444.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2821917787604369 / 4000000000000) 2 (IntervalRat.scale (631 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (16804727800 / 1000000000000) (16804728220 / 1000000000000), orderedInterval (-24911594746 / 1000000000000) (-24911594327 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1629234994304201 / 4000000000000) 2 (IntervalRat.scale (631 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-12181001239 / 1000000000000) (-12181001166 / 1000000000000), orderedInterval (37626318676 / 1000000000000) (37626318749 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2891106087735709 / 4000000000000) 2 (IntervalRat.scale (631 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (24899937928 / 1000000000000) (24899937929 / 1000000000000), orderedInterval (16131785033 / 1000000000000) (16131785035 / 1000000000000)))) (orderedInterval (-2202125800 / 1000000000000) (-2202124861 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2701246331580721 / 4000000000000) 2 (IntervalRat.scale (631 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-18688110240 / 1000000000000) (-18688110239 / 1000000000000), orderedInterval (-24347194719 / 1000000000000) (-24347194718 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1927736842344193 / 4000000000000) 2 (IntervalRat.scale (631 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-32155731531 / 1000000000000) (-32155660871 / 1000000000000), orderedInterval (16973777899 / 1000000000000) (16973848560 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2185848119151447 / 4000000000000) 2 (IntervalRat.scale (631 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (19555200436 / 1000000000000) (19555200437 / 1000000000000), orderedInterval (27956716715 / 1000000000000) (27956716716 / 1000000000000)))) (orderedInterval (5836240568 / 1000000000000) (5836256293 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1822332275626343 / 4000000000000) 2 (IntervalRat.scale (631 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-27767318230 / 1000000000000) (-27767318229 / 1000000000000), orderedInterval (-24996502867 / 1000000000000) (-24996502866 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1610085831309203 / 4000000000000) 2 (IntervalRat.scale (631 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (36811270603 / 1000000000000) (36811270604 / 1000000000000), orderedInterval (15004496825 / 1000000000000) (15004496826 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (466665630023097 / 800000000000) 2 (IntervalRat.scale (631 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-7177493561 / 1000000000000) (-7177493557 / 1000000000000), orderedInterval (32252617916 / 1000000000000) (32252617921 / 1000000000000)))) (orderedInterval (4725703311 / 1000000000000) (4725703377 / 1000000000000))) = true
  rfl'

theorem compactCertificate444_chunkChecks2_2 :
    compactCertificate444.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1290821691910459 / 4000000000000) 2 (IntervalRat.scale (631 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (4151664643 / 1000000000000) (4151664648 / 1000000000000), orderedInterval (-44227742109 / 1000000000000) (-44227742104 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1094243843691299 / 4000000000000) 2 (IntervalRat.scale (631 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-41290436104 / 1000000000000) (-41290436103 / 1000000000000), orderedInterval (-24869607201 / 1000000000000) (-24869607200 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (684726990011297 / 4000000000000) 2 (IntervalRat.scale (631 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (44636676250 / 1000000000000) (44636749402 / 1000000000000), orderedInterval (-41681976762 / 1000000000000) (-41681903610 / 1000000000000)))) (orderedInterval (-1514777058 / 1000000000000) (-1514776282 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (368248452527199 / 4000000000000) 2 (IntervalRat.scale (631 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-81969459568 / 1000000000000) (-81969459237 / 1000000000000), orderedInterval (14445993180 / 1000000000000) (14445993511 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (999866183138597 / 4000000000000) 2 (IntervalRat.scale (631 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-27486155801 / 1000000000000) (-27486150887 / 1000000000000), orderedInterval (42379122956 / 1000000000000) (42379127870 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1365231791886469 / 4000000000000) 2 (IntervalRat.scale (631 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (14427972087 / 1000000000000) (14427972258 / 1000000000000), orderedInterval (-40728271861 / 1000000000000) (-40728271690 / 1000000000000)))) (orderedInterval (765696651 / 1000000000000) (765696771 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (577273009988703 / 4000000000000) 2 (IntervalRat.scale (631 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (36925376105 / 1000000000000) (36925376106 / 1000000000000), orderedInterval (55078485336 / 1000000000000) (55078485337 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2346582736364863 / 4000000000000) 2 (IntervalRat.scale (631 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (1546297889 / 1000000000000) (1546297890 / 1000000000000), orderedInterval (-32907176162 / 1000000000000) (-32907176161 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1567408517712017 / 4000000000000) 2 (IntervalRat.scale (631 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (2492318540 / 1000000000000) (2492318542 / 1000000000000), orderedInterval (-40232927146 / 1000000000000) (-40232927143 / 1000000000000)))) (orderedInterval (1063975394 / 1000000000000) (1063975577 / 1000000000000))) = true
  rfl'

theorem compactCertificate444_chunkChecks2 :
    compactCertificate444.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate444.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate444_chunkChecks2_0
    compactCertificate444_chunkChecks2_1 compactCertificate444_chunkChecks2_2

theorem compactCertificate444_chunkChecks3_0 :
    compactCertificate444.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (631 / 2) 3 (IntervalRat.scale (631 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (38178940545 / 1000000000000) (38179003054 / 1000000000000), orderedInterval (-23728598119 / 1000000000000) (-23728535610 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (929583488125531 / 4000000000000) 3 (IntervalRat.scale (631 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (33832692481 / 1000000000000) (33832692482 / 1000000000000), orderedInterval (39861234636 / 1000000000000) (39861234637 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (300608200561723 / 800000000000) 3 (IntervalRat.scale (631 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-17747815905 / 1000000000000) (-17747815371 / 1000000000000), orderedInterval (37161654828 / 1000000000000) (37161655362 / 1000000000000)))) (orderedInterval (5616338356 / 1000000000000) (5616363297 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (271250143420817 / 4000000000000) 3 (IntervalRat.scale (631 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-48054216685 / 1000000000000) (-48054209687 / 1000000000000), orderedInterval (84490246418 / 1000000000000) (84490253416 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (728616039717149 / 4000000000000) 3 (IntervalRat.scale (631 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (39262865386 / 1000000000000) (39262865387 / 1000000000000), orderedInterval (44089312095 / 1000000000000) (44089312096 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1978334283837033 / 4000000000000) 3 (IntervalRat.scale (631 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30246302857 / 1000000000000) (-30246217465 / 1000000000000), orderedInterval (19326824078 / 1000000000000) (19326909470 / 1000000000000)))) (orderedInterval (5010438350 / 1000000000000) (5010461873 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1457232079434929 / 4000000000000) 3 (IntervalRat.scale (631 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (25904109359 / 1000000000000) (25904109360 / 1000000000000), orderedInterval (32773808889 / 1000000000000) (32773808890 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2496992005836917 / 4000000000000) 3 (IntervalRat.scale (631 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (4574446582 / 1000000000000) (4574446583 / 1000000000000), orderedInterval (-31608939337 / 1000000000000) (-31608939336 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1839273009988703 / 4000000000000) 3 (IntervalRat.scale (631 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (34822958690 / 1000000000000) (34822979489 / 1000000000000), orderedInterval (-13147538062 / 1000000000000) (-13147517262 / 1000000000000)))) (orderedInterval (-6564255846 / 1000000000000) (-6564254186 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate444_chunkChecks3_1 :
    compactCertificate444.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2821917787604369 / 4000000000000) 3 (IntervalRat.scale (631 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (16804727800 / 1000000000000) (16804728220 / 1000000000000), orderedInterval (-24911594746 / 1000000000000) (-24911594327 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1629234994304201 / 4000000000000) 3 (IntervalRat.scale (631 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-12181001239 / 1000000000000) (-12181001166 / 1000000000000), orderedInterval (37626318676 / 1000000000000) (37626318749 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2891106087735709 / 4000000000000) 3 (IntervalRat.scale (631 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (24899937928 / 1000000000000) (24899937929 / 1000000000000), orderedInterval (16131785033 / 1000000000000) (16131785035 / 1000000000000)))) (orderedInterval (-83052440734 / 1000000000000) (-83052438667 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2701246331580721 / 4000000000000) 3 (IntervalRat.scale (631 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-18688110240 / 1000000000000) (-18688110239 / 1000000000000), orderedInterval (-24347194719 / 1000000000000) (-24347194718 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1927736842344193 / 4000000000000) 3 (IntervalRat.scale (631 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-32155731531 / 1000000000000) (-32155660871 / 1000000000000), orderedInterval (16973777899 / 1000000000000) (16973848560 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2185848119151447 / 4000000000000) 3 (IntervalRat.scale (631 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (19555200436 / 1000000000000) (19555200437 / 1000000000000), orderedInterval (27956716715 / 1000000000000) (27956716716 / 1000000000000)))) (orderedInterval (-9314627022 / 1000000000000) (-9314602986 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1822332275626343 / 4000000000000) 3 (IntervalRat.scale (631 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-27767318230 / 1000000000000) (-27767318229 / 1000000000000), orderedInterval (-24996502867 / 1000000000000) (-24996502866 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1610085831309203 / 4000000000000) 3 (IntervalRat.scale (631 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (36811270603 / 1000000000000) (36811270604 / 1000000000000), orderedInterval (15004496825 / 1000000000000) (15004496826 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (466665630023097 / 800000000000) 3 (IntervalRat.scale (631 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-7177493561 / 1000000000000) (-7177493557 / 1000000000000), orderedInterval (32252617916 / 1000000000000) (32252617921 / 1000000000000)))) (orderedInterval (-2582115910 / 1000000000000) (-2582115808 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate444_chunkChecks3_2 :
    compactCertificate444.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1290821691910459 / 4000000000000) 3 (IntervalRat.scale (631 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (4151664643 / 1000000000000) (4151664648 / 1000000000000), orderedInterval (-44227742109 / 1000000000000) (-44227742104 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1094243843691299 / 4000000000000) 3 (IntervalRat.scale (631 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-41290436104 / 1000000000000) (-41290436103 / 1000000000000), orderedInterval (-24869607201 / 1000000000000) (-24869607200 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (684726990011297 / 4000000000000) 3 (IntervalRat.scale (631 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (44636676250 / 1000000000000) (44636749402 / 1000000000000), orderedInterval (-41681976762 / 1000000000000) (-41681903610 / 1000000000000)))) (orderedInterval (-8263313324 / 1000000000000) (-8263312873 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (368248452527199 / 4000000000000) 3 (IntervalRat.scale (631 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-81969459568 / 1000000000000) (-81969459237 / 1000000000000), orderedInterval (14445993180 / 1000000000000) (14445993511 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (999866183138597 / 4000000000000) 3 (IntervalRat.scale (631 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-27486155801 / 1000000000000) (-27486150887 / 1000000000000), orderedInterval (42379122956 / 1000000000000) (42379127870 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1365231791886469 / 4000000000000) 3 (IntervalRat.scale (631 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (14427972087 / 1000000000000) (14427972258 / 1000000000000), orderedInterval (-40728271861 / 1000000000000) (-40728271690 / 1000000000000)))) (orderedInterval (-3469333473 / 1000000000000) (-3469333365 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (577273009988703 / 4000000000000) 3 (IntervalRat.scale (631 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (36925376105 / 1000000000000) (36925376106 / 1000000000000), orderedInterval (55078485336 / 1000000000000) (55078485337 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2346582736364863 / 4000000000000) 3 (IntervalRat.scale (631 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (1546297889 / 1000000000000) (1546297890 / 1000000000000), orderedInterval (-32907176162 / 1000000000000) (-32907176161 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1567408517712017 / 4000000000000) 3 (IntervalRat.scale (631 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (2492318540 / 1000000000000) (2492318542 / 1000000000000), orderedInterval (-40232927146 / 1000000000000) (-40232927143 / 1000000000000)))) (orderedInterval (-31718369595 / 1000000000000) (-31718369314 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate444_chunkChecks3 :
    compactCertificate444.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate444.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate444_chunkChecks3_0
    compactCertificate444_chunkChecks3_1 compactCertificate444_chunkChecks3_2

theorem compactCertificate444_chunkChecks4_0 :
    compactCertificate444.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (631 / 2) 4 (IntervalRat.scale (631 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (38178940545 / 1000000000000) (38179003054 / 1000000000000), orderedInterval (-23728598119 / 1000000000000) (-23728535610 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (929583488125531 / 4000000000000) 4 (IntervalRat.scale (631 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (33832692481 / 1000000000000) (33832692482 / 1000000000000), orderedInterval (39861234636 / 1000000000000) (39861234637 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (300608200561723 / 800000000000) 4 (IntervalRat.scale (631 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-17747815905 / 1000000000000) (-17747815371 / 1000000000000), orderedInterval (37161654828 / 1000000000000) (37161655362 / 1000000000000)))) (orderedInterval (13094352393 / 1000000000000) (13094377428 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (271250143420817 / 4000000000000) 4 (IntervalRat.scale (631 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-48054216685 / 1000000000000) (-48054209687 / 1000000000000), orderedInterval (84490246418 / 1000000000000) (84490253416 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (728616039717149 / 4000000000000) 4 (IntervalRat.scale (631 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (39262865386 / 1000000000000) (39262865387 / 1000000000000), orderedInterval (44089312095 / 1000000000000) (44089312096 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1978334283837033 / 4000000000000) 4 (IntervalRat.scale (631 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30246302857 / 1000000000000) (-30246217465 / 1000000000000), orderedInterval (19326824078 / 1000000000000) (19326909470 / 1000000000000)))) (orderedInterval (13113478655 / 1000000000000) (13113515600 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1457232079434929 / 4000000000000) 4 (IntervalRat.scale (631 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (25904109359 / 1000000000000) (25904109360 / 1000000000000), orderedInterval (32773808889 / 1000000000000) (32773808890 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2496992005836917 / 4000000000000) 4 (IntervalRat.scale (631 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (4574446582 / 1000000000000) (4574446583 / 1000000000000), orderedInterval (-31608939337 / 1000000000000) (-31608939336 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1839273009988703 / 4000000000000) 4 (IntervalRat.scale (631 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (34822958690 / 1000000000000) (34822979489 / 1000000000000), orderedInterval (-13147538062 / 1000000000000) (-13147517262 / 1000000000000)))) (orderedInterval (1676296384 / 1000000000000) (1676298847 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate444_chunkChecks4_1 :
    compactCertificate444.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2821917787604369 / 4000000000000) 4 (IntervalRat.scale (631 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (16804727800 / 1000000000000) (16804728220 / 1000000000000), orderedInterval (-24911594746 / 1000000000000) (-24911594327 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1629234994304201 / 4000000000000) 4 (IntervalRat.scale (631 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-12181001239 / 1000000000000) (-12181001166 / 1000000000000), orderedInterval (37626318676 / 1000000000000) (37626318749 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2891106087735709 / 4000000000000) 4 (IntervalRat.scale (631 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (24899937928 / 1000000000000) (24899937929 / 1000000000000), orderedInterval (16131785033 / 1000000000000) (16131785035 / 1000000000000)))) (orderedInterval (20864430046 / 1000000000000) (20864434639 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2701246331580721 / 4000000000000) 4 (IntervalRat.scale (631 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-18688110240 / 1000000000000) (-18688110239 / 1000000000000), orderedInterval (-24347194719 / 1000000000000) (-24347194718 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1927736842344193 / 4000000000000) 4 (IntervalRat.scale (631 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-32155731531 / 1000000000000) (-32155660871 / 1000000000000), orderedInterval (16973777899 / 1000000000000) (16973848560 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2185848119151447 / 4000000000000) 4 (IntervalRat.scale (631 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (19555200436 / 1000000000000) (19555200437 / 1000000000000), orderedInterval (27956716715 / 1000000000000) (27956716716 / 1000000000000)))) (orderedInterval (-10304991981 / 1000000000000) (-10304955154 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1822332275626343 / 4000000000000) 4 (IntervalRat.scale (631 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-27767318230 / 1000000000000) (-27767318229 / 1000000000000), orderedInterval (-24996502867 / 1000000000000) (-24996502866 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1610085831309203 / 4000000000000) 4 (IntervalRat.scale (631 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (36811270603 / 1000000000000) (36811270604 / 1000000000000), orderedInterval (15004496825 / 1000000000000) (15004496826 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (466665630023097 / 800000000000) 4 (IntervalRat.scale (631 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-7177493561 / 1000000000000) (-7177493557 / 1000000000000), orderedInterval (32252617916 / 1000000000000) (32252617921 / 1000000000000)))) (orderedInterval (-9106603284 / 1000000000000) (-9106603123 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate444_chunkChecks4_2 :
    compactCertificate444.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1290821691910459 / 4000000000000) 4 (IntervalRat.scale (631 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (4151664643 / 1000000000000) (4151664648 / 1000000000000), orderedInterval (-44227742109 / 1000000000000) (-44227742104 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1094243843691299 / 4000000000000) 4 (IntervalRat.scale (631 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-41290436104 / 1000000000000) (-41290436103 / 1000000000000), orderedInterval (-24869607201 / 1000000000000) (-24869607200 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (684726990011297 / 4000000000000) 4 (IntervalRat.scale (631 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (44636676250 / 1000000000000) (44636749402 / 1000000000000), orderedInterval (-41681976762 / 1000000000000) (-41681903610 / 1000000000000)))) (orderedInterval (772675564 / 1000000000000) (772675840 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (368248452527199 / 4000000000000) 4 (IntervalRat.scale (631 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-81969459568 / 1000000000000) (-81969459237 / 1000000000000), orderedInterval (14445993180 / 1000000000000) (14445993511 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (999866183138597 / 4000000000000) 4 (IntervalRat.scale (631 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-27486155801 / 1000000000000) (-27486150887 / 1000000000000), orderedInterval (42379122956 / 1000000000000) (42379127870 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1365231791886469 / 4000000000000) 4 (IntervalRat.scale (631 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (14427972087 / 1000000000000) (14427972258 / 1000000000000), orderedInterval (-40728271861 / 1000000000000) (-40728271690 / 1000000000000)))) (orderedInterval (-1235725925 / 1000000000000) (-1235725825 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (577273009988703 / 4000000000000) 4 (IntervalRat.scale (631 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (36925376105 / 1000000000000) (36925376106 / 1000000000000), orderedInterval (55078485336 / 1000000000000) (55078485337 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2346582736364863 / 4000000000000) 4 (IntervalRat.scale (631 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (1546297889 / 1000000000000) (1546297890 / 1000000000000), orderedInterval (-32907176162 / 1000000000000) (-32907176161 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1567408517712017 / 4000000000000) 4 (IntervalRat.scale (631 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (2492318540 / 1000000000000) (2492318542 / 1000000000000), orderedInterval (-40232927146 / 1000000000000) (-40232927143 / 1000000000000)))) (orderedInterval (-2406547248 / 1000000000000) (-2406546797 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate444_chunkChecks4 :
    compactCertificate444.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate444.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate444_chunkChecks4_0
    compactCertificate444_chunkChecks4_1 compactCertificate444_chunkChecks4_2

theorem compactCertificate444_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate444.chunkCheck r b = true :=
  compactCertificate444.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate444_chunkChecks0
    · exact compactCertificate444_chunkChecks1
    · exact compactCertificate444_chunkChecks2
    · exact compactCertificate444_chunkChecks3
    · exact compactCertificate444_chunkChecks4)

theorem compactCertificate444_coefficient0 :
    compactCertificate444.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate444_coefficient1 :
    compactCertificate444.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate444_coefficient2 :
    compactCertificate444.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate444_coefficient3 :
    compactCertificate444.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate444_coefficient4 :
    compactCertificate444.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate444_coefficients : ∀ r : Fin 5,
    compactCertificate444.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate444_coefficient0
  · exact compactCertificate444_coefficient1
  · exact compactCertificate444_coefficient2
  · exact compactCertificate444_coefficient3
  · exact compactCertificate444_coefficient4

theorem compactCertificate444_lower : (1 : ℚ) ≤ compactCertificate444.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate444, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate444_proves {t : ℝ} (ht : t ∈ compactCertificate444.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate444.proves compactCertificate444_states compactCertificate444_chunks
    compactCertificate444_coefficients compactCertificate444_lower ht

end Erdos232
