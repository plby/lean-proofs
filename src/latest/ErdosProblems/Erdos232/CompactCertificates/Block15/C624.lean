/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate624 : CompactCertificate where
  left := 495
  right := 496
  center := 991 / 2
  grid := fun i =>
    match i.val with
    | 0 => 158
    | 1 => 116
    | 2 => 188
    | 3 => 34
    | 4 => 91
    | 5 => 247
    | 6 => 182
    | 7 => 312
    | 8 => 230
    | 9 => 353
    | 10 => 204
    | 11 => 362
    | 12 => 338
    | 13 => 241
    | 14 => 273
    | 15 => 228
    | 16 => 201
    | 17 => 292
    | 18 => 161
    | 19 => 137
    | 20 => 86
    | 21 => 46
    | 22 => 125
    | 23 => 171
    | 24 => 72
    | 25 => 293
    | _ => 196
  point := fun i =>
    match i.val with
    | 0 => 991 / 2
    | 1 => 1459932229369891 / 4000000000000
    | 2 => 472112086777603 / 800000000000
    | 3 => 426004583407337 / 4000000000000
    | 4 => 1144308233533589 / 4000000000000
    | 5 => 3107019453696513 / 4000000000000
    | 6 => 2288616467068169 / 4000000000000
    | 7 => 3921583324539437 / 4000000000000
    | 8 => 2888620527573383 / 4000000000000
    | 9 => 4431886731404009 / 4000000000000
    | 10 => 2558750997393761 / 4000000000000
    | 11 => 4540548546665749 / 4000000000000
    | 12 => 4242369436761481 / 4000000000000
    | 13 => 3027555009133273 / 4000000000000
    | 14 => 3432924700600767 / 4000000000000
    | 15 => 2862014714969423 / 4000000000000
    | 16 => 2528676796873883 / 4000000000000
    | 17 => 732909095646417 / 800000000000
    | 18 => 2027265129450499 / 4000000000000
    | 19 => 1718535101581739 / 4000000000000
    | 20 => 1075379472426617 / 4000000000000
    | 21 => 578342656821639 / 4000000000000
    | 22 => 1570312816941917 / 4000000000000
    | 23 => 2144127901362109 / 4000000000000
    | 24 => 906620527573383 / 4000000000000
    | 25 => 3685362110519143 / 4000000000000
    | _ => 2461651095170537 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-3096416146 / 1000000000000) (-3096416144 / 1000000000000), orderedInterval (35713285847 / 1000000000000) (35713285849 / 1000000000000))
    | 1 => (orderedInterval (40688660968 / 1000000000000) (40688660976 / 1000000000000), orderedInterval (9361059647 / 1000000000000) (9361059655 / 1000000000000))
    | 2 => (orderedInterval (9890412206 / 1000000000000) (9890412207 / 1000000000000), orderedInterval (31311589181 / 1000000000000) (31311589182 / 1000000000000))
    | 3 => (orderedInterval (35098722838 / 1000000000000) (35098722839 / 1000000000000), orderedInterval (68724296574 / 1000000000000) (68724296575 / 1000000000000))
    | 4 => (orderedInterval (-39100797630 / 1000000000000) (-39100797629 / 1000000000000), orderedInterval (-26322379183 / 1000000000000) (-26322379182 / 1000000000000))
    | 5 => (orderedInterval (-28628225442 / 1000000000000) (-28628222831 / 1000000000000), orderedInterval (-98408604 / 1000000000000) (-98405993 / 1000000000000))
    | 6 => (orderedInterval (30705851356 / 1000000000000) (30705851359 / 1000000000000), orderedInterval (13004752506 / 1000000000000) (13004752508 / 1000000000000))
    | 7 => (orderedInterval (21500202979 / 1000000000000) (21500202984 / 1000000000000), orderedInterval (13667155064 / 1000000000000) (13667155069 / 1000000000000))
    | 8 => (orderedInterval (10848651868 / 1000000000000) (10848651869 / 1000000000000), orderedInterval (27630548147 / 1000000000000) (27630548148 / 1000000000000))
    | 9 => (orderedInterval (5353527204 / 1000000000000) (5353527205 / 1000000000000), orderedInterval (-23367369696 / 1000000000000) (-23367369695 / 1000000000000))
    | 10 => (orderedInterval (-12631239726 / 1000000000000) (-12631239671 / 1000000000000), orderedInterval (28917587069 / 1000000000000) (28917587124 / 1000000000000))
    | 11 => (orderedInterval (-23021697238 / 1000000000000) (-23021607079 / 1000000000000), orderedInterval (5562945918 / 1000000000000) (5563036078 / 1000000000000))
    | 12 => (orderedInterval (-11328300767 / 1000000000000) (-11328300761 / 1000000000000), orderedInterval (21729034847 / 1000000000000) (21729034854 / 1000000000000))
    | 13 => (orderedInterval (-15162688274 / 1000000000000) (-15162688273 / 1000000000000), orderedInterval (-24712317919 / 1000000000000) (-24712317918 / 1000000000000))
    | 14 => (orderedInterval (-26642058523 / 1000000000000) (-26642058151 / 1000000000000), orderedInterval (-5639727341 / 1000000000000) (-5639726969 / 1000000000000))
    | 15 => (orderedInterval (172324869 / 1000000000000) (172324870 / 1000000000000), orderedInterval (29828071684 / 1000000000000) (29828071685 / 1000000000000))
    | 16 => (orderedInterval (-31641030675 / 1000000000000) (-31641030207 / 1000000000000), orderedInterval (-2400885096 / 1000000000000) (-2400884629 / 1000000000000))
    | 17 => (orderedInterval (-10831267511 / 1000000000000) (-10831267503 / 1000000000000), orderedInterval (24038805742 / 1000000000000) (24038805750 / 1000000000000))
    | 18 => (orderedInterval (-34473999269 / 1000000000000) (-34473991611 / 1000000000000), orderedInterval (8259488444 / 1000000000000) (8259496102 / 1000000000000))
    | 19 => (orderedInterval (-796344056 / 1000000000000) (-796344055 / 1000000000000), orderedInterval (-38484654185 / 1000000000000) (-38484654184 / 1000000000000))
    | 20 => (orderedInterval (-25317305672 / 1000000000000) (-25317302411 / 1000000000000), orderedInterval (41604487858 / 1000000000000) (41604491118 / 1000000000000))
    | 21 => (orderedInterval (50154037769 / 1000000000000) (50154037770 / 1000000000000), orderedInterval (43273444379 / 1000000000000) (43273444380 / 1000000000000))
    | 22 => (orderedInterval (-24823408300 / 1000000000000) (-24823408299 / 1000000000000), orderedInterval (-31677007827 / 1000000000000) (-31677007826 / 1000000000000))
    | 23 => (orderedInterval (13267857517 / 1000000000000) (13267857609 / 1000000000000), orderedInterval (-31818301972 / 1000000000000) (-31818301879 / 1000000000000))
    | 24 => (orderedInterval (50214999805 / 1000000000000) (50214999806 / 1000000000000), orderedInterval (16836436763 / 1000000000000) (16836436764 / 1000000000000))
    | 25 => (orderedInterval (-26224964321 / 1000000000000) (-26224952395 / 1000000000000), orderedInterval (1809400970 / 1000000000000) (1809412896 / 1000000000000))
    | _ => (orderedInterval (13868296383 / 1000000000000) (13868296384 / 1000000000000), orderedInterval (29008215052 / 1000000000000) (29008215053 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-267790934 / 1000000000000) (-267790898 / 1000000000000)
      | 1 => orderedInterval (226735404 / 1000000000000) (226735650 / 1000000000000)
      | 2 => orderedInterval (-400961785 / 1000000000000) (-400961757 / 1000000000000)
      | 3 => orderedInterval (-5159798071 / 1000000000000) (-5159785054 / 1000000000000)
      | 4 => orderedInterval (-1094492341 / 1000000000000) (-1094492280 / 1000000000000)
      | 5 => orderedInterval (1535377711 / 1000000000000) (1535377785 / 1000000000000)
      | 6 => orderedInterval (4732991933 / 1000000000000) (4732993388 / 1000000000000)
      | 7 => orderedInterval (-1379768581 / 1000000000000) (-1379768515 / 1000000000000)
      | _ => orderedInterval (-164590139 / 1000000000000) (-164589030 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (16408088875 / 1000000000000) (16408088915 / 1000000000000)
      | 1 => orderedInterval (-704169977 / 1000000000000) (-704169618 / 1000000000000)
      | 2 => orderedInterval (139156652 / 1000000000000) (139156701 / 1000000000000)
      | 3 => orderedInterval (13862053676 / 1000000000000) (13862083450 / 1000000000000)
      | 4 => orderedInterval (-4359838055 / 1000000000000) (-4359837955 / 1000000000000)
      | 5 => orderedInterval (1810654710 / 1000000000000) (1810654814 / 1000000000000)
      | 6 => orderedInterval (1272773824 / 1000000000000) (1272775249 / 1000000000000)
      | 7 => orderedInterval (2974207863 / 1000000000000) (2974207925 / 1000000000000)
      | _ => orderedInterval (-6987311663 / 1000000000000) (-6987309665 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (165228132 / 1000000000000) (165228177 / 1000000000000)
      | 1 => orderedInterval (-4506390095 / 1000000000000) (-4506389544 / 1000000000000)
      | 2 => orderedInterval (2038946391 / 1000000000000) (2038946478 / 1000000000000)
      | 3 => orderedInterval (23463612393 / 1000000000000) (23463680597 / 1000000000000)
      | 4 => orderedInterval (2012952793 / 1000000000000) (2012952958 / 1000000000000)
      | 5 => orderedInterval (-2007108092 / 1000000000000) (-2007107945 / 1000000000000)
      | 6 => orderedInterval (-5560599635 / 1000000000000) (-5560598210 / 1000000000000)
      | 7 => orderedInterval (909333521 / 1000000000000) (909333583 / 1000000000000)
      | _ => orderedInterval (-3416142965 / 1000000000000) (-3416139320 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-17294740705 / 1000000000000) (-17294740652 / 1000000000000)
      | 1 => orderedInterval (174504371 / 1000000000000) (174505227 / 1000000000000)
      | 2 => orderedInterval (1193937485 / 1000000000000) (1193937643 / 1000000000000)
      | 3 => orderedInterval (-60587260860 / 1000000000000) (-60587104706 / 1000000000000)
      | 4 => orderedInterval (12023603370 / 1000000000000) (12023603651 / 1000000000000)
      | 5 => orderedInterval (-5208550952 / 1000000000000) (-5208550738 / 1000000000000)
      | 6 => orderedInterval (-211851491 / 1000000000000) (-211850054 / 1000000000000)
      | 7 => orderedInterval (-3426597362 / 1000000000000) (-3426597298 / 1000000000000)
      | _ => orderedInterval (11371624746 / 1000000000000) (11371631433 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (121883920 / 1000000000000) (121883982 / 1000000000000)
      | 1 => orderedInterval (12130124272 / 1000000000000) (12130125611 / 1000000000000)
      | 2 => orderedInterval (-8985393808 / 1000000000000) (-8985393516 / 1000000000000)
      | 3 => orderedInterval (-116277121116 / 1000000000000) (-116276763220 / 1000000000000)
      | 4 => orderedInterval (-2348748949 / 1000000000000) (-2348748463 / 1000000000000)
      | 5 => orderedInterval (1586288988 / 1000000000000) (1586289311 / 1000000000000)
      | 6 => orderedInterval (5988071673 / 1000000000000) (5988073132 / 1000000000000)
      | 7 => orderedInterval (-1163612491 / 1000000000000) (-1163612424 / 1000000000000)
      | _ => orderedInterval (19294127458 / 1000000000000) (19294139793 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-1972296803 / 1000000000000) (-1972280711 / 1000000000000)
    | 1 => orderedInterval (24415615905 / 1000000000000) (24415649816 / 1000000000000)
    | 2 => orderedInterval (13099832443 / 1000000000000) (13099906774 / 1000000000000)
    | 3 => orderedInterval (-61965331398 / 1000000000000) (-61965165494 / 1000000000000)
    | _ => orderedInterval (-89654380053 / 1000000000000) (-89654005794 / 1000000000000)

theorem compactCertificate624_stateChecks0 :
    compactCertificate624.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 158 12 (991 / 2)) (orderedInterval (-3096416146 / 1000000000000) (-3096416144 / 1000000000000), orderedInterval (35713285847 / 1000000000000) (35713285849 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 116 12 (1459932229369891 / 4000000000000)) (orderedInterval (40688660968 / 1000000000000) (40688660976 / 1000000000000), orderedInterval (9361059647 / 1000000000000) (9361059655 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 188 12 (472112086777603 / 800000000000)) (orderedInterval (9890412206 / 1000000000000) (9890412207 / 1000000000000), orderedInterval (31311589181 / 1000000000000) (31311589182 / 1000000000000))) = true
  rfl'

theorem compactCertificate624_stateChecks1 :
    compactCertificate624.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (426004583407337 / 4000000000000)) (orderedInterval (35098722838 / 1000000000000) (35098722839 / 1000000000000), orderedInterval (68724296574 / 1000000000000) (68724296575 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 91 12 (1144308233533589 / 4000000000000)) (orderedInterval (-39100797630 / 1000000000000) (-39100797629 / 1000000000000), orderedInterval (-26322379183 / 1000000000000) (-26322379182 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 247 12 (3107019453696513 / 4000000000000)) (orderedInterval (-28628225442 / 1000000000000) (-28628222831 / 1000000000000), orderedInterval (-98408604 / 1000000000000) (-98405993 / 1000000000000))) = true
  rfl'

theorem compactCertificate624_stateChecks2 :
    compactCertificate624.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 182 12 (2288616467068169 / 4000000000000)) (orderedInterval (30705851356 / 1000000000000) (30705851359 / 1000000000000), orderedInterval (13004752506 / 1000000000000) (13004752508 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 312 12 (3921583324539437 / 4000000000000)) (orderedInterval (21500202979 / 1000000000000) (21500202984 / 1000000000000), orderedInterval (13667155064 / 1000000000000) (13667155069 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 230 12 (2888620527573383 / 4000000000000)) (orderedInterval (10848651868 / 1000000000000) (10848651869 / 1000000000000), orderedInterval (27630548147 / 1000000000000) (27630548148 / 1000000000000))) = true
  rfl'

theorem compactCertificate624_stateChecks3 :
    compactCertificate624.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 353 12 (4431886731404009 / 4000000000000)) (orderedInterval (5353527204 / 1000000000000) (5353527205 / 1000000000000), orderedInterval (-23367369696 / 1000000000000) (-23367369695 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 204 12 (2558750997393761 / 4000000000000)) (orderedInterval (-12631239726 / 1000000000000) (-12631239671 / 1000000000000), orderedInterval (28917587069 / 1000000000000) (28917587124 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 362 12 (4540548546665749 / 4000000000000)) (orderedInterval (-23021697238 / 1000000000000) (-23021607079 / 1000000000000), orderedInterval (5562945918 / 1000000000000) (5563036078 / 1000000000000))) = true
  rfl'

theorem compactCertificate624_stateChecks4 :
    compactCertificate624.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 338 12 (4242369436761481 / 4000000000000)) (orderedInterval (-11328300767 / 1000000000000) (-11328300761 / 1000000000000), orderedInterval (21729034847 / 1000000000000) (21729034854 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 241 12 (3027555009133273 / 4000000000000)) (orderedInterval (-15162688274 / 1000000000000) (-15162688273 / 1000000000000), orderedInterval (-24712317919 / 1000000000000) (-24712317918 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 273 12 (3432924700600767 / 4000000000000)) (orderedInterval (-26642058523 / 1000000000000) (-26642058151 / 1000000000000), orderedInterval (-5639727341 / 1000000000000) (-5639726969 / 1000000000000))) = true
  rfl'

theorem compactCertificate624_stateChecks5 :
    compactCertificate624.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 228 12 (2862014714969423 / 4000000000000)) (orderedInterval (172324869 / 1000000000000) (172324870 / 1000000000000), orderedInterval (29828071684 / 1000000000000) (29828071685 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 201 12 (2528676796873883 / 4000000000000)) (orderedInterval (-31641030675 / 1000000000000) (-31641030207 / 1000000000000), orderedInterval (-2400885096 / 1000000000000) (-2400884629 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 292 12 (732909095646417 / 800000000000)) (orderedInterval (-10831267511 / 1000000000000) (-10831267503 / 1000000000000), orderedInterval (24038805742 / 1000000000000) (24038805750 / 1000000000000))) = true
  rfl'

theorem compactCertificate624_stateChecks6 :
    compactCertificate624.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 161 12 (2027265129450499 / 4000000000000)) (orderedInterval (-34473999269 / 1000000000000) (-34473991611 / 1000000000000), orderedInterval (8259488444 / 1000000000000) (8259496102 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 137 12 (1718535101581739 / 4000000000000)) (orderedInterval (-796344056 / 1000000000000) (-796344055 / 1000000000000), orderedInterval (-38484654185 / 1000000000000) (-38484654184 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (1075379472426617 / 4000000000000)) (orderedInterval (-25317305672 / 1000000000000) (-25317302411 / 1000000000000), orderedInterval (41604487858 / 1000000000000) (41604491118 / 1000000000000))) = true
  rfl'

theorem compactCertificate624_stateChecks7 :
    compactCertificate624.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (578342656821639 / 4000000000000)) (orderedInterval (50154037769 / 1000000000000) (50154037770 / 1000000000000), orderedInterval (43273444379 / 1000000000000) (43273444380 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 125 12 (1570312816941917 / 4000000000000)) (orderedInterval (-24823408300 / 1000000000000) (-24823408299 / 1000000000000), orderedInterval (-31677007827 / 1000000000000) (-31677007826 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 171 12 (2144127901362109 / 4000000000000)) (orderedInterval (13267857517 / 1000000000000) (13267857609 / 1000000000000), orderedInterval (-31818301972 / 1000000000000) (-31818301879 / 1000000000000))) = true
  rfl'

theorem compactCertificate624_stateChecks8 :
    compactCertificate624.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (906620527573383 / 4000000000000)) (orderedInterval (50214999805 / 1000000000000) (50214999806 / 1000000000000), orderedInterval (16836436763 / 1000000000000) (16836436764 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 293 12 (3685362110519143 / 4000000000000)) (orderedInterval (-26224964321 / 1000000000000) (-26224952395 / 1000000000000), orderedInterval (1809400970 / 1000000000000) (1809412896 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 196 12 (2461651095170537 / 4000000000000)) (orderedInterval (13868296383 / 1000000000000) (13868296384 / 1000000000000), orderedInterval (29008215052 / 1000000000000) (29008215053 / 1000000000000))) = true
  rfl'

theorem compactCertificate624_states : ∀ j,
    BesselStateValid (compactCertificate624.point j) (compactCertificate624.state j) :=
  compactCertificate624.statesValid_of_checks3 compactCertificate624_stateChecks0
    compactCertificate624_stateChecks1 compactCertificate624_stateChecks2
    compactCertificate624_stateChecks3 compactCertificate624_stateChecks4
    compactCertificate624_stateChecks5 compactCertificate624_stateChecks6
    compactCertificate624_stateChecks7 compactCertificate624_stateChecks8

theorem compactCertificate624_chunkChecks0_0 :
    compactCertificate624.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (991 / 2) 0 (IntervalRat.scale (991 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-3096416146 / 1000000000000) (-3096416144 / 1000000000000), orderedInterval (35713285847 / 1000000000000) (35713285849 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1459932229369891 / 4000000000000) 0 (IntervalRat.scale (991 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (40688660968 / 1000000000000) (40688660976 / 1000000000000), orderedInterval (9361059647 / 1000000000000) (9361059655 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (472112086777603 / 800000000000) 0 (IntervalRat.scale (991 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (9890412206 / 1000000000000) (9890412207 / 1000000000000), orderedInterval (31311589181 / 1000000000000) (31311589182 / 1000000000000)))) (orderedInterval (-267790934 / 1000000000000) (-267790898 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (426004583407337 / 4000000000000) 0 (IntervalRat.scale (991 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (35098722838 / 1000000000000) (35098722839 / 1000000000000), orderedInterval (68724296574 / 1000000000000) (68724296575 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (1144308233533589 / 4000000000000) 0 (IntervalRat.scale (991 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-39100797630 / 1000000000000) (-39100797629 / 1000000000000), orderedInterval (-26322379183 / 1000000000000) (-26322379182 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (3107019453696513 / 4000000000000) 0 (IntervalRat.scale (991 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28628225442 / 1000000000000) (-28628222831 / 1000000000000), orderedInterval (-98408604 / 1000000000000) (-98405993 / 1000000000000)))) (orderedInterval (226735404 / 1000000000000) (226735650 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (2288616467068169 / 4000000000000) 0 (IntervalRat.scale (991 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (30705851356 / 1000000000000) (30705851359 / 1000000000000), orderedInterval (13004752506 / 1000000000000) (13004752508 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3921583324539437 / 4000000000000) 0 (IntervalRat.scale (991 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (21500202979 / 1000000000000) (21500202984 / 1000000000000), orderedInterval (13667155064 / 1000000000000) (13667155069 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2888620527573383 / 4000000000000) 0 (IntervalRat.scale (991 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (10848651868 / 1000000000000) (10848651869 / 1000000000000), orderedInterval (27630548147 / 1000000000000) (27630548148 / 1000000000000)))) (orderedInterval (-400961785 / 1000000000000) (-400961757 / 1000000000000))) = true
  rfl'

theorem compactCertificate624_chunkChecks0_1 :
    compactCertificate624.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (4431886731404009 / 4000000000000) 0 (IntervalRat.scale (991 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (5353527204 / 1000000000000) (5353527205 / 1000000000000), orderedInterval (-23367369696 / 1000000000000) (-23367369695 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2558750997393761 / 4000000000000) 0 (IntervalRat.scale (991 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-12631239726 / 1000000000000) (-12631239671 / 1000000000000), orderedInterval (28917587069 / 1000000000000) (28917587124 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (4540548546665749 / 4000000000000) 0 (IntervalRat.scale (991 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-23021697238 / 1000000000000) (-23021607079 / 1000000000000), orderedInterval (5562945918 / 1000000000000) (5563036078 / 1000000000000)))) (orderedInterval (-5159798071 / 1000000000000) (-5159785054 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (4242369436761481 / 4000000000000) 0 (IntervalRat.scale (991 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-11328300767 / 1000000000000) (-11328300761 / 1000000000000), orderedInterval (21729034847 / 1000000000000) (21729034854 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (3027555009133273 / 4000000000000) 0 (IntervalRat.scale (991 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-15162688274 / 1000000000000) (-15162688273 / 1000000000000), orderedInterval (-24712317919 / 1000000000000) (-24712317918 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (3432924700600767 / 4000000000000) 0 (IntervalRat.scale (991 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-26642058523 / 1000000000000) (-26642058151 / 1000000000000), orderedInterval (-5639727341 / 1000000000000) (-5639726969 / 1000000000000)))) (orderedInterval (-1094492341 / 1000000000000) (-1094492280 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2862014714969423 / 4000000000000) 0 (IntervalRat.scale (991 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (172324869 / 1000000000000) (172324870 / 1000000000000), orderedInterval (29828071684 / 1000000000000) (29828071685 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2528676796873883 / 4000000000000) 0 (IntervalRat.scale (991 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-31641030675 / 1000000000000) (-31641030207 / 1000000000000), orderedInterval (-2400885096 / 1000000000000) (-2400884629 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (732909095646417 / 800000000000) 0 (IntervalRat.scale (991 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-10831267511 / 1000000000000) (-10831267503 / 1000000000000), orderedInterval (24038805742 / 1000000000000) (24038805750 / 1000000000000)))) (orderedInterval (1535377711 / 1000000000000) (1535377785 / 1000000000000))) = true
  rfl'

theorem compactCertificate624_chunkChecks0_2 :
    compactCertificate624.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (2027265129450499 / 4000000000000) 0 (IntervalRat.scale (991 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-34473999269 / 1000000000000) (-34473991611 / 1000000000000), orderedInterval (8259488444 / 1000000000000) (8259496102 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1718535101581739 / 4000000000000) 0 (IntervalRat.scale (991 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-796344056 / 1000000000000) (-796344055 / 1000000000000), orderedInterval (-38484654185 / 1000000000000) (-38484654184 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (1075379472426617 / 4000000000000) 0 (IntervalRat.scale (991 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-25317305672 / 1000000000000) (-25317302411 / 1000000000000), orderedInterval (41604487858 / 1000000000000) (41604491118 / 1000000000000)))) (orderedInterval (4732991933 / 1000000000000) (4732993388 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (578342656821639 / 4000000000000) 0 (IntervalRat.scale (991 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (50154037769 / 1000000000000) (50154037770 / 1000000000000), orderedInterval (43273444379 / 1000000000000) (43273444380 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1570312816941917 / 4000000000000) 0 (IntervalRat.scale (991 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-24823408300 / 1000000000000) (-24823408299 / 1000000000000), orderedInterval (-31677007827 / 1000000000000) (-31677007826 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (2144127901362109 / 4000000000000) 0 (IntervalRat.scale (991 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (13267857517 / 1000000000000) (13267857609 / 1000000000000), orderedInterval (-31818301972 / 1000000000000) (-31818301879 / 1000000000000)))) (orderedInterval (-1379768581 / 1000000000000) (-1379768515 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (906620527573383 / 4000000000000) 0 (IntervalRat.scale (991 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (50214999805 / 1000000000000) (50214999806 / 1000000000000), orderedInterval (16836436763 / 1000000000000) (16836436764 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3685362110519143 / 4000000000000) 0 (IntervalRat.scale (991 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-26224964321 / 1000000000000) (-26224952395 / 1000000000000), orderedInterval (1809400970 / 1000000000000) (1809412896 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2461651095170537 / 4000000000000) 0 (IntervalRat.scale (991 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (13868296383 / 1000000000000) (13868296384 / 1000000000000), orderedInterval (29008215052 / 1000000000000) (29008215053 / 1000000000000)))) (orderedInterval (-164590139 / 1000000000000) (-164589030 / 1000000000000))) = true
  rfl'

theorem compactCertificate624_chunkChecks0 :
    compactCertificate624.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate624.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate624_chunkChecks0_0
    compactCertificate624_chunkChecks0_1 compactCertificate624_chunkChecks0_2

theorem compactCertificate624_chunkChecks1_0 :
    compactCertificate624.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (991 / 2) 1 (IntervalRat.scale (991 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-3096416146 / 1000000000000) (-3096416144 / 1000000000000), orderedInterval (35713285847 / 1000000000000) (35713285849 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1459932229369891 / 4000000000000) 1 (IntervalRat.scale (991 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (40688660968 / 1000000000000) (40688660976 / 1000000000000), orderedInterval (9361059647 / 1000000000000) (9361059655 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (472112086777603 / 800000000000) 1 (IntervalRat.scale (991 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (9890412206 / 1000000000000) (9890412207 / 1000000000000), orderedInterval (31311589181 / 1000000000000) (31311589182 / 1000000000000)))) (orderedInterval (16408088875 / 1000000000000) (16408088915 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (426004583407337 / 4000000000000) 1 (IntervalRat.scale (991 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (35098722838 / 1000000000000) (35098722839 / 1000000000000), orderedInterval (68724296574 / 1000000000000) (68724296575 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (1144308233533589 / 4000000000000) 1 (IntervalRat.scale (991 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-39100797630 / 1000000000000) (-39100797629 / 1000000000000), orderedInterval (-26322379183 / 1000000000000) (-26322379182 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (3107019453696513 / 4000000000000) 1 (IntervalRat.scale (991 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28628225442 / 1000000000000) (-28628222831 / 1000000000000), orderedInterval (-98408604 / 1000000000000) (-98405993 / 1000000000000)))) (orderedInterval (-704169977 / 1000000000000) (-704169618 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (2288616467068169 / 4000000000000) 1 (IntervalRat.scale (991 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (30705851356 / 1000000000000) (30705851359 / 1000000000000), orderedInterval (13004752506 / 1000000000000) (13004752508 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3921583324539437 / 4000000000000) 1 (IntervalRat.scale (991 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (21500202979 / 1000000000000) (21500202984 / 1000000000000), orderedInterval (13667155064 / 1000000000000) (13667155069 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2888620527573383 / 4000000000000) 1 (IntervalRat.scale (991 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (10848651868 / 1000000000000) (10848651869 / 1000000000000), orderedInterval (27630548147 / 1000000000000) (27630548148 / 1000000000000)))) (orderedInterval (139156652 / 1000000000000) (139156701 / 1000000000000))) = true
  rfl'

theorem compactCertificate624_chunkChecks1_1 :
    compactCertificate624.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (4431886731404009 / 4000000000000) 1 (IntervalRat.scale (991 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (5353527204 / 1000000000000) (5353527205 / 1000000000000), orderedInterval (-23367369696 / 1000000000000) (-23367369695 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2558750997393761 / 4000000000000) 1 (IntervalRat.scale (991 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-12631239726 / 1000000000000) (-12631239671 / 1000000000000), orderedInterval (28917587069 / 1000000000000) (28917587124 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (4540548546665749 / 4000000000000) 1 (IntervalRat.scale (991 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-23021697238 / 1000000000000) (-23021607079 / 1000000000000), orderedInterval (5562945918 / 1000000000000) (5563036078 / 1000000000000)))) (orderedInterval (13862053676 / 1000000000000) (13862083450 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (4242369436761481 / 4000000000000) 1 (IntervalRat.scale (991 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-11328300767 / 1000000000000) (-11328300761 / 1000000000000), orderedInterval (21729034847 / 1000000000000) (21729034854 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (3027555009133273 / 4000000000000) 1 (IntervalRat.scale (991 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-15162688274 / 1000000000000) (-15162688273 / 1000000000000), orderedInterval (-24712317919 / 1000000000000) (-24712317918 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (3432924700600767 / 4000000000000) 1 (IntervalRat.scale (991 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-26642058523 / 1000000000000) (-26642058151 / 1000000000000), orderedInterval (-5639727341 / 1000000000000) (-5639726969 / 1000000000000)))) (orderedInterval (-4359838055 / 1000000000000) (-4359837955 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2862014714969423 / 4000000000000) 1 (IntervalRat.scale (991 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (172324869 / 1000000000000) (172324870 / 1000000000000), orderedInterval (29828071684 / 1000000000000) (29828071685 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2528676796873883 / 4000000000000) 1 (IntervalRat.scale (991 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-31641030675 / 1000000000000) (-31641030207 / 1000000000000), orderedInterval (-2400885096 / 1000000000000) (-2400884629 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (732909095646417 / 800000000000) 1 (IntervalRat.scale (991 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-10831267511 / 1000000000000) (-10831267503 / 1000000000000), orderedInterval (24038805742 / 1000000000000) (24038805750 / 1000000000000)))) (orderedInterval (1810654710 / 1000000000000) (1810654814 / 1000000000000))) = true
  rfl'

theorem compactCertificate624_chunkChecks1_2 :
    compactCertificate624.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (2027265129450499 / 4000000000000) 1 (IntervalRat.scale (991 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-34473999269 / 1000000000000) (-34473991611 / 1000000000000), orderedInterval (8259488444 / 1000000000000) (8259496102 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1718535101581739 / 4000000000000) 1 (IntervalRat.scale (991 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-796344056 / 1000000000000) (-796344055 / 1000000000000), orderedInterval (-38484654185 / 1000000000000) (-38484654184 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (1075379472426617 / 4000000000000) 1 (IntervalRat.scale (991 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-25317305672 / 1000000000000) (-25317302411 / 1000000000000), orderedInterval (41604487858 / 1000000000000) (41604491118 / 1000000000000)))) (orderedInterval (1272773824 / 1000000000000) (1272775249 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (578342656821639 / 4000000000000) 1 (IntervalRat.scale (991 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (50154037769 / 1000000000000) (50154037770 / 1000000000000), orderedInterval (43273444379 / 1000000000000) (43273444380 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1570312816941917 / 4000000000000) 1 (IntervalRat.scale (991 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-24823408300 / 1000000000000) (-24823408299 / 1000000000000), orderedInterval (-31677007827 / 1000000000000) (-31677007826 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (2144127901362109 / 4000000000000) 1 (IntervalRat.scale (991 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (13267857517 / 1000000000000) (13267857609 / 1000000000000), orderedInterval (-31818301972 / 1000000000000) (-31818301879 / 1000000000000)))) (orderedInterval (2974207863 / 1000000000000) (2974207925 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (906620527573383 / 4000000000000) 1 (IntervalRat.scale (991 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (50214999805 / 1000000000000) (50214999806 / 1000000000000), orderedInterval (16836436763 / 1000000000000) (16836436764 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3685362110519143 / 4000000000000) 1 (IntervalRat.scale (991 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-26224964321 / 1000000000000) (-26224952395 / 1000000000000), orderedInterval (1809400970 / 1000000000000) (1809412896 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2461651095170537 / 4000000000000) 1 (IntervalRat.scale (991 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (13868296383 / 1000000000000) (13868296384 / 1000000000000), orderedInterval (29008215052 / 1000000000000) (29008215053 / 1000000000000)))) (orderedInterval (-6987311663 / 1000000000000) (-6987309665 / 1000000000000))) = true
  rfl'

theorem compactCertificate624_chunkChecks1 :
    compactCertificate624.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate624.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate624_chunkChecks1_0
    compactCertificate624_chunkChecks1_1 compactCertificate624_chunkChecks1_2

theorem compactCertificate624_chunkChecks2_0 :
    compactCertificate624.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (991 / 2) 2 (IntervalRat.scale (991 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-3096416146 / 1000000000000) (-3096416144 / 1000000000000), orderedInterval (35713285847 / 1000000000000) (35713285849 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1459932229369891 / 4000000000000) 2 (IntervalRat.scale (991 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (40688660968 / 1000000000000) (40688660976 / 1000000000000), orderedInterval (9361059647 / 1000000000000) (9361059655 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (472112086777603 / 800000000000) 2 (IntervalRat.scale (991 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (9890412206 / 1000000000000) (9890412207 / 1000000000000), orderedInterval (31311589181 / 1000000000000) (31311589182 / 1000000000000)))) (orderedInterval (165228132 / 1000000000000) (165228177 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (426004583407337 / 4000000000000) 2 (IntervalRat.scale (991 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (35098722838 / 1000000000000) (35098722839 / 1000000000000), orderedInterval (68724296574 / 1000000000000) (68724296575 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (1144308233533589 / 4000000000000) 2 (IntervalRat.scale (991 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-39100797630 / 1000000000000) (-39100797629 / 1000000000000), orderedInterval (-26322379183 / 1000000000000) (-26322379182 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (3107019453696513 / 4000000000000) 2 (IntervalRat.scale (991 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28628225442 / 1000000000000) (-28628222831 / 1000000000000), orderedInterval (-98408604 / 1000000000000) (-98405993 / 1000000000000)))) (orderedInterval (-4506390095 / 1000000000000) (-4506389544 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (2288616467068169 / 4000000000000) 2 (IntervalRat.scale (991 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (30705851356 / 1000000000000) (30705851359 / 1000000000000), orderedInterval (13004752506 / 1000000000000) (13004752508 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3921583324539437 / 4000000000000) 2 (IntervalRat.scale (991 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (21500202979 / 1000000000000) (21500202984 / 1000000000000), orderedInterval (13667155064 / 1000000000000) (13667155069 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2888620527573383 / 4000000000000) 2 (IntervalRat.scale (991 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (10848651868 / 1000000000000) (10848651869 / 1000000000000), orderedInterval (27630548147 / 1000000000000) (27630548148 / 1000000000000)))) (orderedInterval (2038946391 / 1000000000000) (2038946478 / 1000000000000))) = true
  rfl'

theorem compactCertificate624_chunkChecks2_1 :
    compactCertificate624.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (4431886731404009 / 4000000000000) 2 (IntervalRat.scale (991 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (5353527204 / 1000000000000) (5353527205 / 1000000000000), orderedInterval (-23367369696 / 1000000000000) (-23367369695 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2558750997393761 / 4000000000000) 2 (IntervalRat.scale (991 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-12631239726 / 1000000000000) (-12631239671 / 1000000000000), orderedInterval (28917587069 / 1000000000000) (28917587124 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (4540548546665749 / 4000000000000) 2 (IntervalRat.scale (991 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-23021697238 / 1000000000000) (-23021607079 / 1000000000000), orderedInterval (5562945918 / 1000000000000) (5563036078 / 1000000000000)))) (orderedInterval (23463612393 / 1000000000000) (23463680597 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (4242369436761481 / 4000000000000) 2 (IntervalRat.scale (991 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-11328300767 / 1000000000000) (-11328300761 / 1000000000000), orderedInterval (21729034847 / 1000000000000) (21729034854 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (3027555009133273 / 4000000000000) 2 (IntervalRat.scale (991 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-15162688274 / 1000000000000) (-15162688273 / 1000000000000), orderedInterval (-24712317919 / 1000000000000) (-24712317918 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (3432924700600767 / 4000000000000) 2 (IntervalRat.scale (991 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-26642058523 / 1000000000000) (-26642058151 / 1000000000000), orderedInterval (-5639727341 / 1000000000000) (-5639726969 / 1000000000000)))) (orderedInterval (2012952793 / 1000000000000) (2012952958 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2862014714969423 / 4000000000000) 2 (IntervalRat.scale (991 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (172324869 / 1000000000000) (172324870 / 1000000000000), orderedInterval (29828071684 / 1000000000000) (29828071685 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2528676796873883 / 4000000000000) 2 (IntervalRat.scale (991 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-31641030675 / 1000000000000) (-31641030207 / 1000000000000), orderedInterval (-2400885096 / 1000000000000) (-2400884629 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (732909095646417 / 800000000000) 2 (IntervalRat.scale (991 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-10831267511 / 1000000000000) (-10831267503 / 1000000000000), orderedInterval (24038805742 / 1000000000000) (24038805750 / 1000000000000)))) (orderedInterval (-2007108092 / 1000000000000) (-2007107945 / 1000000000000))) = true
  rfl'

theorem compactCertificate624_chunkChecks2_2 :
    compactCertificate624.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (2027265129450499 / 4000000000000) 2 (IntervalRat.scale (991 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-34473999269 / 1000000000000) (-34473991611 / 1000000000000), orderedInterval (8259488444 / 1000000000000) (8259496102 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1718535101581739 / 4000000000000) 2 (IntervalRat.scale (991 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-796344056 / 1000000000000) (-796344055 / 1000000000000), orderedInterval (-38484654185 / 1000000000000) (-38484654184 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (1075379472426617 / 4000000000000) 2 (IntervalRat.scale (991 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-25317305672 / 1000000000000) (-25317302411 / 1000000000000), orderedInterval (41604487858 / 1000000000000) (41604491118 / 1000000000000)))) (orderedInterval (-5560599635 / 1000000000000) (-5560598210 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (578342656821639 / 4000000000000) 2 (IntervalRat.scale (991 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (50154037769 / 1000000000000) (50154037770 / 1000000000000), orderedInterval (43273444379 / 1000000000000) (43273444380 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1570312816941917 / 4000000000000) 2 (IntervalRat.scale (991 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-24823408300 / 1000000000000) (-24823408299 / 1000000000000), orderedInterval (-31677007827 / 1000000000000) (-31677007826 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (2144127901362109 / 4000000000000) 2 (IntervalRat.scale (991 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (13267857517 / 1000000000000) (13267857609 / 1000000000000), orderedInterval (-31818301972 / 1000000000000) (-31818301879 / 1000000000000)))) (orderedInterval (909333521 / 1000000000000) (909333583 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (906620527573383 / 4000000000000) 2 (IntervalRat.scale (991 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (50214999805 / 1000000000000) (50214999806 / 1000000000000), orderedInterval (16836436763 / 1000000000000) (16836436764 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3685362110519143 / 4000000000000) 2 (IntervalRat.scale (991 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-26224964321 / 1000000000000) (-26224952395 / 1000000000000), orderedInterval (1809400970 / 1000000000000) (1809412896 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2461651095170537 / 4000000000000) 2 (IntervalRat.scale (991 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (13868296383 / 1000000000000) (13868296384 / 1000000000000), orderedInterval (29008215052 / 1000000000000) (29008215053 / 1000000000000)))) (orderedInterval (-3416142965 / 1000000000000) (-3416139320 / 1000000000000))) = true
  rfl'

theorem compactCertificate624_chunkChecks2 :
    compactCertificate624.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate624.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate624_chunkChecks2_0
    compactCertificate624_chunkChecks2_1 compactCertificate624_chunkChecks2_2

theorem compactCertificate624_chunkChecks3_0 :
    compactCertificate624.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (991 / 2) 3 (IntervalRat.scale (991 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-3096416146 / 1000000000000) (-3096416144 / 1000000000000), orderedInterval (35713285847 / 1000000000000) (35713285849 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1459932229369891 / 4000000000000) 3 (IntervalRat.scale (991 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (40688660968 / 1000000000000) (40688660976 / 1000000000000), orderedInterval (9361059647 / 1000000000000) (9361059655 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (472112086777603 / 800000000000) 3 (IntervalRat.scale (991 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (9890412206 / 1000000000000) (9890412207 / 1000000000000), orderedInterval (31311589181 / 1000000000000) (31311589182 / 1000000000000)))) (orderedInterval (-17294740705 / 1000000000000) (-17294740652 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (426004583407337 / 4000000000000) 3 (IntervalRat.scale (991 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (35098722838 / 1000000000000) (35098722839 / 1000000000000), orderedInterval (68724296574 / 1000000000000) (68724296575 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (1144308233533589 / 4000000000000) 3 (IntervalRat.scale (991 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-39100797630 / 1000000000000) (-39100797629 / 1000000000000), orderedInterval (-26322379183 / 1000000000000) (-26322379182 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (3107019453696513 / 4000000000000) 3 (IntervalRat.scale (991 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28628225442 / 1000000000000) (-28628222831 / 1000000000000), orderedInterval (-98408604 / 1000000000000) (-98405993 / 1000000000000)))) (orderedInterval (174504371 / 1000000000000) (174505227 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (2288616467068169 / 4000000000000) 3 (IntervalRat.scale (991 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (30705851356 / 1000000000000) (30705851359 / 1000000000000), orderedInterval (13004752506 / 1000000000000) (13004752508 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3921583324539437 / 4000000000000) 3 (IntervalRat.scale (991 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (21500202979 / 1000000000000) (21500202984 / 1000000000000), orderedInterval (13667155064 / 1000000000000) (13667155069 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2888620527573383 / 4000000000000) 3 (IntervalRat.scale (991 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (10848651868 / 1000000000000) (10848651869 / 1000000000000), orderedInterval (27630548147 / 1000000000000) (27630548148 / 1000000000000)))) (orderedInterval (1193937485 / 1000000000000) (1193937643 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate624_chunkChecks3_1 :
    compactCertificate624.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (4431886731404009 / 4000000000000) 3 (IntervalRat.scale (991 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (5353527204 / 1000000000000) (5353527205 / 1000000000000), orderedInterval (-23367369696 / 1000000000000) (-23367369695 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2558750997393761 / 4000000000000) 3 (IntervalRat.scale (991 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-12631239726 / 1000000000000) (-12631239671 / 1000000000000), orderedInterval (28917587069 / 1000000000000) (28917587124 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (4540548546665749 / 4000000000000) 3 (IntervalRat.scale (991 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-23021697238 / 1000000000000) (-23021607079 / 1000000000000), orderedInterval (5562945918 / 1000000000000) (5563036078 / 1000000000000)))) (orderedInterval (-60587260860 / 1000000000000) (-60587104706 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (4242369436761481 / 4000000000000) 3 (IntervalRat.scale (991 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-11328300767 / 1000000000000) (-11328300761 / 1000000000000), orderedInterval (21729034847 / 1000000000000) (21729034854 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (3027555009133273 / 4000000000000) 3 (IntervalRat.scale (991 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-15162688274 / 1000000000000) (-15162688273 / 1000000000000), orderedInterval (-24712317919 / 1000000000000) (-24712317918 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (3432924700600767 / 4000000000000) 3 (IntervalRat.scale (991 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-26642058523 / 1000000000000) (-26642058151 / 1000000000000), orderedInterval (-5639727341 / 1000000000000) (-5639726969 / 1000000000000)))) (orderedInterval (12023603370 / 1000000000000) (12023603651 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2862014714969423 / 4000000000000) 3 (IntervalRat.scale (991 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (172324869 / 1000000000000) (172324870 / 1000000000000), orderedInterval (29828071684 / 1000000000000) (29828071685 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2528676796873883 / 4000000000000) 3 (IntervalRat.scale (991 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-31641030675 / 1000000000000) (-31641030207 / 1000000000000), orderedInterval (-2400885096 / 1000000000000) (-2400884629 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (732909095646417 / 800000000000) 3 (IntervalRat.scale (991 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-10831267511 / 1000000000000) (-10831267503 / 1000000000000), orderedInterval (24038805742 / 1000000000000) (24038805750 / 1000000000000)))) (orderedInterval (-5208550952 / 1000000000000) (-5208550738 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate624_chunkChecks3_2 :
    compactCertificate624.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (2027265129450499 / 4000000000000) 3 (IntervalRat.scale (991 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-34473999269 / 1000000000000) (-34473991611 / 1000000000000), orderedInterval (8259488444 / 1000000000000) (8259496102 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1718535101581739 / 4000000000000) 3 (IntervalRat.scale (991 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-796344056 / 1000000000000) (-796344055 / 1000000000000), orderedInterval (-38484654185 / 1000000000000) (-38484654184 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (1075379472426617 / 4000000000000) 3 (IntervalRat.scale (991 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-25317305672 / 1000000000000) (-25317302411 / 1000000000000), orderedInterval (41604487858 / 1000000000000) (41604491118 / 1000000000000)))) (orderedInterval (-211851491 / 1000000000000) (-211850054 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (578342656821639 / 4000000000000) 3 (IntervalRat.scale (991 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (50154037769 / 1000000000000) (50154037770 / 1000000000000), orderedInterval (43273444379 / 1000000000000) (43273444380 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1570312816941917 / 4000000000000) 3 (IntervalRat.scale (991 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-24823408300 / 1000000000000) (-24823408299 / 1000000000000), orderedInterval (-31677007827 / 1000000000000) (-31677007826 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (2144127901362109 / 4000000000000) 3 (IntervalRat.scale (991 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (13267857517 / 1000000000000) (13267857609 / 1000000000000), orderedInterval (-31818301972 / 1000000000000) (-31818301879 / 1000000000000)))) (orderedInterval (-3426597362 / 1000000000000) (-3426597298 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (906620527573383 / 4000000000000) 3 (IntervalRat.scale (991 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (50214999805 / 1000000000000) (50214999806 / 1000000000000), orderedInterval (16836436763 / 1000000000000) (16836436764 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3685362110519143 / 4000000000000) 3 (IntervalRat.scale (991 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-26224964321 / 1000000000000) (-26224952395 / 1000000000000), orderedInterval (1809400970 / 1000000000000) (1809412896 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2461651095170537 / 4000000000000) 3 (IntervalRat.scale (991 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (13868296383 / 1000000000000) (13868296384 / 1000000000000), orderedInterval (29008215052 / 1000000000000) (29008215053 / 1000000000000)))) (orderedInterval (11371624746 / 1000000000000) (11371631433 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate624_chunkChecks3 :
    compactCertificate624.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate624.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate624_chunkChecks3_0
    compactCertificate624_chunkChecks3_1 compactCertificate624_chunkChecks3_2

theorem compactCertificate624_chunkChecks4_0 :
    compactCertificate624.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (991 / 2) 4 (IntervalRat.scale (991 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-3096416146 / 1000000000000) (-3096416144 / 1000000000000), orderedInterval (35713285847 / 1000000000000) (35713285849 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1459932229369891 / 4000000000000) 4 (IntervalRat.scale (991 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (40688660968 / 1000000000000) (40688660976 / 1000000000000), orderedInterval (9361059647 / 1000000000000) (9361059655 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (472112086777603 / 800000000000) 4 (IntervalRat.scale (991 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (9890412206 / 1000000000000) (9890412207 / 1000000000000), orderedInterval (31311589181 / 1000000000000) (31311589182 / 1000000000000)))) (orderedInterval (121883920 / 1000000000000) (121883982 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (426004583407337 / 4000000000000) 4 (IntervalRat.scale (991 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (35098722838 / 1000000000000) (35098722839 / 1000000000000), orderedInterval (68724296574 / 1000000000000) (68724296575 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (1144308233533589 / 4000000000000) 4 (IntervalRat.scale (991 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-39100797630 / 1000000000000) (-39100797629 / 1000000000000), orderedInterval (-26322379183 / 1000000000000) (-26322379182 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (3107019453696513 / 4000000000000) 4 (IntervalRat.scale (991 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28628225442 / 1000000000000) (-28628222831 / 1000000000000), orderedInterval (-98408604 / 1000000000000) (-98405993 / 1000000000000)))) (orderedInterval (12130124272 / 1000000000000) (12130125611 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (2288616467068169 / 4000000000000) 4 (IntervalRat.scale (991 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (30705851356 / 1000000000000) (30705851359 / 1000000000000), orderedInterval (13004752506 / 1000000000000) (13004752508 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3921583324539437 / 4000000000000) 4 (IntervalRat.scale (991 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (21500202979 / 1000000000000) (21500202984 / 1000000000000), orderedInterval (13667155064 / 1000000000000) (13667155069 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2888620527573383 / 4000000000000) 4 (IntervalRat.scale (991 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (10848651868 / 1000000000000) (10848651869 / 1000000000000), orderedInterval (27630548147 / 1000000000000) (27630548148 / 1000000000000)))) (orderedInterval (-8985393808 / 1000000000000) (-8985393516 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate624_chunkChecks4_1 :
    compactCertificate624.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (4431886731404009 / 4000000000000) 4 (IntervalRat.scale (991 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (5353527204 / 1000000000000) (5353527205 / 1000000000000), orderedInterval (-23367369696 / 1000000000000) (-23367369695 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2558750997393761 / 4000000000000) 4 (IntervalRat.scale (991 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-12631239726 / 1000000000000) (-12631239671 / 1000000000000), orderedInterval (28917587069 / 1000000000000) (28917587124 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (4540548546665749 / 4000000000000) 4 (IntervalRat.scale (991 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-23021697238 / 1000000000000) (-23021607079 / 1000000000000), orderedInterval (5562945918 / 1000000000000) (5563036078 / 1000000000000)))) (orderedInterval (-116277121116 / 1000000000000) (-116276763220 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (4242369436761481 / 4000000000000) 4 (IntervalRat.scale (991 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-11328300767 / 1000000000000) (-11328300761 / 1000000000000), orderedInterval (21729034847 / 1000000000000) (21729034854 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (3027555009133273 / 4000000000000) 4 (IntervalRat.scale (991 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-15162688274 / 1000000000000) (-15162688273 / 1000000000000), orderedInterval (-24712317919 / 1000000000000) (-24712317918 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (3432924700600767 / 4000000000000) 4 (IntervalRat.scale (991 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-26642058523 / 1000000000000) (-26642058151 / 1000000000000), orderedInterval (-5639727341 / 1000000000000) (-5639726969 / 1000000000000)))) (orderedInterval (-2348748949 / 1000000000000) (-2348748463 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2862014714969423 / 4000000000000) 4 (IntervalRat.scale (991 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (172324869 / 1000000000000) (172324870 / 1000000000000), orderedInterval (29828071684 / 1000000000000) (29828071685 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2528676796873883 / 4000000000000) 4 (IntervalRat.scale (991 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-31641030675 / 1000000000000) (-31641030207 / 1000000000000), orderedInterval (-2400885096 / 1000000000000) (-2400884629 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (732909095646417 / 800000000000) 4 (IntervalRat.scale (991 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-10831267511 / 1000000000000) (-10831267503 / 1000000000000), orderedInterval (24038805742 / 1000000000000) (24038805750 / 1000000000000)))) (orderedInterval (1586288988 / 1000000000000) (1586289311 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate624_chunkChecks4_2 :
    compactCertificate624.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (2027265129450499 / 4000000000000) 4 (IntervalRat.scale (991 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-34473999269 / 1000000000000) (-34473991611 / 1000000000000), orderedInterval (8259488444 / 1000000000000) (8259496102 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1718535101581739 / 4000000000000) 4 (IntervalRat.scale (991 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-796344056 / 1000000000000) (-796344055 / 1000000000000), orderedInterval (-38484654185 / 1000000000000) (-38484654184 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (1075379472426617 / 4000000000000) 4 (IntervalRat.scale (991 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-25317305672 / 1000000000000) (-25317302411 / 1000000000000), orderedInterval (41604487858 / 1000000000000) (41604491118 / 1000000000000)))) (orderedInterval (5988071673 / 1000000000000) (5988073132 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (578342656821639 / 4000000000000) 4 (IntervalRat.scale (991 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (50154037769 / 1000000000000) (50154037770 / 1000000000000), orderedInterval (43273444379 / 1000000000000) (43273444380 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1570312816941917 / 4000000000000) 4 (IntervalRat.scale (991 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-24823408300 / 1000000000000) (-24823408299 / 1000000000000), orderedInterval (-31677007827 / 1000000000000) (-31677007826 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (2144127901362109 / 4000000000000) 4 (IntervalRat.scale (991 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (13267857517 / 1000000000000) (13267857609 / 1000000000000), orderedInterval (-31818301972 / 1000000000000) (-31818301879 / 1000000000000)))) (orderedInterval (-1163612491 / 1000000000000) (-1163612424 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (906620527573383 / 4000000000000) 4 (IntervalRat.scale (991 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (50214999805 / 1000000000000) (50214999806 / 1000000000000), orderedInterval (16836436763 / 1000000000000) (16836436764 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3685362110519143 / 4000000000000) 4 (IntervalRat.scale (991 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-26224964321 / 1000000000000) (-26224952395 / 1000000000000), orderedInterval (1809400970 / 1000000000000) (1809412896 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2461651095170537 / 4000000000000) 4 (IntervalRat.scale (991 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (13868296383 / 1000000000000) (13868296384 / 1000000000000), orderedInterval (29008215052 / 1000000000000) (29008215053 / 1000000000000)))) (orderedInterval (19294127458 / 1000000000000) (19294139793 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate624_chunkChecks4 :
    compactCertificate624.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate624.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate624_chunkChecks4_0
    compactCertificate624_chunkChecks4_1 compactCertificate624_chunkChecks4_2

theorem compactCertificate624_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate624.chunkCheck r b = true :=
  compactCertificate624.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate624_chunkChecks0
    · exact compactCertificate624_chunkChecks1
    · exact compactCertificate624_chunkChecks2
    · exact compactCertificate624_chunkChecks3
    · exact compactCertificate624_chunkChecks4)

theorem compactCertificate624_coefficient0 :
    compactCertificate624.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate624_coefficient1 :
    compactCertificate624.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate624_coefficient2 :
    compactCertificate624.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate624_coefficient3 :
    compactCertificate624.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate624_coefficient4 :
    compactCertificate624.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate624_coefficients : ∀ r : Fin 5,
    compactCertificate624.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate624_coefficient0
  · exact compactCertificate624_coefficient1
  · exact compactCertificate624_coefficient2
  · exact compactCertificate624_coefficient3
  · exact compactCertificate624_coefficient4

theorem compactCertificate624_lower : (1 : ℚ) ≤ compactCertificate624.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate624, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate624_proves {t : ℝ} (ht : t ∈ compactCertificate624.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate624.proves compactCertificate624_states compactCertificate624_chunks
    compactCertificate624_coefficients compactCertificate624_lower ht

end Erdos232
