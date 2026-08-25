/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate499 : CompactCertificate where
  left := 370
  right := 371
  center := 741 / 2
  grid := fun i =>
    match i.val with
    | 0 => 118
    | 1 => 87
    | 2 => 141
    | 3 => 25
    | 4 => 68
    | 5 => 185
    | 6 => 136
    | 7 => 233
    | 8 => 172
    | 9 => 264
    | 10 => 152
    | 11 => 270
    | 12 => 253
    | 13 => 180
    | 14 => 204
    | 15 => 170
    | 16 => 151
    | 17 => 218
    | 18 => 121
    | 19 => 102
    | 20 => 64
    | 21 => 34
    | 22 => 93
    | 23 => 128
    | 24 => 54
    | 25 => 219
    | _ => 147
  point := fun i =>
    match i.val with
    | 0 => 741 / 2
    | 1 => 1091634492394641 / 4000000000000
    | 2 => 353012165794353 / 800000000000
    | 3 => 318536222305587 / 4000000000000
    | 4 => 855633098938839 / 4000000000000
    | 5 => 2323210307960763 / 4000000000000
    | 6 => 1711266197878419 / 4000000000000
    | 7 => 2932283797662687 / 4000000000000
    | 8 => 2159906973695133 / 4000000000000
    | 9 => 3313852742654259 / 4000000000000
    | 10 => 1913253773026011 / 4000000000000
    | 11 => 3395102394630999 / 4000000000000
    | 12 => 3172145058163731 / 4000000000000
    | 13 => 2263792393307523 / 4000000000000
    | 14 => 2566899296816517 / 4000000000000
    | 15 => 2140013020981173 / 4000000000000
    | 16 => 1890766404120633 / 4000000000000
    | 17 => 548017800074667 / 800000000000
    | 18 => 1515846075603249 / 4000000000000
    | 19 => 1284999505824489 / 4000000000000
    | 20 => 804093026304867 / 4000000000000
    | 21 => 432443903839389 / 4000000000000
    | 22 => 1174169321245167 / 4000000000000
    | 23 => 1603227825337359 / 4000000000000
    | 24 => 677906973695133 / 4000000000000
    | 25 => 2755654211800893 / 4000000000000
    | _ => 1840649305268787 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (22617015800 / 1000000000000) (22617015801 / 1000000000000), orderedInterval (34707687558 / 1000000000000) (34707687559 / 1000000000000))
    | 1 => (orderedInterval (-17690415548 / 1000000000000) (-17690415547 / 1000000000000), orderedInterval (-44909478542 / 1000000000000) (-44909478541 / 1000000000000))
    | 2 => (orderedInterval (30086370724 / 1000000000000) (30086420873 / 1000000000000), orderedInterval (-23218660857 / 1000000000000) (-23218610708 / 1000000000000))
    | 3 => (orderedInterval (-85222301349 / 1000000000000) (-85222299700 / 1000000000000), orderedInterval (27578481424 / 1000000000000) (27578483073 / 1000000000000))
    | 4 => (orderedInterval (47717531723 / 1000000000000) (47717531725 / 1000000000000), orderedInterval (26330234065 / 1000000000000) (26330234066 / 1000000000000))
    | 5 => (orderedInterval (-12682515745 / 1000000000000) (-12682515744 / 1000000000000), orderedInterval (-30571064215 / 1000000000000) (-30571064214 / 1000000000000))
    | 6 => (orderedInterval (37596737611 / 1000000000000) (37596737624 / 1000000000000), orderedInterval (8590386649 / 1000000000000) (8590386662 / 1000000000000))
    | 7 => (orderedInterval (-28202181587 / 1000000000000) (-28202141013 / 1000000000000), orderedInterval (8567109094 / 1000000000000) (8567149667 / 1000000000000))
    | 8 => (orderedInterval (13622898406 / 1000000000000) (13622898407 / 1000000000000), orderedInterval (31505527520 / 1000000000000) (31505527521 / 1000000000000))
    | 9 => (orderedInterval (-3649267495 / 1000000000000) (-3649267494 / 1000000000000), orderedInterval (27481605201 / 1000000000000) (27481605202 / 1000000000000))
    | 10 => (orderedInterval (36481827885 / 1000000000000) (36481828378 / 1000000000000), orderedInterval (-246099960 / 1000000000000) (-246099466 / 1000000000000))
    | 11 => (orderedInterval (26602218297 / 1000000000000) (26602218530 / 1000000000000), orderedInterval (6493300969 / 1000000000000) (6493301203 / 1000000000000))
    | 12 => (orderedInterval (23863399895 / 1000000000000) (23863421796 / 1000000000000), orderedInterval (-15289218934 / 1000000000000) (-15289197033 / 1000000000000))
    | 13 => (orderedInterval (31791947141 / 1000000000000) (31791947149 / 1000000000000), orderedInterval (10655770248 / 1000000000000) (10655770256 / 1000000000000))
    | 14 => (orderedInterval (31450262985 / 1000000000000) (31450265320 / 1000000000000), orderedInterval (-1734879694 / 1000000000000) (-1734877359 / 1000000000000))
    | 15 => (orderedInterval (34124052796 / 1000000000000) (34124056357 / 1000000000000), orderedInterval (-5080126314 / 1000000000000) (-5080122754 / 1000000000000))
    | 16 => (orderedInterval (28832558419 / 1000000000000) (28832598075 / 1000000000000), orderedInterval (-22734691801 / 1000000000000) (-22734652145 / 1000000000000))
    | 17 => (orderedInterval (24623296833 / 1000000000000) (24623296834 / 1000000000000), orderedInterval (17955199648 / 1000000000000) (17955199649 / 1000000000000))
    | 18 => (orderedInterval (15435588885 / 1000000000000) (15435589129 / 1000000000000), orderedInterval (-37989428826 / 1000000000000) (-37989428583 / 1000000000000))
    | 19 => (orderedInterval (44505801937 / 1000000000000) (44505802154 / 1000000000000), orderedInterval (-1032461032 / 1000000000000) (-1032460815 / 1000000000000))
    | 20 => (orderedInterval (38198536958 / 1000000000000) (38198536959 / 1000000000000), orderedInterval (41230148163 / 1000000000000) (41230148164 / 1000000000000))
    | 21 => (orderedInterval (66961313261 / 1000000000000) (66961329300 / 1000000000000), orderedInterval (-37789352088 / 1000000000000) (-37789336048 / 1000000000000))
    | 22 => (orderedInterval (-38738454655 / 1000000000000) (-38738378907 / 1000000000000), orderedInterval (25913251071 / 1000000000000) (25913326819 / 1000000000000))
    | 23 => (orderedInterval (-20209990453 / 1000000000000) (-20209989160 / 1000000000000), orderedInterval (34374912955 / 1000000000000) (34374914249 / 1000000000000))
    | 24 => (orderedInterval (35381393206 / 1000000000000) (35381393207 / 1000000000000), orderedInterval (49941063357 / 1000000000000) (49941063358 / 1000000000000))
    | 25 => (orderedInterval (-30183243452 / 1000000000000) (-30183237389 / 1000000000000), orderedInterval (3636339300 / 1000000000000) (3636345363 / 1000000000000))
    | _ => (orderedInterval (28349097149 / 1000000000000) (28349127158 / 1000000000000), orderedInterval (-24109761269 / 1000000000000) (-24109731260 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (10565255475 / 1000000000000) (10565258445 / 1000000000000)
      | 1 => orderedInterval (3568447396 / 1000000000000) (3568447459 / 1000000000000)
      | 2 => orderedInterval (1199105431 / 1000000000000) (1199106704 / 1000000000000)
      | 3 => orderedInterval (7133096007 / 1000000000000) (7133096224 / 1000000000000)
      | 4 => orderedInterval (2416372751 / 1000000000000) (2416373204 / 1000000000000)
      | 5 => orderedInterval (-625486833 / 1000000000000) (-625484487 / 1000000000000)
      | 6 => orderedInterval (-3743496807 / 1000000000000) (-3743496663 / 1000000000000)
      | 7 => orderedInterval (1191274186 / 1000000000000) (1191276344 / 1000000000000)
      | _ => orderedInterval (-2648788521 / 1000000000000) (-2648782294 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (11825936359 / 1000000000000) (11825939894 / 1000000000000)
      | 1 => orderedInterval (3897615342 / 1000000000000) (3897615397 / 1000000000000)
      | 2 => orderedInterval (586888266 / 1000000000000) (586890779 / 1000000000000)
      | 3 => orderedInterval (-8827960874 / 1000000000000) (-8827960445 / 1000000000000)
      | 4 => orderedInterval (2145202906 / 1000000000000) (2145203846 / 1000000000000)
      | 5 => orderedInterval (2425158551 / 1000000000000) (2425161558 / 1000000000000)
      | 6 => orderedInterval (6991888612 / 1000000000000) (6991888748 / 1000000000000)
      | 7 => orderedInterval (-3112120849 / 1000000000000) (-3112119253 / 1000000000000)
      | _ => orderedInterval (5205675737 / 1000000000000) (5205683792 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-11411406934 / 1000000000000) (-11411402717 / 1000000000000)
      | 1 => orderedInterval (-2849589800 / 1000000000000) (-2849589729 / 1000000000000)
      | 2 => orderedInterval (-4106324559 / 1000000000000) (-4106319588 / 1000000000000)
      | 3 => orderedInterval (-27570204461 / 1000000000000) (-27570203573 / 1000000000000)
      | 4 => orderedInterval (-4569352671 / 1000000000000) (-4569350701 / 1000000000000)
      | 5 => orderedInterval (-297675029 / 1000000000000) (-297671165 / 1000000000000)
      | 6 => orderedInterval (4090928695 / 1000000000000) (4090928828 / 1000000000000)
      | 7 => orderedInterval (-2250625391 / 1000000000000) (-2250624127 / 1000000000000)
      | _ => orderedInterval (-348461863 / 1000000000000) (-348451237 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-11256973641 / 1000000000000) (-11256968619 / 1000000000000)
      | 1 => orderedInterval (-8546490093 / 1000000000000) (-8546489988 / 1000000000000)
      | 2 => orderedInterval (-299255364 / 1000000000000) (-299245540 / 1000000000000)
      | 3 => orderedInterval (43610859381 / 1000000000000) (43610861292 / 1000000000000)
      | 4 => orderedInterval (-6331497348 / 1000000000000) (-6331493200 / 1000000000000)
      | 5 => orderedInterval (-5430038813 / 1000000000000) (-5430033849 / 1000000000000)
      | 6 => orderedInterval (-6763448178 / 1000000000000) (-6763448049 / 1000000000000)
      | 7 => orderedInterval (3616368923 / 1000000000000) (3616369955 / 1000000000000)
      | _ => orderedInterval (-6791623360 / 1000000000000) (-6791609043 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (12529087347 / 1000000000000) (12529093341 / 1000000000000)
      | 1 => orderedInterval (5686358958 / 1000000000000) (5686359120 / 1000000000000)
      | 2 => orderedInterval (14818687737 / 1000000000000) (14818707186 / 1000000000000)
      | 3 => orderedInterval (127643598569 / 1000000000000) (127643602763 / 1000000000000)
      | 4 => orderedInterval (5926762569 / 1000000000000) (5926771349 / 1000000000000)
      | 5 => orderedInterval (4738462828 / 1000000000000) (4738469232 / 1000000000000)
      | 6 => orderedInterval (-3980835840 / 1000000000000) (-3980835712 / 1000000000000)
      | 7 => orderedInterval (2439098896 / 1000000000000) (2439099760 / 1000000000000)
      | _ => orderedInterval (16759279491 / 1000000000000) (16759299391 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (19055779085 / 1000000000000) (19055794936 / 1000000000000)
    | 1 => orderedInterval (21138284050 / 1000000000000) (21138304316 / 1000000000000)
    | 2 => orderedInterval (-49312712013 / 1000000000000) (-49312684009 / 1000000000000)
    | 3 => orderedInterval (1807901507 / 1000000000000) (1807942959 / 1000000000000)
    | _ => orderedInterval (186560500555 / 1000000000000) (186560566430 / 1000000000000)

theorem compactCertificate499_stateChecks0 :
    compactCertificate499.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 118 12 (741 / 2)) (orderedInterval (22617015800 / 1000000000000) (22617015801 / 1000000000000), orderedInterval (34707687558 / 1000000000000) (34707687559 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (1091634492394641 / 4000000000000)) (orderedInterval (-17690415548 / 1000000000000) (-17690415547 / 1000000000000), orderedInterval (-44909478542 / 1000000000000) (-44909478541 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 141 12 (353012165794353 / 800000000000)) (orderedInterval (30086370724 / 1000000000000) (30086420873 / 1000000000000), orderedInterval (-23218660857 / 1000000000000) (-23218610708 / 1000000000000))) = true
  rfl'

theorem compactCertificate499_stateChecks1 :
    compactCertificate499.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (318536222305587 / 4000000000000)) (orderedInterval (-85222301349 / 1000000000000) (-85222299700 / 1000000000000), orderedInterval (27578481424 / 1000000000000) (27578483073 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (855633098938839 / 4000000000000)) (orderedInterval (47717531723 / 1000000000000) (47717531725 / 1000000000000), orderedInterval (26330234065 / 1000000000000) (26330234066 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 185 12 (2323210307960763 / 4000000000000)) (orderedInterval (-12682515745 / 1000000000000) (-12682515744 / 1000000000000), orderedInterval (-30571064215 / 1000000000000) (-30571064214 / 1000000000000))) = true
  rfl'

theorem compactCertificate499_stateChecks2 :
    compactCertificate499.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 136 12 (1711266197878419 / 4000000000000)) (orderedInterval (37596737611 / 1000000000000) (37596737624 / 1000000000000), orderedInterval (8590386649 / 1000000000000) (8590386662 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 233 12 (2932283797662687 / 4000000000000)) (orderedInterval (-28202181587 / 1000000000000) (-28202141013 / 1000000000000), orderedInterval (8567109094 / 1000000000000) (8567149667 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 172 12 (2159906973695133 / 4000000000000)) (orderedInterval (13622898406 / 1000000000000) (13622898407 / 1000000000000), orderedInterval (31505527520 / 1000000000000) (31505527521 / 1000000000000))) = true
  rfl'

theorem compactCertificate499_stateChecks3 :
    compactCertificate499.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 264 12 (3313852742654259 / 4000000000000)) (orderedInterval (-3649267495 / 1000000000000) (-3649267494 / 1000000000000), orderedInterval (27481605201 / 1000000000000) (27481605202 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 152 12 (1913253773026011 / 4000000000000)) (orderedInterval (36481827885 / 1000000000000) (36481828378 / 1000000000000), orderedInterval (-246099960 / 1000000000000) (-246099466 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 270 12 (3395102394630999 / 4000000000000)) (orderedInterval (26602218297 / 1000000000000) (26602218530 / 1000000000000), orderedInterval (6493300969 / 1000000000000) (6493301203 / 1000000000000))) = true
  rfl'

theorem compactCertificate499_stateChecks4 :
    compactCertificate499.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 253 12 (3172145058163731 / 4000000000000)) (orderedInterval (23863399895 / 1000000000000) (23863421796 / 1000000000000), orderedInterval (-15289218934 / 1000000000000) (-15289197033 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 180 12 (2263792393307523 / 4000000000000)) (orderedInterval (31791947141 / 1000000000000) (31791947149 / 1000000000000), orderedInterval (10655770248 / 1000000000000) (10655770256 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 204 12 (2566899296816517 / 4000000000000)) (orderedInterval (31450262985 / 1000000000000) (31450265320 / 1000000000000), orderedInterval (-1734879694 / 1000000000000) (-1734877359 / 1000000000000))) = true
  rfl'

theorem compactCertificate499_stateChecks5 :
    compactCertificate499.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 170 12 (2140013020981173 / 4000000000000)) (orderedInterval (34124052796 / 1000000000000) (34124056357 / 1000000000000), orderedInterval (-5080126314 / 1000000000000) (-5080122754 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 151 12 (1890766404120633 / 4000000000000)) (orderedInterval (28832558419 / 1000000000000) (28832598075 / 1000000000000), orderedInterval (-22734691801 / 1000000000000) (-22734652145 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 218 12 (548017800074667 / 800000000000)) (orderedInterval (24623296833 / 1000000000000) (24623296834 / 1000000000000), orderedInterval (17955199648 / 1000000000000) (17955199649 / 1000000000000))) = true
  rfl'

theorem compactCertificate499_stateChecks6 :
    compactCertificate499.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 121 12 (1515846075603249 / 4000000000000)) (orderedInterval (15435588885 / 1000000000000) (15435589129 / 1000000000000), orderedInterval (-37989428826 / 1000000000000) (-37989428583 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 102 12 (1284999505824489 / 4000000000000)) (orderedInterval (44505801937 / 1000000000000) (44505802154 / 1000000000000), orderedInterval (-1032461032 / 1000000000000) (-1032460815 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (804093026304867 / 4000000000000)) (orderedInterval (38198536958 / 1000000000000) (38198536959 / 1000000000000), orderedInterval (41230148163 / 1000000000000) (41230148164 / 1000000000000))) = true
  rfl'

theorem compactCertificate499_stateChecks7 :
    compactCertificate499.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (432443903839389 / 4000000000000)) (orderedInterval (66961313261 / 1000000000000) (66961329300 / 1000000000000), orderedInterval (-37789352088 / 1000000000000) (-37789336048 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 93 12 (1174169321245167 / 4000000000000)) (orderedInterval (-38738454655 / 1000000000000) (-38738378907 / 1000000000000), orderedInterval (25913251071 / 1000000000000) (25913326819 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 128 12 (1603227825337359 / 4000000000000)) (orderedInterval (-20209990453 / 1000000000000) (-20209989160 / 1000000000000), orderedInterval (34374912955 / 1000000000000) (34374914249 / 1000000000000))) = true
  rfl'

theorem compactCertificate499_stateChecks8 :
    compactCertificate499.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (677906973695133 / 4000000000000)) (orderedInterval (35381393206 / 1000000000000) (35381393207 / 1000000000000), orderedInterval (49941063357 / 1000000000000) (49941063358 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 219 12 (2755654211800893 / 4000000000000)) (orderedInterval (-30183243452 / 1000000000000) (-30183237389 / 1000000000000), orderedInterval (3636339300 / 1000000000000) (3636345363 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 147 12 (1840649305268787 / 4000000000000)) (orderedInterval (28349097149 / 1000000000000) (28349127158 / 1000000000000), orderedInterval (-24109761269 / 1000000000000) (-24109731260 / 1000000000000))) = true
  rfl'

theorem compactCertificate499_states : ∀ j,
    BesselStateValid (compactCertificate499.point j) (compactCertificate499.state j) :=
  compactCertificate499.statesValid_of_checks3 compactCertificate499_stateChecks0
    compactCertificate499_stateChecks1 compactCertificate499_stateChecks2
    compactCertificate499_stateChecks3 compactCertificate499_stateChecks4
    compactCertificate499_stateChecks5 compactCertificate499_stateChecks6
    compactCertificate499_stateChecks7 compactCertificate499_stateChecks8

theorem compactCertificate499_chunkChecks0_0 :
    compactCertificate499.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (741 / 2) 0 (IntervalRat.scale (741 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (22617015800 / 1000000000000) (22617015801 / 1000000000000), orderedInterval (34707687558 / 1000000000000) (34707687559 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1091634492394641 / 4000000000000) 0 (IntervalRat.scale (741 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-17690415548 / 1000000000000) (-17690415547 / 1000000000000), orderedInterval (-44909478542 / 1000000000000) (-44909478541 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (353012165794353 / 800000000000) 0 (IntervalRat.scale (741 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (30086370724 / 1000000000000) (30086420873 / 1000000000000), orderedInterval (-23218660857 / 1000000000000) (-23218610708 / 1000000000000)))) (orderedInterval (10565255475 / 1000000000000) (10565258445 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (318536222305587 / 4000000000000) 0 (IntervalRat.scale (741 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-85222301349 / 1000000000000) (-85222299700 / 1000000000000), orderedInterval (27578481424 / 1000000000000) (27578483073 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (855633098938839 / 4000000000000) 0 (IntervalRat.scale (741 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (47717531723 / 1000000000000) (47717531725 / 1000000000000), orderedInterval (26330234065 / 1000000000000) (26330234066 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2323210307960763 / 4000000000000) 0 (IntervalRat.scale (741 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-12682515745 / 1000000000000) (-12682515744 / 1000000000000), orderedInterval (-30571064215 / 1000000000000) (-30571064214 / 1000000000000)))) (orderedInterval (3568447396 / 1000000000000) (3568447459 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1711266197878419 / 4000000000000) 0 (IntervalRat.scale (741 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (37596737611 / 1000000000000) (37596737624 / 1000000000000), orderedInterval (8590386649 / 1000000000000) (8590386662 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2932283797662687 / 4000000000000) 0 (IntervalRat.scale (741 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-28202181587 / 1000000000000) (-28202141013 / 1000000000000), orderedInterval (8567109094 / 1000000000000) (8567149667 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2159906973695133 / 4000000000000) 0 (IntervalRat.scale (741 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (13622898406 / 1000000000000) (13622898407 / 1000000000000), orderedInterval (31505527520 / 1000000000000) (31505527521 / 1000000000000)))) (orderedInterval (1199105431 / 1000000000000) (1199106704 / 1000000000000))) = true
  rfl'

theorem compactCertificate499_chunkChecks0_1 :
    compactCertificate499.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3313852742654259 / 4000000000000) 0 (IntervalRat.scale (741 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-3649267495 / 1000000000000) (-3649267494 / 1000000000000), orderedInterval (27481605201 / 1000000000000) (27481605202 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1913253773026011 / 4000000000000) 0 (IntervalRat.scale (741 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (36481827885 / 1000000000000) (36481828378 / 1000000000000), orderedInterval (-246099960 / 1000000000000) (-246099466 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3395102394630999 / 4000000000000) 0 (IntervalRat.scale (741 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (26602218297 / 1000000000000) (26602218530 / 1000000000000), orderedInterval (6493300969 / 1000000000000) (6493301203 / 1000000000000)))) (orderedInterval (7133096007 / 1000000000000) (7133096224 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3172145058163731 / 4000000000000) 0 (IntervalRat.scale (741 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (23863399895 / 1000000000000) (23863421796 / 1000000000000), orderedInterval (-15289218934 / 1000000000000) (-15289197033 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2263792393307523 / 4000000000000) 0 (IntervalRat.scale (741 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (31791947141 / 1000000000000) (31791947149 / 1000000000000), orderedInterval (10655770248 / 1000000000000) (10655770256 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2566899296816517 / 4000000000000) 0 (IntervalRat.scale (741 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (31450262985 / 1000000000000) (31450265320 / 1000000000000), orderedInterval (-1734879694 / 1000000000000) (-1734877359 / 1000000000000)))) (orderedInterval (2416372751 / 1000000000000) (2416373204 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2140013020981173 / 4000000000000) 0 (IntervalRat.scale (741 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (34124052796 / 1000000000000) (34124056357 / 1000000000000), orderedInterval (-5080126314 / 1000000000000) (-5080122754 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1890766404120633 / 4000000000000) 0 (IntervalRat.scale (741 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (28832558419 / 1000000000000) (28832598075 / 1000000000000), orderedInterval (-22734691801 / 1000000000000) (-22734652145 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (548017800074667 / 800000000000) 0 (IntervalRat.scale (741 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (24623296833 / 1000000000000) (24623296834 / 1000000000000), orderedInterval (17955199648 / 1000000000000) (17955199649 / 1000000000000)))) (orderedInterval (-625486833 / 1000000000000) (-625484487 / 1000000000000))) = true
  rfl'

theorem compactCertificate499_chunkChecks0_2 :
    compactCertificate499.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1515846075603249 / 4000000000000) 0 (IntervalRat.scale (741 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (15435588885 / 1000000000000) (15435589129 / 1000000000000), orderedInterval (-37989428826 / 1000000000000) (-37989428583 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1284999505824489 / 4000000000000) 0 (IntervalRat.scale (741 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (44505801937 / 1000000000000) (44505802154 / 1000000000000), orderedInterval (-1032461032 / 1000000000000) (-1032460815 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (804093026304867 / 4000000000000) 0 (IntervalRat.scale (741 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (38198536958 / 1000000000000) (38198536959 / 1000000000000), orderedInterval (41230148163 / 1000000000000) (41230148164 / 1000000000000)))) (orderedInterval (-3743496807 / 1000000000000) (-3743496663 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (432443903839389 / 4000000000000) 0 (IntervalRat.scale (741 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (66961313261 / 1000000000000) (66961329300 / 1000000000000), orderedInterval (-37789352088 / 1000000000000) (-37789336048 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1174169321245167 / 4000000000000) 0 (IntervalRat.scale (741 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-38738454655 / 1000000000000) (-38738378907 / 1000000000000), orderedInterval (25913251071 / 1000000000000) (25913326819 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1603227825337359 / 4000000000000) 0 (IntervalRat.scale (741 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-20209990453 / 1000000000000) (-20209989160 / 1000000000000), orderedInterval (34374912955 / 1000000000000) (34374914249 / 1000000000000)))) (orderedInterval (1191274186 / 1000000000000) (1191276344 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (677906973695133 / 4000000000000) 0 (IntervalRat.scale (741 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (35381393206 / 1000000000000) (35381393207 / 1000000000000), orderedInterval (49941063357 / 1000000000000) (49941063358 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2755654211800893 / 4000000000000) 0 (IntervalRat.scale (741 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-30183243452 / 1000000000000) (-30183237389 / 1000000000000), orderedInterval (3636339300 / 1000000000000) (3636345363 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1840649305268787 / 4000000000000) 0 (IntervalRat.scale (741 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (28349097149 / 1000000000000) (28349127158 / 1000000000000), orderedInterval (-24109761269 / 1000000000000) (-24109731260 / 1000000000000)))) (orderedInterval (-2648788521 / 1000000000000) (-2648782294 / 1000000000000))) = true
  rfl'

theorem compactCertificate499_chunkChecks0 :
    compactCertificate499.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate499.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate499_chunkChecks0_0
    compactCertificate499_chunkChecks0_1 compactCertificate499_chunkChecks0_2

theorem compactCertificate499_chunkChecks1_0 :
    compactCertificate499.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (741 / 2) 1 (IntervalRat.scale (741 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (22617015800 / 1000000000000) (22617015801 / 1000000000000), orderedInterval (34707687558 / 1000000000000) (34707687559 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1091634492394641 / 4000000000000) 1 (IntervalRat.scale (741 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-17690415548 / 1000000000000) (-17690415547 / 1000000000000), orderedInterval (-44909478542 / 1000000000000) (-44909478541 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (353012165794353 / 800000000000) 1 (IntervalRat.scale (741 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (30086370724 / 1000000000000) (30086420873 / 1000000000000), orderedInterval (-23218660857 / 1000000000000) (-23218610708 / 1000000000000)))) (orderedInterval (11825936359 / 1000000000000) (11825939894 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (318536222305587 / 4000000000000) 1 (IntervalRat.scale (741 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-85222301349 / 1000000000000) (-85222299700 / 1000000000000), orderedInterval (27578481424 / 1000000000000) (27578483073 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (855633098938839 / 4000000000000) 1 (IntervalRat.scale (741 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (47717531723 / 1000000000000) (47717531725 / 1000000000000), orderedInterval (26330234065 / 1000000000000) (26330234066 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2323210307960763 / 4000000000000) 1 (IntervalRat.scale (741 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-12682515745 / 1000000000000) (-12682515744 / 1000000000000), orderedInterval (-30571064215 / 1000000000000) (-30571064214 / 1000000000000)))) (orderedInterval (3897615342 / 1000000000000) (3897615397 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1711266197878419 / 4000000000000) 1 (IntervalRat.scale (741 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (37596737611 / 1000000000000) (37596737624 / 1000000000000), orderedInterval (8590386649 / 1000000000000) (8590386662 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2932283797662687 / 4000000000000) 1 (IntervalRat.scale (741 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-28202181587 / 1000000000000) (-28202141013 / 1000000000000), orderedInterval (8567109094 / 1000000000000) (8567149667 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2159906973695133 / 4000000000000) 1 (IntervalRat.scale (741 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (13622898406 / 1000000000000) (13622898407 / 1000000000000), orderedInterval (31505527520 / 1000000000000) (31505527521 / 1000000000000)))) (orderedInterval (586888266 / 1000000000000) (586890779 / 1000000000000))) = true
  rfl'

theorem compactCertificate499_chunkChecks1_1 :
    compactCertificate499.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3313852742654259 / 4000000000000) 1 (IntervalRat.scale (741 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-3649267495 / 1000000000000) (-3649267494 / 1000000000000), orderedInterval (27481605201 / 1000000000000) (27481605202 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1913253773026011 / 4000000000000) 1 (IntervalRat.scale (741 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (36481827885 / 1000000000000) (36481828378 / 1000000000000), orderedInterval (-246099960 / 1000000000000) (-246099466 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3395102394630999 / 4000000000000) 1 (IntervalRat.scale (741 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (26602218297 / 1000000000000) (26602218530 / 1000000000000), orderedInterval (6493300969 / 1000000000000) (6493301203 / 1000000000000)))) (orderedInterval (-8827960874 / 1000000000000) (-8827960445 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3172145058163731 / 4000000000000) 1 (IntervalRat.scale (741 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (23863399895 / 1000000000000) (23863421796 / 1000000000000), orderedInterval (-15289218934 / 1000000000000) (-15289197033 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2263792393307523 / 4000000000000) 1 (IntervalRat.scale (741 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (31791947141 / 1000000000000) (31791947149 / 1000000000000), orderedInterval (10655770248 / 1000000000000) (10655770256 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2566899296816517 / 4000000000000) 1 (IntervalRat.scale (741 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (31450262985 / 1000000000000) (31450265320 / 1000000000000), orderedInterval (-1734879694 / 1000000000000) (-1734877359 / 1000000000000)))) (orderedInterval (2145202906 / 1000000000000) (2145203846 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2140013020981173 / 4000000000000) 1 (IntervalRat.scale (741 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (34124052796 / 1000000000000) (34124056357 / 1000000000000), orderedInterval (-5080126314 / 1000000000000) (-5080122754 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1890766404120633 / 4000000000000) 1 (IntervalRat.scale (741 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (28832558419 / 1000000000000) (28832598075 / 1000000000000), orderedInterval (-22734691801 / 1000000000000) (-22734652145 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (548017800074667 / 800000000000) 1 (IntervalRat.scale (741 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (24623296833 / 1000000000000) (24623296834 / 1000000000000), orderedInterval (17955199648 / 1000000000000) (17955199649 / 1000000000000)))) (orderedInterval (2425158551 / 1000000000000) (2425161558 / 1000000000000))) = true
  rfl'

theorem compactCertificate499_chunkChecks1_2 :
    compactCertificate499.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1515846075603249 / 4000000000000) 1 (IntervalRat.scale (741 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (15435588885 / 1000000000000) (15435589129 / 1000000000000), orderedInterval (-37989428826 / 1000000000000) (-37989428583 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1284999505824489 / 4000000000000) 1 (IntervalRat.scale (741 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (44505801937 / 1000000000000) (44505802154 / 1000000000000), orderedInterval (-1032461032 / 1000000000000) (-1032460815 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (804093026304867 / 4000000000000) 1 (IntervalRat.scale (741 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (38198536958 / 1000000000000) (38198536959 / 1000000000000), orderedInterval (41230148163 / 1000000000000) (41230148164 / 1000000000000)))) (orderedInterval (6991888612 / 1000000000000) (6991888748 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (432443903839389 / 4000000000000) 1 (IntervalRat.scale (741 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (66961313261 / 1000000000000) (66961329300 / 1000000000000), orderedInterval (-37789352088 / 1000000000000) (-37789336048 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1174169321245167 / 4000000000000) 1 (IntervalRat.scale (741 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-38738454655 / 1000000000000) (-38738378907 / 1000000000000), orderedInterval (25913251071 / 1000000000000) (25913326819 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1603227825337359 / 4000000000000) 1 (IntervalRat.scale (741 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-20209990453 / 1000000000000) (-20209989160 / 1000000000000), orderedInterval (34374912955 / 1000000000000) (34374914249 / 1000000000000)))) (orderedInterval (-3112120849 / 1000000000000) (-3112119253 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (677906973695133 / 4000000000000) 1 (IntervalRat.scale (741 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (35381393206 / 1000000000000) (35381393207 / 1000000000000), orderedInterval (49941063357 / 1000000000000) (49941063358 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2755654211800893 / 4000000000000) 1 (IntervalRat.scale (741 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-30183243452 / 1000000000000) (-30183237389 / 1000000000000), orderedInterval (3636339300 / 1000000000000) (3636345363 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1840649305268787 / 4000000000000) 1 (IntervalRat.scale (741 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (28349097149 / 1000000000000) (28349127158 / 1000000000000), orderedInterval (-24109761269 / 1000000000000) (-24109731260 / 1000000000000)))) (orderedInterval (5205675737 / 1000000000000) (5205683792 / 1000000000000))) = true
  rfl'

theorem compactCertificate499_chunkChecks1 :
    compactCertificate499.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate499.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate499_chunkChecks1_0
    compactCertificate499_chunkChecks1_1 compactCertificate499_chunkChecks1_2

theorem compactCertificate499_chunkChecks2_0 :
    compactCertificate499.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (741 / 2) 2 (IntervalRat.scale (741 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (22617015800 / 1000000000000) (22617015801 / 1000000000000), orderedInterval (34707687558 / 1000000000000) (34707687559 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1091634492394641 / 4000000000000) 2 (IntervalRat.scale (741 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-17690415548 / 1000000000000) (-17690415547 / 1000000000000), orderedInterval (-44909478542 / 1000000000000) (-44909478541 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (353012165794353 / 800000000000) 2 (IntervalRat.scale (741 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (30086370724 / 1000000000000) (30086420873 / 1000000000000), orderedInterval (-23218660857 / 1000000000000) (-23218610708 / 1000000000000)))) (orderedInterval (-11411406934 / 1000000000000) (-11411402717 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (318536222305587 / 4000000000000) 2 (IntervalRat.scale (741 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-85222301349 / 1000000000000) (-85222299700 / 1000000000000), orderedInterval (27578481424 / 1000000000000) (27578483073 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (855633098938839 / 4000000000000) 2 (IntervalRat.scale (741 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (47717531723 / 1000000000000) (47717531725 / 1000000000000), orderedInterval (26330234065 / 1000000000000) (26330234066 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2323210307960763 / 4000000000000) 2 (IntervalRat.scale (741 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-12682515745 / 1000000000000) (-12682515744 / 1000000000000), orderedInterval (-30571064215 / 1000000000000) (-30571064214 / 1000000000000)))) (orderedInterval (-2849589800 / 1000000000000) (-2849589729 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1711266197878419 / 4000000000000) 2 (IntervalRat.scale (741 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (37596737611 / 1000000000000) (37596737624 / 1000000000000), orderedInterval (8590386649 / 1000000000000) (8590386662 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2932283797662687 / 4000000000000) 2 (IntervalRat.scale (741 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-28202181587 / 1000000000000) (-28202141013 / 1000000000000), orderedInterval (8567109094 / 1000000000000) (8567149667 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2159906973695133 / 4000000000000) 2 (IntervalRat.scale (741 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (13622898406 / 1000000000000) (13622898407 / 1000000000000), orderedInterval (31505527520 / 1000000000000) (31505527521 / 1000000000000)))) (orderedInterval (-4106324559 / 1000000000000) (-4106319588 / 1000000000000))) = true
  rfl'

theorem compactCertificate499_chunkChecks2_1 :
    compactCertificate499.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3313852742654259 / 4000000000000) 2 (IntervalRat.scale (741 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-3649267495 / 1000000000000) (-3649267494 / 1000000000000), orderedInterval (27481605201 / 1000000000000) (27481605202 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1913253773026011 / 4000000000000) 2 (IntervalRat.scale (741 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (36481827885 / 1000000000000) (36481828378 / 1000000000000), orderedInterval (-246099960 / 1000000000000) (-246099466 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3395102394630999 / 4000000000000) 2 (IntervalRat.scale (741 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (26602218297 / 1000000000000) (26602218530 / 1000000000000), orderedInterval (6493300969 / 1000000000000) (6493301203 / 1000000000000)))) (orderedInterval (-27570204461 / 1000000000000) (-27570203573 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3172145058163731 / 4000000000000) 2 (IntervalRat.scale (741 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (23863399895 / 1000000000000) (23863421796 / 1000000000000), orderedInterval (-15289218934 / 1000000000000) (-15289197033 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2263792393307523 / 4000000000000) 2 (IntervalRat.scale (741 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (31791947141 / 1000000000000) (31791947149 / 1000000000000), orderedInterval (10655770248 / 1000000000000) (10655770256 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2566899296816517 / 4000000000000) 2 (IntervalRat.scale (741 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (31450262985 / 1000000000000) (31450265320 / 1000000000000), orderedInterval (-1734879694 / 1000000000000) (-1734877359 / 1000000000000)))) (orderedInterval (-4569352671 / 1000000000000) (-4569350701 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2140013020981173 / 4000000000000) 2 (IntervalRat.scale (741 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (34124052796 / 1000000000000) (34124056357 / 1000000000000), orderedInterval (-5080126314 / 1000000000000) (-5080122754 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1890766404120633 / 4000000000000) 2 (IntervalRat.scale (741 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (28832558419 / 1000000000000) (28832598075 / 1000000000000), orderedInterval (-22734691801 / 1000000000000) (-22734652145 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (548017800074667 / 800000000000) 2 (IntervalRat.scale (741 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (24623296833 / 1000000000000) (24623296834 / 1000000000000), orderedInterval (17955199648 / 1000000000000) (17955199649 / 1000000000000)))) (orderedInterval (-297675029 / 1000000000000) (-297671165 / 1000000000000))) = true
  rfl'

theorem compactCertificate499_chunkChecks2_2 :
    compactCertificate499.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1515846075603249 / 4000000000000) 2 (IntervalRat.scale (741 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (15435588885 / 1000000000000) (15435589129 / 1000000000000), orderedInterval (-37989428826 / 1000000000000) (-37989428583 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1284999505824489 / 4000000000000) 2 (IntervalRat.scale (741 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (44505801937 / 1000000000000) (44505802154 / 1000000000000), orderedInterval (-1032461032 / 1000000000000) (-1032460815 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (804093026304867 / 4000000000000) 2 (IntervalRat.scale (741 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (38198536958 / 1000000000000) (38198536959 / 1000000000000), orderedInterval (41230148163 / 1000000000000) (41230148164 / 1000000000000)))) (orderedInterval (4090928695 / 1000000000000) (4090928828 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (432443903839389 / 4000000000000) 2 (IntervalRat.scale (741 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (66961313261 / 1000000000000) (66961329300 / 1000000000000), orderedInterval (-37789352088 / 1000000000000) (-37789336048 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1174169321245167 / 4000000000000) 2 (IntervalRat.scale (741 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-38738454655 / 1000000000000) (-38738378907 / 1000000000000), orderedInterval (25913251071 / 1000000000000) (25913326819 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1603227825337359 / 4000000000000) 2 (IntervalRat.scale (741 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-20209990453 / 1000000000000) (-20209989160 / 1000000000000), orderedInterval (34374912955 / 1000000000000) (34374914249 / 1000000000000)))) (orderedInterval (-2250625391 / 1000000000000) (-2250624127 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (677906973695133 / 4000000000000) 2 (IntervalRat.scale (741 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (35381393206 / 1000000000000) (35381393207 / 1000000000000), orderedInterval (49941063357 / 1000000000000) (49941063358 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2755654211800893 / 4000000000000) 2 (IntervalRat.scale (741 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-30183243452 / 1000000000000) (-30183237389 / 1000000000000), orderedInterval (3636339300 / 1000000000000) (3636345363 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1840649305268787 / 4000000000000) 2 (IntervalRat.scale (741 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (28349097149 / 1000000000000) (28349127158 / 1000000000000), orderedInterval (-24109761269 / 1000000000000) (-24109731260 / 1000000000000)))) (orderedInterval (-348461863 / 1000000000000) (-348451237 / 1000000000000))) = true
  rfl'

theorem compactCertificate499_chunkChecks2 :
    compactCertificate499.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate499.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate499_chunkChecks2_0
    compactCertificate499_chunkChecks2_1 compactCertificate499_chunkChecks2_2

theorem compactCertificate499_chunkChecks3_0 :
    compactCertificate499.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (741 / 2) 3 (IntervalRat.scale (741 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (22617015800 / 1000000000000) (22617015801 / 1000000000000), orderedInterval (34707687558 / 1000000000000) (34707687559 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1091634492394641 / 4000000000000) 3 (IntervalRat.scale (741 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-17690415548 / 1000000000000) (-17690415547 / 1000000000000), orderedInterval (-44909478542 / 1000000000000) (-44909478541 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (353012165794353 / 800000000000) 3 (IntervalRat.scale (741 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (30086370724 / 1000000000000) (30086420873 / 1000000000000), orderedInterval (-23218660857 / 1000000000000) (-23218610708 / 1000000000000)))) (orderedInterval (-11256973641 / 1000000000000) (-11256968619 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (318536222305587 / 4000000000000) 3 (IntervalRat.scale (741 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-85222301349 / 1000000000000) (-85222299700 / 1000000000000), orderedInterval (27578481424 / 1000000000000) (27578483073 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (855633098938839 / 4000000000000) 3 (IntervalRat.scale (741 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (47717531723 / 1000000000000) (47717531725 / 1000000000000), orderedInterval (26330234065 / 1000000000000) (26330234066 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2323210307960763 / 4000000000000) 3 (IntervalRat.scale (741 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-12682515745 / 1000000000000) (-12682515744 / 1000000000000), orderedInterval (-30571064215 / 1000000000000) (-30571064214 / 1000000000000)))) (orderedInterval (-8546490093 / 1000000000000) (-8546489988 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1711266197878419 / 4000000000000) 3 (IntervalRat.scale (741 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (37596737611 / 1000000000000) (37596737624 / 1000000000000), orderedInterval (8590386649 / 1000000000000) (8590386662 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2932283797662687 / 4000000000000) 3 (IntervalRat.scale (741 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-28202181587 / 1000000000000) (-28202141013 / 1000000000000), orderedInterval (8567109094 / 1000000000000) (8567149667 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2159906973695133 / 4000000000000) 3 (IntervalRat.scale (741 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (13622898406 / 1000000000000) (13622898407 / 1000000000000), orderedInterval (31505527520 / 1000000000000) (31505527521 / 1000000000000)))) (orderedInterval (-299255364 / 1000000000000) (-299245540 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate499_chunkChecks3_1 :
    compactCertificate499.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3313852742654259 / 4000000000000) 3 (IntervalRat.scale (741 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-3649267495 / 1000000000000) (-3649267494 / 1000000000000), orderedInterval (27481605201 / 1000000000000) (27481605202 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1913253773026011 / 4000000000000) 3 (IntervalRat.scale (741 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (36481827885 / 1000000000000) (36481828378 / 1000000000000), orderedInterval (-246099960 / 1000000000000) (-246099466 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3395102394630999 / 4000000000000) 3 (IntervalRat.scale (741 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (26602218297 / 1000000000000) (26602218530 / 1000000000000), orderedInterval (6493300969 / 1000000000000) (6493301203 / 1000000000000)))) (orderedInterval (43610859381 / 1000000000000) (43610861292 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3172145058163731 / 4000000000000) 3 (IntervalRat.scale (741 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (23863399895 / 1000000000000) (23863421796 / 1000000000000), orderedInterval (-15289218934 / 1000000000000) (-15289197033 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2263792393307523 / 4000000000000) 3 (IntervalRat.scale (741 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (31791947141 / 1000000000000) (31791947149 / 1000000000000), orderedInterval (10655770248 / 1000000000000) (10655770256 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2566899296816517 / 4000000000000) 3 (IntervalRat.scale (741 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (31450262985 / 1000000000000) (31450265320 / 1000000000000), orderedInterval (-1734879694 / 1000000000000) (-1734877359 / 1000000000000)))) (orderedInterval (-6331497348 / 1000000000000) (-6331493200 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2140013020981173 / 4000000000000) 3 (IntervalRat.scale (741 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (34124052796 / 1000000000000) (34124056357 / 1000000000000), orderedInterval (-5080126314 / 1000000000000) (-5080122754 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1890766404120633 / 4000000000000) 3 (IntervalRat.scale (741 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (28832558419 / 1000000000000) (28832598075 / 1000000000000), orderedInterval (-22734691801 / 1000000000000) (-22734652145 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (548017800074667 / 800000000000) 3 (IntervalRat.scale (741 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (24623296833 / 1000000000000) (24623296834 / 1000000000000), orderedInterval (17955199648 / 1000000000000) (17955199649 / 1000000000000)))) (orderedInterval (-5430038813 / 1000000000000) (-5430033849 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate499_chunkChecks3_2 :
    compactCertificate499.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1515846075603249 / 4000000000000) 3 (IntervalRat.scale (741 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (15435588885 / 1000000000000) (15435589129 / 1000000000000), orderedInterval (-37989428826 / 1000000000000) (-37989428583 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1284999505824489 / 4000000000000) 3 (IntervalRat.scale (741 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (44505801937 / 1000000000000) (44505802154 / 1000000000000), orderedInterval (-1032461032 / 1000000000000) (-1032460815 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (804093026304867 / 4000000000000) 3 (IntervalRat.scale (741 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (38198536958 / 1000000000000) (38198536959 / 1000000000000), orderedInterval (41230148163 / 1000000000000) (41230148164 / 1000000000000)))) (orderedInterval (-6763448178 / 1000000000000) (-6763448049 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (432443903839389 / 4000000000000) 3 (IntervalRat.scale (741 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (66961313261 / 1000000000000) (66961329300 / 1000000000000), orderedInterval (-37789352088 / 1000000000000) (-37789336048 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1174169321245167 / 4000000000000) 3 (IntervalRat.scale (741 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-38738454655 / 1000000000000) (-38738378907 / 1000000000000), orderedInterval (25913251071 / 1000000000000) (25913326819 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1603227825337359 / 4000000000000) 3 (IntervalRat.scale (741 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-20209990453 / 1000000000000) (-20209989160 / 1000000000000), orderedInterval (34374912955 / 1000000000000) (34374914249 / 1000000000000)))) (orderedInterval (3616368923 / 1000000000000) (3616369955 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (677906973695133 / 4000000000000) 3 (IntervalRat.scale (741 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (35381393206 / 1000000000000) (35381393207 / 1000000000000), orderedInterval (49941063357 / 1000000000000) (49941063358 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2755654211800893 / 4000000000000) 3 (IntervalRat.scale (741 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-30183243452 / 1000000000000) (-30183237389 / 1000000000000), orderedInterval (3636339300 / 1000000000000) (3636345363 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1840649305268787 / 4000000000000) 3 (IntervalRat.scale (741 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (28349097149 / 1000000000000) (28349127158 / 1000000000000), orderedInterval (-24109761269 / 1000000000000) (-24109731260 / 1000000000000)))) (orderedInterval (-6791623360 / 1000000000000) (-6791609043 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate499_chunkChecks3 :
    compactCertificate499.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate499.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate499_chunkChecks3_0
    compactCertificate499_chunkChecks3_1 compactCertificate499_chunkChecks3_2

theorem compactCertificate499_chunkChecks4_0 :
    compactCertificate499.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (741 / 2) 4 (IntervalRat.scale (741 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (22617015800 / 1000000000000) (22617015801 / 1000000000000), orderedInterval (34707687558 / 1000000000000) (34707687559 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1091634492394641 / 4000000000000) 4 (IntervalRat.scale (741 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-17690415548 / 1000000000000) (-17690415547 / 1000000000000), orderedInterval (-44909478542 / 1000000000000) (-44909478541 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (353012165794353 / 800000000000) 4 (IntervalRat.scale (741 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (30086370724 / 1000000000000) (30086420873 / 1000000000000), orderedInterval (-23218660857 / 1000000000000) (-23218610708 / 1000000000000)))) (orderedInterval (12529087347 / 1000000000000) (12529093341 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (318536222305587 / 4000000000000) 4 (IntervalRat.scale (741 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-85222301349 / 1000000000000) (-85222299700 / 1000000000000), orderedInterval (27578481424 / 1000000000000) (27578483073 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (855633098938839 / 4000000000000) 4 (IntervalRat.scale (741 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (47717531723 / 1000000000000) (47717531725 / 1000000000000), orderedInterval (26330234065 / 1000000000000) (26330234066 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2323210307960763 / 4000000000000) 4 (IntervalRat.scale (741 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-12682515745 / 1000000000000) (-12682515744 / 1000000000000), orderedInterval (-30571064215 / 1000000000000) (-30571064214 / 1000000000000)))) (orderedInterval (5686358958 / 1000000000000) (5686359120 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1711266197878419 / 4000000000000) 4 (IntervalRat.scale (741 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (37596737611 / 1000000000000) (37596737624 / 1000000000000), orderedInterval (8590386649 / 1000000000000) (8590386662 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2932283797662687 / 4000000000000) 4 (IntervalRat.scale (741 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-28202181587 / 1000000000000) (-28202141013 / 1000000000000), orderedInterval (8567109094 / 1000000000000) (8567149667 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2159906973695133 / 4000000000000) 4 (IntervalRat.scale (741 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (13622898406 / 1000000000000) (13622898407 / 1000000000000), orderedInterval (31505527520 / 1000000000000) (31505527521 / 1000000000000)))) (orderedInterval (14818687737 / 1000000000000) (14818707186 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate499_chunkChecks4_1 :
    compactCertificate499.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3313852742654259 / 4000000000000) 4 (IntervalRat.scale (741 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-3649267495 / 1000000000000) (-3649267494 / 1000000000000), orderedInterval (27481605201 / 1000000000000) (27481605202 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1913253773026011 / 4000000000000) 4 (IntervalRat.scale (741 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (36481827885 / 1000000000000) (36481828378 / 1000000000000), orderedInterval (-246099960 / 1000000000000) (-246099466 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3395102394630999 / 4000000000000) 4 (IntervalRat.scale (741 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (26602218297 / 1000000000000) (26602218530 / 1000000000000), orderedInterval (6493300969 / 1000000000000) (6493301203 / 1000000000000)))) (orderedInterval (127643598569 / 1000000000000) (127643602763 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3172145058163731 / 4000000000000) 4 (IntervalRat.scale (741 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (23863399895 / 1000000000000) (23863421796 / 1000000000000), orderedInterval (-15289218934 / 1000000000000) (-15289197033 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2263792393307523 / 4000000000000) 4 (IntervalRat.scale (741 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (31791947141 / 1000000000000) (31791947149 / 1000000000000), orderedInterval (10655770248 / 1000000000000) (10655770256 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2566899296816517 / 4000000000000) 4 (IntervalRat.scale (741 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (31450262985 / 1000000000000) (31450265320 / 1000000000000), orderedInterval (-1734879694 / 1000000000000) (-1734877359 / 1000000000000)))) (orderedInterval (5926762569 / 1000000000000) (5926771349 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2140013020981173 / 4000000000000) 4 (IntervalRat.scale (741 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (34124052796 / 1000000000000) (34124056357 / 1000000000000), orderedInterval (-5080126314 / 1000000000000) (-5080122754 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1890766404120633 / 4000000000000) 4 (IntervalRat.scale (741 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (28832558419 / 1000000000000) (28832598075 / 1000000000000), orderedInterval (-22734691801 / 1000000000000) (-22734652145 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (548017800074667 / 800000000000) 4 (IntervalRat.scale (741 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (24623296833 / 1000000000000) (24623296834 / 1000000000000), orderedInterval (17955199648 / 1000000000000) (17955199649 / 1000000000000)))) (orderedInterval (4738462828 / 1000000000000) (4738469232 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate499_chunkChecks4_2 :
    compactCertificate499.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1515846075603249 / 4000000000000) 4 (IntervalRat.scale (741 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (15435588885 / 1000000000000) (15435589129 / 1000000000000), orderedInterval (-37989428826 / 1000000000000) (-37989428583 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1284999505824489 / 4000000000000) 4 (IntervalRat.scale (741 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (44505801937 / 1000000000000) (44505802154 / 1000000000000), orderedInterval (-1032461032 / 1000000000000) (-1032460815 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (804093026304867 / 4000000000000) 4 (IntervalRat.scale (741 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (38198536958 / 1000000000000) (38198536959 / 1000000000000), orderedInterval (41230148163 / 1000000000000) (41230148164 / 1000000000000)))) (orderedInterval (-3980835840 / 1000000000000) (-3980835712 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (432443903839389 / 4000000000000) 4 (IntervalRat.scale (741 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (66961313261 / 1000000000000) (66961329300 / 1000000000000), orderedInterval (-37789352088 / 1000000000000) (-37789336048 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1174169321245167 / 4000000000000) 4 (IntervalRat.scale (741 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-38738454655 / 1000000000000) (-38738378907 / 1000000000000), orderedInterval (25913251071 / 1000000000000) (25913326819 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1603227825337359 / 4000000000000) 4 (IntervalRat.scale (741 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-20209990453 / 1000000000000) (-20209989160 / 1000000000000), orderedInterval (34374912955 / 1000000000000) (34374914249 / 1000000000000)))) (orderedInterval (2439098896 / 1000000000000) (2439099760 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (677906973695133 / 4000000000000) 4 (IntervalRat.scale (741 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (35381393206 / 1000000000000) (35381393207 / 1000000000000), orderedInterval (49941063357 / 1000000000000) (49941063358 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2755654211800893 / 4000000000000) 4 (IntervalRat.scale (741 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-30183243452 / 1000000000000) (-30183237389 / 1000000000000), orderedInterval (3636339300 / 1000000000000) (3636345363 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1840649305268787 / 4000000000000) 4 (IntervalRat.scale (741 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (28349097149 / 1000000000000) (28349127158 / 1000000000000), orderedInterval (-24109761269 / 1000000000000) (-24109731260 / 1000000000000)))) (orderedInterval (16759279491 / 1000000000000) (16759299391 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate499_chunkChecks4 :
    compactCertificate499.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate499.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate499_chunkChecks4_0
    compactCertificate499_chunkChecks4_1 compactCertificate499_chunkChecks4_2

theorem compactCertificate499_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate499.chunkCheck r b = true :=
  compactCertificate499.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate499_chunkChecks0
    · exact compactCertificate499_chunkChecks1
    · exact compactCertificate499_chunkChecks2
    · exact compactCertificate499_chunkChecks3
    · exact compactCertificate499_chunkChecks4)

theorem compactCertificate499_coefficient0 :
    compactCertificate499.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate499_coefficient1 :
    compactCertificate499.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate499_coefficient2 :
    compactCertificate499.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate499_coefficient3 :
    compactCertificate499.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate499_coefficient4 :
    compactCertificate499.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate499_coefficients : ∀ r : Fin 5,
    compactCertificate499.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate499_coefficient0
  · exact compactCertificate499_coefficient1
  · exact compactCertificate499_coefficient2
  · exact compactCertificate499_coefficient3
  · exact compactCertificate499_coefficient4

theorem compactCertificate499_lower : (1 : ℚ) ≤ compactCertificate499.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate499, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate499_proves {t : ℝ} (ht : t ∈ compactCertificate499.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate499.proves compactCertificate499_states compactCertificate499_chunks
    compactCertificate499_coefficients compactCertificate499_lower ht

end Erdos232
