/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate435 : CompactCertificate where
  left := 306
  right := 307
  center := 613 / 2
  grid := fun i =>
    match i.val with
    | 0 => 98
    | 1 => 72
    | 2 => 116
    | 3 => 21
    | 4 => 56
    | 5 => 153
    | 6 => 113
    | 7 => 193
    | 8 => 142
    | 9 => 218
    | 10 => 126
    | 11 => 224
    | 12 => 209
    | 13 => 149
    | 14 => 169
    | 15 => 141
    | 16 => 125
    | 17 => 180
    | 18 => 100
    | 19 => 85
    | 20 => 53
    | 21 => 28
    | 22 => 77
    | 23 => 106
    | 24 => 45
    | 25 => 182
    | _ => 121
  point := fun i =>
    match i.val with
    | 0 => 613 / 2
    | 1 => 903066051063313 / 4000000000000
    | 2 => 292033006250929 / 800000000000
    | 3 => 263512421421491 / 4000000000000
    | 4 => 707831430026327 / 4000000000000
    | 5 => 1921900025344059 / 4000000000000
    | 6 => 1415662860053267 / 4000000000000
    | 7 => 2425762439901791 / 4000000000000
    | 8 => 1786805634109469 / 4000000000000
    | 9 => 2741419340414387 / 4000000000000
    | 10 => 1582759194149723 / 4000000000000
    | 11 => 2808633964789207 / 4000000000000
    | 12 => 2624190176321683 / 4000000000000
    | 13 => 1872745934004739 / 4000000000000
    | 14 => 2123494290078981 / 4000000000000
    | 15 => 1770348153659189 / 4000000000000
    | 16 => 1564156283030969 / 4000000000000
    | 17 => 453353456741931 / 800000000000
    | 18 => 1253999520033457 / 4000000000000
    | 19 => 1063029280796777 / 4000000000000
    | 20 => 665194365890531 / 4000000000000
    | 21 => 357743742312477 / 4000000000000
    | 22 => 971343851448431 / 4000000000000
    | 23 => 1326286986412687 / 4000000000000
    | 24 => 560805634109469 / 4000000000000
    | 25 => 2279643767657149 / 4000000000000
    | _ => 1522696388839091 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-25397282909 / 1000000000000) (-25397278648 / 1000000000000), orderedInterval (37883760303 / 1000000000000) (37883764564 / 1000000000000))
    | 1 => (orderedInterval (18541627600 / 1000000000000) (18541627601 / 1000000000000), orderedInterval (49718640616 / 1000000000000) (49718640617 / 1000000000000))
    | 2 => (orderedInterval (41164238976 / 1000000000000) (41164238995 / 1000000000000), orderedInterval (6977145097 / 1000000000000) (6977145116 / 1000000000000))
    | 3 => (orderedInterval (-62433446580 / 1000000000000) (-62433446579 / 1000000000000), orderedInterval (-75458511363 / 1000000000000) (-75458511362 / 1000000000000))
    | 4 => (orderedInterval (58223804293 / 1000000000000) (58223805661 / 1000000000000), orderedInterval (-14571256244 / 1000000000000) (-14571254876 / 1000000000000))
    | 5 => (orderedInterval (-20446907990 / 1000000000000) (-20446907989 / 1000000000000), orderedInterval (-30093572627 / 1000000000000) (-30093572626 / 1000000000000))
    | 6 => (orderedInterval (12501618366 / 1000000000000) (12501618454 / 1000000000000), orderedInterval (-40545433068 / 1000000000000) (-40545432980 / 1000000000000))
    | 7 => (orderedInterval (-25347985237 / 1000000000000) (-25347985236 / 1000000000000), orderedInterval (-20159387942 / 1000000000000) (-20159387941 / 1000000000000))
    | 8 => (orderedInterval (37068838681 / 1000000000000) (37068838707 / 1000000000000), orderedInterval (7103973086 / 1000000000000) (7103973112 / 1000000000000))
    | 9 => (orderedInterval (29134920828 / 1000000000000) (29134920859 / 1000000000000), orderedInterval (8925640245 / 1000000000000) (8925640277 / 1000000000000))
    | 10 => (orderedInterval (23767253879 / 1000000000000) (23767253880 / 1000000000000), orderedInterval (32281018310 / 1000000000000) (32281018311 / 1000000000000))
    | 11 => (orderedInterval (-21026881617 / 1000000000000) (-21026878123 / 1000000000000), orderedInterval (21567961802 / 1000000000000) (21567965296 / 1000000000000))
    | 12 => (orderedInterval (-7401264531 / 1000000000000) (-7401264530 / 1000000000000), orderedInterval (-30253377265 / 1000000000000) (-30253377264 / 1000000000000))
    | 13 => (orderedInterval (-28286734350 / 1000000000000) (-28286734349 / 1000000000000), orderedInterval (-23626024220 / 1000000000000) (-23626024219 / 1000000000000))
    | 14 => (orderedInterval (-23082342252 / 1000000000000) (-23082342251 / 1000000000000), orderedInterval (-25792952535 / 1000000000000) (-25792952534 / 1000000000000))
    | 15 => (orderedInterval (-15033909353 / 1000000000000) (-15033909352 / 1000000000000), orderedInterval (-34802378612 / 1000000000000) (-34802378611 / 1000000000000))
    | 16 => (orderedInterval (30967630712 / 1000000000000) (30967675067 / 1000000000000), orderedInterval (-25905137246 / 1000000000000) (-25905092891 / 1000000000000))
    | 17 => (orderedInterval (30610562954 / 1000000000000) (30610621174 / 1000000000000), orderedInterval (-13679439484 / 1000000000000) (-13679381263 / 1000000000000))
    | 18 => (orderedInterval (5645686239 / 1000000000000) (5645686240 / 1000000000000), orderedInterval (44699099978 / 1000000000000) (44699099979 / 1000000000000))
    | 19 => (orderedInterval (23169134220 / 1000000000000) (23169136039 / 1000000000000), orderedInterval (-43156077056 / 1000000000000) (-43156075236 / 1000000000000))
    | 20 => (orderedInterval (-33846674707 / 1000000000000) (-33846674706 / 1000000000000), orderedInterval (-51691889483 / 1000000000000) (-51691889482 / 1000000000000))
    | 21 => (orderedInterval (65360833283 / 1000000000000) (65360904997 / 1000000000000), orderedInterval (-53714275874 / 1000000000000) (-53714204160 / 1000000000000))
    | 22 => (orderedInterval (-50646216178 / 1000000000000) (-50646215526 / 1000000000000), orderedInterval (7624896226 / 1000000000000) (7624896879 / 1000000000000))
    | 23 => (orderedInterval (-26589545819 / 1000000000000) (-26589538765 / 1000000000000), orderedInterval (34868283651 / 1000000000000) (34868290706 / 1000000000000))
    | 24 => (orderedInterval (25354107437 / 1000000000000) (25354108529 / 1000000000000), orderedInterval (-62523916467 / 1000000000000) (-62523915375 / 1000000000000))
    | 25 => (orderedInterval (-29377968002 / 1000000000000) (-29377855785 / 1000000000000), orderedInterval (15962758461 / 1000000000000) (15962870679 / 1000000000000))
    | _ => (orderedInterval (-39679660348 / 1000000000000) (-39679660341 / 1000000000000), orderedInterval (-9840901504 / 1000000000000) (-9840901497 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-7478257405 / 1000000000000) (-7478255693 / 1000000000000)
      | 1 => orderedInterval (4256774713 / 1000000000000) (4256774801 / 1000000000000)
      | 2 => orderedInterval (1677713967 / 1000000000000) (1677713986 / 1000000000000)
      | 3 => orderedInterval (-6405060903 / 1000000000000) (-6405060279 / 1000000000000)
      | 4 => orderedInterval (-2424449076 / 1000000000000) (-2424449039 / 1000000000000)
      | 5 => orderedInterval (-1162032454 / 1000000000000) (-1162028395 / 1000000000000)
      | 6 => orderedInterval (-3315962346 / 1000000000000) (-3315962166 / 1000000000000)
      | 7 => orderedInterval (1979899131 / 1000000000000) (1979901047 / 1000000000000)
      | _ => orderedInterval (9989209361 / 1000000000000) (9989218589 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (15844674295 / 1000000000000) (15844676010 / 1000000000000)
      | 1 => orderedInterval (3222469980 / 1000000000000) (3222470051 / 1000000000000)
      | 2 => orderedInterval (1480509544 / 1000000000000) (1480509575 / 1000000000000)
      | 3 => orderedInterval (6565295419 / 1000000000000) (6565296822 / 1000000000000)
      | 4 => orderedInterval (-2017590390 / 1000000000000) (-2017590330 / 1000000000000)
      | 5 => orderedInterval (663453520 / 1000000000000) (663459558 / 1000000000000)
      | 6 => orderedInterval (-6105402790 / 1000000000000) (-6105402629 / 1000000000000)
      | 7 => orderedInterval (-2738495800 / 1000000000000) (-2738494783 / 1000000000000)
      | _ => orderedInterval (-295294157 / 1000000000000) (-295277048 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (6494727479 / 1000000000000) (6494729203 / 1000000000000)
      | 1 => orderedInterval (-4322449849 / 1000000000000) (-4322449774 / 1000000000000)
      | 2 => orderedInterval (-4968528327 / 1000000000000) (-4968528272 / 1000000000000)
      | 3 => orderedInterval (38615597050 / 1000000000000) (38615600228 / 1000000000000)
      | 4 => orderedInterval (5285364055 / 1000000000000) (5285364154 / 1000000000000)
      | 5 => orderedInterval (565189524 / 1000000000000) (565198835 / 1000000000000)
      | 6 => orderedInterval (2274610501 / 1000000000000) (2274610647 / 1000000000000)
      | 7 => orderedInterval (-2994365990 / 1000000000000) (-2994365199 / 1000000000000)
      | _ => orderedInterval (-19783562309 / 1000000000000) (-19783530491 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-15913661652 / 1000000000000) (-15913659923 / 1000000000000)
      | 1 => orderedInterval (-8133005370 / 1000000000000) (-8133005273 / 1000000000000)
      | 2 => orderedInterval (-5331661208 / 1000000000000) (-5331661109 / 1000000000000)
      | 3 => orderedInterval (-24403162321 / 1000000000000) (-24403155094 / 1000000000000)
      | 4 => orderedInterval (1911499319 / 1000000000000) (1911499486 / 1000000000000)
      | 5 => orderedInterval (343345218 / 1000000000000) (343360039 / 1000000000000)
      | 6 => orderedInterval (6317007999 / 1000000000000) (6317008133 / 1000000000000)
      | 7 => orderedInterval (3454275259 / 1000000000000) (3454276020 / 1000000000000)
      | _ => orderedInterval (4916664363 / 1000000000000) (4916723466 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-5051506353 / 1000000000000) (-5051504613 / 1000000000000)
      | 1 => orderedInterval (9068668957 / 1000000000000) (9068669097 / 1000000000000)
      | 2 => orderedInterval (16059191313 / 1000000000000) (16059191496 / 1000000000000)
      | 3 => orderedInterval (-206701953824 / 1000000000000) (-206701937340 / 1000000000000)
      | 4 => orderedInterval (-10719696520 / 1000000000000) (-10719696230 / 1000000000000)
      | 5 => orderedInterval (3706543572 / 1000000000000) (3706567968 / 1000000000000)
      | 6 => orderedInterval (-1865939658 / 1000000000000) (-1865939533 / 1000000000000)
      | 7 => orderedInterval (3212345325 / 1000000000000) (3212346122 / 1000000000000)
      | _ => orderedInterval (46276342552 / 1000000000000) (46276452568 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-2882165012 / 1000000000000) (-2882147149 / 1000000000000)
    | 1 => orderedInterval (16619619621 / 1000000000000) (16619647226 / 1000000000000)
    | 2 => orderedInterval (21166582134 / 1000000000000) (21166629331 / 1000000000000)
    | 3 => orderedInterval (-36838698393 / 1000000000000) (-36838614255 / 1000000000000)
    | _ => orderedInterval (-146016004636 / 1000000000000) (-146015850465 / 1000000000000)

theorem compactCertificate435_stateChecks0 :
    compactCertificate435.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 98 12 (613 / 2)) (orderedInterval (-25397282909 / 1000000000000) (-25397278648 / 1000000000000), orderedInterval (37883760303 / 1000000000000) (37883764564 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (903066051063313 / 4000000000000)) (orderedInterval (18541627600 / 1000000000000) (18541627601 / 1000000000000), orderedInterval (49718640616 / 1000000000000) (49718640617 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 116 12 (292033006250929 / 800000000000)) (orderedInterval (41164238976 / 1000000000000) (41164238995 / 1000000000000), orderedInterval (6977145097 / 1000000000000) (6977145116 / 1000000000000))) = true
  rfl'

theorem compactCertificate435_stateChecks1 :
    compactCertificate435.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 21 12 (263512421421491 / 4000000000000)) (orderedInterval (-62433446580 / 1000000000000) (-62433446579 / 1000000000000), orderedInterval (-75458511363 / 1000000000000) (-75458511362 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (707831430026327 / 4000000000000)) (orderedInterval (58223804293 / 1000000000000) (58223805661 / 1000000000000), orderedInterval (-14571256244 / 1000000000000) (-14571254876 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 153 12 (1921900025344059 / 4000000000000)) (orderedInterval (-20446907990 / 1000000000000) (-20446907989 / 1000000000000), orderedInterval (-30093572627 / 1000000000000) (-30093572626 / 1000000000000))) = true
  rfl'

theorem compactCertificate435_stateChecks2 :
    compactCertificate435.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 113 12 (1415662860053267 / 4000000000000)) (orderedInterval (12501618366 / 1000000000000) (12501618454 / 1000000000000), orderedInterval (-40545433068 / 1000000000000) (-40545432980 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 193 12 (2425762439901791 / 4000000000000)) (orderedInterval (-25347985237 / 1000000000000) (-25347985236 / 1000000000000), orderedInterval (-20159387942 / 1000000000000) (-20159387941 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 142 12 (1786805634109469 / 4000000000000)) (orderedInterval (37068838681 / 1000000000000) (37068838707 / 1000000000000), orderedInterval (7103973086 / 1000000000000) (7103973112 / 1000000000000))) = true
  rfl'

theorem compactCertificate435_stateChecks3 :
    compactCertificate435.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 218 12 (2741419340414387 / 4000000000000)) (orderedInterval (29134920828 / 1000000000000) (29134920859 / 1000000000000), orderedInterval (8925640245 / 1000000000000) (8925640277 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 126 12 (1582759194149723 / 4000000000000)) (orderedInterval (23767253879 / 1000000000000) (23767253880 / 1000000000000), orderedInterval (32281018310 / 1000000000000) (32281018311 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 224 12 (2808633964789207 / 4000000000000)) (orderedInterval (-21026881617 / 1000000000000) (-21026878123 / 1000000000000), orderedInterval (21567961802 / 1000000000000) (21567965296 / 1000000000000))) = true
  rfl'

theorem compactCertificate435_stateChecks4 :
    compactCertificate435.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 209 12 (2624190176321683 / 4000000000000)) (orderedInterval (-7401264531 / 1000000000000) (-7401264530 / 1000000000000), orderedInterval (-30253377265 / 1000000000000) (-30253377264 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 149 12 (1872745934004739 / 4000000000000)) (orderedInterval (-28286734350 / 1000000000000) (-28286734349 / 1000000000000), orderedInterval (-23626024220 / 1000000000000) (-23626024219 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 169 12 (2123494290078981 / 4000000000000)) (orderedInterval (-23082342252 / 1000000000000) (-23082342251 / 1000000000000), orderedInterval (-25792952535 / 1000000000000) (-25792952534 / 1000000000000))) = true
  rfl'

theorem compactCertificate435_stateChecks5 :
    compactCertificate435.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 141 12 (1770348153659189 / 4000000000000)) (orderedInterval (-15033909353 / 1000000000000) (-15033909352 / 1000000000000), orderedInterval (-34802378612 / 1000000000000) (-34802378611 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 125 12 (1564156283030969 / 4000000000000)) (orderedInterval (30967630712 / 1000000000000) (30967675067 / 1000000000000), orderedInterval (-25905137246 / 1000000000000) (-25905092891 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 180 12 (453353456741931 / 800000000000)) (orderedInterval (30610562954 / 1000000000000) (30610621174 / 1000000000000), orderedInterval (-13679439484 / 1000000000000) (-13679381263 / 1000000000000))) = true
  rfl'

theorem compactCertificate435_stateChecks6 :
    compactCertificate435.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 100 12 (1253999520033457 / 4000000000000)) (orderedInterval (5645686239 / 1000000000000) (5645686240 / 1000000000000), orderedInterval (44699099978 / 1000000000000) (44699099979 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (1063029280796777 / 4000000000000)) (orderedInterval (23169134220 / 1000000000000) (23169136039 / 1000000000000), orderedInterval (-43156077056 / 1000000000000) (-43156075236 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (665194365890531 / 4000000000000)) (orderedInterval (-33846674707 / 1000000000000) (-33846674706 / 1000000000000), orderedInterval (-51691889483 / 1000000000000) (-51691889482 / 1000000000000))) = true
  rfl'

theorem compactCertificate435_stateChecks7 :
    compactCertificate435.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 28 12 (357743742312477 / 4000000000000)) (orderedInterval (65360833283 / 1000000000000) (65360904997 / 1000000000000), orderedInterval (-53714275874 / 1000000000000) (-53714204160 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (971343851448431 / 4000000000000)) (orderedInterval (-50646216178 / 1000000000000) (-50646215526 / 1000000000000), orderedInterval (7624896226 / 1000000000000) (7624896879 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 106 12 (1326286986412687 / 4000000000000)) (orderedInterval (-26589545819 / 1000000000000) (-26589538765 / 1000000000000), orderedInterval (34868283651 / 1000000000000) (34868290706 / 1000000000000))) = true
  rfl'

theorem compactCertificate435_stateChecks8 :
    compactCertificate435.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (560805634109469 / 4000000000000)) (orderedInterval (25354107437 / 1000000000000) (25354108529 / 1000000000000), orderedInterval (-62523916467 / 1000000000000) (-62523915375 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 182 12 (2279643767657149 / 4000000000000)) (orderedInterval (-29377968002 / 1000000000000) (-29377855785 / 1000000000000), orderedInterval (15962758461 / 1000000000000) (15962870679 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 121 12 (1522696388839091 / 4000000000000)) (orderedInterval (-39679660348 / 1000000000000) (-39679660341 / 1000000000000), orderedInterval (-9840901504 / 1000000000000) (-9840901497 / 1000000000000))) = true
  rfl'

theorem compactCertificate435_states : ∀ j,
    BesselStateValid (compactCertificate435.point j) (compactCertificate435.state j) :=
  compactCertificate435.statesValid_of_checks3 compactCertificate435_stateChecks0
    compactCertificate435_stateChecks1 compactCertificate435_stateChecks2
    compactCertificate435_stateChecks3 compactCertificate435_stateChecks4
    compactCertificate435_stateChecks5 compactCertificate435_stateChecks6
    compactCertificate435_stateChecks7 compactCertificate435_stateChecks8

theorem compactCertificate435_chunkChecks0_0 :
    compactCertificate435.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (613 / 2) 0 (IntervalRat.scale (613 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-25397282909 / 1000000000000) (-25397278648 / 1000000000000), orderedInterval (37883760303 / 1000000000000) (37883764564 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (903066051063313 / 4000000000000) 0 (IntervalRat.scale (613 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (18541627600 / 1000000000000) (18541627601 / 1000000000000), orderedInterval (49718640616 / 1000000000000) (49718640617 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (292033006250929 / 800000000000) 0 (IntervalRat.scale (613 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (41164238976 / 1000000000000) (41164238995 / 1000000000000), orderedInterval (6977145097 / 1000000000000) (6977145116 / 1000000000000)))) (orderedInterval (-7478257405 / 1000000000000) (-7478255693 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (263512421421491 / 4000000000000) 0 (IntervalRat.scale (613 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-62433446580 / 1000000000000) (-62433446579 / 1000000000000), orderedInterval (-75458511363 / 1000000000000) (-75458511362 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (707831430026327 / 4000000000000) 0 (IntervalRat.scale (613 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (58223804293 / 1000000000000) (58223805661 / 1000000000000), orderedInterval (-14571256244 / 1000000000000) (-14571254876 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1921900025344059 / 4000000000000) 0 (IntervalRat.scale (613 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-20446907990 / 1000000000000) (-20446907989 / 1000000000000), orderedInterval (-30093572627 / 1000000000000) (-30093572626 / 1000000000000)))) (orderedInterval (4256774713 / 1000000000000) (4256774801 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1415662860053267 / 4000000000000) 0 (IntervalRat.scale (613 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (12501618366 / 1000000000000) (12501618454 / 1000000000000), orderedInterval (-40545433068 / 1000000000000) (-40545432980 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2425762439901791 / 4000000000000) 0 (IntervalRat.scale (613 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-25347985237 / 1000000000000) (-25347985236 / 1000000000000), orderedInterval (-20159387942 / 1000000000000) (-20159387941 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1786805634109469 / 4000000000000) 0 (IntervalRat.scale (613 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (37068838681 / 1000000000000) (37068838707 / 1000000000000), orderedInterval (7103973086 / 1000000000000) (7103973112 / 1000000000000)))) (orderedInterval (1677713967 / 1000000000000) (1677713986 / 1000000000000))) = true
  rfl'

theorem compactCertificate435_chunkChecks0_1 :
    compactCertificate435.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2741419340414387 / 4000000000000) 0 (IntervalRat.scale (613 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (29134920828 / 1000000000000) (29134920859 / 1000000000000), orderedInterval (8925640245 / 1000000000000) (8925640277 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1582759194149723 / 4000000000000) 0 (IntervalRat.scale (613 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (23767253879 / 1000000000000) (23767253880 / 1000000000000), orderedInterval (32281018310 / 1000000000000) (32281018311 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2808633964789207 / 4000000000000) 0 (IntervalRat.scale (613 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-21026881617 / 1000000000000) (-21026878123 / 1000000000000), orderedInterval (21567961802 / 1000000000000) (21567965296 / 1000000000000)))) (orderedInterval (-6405060903 / 1000000000000) (-6405060279 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2624190176321683 / 4000000000000) 0 (IntervalRat.scale (613 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-7401264531 / 1000000000000) (-7401264530 / 1000000000000), orderedInterval (-30253377265 / 1000000000000) (-30253377264 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1872745934004739 / 4000000000000) 0 (IntervalRat.scale (613 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-28286734350 / 1000000000000) (-28286734349 / 1000000000000), orderedInterval (-23626024220 / 1000000000000) (-23626024219 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2123494290078981 / 4000000000000) 0 (IntervalRat.scale (613 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-23082342252 / 1000000000000) (-23082342251 / 1000000000000), orderedInterval (-25792952535 / 1000000000000) (-25792952534 / 1000000000000)))) (orderedInterval (-2424449076 / 1000000000000) (-2424449039 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1770348153659189 / 4000000000000) 0 (IntervalRat.scale (613 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-15033909353 / 1000000000000) (-15033909352 / 1000000000000), orderedInterval (-34802378612 / 1000000000000) (-34802378611 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1564156283030969 / 4000000000000) 0 (IntervalRat.scale (613 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (30967630712 / 1000000000000) (30967675067 / 1000000000000), orderedInterval (-25905137246 / 1000000000000) (-25905092891 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (453353456741931 / 800000000000) 0 (IntervalRat.scale (613 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (30610562954 / 1000000000000) (30610621174 / 1000000000000), orderedInterval (-13679439484 / 1000000000000) (-13679381263 / 1000000000000)))) (orderedInterval (-1162032454 / 1000000000000) (-1162028395 / 1000000000000))) = true
  rfl'

theorem compactCertificate435_chunkChecks0_2 :
    compactCertificate435.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1253999520033457 / 4000000000000) 0 (IntervalRat.scale (613 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (5645686239 / 1000000000000) (5645686240 / 1000000000000), orderedInterval (44699099978 / 1000000000000) (44699099979 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1063029280796777 / 4000000000000) 0 (IntervalRat.scale (613 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (23169134220 / 1000000000000) (23169136039 / 1000000000000), orderedInterval (-43156077056 / 1000000000000) (-43156075236 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (665194365890531 / 4000000000000) 0 (IntervalRat.scale (613 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-33846674707 / 1000000000000) (-33846674706 / 1000000000000), orderedInterval (-51691889483 / 1000000000000) (-51691889482 / 1000000000000)))) (orderedInterval (-3315962346 / 1000000000000) (-3315962166 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (357743742312477 / 4000000000000) 0 (IntervalRat.scale (613 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (65360833283 / 1000000000000) (65360904997 / 1000000000000), orderedInterval (-53714275874 / 1000000000000) (-53714204160 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (971343851448431 / 4000000000000) 0 (IntervalRat.scale (613 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-50646216178 / 1000000000000) (-50646215526 / 1000000000000), orderedInterval (7624896226 / 1000000000000) (7624896879 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1326286986412687 / 4000000000000) 0 (IntervalRat.scale (613 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-26589545819 / 1000000000000) (-26589538765 / 1000000000000), orderedInterval (34868283651 / 1000000000000) (34868290706 / 1000000000000)))) (orderedInterval (1979899131 / 1000000000000) (1979901047 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (560805634109469 / 4000000000000) 0 (IntervalRat.scale (613 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (25354107437 / 1000000000000) (25354108529 / 1000000000000), orderedInterval (-62523916467 / 1000000000000) (-62523915375 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2279643767657149 / 4000000000000) 0 (IntervalRat.scale (613 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-29377968002 / 1000000000000) (-29377855785 / 1000000000000), orderedInterval (15962758461 / 1000000000000) (15962870679 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1522696388839091 / 4000000000000) 0 (IntervalRat.scale (613 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-39679660348 / 1000000000000) (-39679660341 / 1000000000000), orderedInterval (-9840901504 / 1000000000000) (-9840901497 / 1000000000000)))) (orderedInterval (9989209361 / 1000000000000) (9989218589 / 1000000000000))) = true
  rfl'

theorem compactCertificate435_chunkChecks0 :
    compactCertificate435.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate435.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate435_chunkChecks0_0
    compactCertificate435_chunkChecks0_1 compactCertificate435_chunkChecks0_2

theorem compactCertificate435_chunkChecks1_0 :
    compactCertificate435.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (613 / 2) 1 (IntervalRat.scale (613 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-25397282909 / 1000000000000) (-25397278648 / 1000000000000), orderedInterval (37883760303 / 1000000000000) (37883764564 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (903066051063313 / 4000000000000) 1 (IntervalRat.scale (613 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (18541627600 / 1000000000000) (18541627601 / 1000000000000), orderedInterval (49718640616 / 1000000000000) (49718640617 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (292033006250929 / 800000000000) 1 (IntervalRat.scale (613 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (41164238976 / 1000000000000) (41164238995 / 1000000000000), orderedInterval (6977145097 / 1000000000000) (6977145116 / 1000000000000)))) (orderedInterval (15844674295 / 1000000000000) (15844676010 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (263512421421491 / 4000000000000) 1 (IntervalRat.scale (613 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-62433446580 / 1000000000000) (-62433446579 / 1000000000000), orderedInterval (-75458511363 / 1000000000000) (-75458511362 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (707831430026327 / 4000000000000) 1 (IntervalRat.scale (613 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (58223804293 / 1000000000000) (58223805661 / 1000000000000), orderedInterval (-14571256244 / 1000000000000) (-14571254876 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1921900025344059 / 4000000000000) 1 (IntervalRat.scale (613 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-20446907990 / 1000000000000) (-20446907989 / 1000000000000), orderedInterval (-30093572627 / 1000000000000) (-30093572626 / 1000000000000)))) (orderedInterval (3222469980 / 1000000000000) (3222470051 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1415662860053267 / 4000000000000) 1 (IntervalRat.scale (613 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (12501618366 / 1000000000000) (12501618454 / 1000000000000), orderedInterval (-40545433068 / 1000000000000) (-40545432980 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2425762439901791 / 4000000000000) 1 (IntervalRat.scale (613 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-25347985237 / 1000000000000) (-25347985236 / 1000000000000), orderedInterval (-20159387942 / 1000000000000) (-20159387941 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1786805634109469 / 4000000000000) 1 (IntervalRat.scale (613 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (37068838681 / 1000000000000) (37068838707 / 1000000000000), orderedInterval (7103973086 / 1000000000000) (7103973112 / 1000000000000)))) (orderedInterval (1480509544 / 1000000000000) (1480509575 / 1000000000000))) = true
  rfl'

theorem compactCertificate435_chunkChecks1_1 :
    compactCertificate435.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2741419340414387 / 4000000000000) 1 (IntervalRat.scale (613 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (29134920828 / 1000000000000) (29134920859 / 1000000000000), orderedInterval (8925640245 / 1000000000000) (8925640277 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1582759194149723 / 4000000000000) 1 (IntervalRat.scale (613 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (23767253879 / 1000000000000) (23767253880 / 1000000000000), orderedInterval (32281018310 / 1000000000000) (32281018311 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2808633964789207 / 4000000000000) 1 (IntervalRat.scale (613 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-21026881617 / 1000000000000) (-21026878123 / 1000000000000), orderedInterval (21567961802 / 1000000000000) (21567965296 / 1000000000000)))) (orderedInterval (6565295419 / 1000000000000) (6565296822 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2624190176321683 / 4000000000000) 1 (IntervalRat.scale (613 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-7401264531 / 1000000000000) (-7401264530 / 1000000000000), orderedInterval (-30253377265 / 1000000000000) (-30253377264 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1872745934004739 / 4000000000000) 1 (IntervalRat.scale (613 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-28286734350 / 1000000000000) (-28286734349 / 1000000000000), orderedInterval (-23626024220 / 1000000000000) (-23626024219 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2123494290078981 / 4000000000000) 1 (IntervalRat.scale (613 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-23082342252 / 1000000000000) (-23082342251 / 1000000000000), orderedInterval (-25792952535 / 1000000000000) (-25792952534 / 1000000000000)))) (orderedInterval (-2017590390 / 1000000000000) (-2017590330 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1770348153659189 / 4000000000000) 1 (IntervalRat.scale (613 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-15033909353 / 1000000000000) (-15033909352 / 1000000000000), orderedInterval (-34802378612 / 1000000000000) (-34802378611 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1564156283030969 / 4000000000000) 1 (IntervalRat.scale (613 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (30967630712 / 1000000000000) (30967675067 / 1000000000000), orderedInterval (-25905137246 / 1000000000000) (-25905092891 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (453353456741931 / 800000000000) 1 (IntervalRat.scale (613 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (30610562954 / 1000000000000) (30610621174 / 1000000000000), orderedInterval (-13679439484 / 1000000000000) (-13679381263 / 1000000000000)))) (orderedInterval (663453520 / 1000000000000) (663459558 / 1000000000000))) = true
  rfl'

theorem compactCertificate435_chunkChecks1_2 :
    compactCertificate435.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1253999520033457 / 4000000000000) 1 (IntervalRat.scale (613 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (5645686239 / 1000000000000) (5645686240 / 1000000000000), orderedInterval (44699099978 / 1000000000000) (44699099979 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1063029280796777 / 4000000000000) 1 (IntervalRat.scale (613 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (23169134220 / 1000000000000) (23169136039 / 1000000000000), orderedInterval (-43156077056 / 1000000000000) (-43156075236 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (665194365890531 / 4000000000000) 1 (IntervalRat.scale (613 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-33846674707 / 1000000000000) (-33846674706 / 1000000000000), orderedInterval (-51691889483 / 1000000000000) (-51691889482 / 1000000000000)))) (orderedInterval (-6105402790 / 1000000000000) (-6105402629 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (357743742312477 / 4000000000000) 1 (IntervalRat.scale (613 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (65360833283 / 1000000000000) (65360904997 / 1000000000000), orderedInterval (-53714275874 / 1000000000000) (-53714204160 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (971343851448431 / 4000000000000) 1 (IntervalRat.scale (613 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-50646216178 / 1000000000000) (-50646215526 / 1000000000000), orderedInterval (7624896226 / 1000000000000) (7624896879 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1326286986412687 / 4000000000000) 1 (IntervalRat.scale (613 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-26589545819 / 1000000000000) (-26589538765 / 1000000000000), orderedInterval (34868283651 / 1000000000000) (34868290706 / 1000000000000)))) (orderedInterval (-2738495800 / 1000000000000) (-2738494783 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (560805634109469 / 4000000000000) 1 (IntervalRat.scale (613 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (25354107437 / 1000000000000) (25354108529 / 1000000000000), orderedInterval (-62523916467 / 1000000000000) (-62523915375 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2279643767657149 / 4000000000000) 1 (IntervalRat.scale (613 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-29377968002 / 1000000000000) (-29377855785 / 1000000000000), orderedInterval (15962758461 / 1000000000000) (15962870679 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1522696388839091 / 4000000000000) 1 (IntervalRat.scale (613 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-39679660348 / 1000000000000) (-39679660341 / 1000000000000), orderedInterval (-9840901504 / 1000000000000) (-9840901497 / 1000000000000)))) (orderedInterval (-295294157 / 1000000000000) (-295277048 / 1000000000000))) = true
  rfl'

theorem compactCertificate435_chunkChecks1 :
    compactCertificate435.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate435.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate435_chunkChecks1_0
    compactCertificate435_chunkChecks1_1 compactCertificate435_chunkChecks1_2

theorem compactCertificate435_chunkChecks2_0 :
    compactCertificate435.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (613 / 2) 2 (IntervalRat.scale (613 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-25397282909 / 1000000000000) (-25397278648 / 1000000000000), orderedInterval (37883760303 / 1000000000000) (37883764564 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (903066051063313 / 4000000000000) 2 (IntervalRat.scale (613 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (18541627600 / 1000000000000) (18541627601 / 1000000000000), orderedInterval (49718640616 / 1000000000000) (49718640617 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (292033006250929 / 800000000000) 2 (IntervalRat.scale (613 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (41164238976 / 1000000000000) (41164238995 / 1000000000000), orderedInterval (6977145097 / 1000000000000) (6977145116 / 1000000000000)))) (orderedInterval (6494727479 / 1000000000000) (6494729203 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (263512421421491 / 4000000000000) 2 (IntervalRat.scale (613 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-62433446580 / 1000000000000) (-62433446579 / 1000000000000), orderedInterval (-75458511363 / 1000000000000) (-75458511362 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (707831430026327 / 4000000000000) 2 (IntervalRat.scale (613 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (58223804293 / 1000000000000) (58223805661 / 1000000000000), orderedInterval (-14571256244 / 1000000000000) (-14571254876 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1921900025344059 / 4000000000000) 2 (IntervalRat.scale (613 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-20446907990 / 1000000000000) (-20446907989 / 1000000000000), orderedInterval (-30093572627 / 1000000000000) (-30093572626 / 1000000000000)))) (orderedInterval (-4322449849 / 1000000000000) (-4322449774 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1415662860053267 / 4000000000000) 2 (IntervalRat.scale (613 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (12501618366 / 1000000000000) (12501618454 / 1000000000000), orderedInterval (-40545433068 / 1000000000000) (-40545432980 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2425762439901791 / 4000000000000) 2 (IntervalRat.scale (613 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-25347985237 / 1000000000000) (-25347985236 / 1000000000000), orderedInterval (-20159387942 / 1000000000000) (-20159387941 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1786805634109469 / 4000000000000) 2 (IntervalRat.scale (613 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (37068838681 / 1000000000000) (37068838707 / 1000000000000), orderedInterval (7103973086 / 1000000000000) (7103973112 / 1000000000000)))) (orderedInterval (-4968528327 / 1000000000000) (-4968528272 / 1000000000000))) = true
  rfl'

theorem compactCertificate435_chunkChecks2_1 :
    compactCertificate435.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2741419340414387 / 4000000000000) 2 (IntervalRat.scale (613 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (29134920828 / 1000000000000) (29134920859 / 1000000000000), orderedInterval (8925640245 / 1000000000000) (8925640277 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1582759194149723 / 4000000000000) 2 (IntervalRat.scale (613 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (23767253879 / 1000000000000) (23767253880 / 1000000000000), orderedInterval (32281018310 / 1000000000000) (32281018311 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2808633964789207 / 4000000000000) 2 (IntervalRat.scale (613 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-21026881617 / 1000000000000) (-21026878123 / 1000000000000), orderedInterval (21567961802 / 1000000000000) (21567965296 / 1000000000000)))) (orderedInterval (38615597050 / 1000000000000) (38615600228 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2624190176321683 / 4000000000000) 2 (IntervalRat.scale (613 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-7401264531 / 1000000000000) (-7401264530 / 1000000000000), orderedInterval (-30253377265 / 1000000000000) (-30253377264 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1872745934004739 / 4000000000000) 2 (IntervalRat.scale (613 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-28286734350 / 1000000000000) (-28286734349 / 1000000000000), orderedInterval (-23626024220 / 1000000000000) (-23626024219 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2123494290078981 / 4000000000000) 2 (IntervalRat.scale (613 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-23082342252 / 1000000000000) (-23082342251 / 1000000000000), orderedInterval (-25792952535 / 1000000000000) (-25792952534 / 1000000000000)))) (orderedInterval (5285364055 / 1000000000000) (5285364154 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1770348153659189 / 4000000000000) 2 (IntervalRat.scale (613 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-15033909353 / 1000000000000) (-15033909352 / 1000000000000), orderedInterval (-34802378612 / 1000000000000) (-34802378611 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1564156283030969 / 4000000000000) 2 (IntervalRat.scale (613 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (30967630712 / 1000000000000) (30967675067 / 1000000000000), orderedInterval (-25905137246 / 1000000000000) (-25905092891 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (453353456741931 / 800000000000) 2 (IntervalRat.scale (613 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (30610562954 / 1000000000000) (30610621174 / 1000000000000), orderedInterval (-13679439484 / 1000000000000) (-13679381263 / 1000000000000)))) (orderedInterval (565189524 / 1000000000000) (565198835 / 1000000000000))) = true
  rfl'

theorem compactCertificate435_chunkChecks2_2 :
    compactCertificate435.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1253999520033457 / 4000000000000) 2 (IntervalRat.scale (613 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (5645686239 / 1000000000000) (5645686240 / 1000000000000), orderedInterval (44699099978 / 1000000000000) (44699099979 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1063029280796777 / 4000000000000) 2 (IntervalRat.scale (613 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (23169134220 / 1000000000000) (23169136039 / 1000000000000), orderedInterval (-43156077056 / 1000000000000) (-43156075236 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (665194365890531 / 4000000000000) 2 (IntervalRat.scale (613 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-33846674707 / 1000000000000) (-33846674706 / 1000000000000), orderedInterval (-51691889483 / 1000000000000) (-51691889482 / 1000000000000)))) (orderedInterval (2274610501 / 1000000000000) (2274610647 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (357743742312477 / 4000000000000) 2 (IntervalRat.scale (613 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (65360833283 / 1000000000000) (65360904997 / 1000000000000), orderedInterval (-53714275874 / 1000000000000) (-53714204160 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (971343851448431 / 4000000000000) 2 (IntervalRat.scale (613 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-50646216178 / 1000000000000) (-50646215526 / 1000000000000), orderedInterval (7624896226 / 1000000000000) (7624896879 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1326286986412687 / 4000000000000) 2 (IntervalRat.scale (613 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-26589545819 / 1000000000000) (-26589538765 / 1000000000000), orderedInterval (34868283651 / 1000000000000) (34868290706 / 1000000000000)))) (orderedInterval (-2994365990 / 1000000000000) (-2994365199 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (560805634109469 / 4000000000000) 2 (IntervalRat.scale (613 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (25354107437 / 1000000000000) (25354108529 / 1000000000000), orderedInterval (-62523916467 / 1000000000000) (-62523915375 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2279643767657149 / 4000000000000) 2 (IntervalRat.scale (613 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-29377968002 / 1000000000000) (-29377855785 / 1000000000000), orderedInterval (15962758461 / 1000000000000) (15962870679 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1522696388839091 / 4000000000000) 2 (IntervalRat.scale (613 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-39679660348 / 1000000000000) (-39679660341 / 1000000000000), orderedInterval (-9840901504 / 1000000000000) (-9840901497 / 1000000000000)))) (orderedInterval (-19783562309 / 1000000000000) (-19783530491 / 1000000000000))) = true
  rfl'

theorem compactCertificate435_chunkChecks2 :
    compactCertificate435.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate435.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate435_chunkChecks2_0
    compactCertificate435_chunkChecks2_1 compactCertificate435_chunkChecks2_2

theorem compactCertificate435_chunkChecks3_0 :
    compactCertificate435.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (613 / 2) 3 (IntervalRat.scale (613 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-25397282909 / 1000000000000) (-25397278648 / 1000000000000), orderedInterval (37883760303 / 1000000000000) (37883764564 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (903066051063313 / 4000000000000) 3 (IntervalRat.scale (613 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (18541627600 / 1000000000000) (18541627601 / 1000000000000), orderedInterval (49718640616 / 1000000000000) (49718640617 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (292033006250929 / 800000000000) 3 (IntervalRat.scale (613 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (41164238976 / 1000000000000) (41164238995 / 1000000000000), orderedInterval (6977145097 / 1000000000000) (6977145116 / 1000000000000)))) (orderedInterval (-15913661652 / 1000000000000) (-15913659923 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (263512421421491 / 4000000000000) 3 (IntervalRat.scale (613 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-62433446580 / 1000000000000) (-62433446579 / 1000000000000), orderedInterval (-75458511363 / 1000000000000) (-75458511362 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (707831430026327 / 4000000000000) 3 (IntervalRat.scale (613 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (58223804293 / 1000000000000) (58223805661 / 1000000000000), orderedInterval (-14571256244 / 1000000000000) (-14571254876 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1921900025344059 / 4000000000000) 3 (IntervalRat.scale (613 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-20446907990 / 1000000000000) (-20446907989 / 1000000000000), orderedInterval (-30093572627 / 1000000000000) (-30093572626 / 1000000000000)))) (orderedInterval (-8133005370 / 1000000000000) (-8133005273 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1415662860053267 / 4000000000000) 3 (IntervalRat.scale (613 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (12501618366 / 1000000000000) (12501618454 / 1000000000000), orderedInterval (-40545433068 / 1000000000000) (-40545432980 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2425762439901791 / 4000000000000) 3 (IntervalRat.scale (613 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-25347985237 / 1000000000000) (-25347985236 / 1000000000000), orderedInterval (-20159387942 / 1000000000000) (-20159387941 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1786805634109469 / 4000000000000) 3 (IntervalRat.scale (613 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (37068838681 / 1000000000000) (37068838707 / 1000000000000), orderedInterval (7103973086 / 1000000000000) (7103973112 / 1000000000000)))) (orderedInterval (-5331661208 / 1000000000000) (-5331661109 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate435_chunkChecks3_1 :
    compactCertificate435.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2741419340414387 / 4000000000000) 3 (IntervalRat.scale (613 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (29134920828 / 1000000000000) (29134920859 / 1000000000000), orderedInterval (8925640245 / 1000000000000) (8925640277 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1582759194149723 / 4000000000000) 3 (IntervalRat.scale (613 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (23767253879 / 1000000000000) (23767253880 / 1000000000000), orderedInterval (32281018310 / 1000000000000) (32281018311 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2808633964789207 / 4000000000000) 3 (IntervalRat.scale (613 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-21026881617 / 1000000000000) (-21026878123 / 1000000000000), orderedInterval (21567961802 / 1000000000000) (21567965296 / 1000000000000)))) (orderedInterval (-24403162321 / 1000000000000) (-24403155094 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2624190176321683 / 4000000000000) 3 (IntervalRat.scale (613 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-7401264531 / 1000000000000) (-7401264530 / 1000000000000), orderedInterval (-30253377265 / 1000000000000) (-30253377264 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1872745934004739 / 4000000000000) 3 (IntervalRat.scale (613 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-28286734350 / 1000000000000) (-28286734349 / 1000000000000), orderedInterval (-23626024220 / 1000000000000) (-23626024219 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2123494290078981 / 4000000000000) 3 (IntervalRat.scale (613 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-23082342252 / 1000000000000) (-23082342251 / 1000000000000), orderedInterval (-25792952535 / 1000000000000) (-25792952534 / 1000000000000)))) (orderedInterval (1911499319 / 1000000000000) (1911499486 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1770348153659189 / 4000000000000) 3 (IntervalRat.scale (613 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-15033909353 / 1000000000000) (-15033909352 / 1000000000000), orderedInterval (-34802378612 / 1000000000000) (-34802378611 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1564156283030969 / 4000000000000) 3 (IntervalRat.scale (613 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (30967630712 / 1000000000000) (30967675067 / 1000000000000), orderedInterval (-25905137246 / 1000000000000) (-25905092891 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (453353456741931 / 800000000000) 3 (IntervalRat.scale (613 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (30610562954 / 1000000000000) (30610621174 / 1000000000000), orderedInterval (-13679439484 / 1000000000000) (-13679381263 / 1000000000000)))) (orderedInterval (343345218 / 1000000000000) (343360039 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate435_chunkChecks3_2 :
    compactCertificate435.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1253999520033457 / 4000000000000) 3 (IntervalRat.scale (613 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (5645686239 / 1000000000000) (5645686240 / 1000000000000), orderedInterval (44699099978 / 1000000000000) (44699099979 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1063029280796777 / 4000000000000) 3 (IntervalRat.scale (613 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (23169134220 / 1000000000000) (23169136039 / 1000000000000), orderedInterval (-43156077056 / 1000000000000) (-43156075236 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (665194365890531 / 4000000000000) 3 (IntervalRat.scale (613 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-33846674707 / 1000000000000) (-33846674706 / 1000000000000), orderedInterval (-51691889483 / 1000000000000) (-51691889482 / 1000000000000)))) (orderedInterval (6317007999 / 1000000000000) (6317008133 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (357743742312477 / 4000000000000) 3 (IntervalRat.scale (613 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (65360833283 / 1000000000000) (65360904997 / 1000000000000), orderedInterval (-53714275874 / 1000000000000) (-53714204160 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (971343851448431 / 4000000000000) 3 (IntervalRat.scale (613 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-50646216178 / 1000000000000) (-50646215526 / 1000000000000), orderedInterval (7624896226 / 1000000000000) (7624896879 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1326286986412687 / 4000000000000) 3 (IntervalRat.scale (613 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-26589545819 / 1000000000000) (-26589538765 / 1000000000000), orderedInterval (34868283651 / 1000000000000) (34868290706 / 1000000000000)))) (orderedInterval (3454275259 / 1000000000000) (3454276020 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (560805634109469 / 4000000000000) 3 (IntervalRat.scale (613 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (25354107437 / 1000000000000) (25354108529 / 1000000000000), orderedInterval (-62523916467 / 1000000000000) (-62523915375 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2279643767657149 / 4000000000000) 3 (IntervalRat.scale (613 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-29377968002 / 1000000000000) (-29377855785 / 1000000000000), orderedInterval (15962758461 / 1000000000000) (15962870679 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1522696388839091 / 4000000000000) 3 (IntervalRat.scale (613 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-39679660348 / 1000000000000) (-39679660341 / 1000000000000), orderedInterval (-9840901504 / 1000000000000) (-9840901497 / 1000000000000)))) (orderedInterval (4916664363 / 1000000000000) (4916723466 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate435_chunkChecks3 :
    compactCertificate435.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate435.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate435_chunkChecks3_0
    compactCertificate435_chunkChecks3_1 compactCertificate435_chunkChecks3_2

theorem compactCertificate435_chunkChecks4_0 :
    compactCertificate435.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (613 / 2) 4 (IntervalRat.scale (613 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-25397282909 / 1000000000000) (-25397278648 / 1000000000000), orderedInterval (37883760303 / 1000000000000) (37883764564 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (903066051063313 / 4000000000000) 4 (IntervalRat.scale (613 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (18541627600 / 1000000000000) (18541627601 / 1000000000000), orderedInterval (49718640616 / 1000000000000) (49718640617 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (292033006250929 / 800000000000) 4 (IntervalRat.scale (613 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (41164238976 / 1000000000000) (41164238995 / 1000000000000), orderedInterval (6977145097 / 1000000000000) (6977145116 / 1000000000000)))) (orderedInterval (-5051506353 / 1000000000000) (-5051504613 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (263512421421491 / 4000000000000) 4 (IntervalRat.scale (613 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-62433446580 / 1000000000000) (-62433446579 / 1000000000000), orderedInterval (-75458511363 / 1000000000000) (-75458511362 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (707831430026327 / 4000000000000) 4 (IntervalRat.scale (613 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (58223804293 / 1000000000000) (58223805661 / 1000000000000), orderedInterval (-14571256244 / 1000000000000) (-14571254876 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1921900025344059 / 4000000000000) 4 (IntervalRat.scale (613 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-20446907990 / 1000000000000) (-20446907989 / 1000000000000), orderedInterval (-30093572627 / 1000000000000) (-30093572626 / 1000000000000)))) (orderedInterval (9068668957 / 1000000000000) (9068669097 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1415662860053267 / 4000000000000) 4 (IntervalRat.scale (613 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (12501618366 / 1000000000000) (12501618454 / 1000000000000), orderedInterval (-40545433068 / 1000000000000) (-40545432980 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2425762439901791 / 4000000000000) 4 (IntervalRat.scale (613 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-25347985237 / 1000000000000) (-25347985236 / 1000000000000), orderedInterval (-20159387942 / 1000000000000) (-20159387941 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1786805634109469 / 4000000000000) 4 (IntervalRat.scale (613 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (37068838681 / 1000000000000) (37068838707 / 1000000000000), orderedInterval (7103973086 / 1000000000000) (7103973112 / 1000000000000)))) (orderedInterval (16059191313 / 1000000000000) (16059191496 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate435_chunkChecks4_1 :
    compactCertificate435.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2741419340414387 / 4000000000000) 4 (IntervalRat.scale (613 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (29134920828 / 1000000000000) (29134920859 / 1000000000000), orderedInterval (8925640245 / 1000000000000) (8925640277 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1582759194149723 / 4000000000000) 4 (IntervalRat.scale (613 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (23767253879 / 1000000000000) (23767253880 / 1000000000000), orderedInterval (32281018310 / 1000000000000) (32281018311 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2808633964789207 / 4000000000000) 4 (IntervalRat.scale (613 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-21026881617 / 1000000000000) (-21026878123 / 1000000000000), orderedInterval (21567961802 / 1000000000000) (21567965296 / 1000000000000)))) (orderedInterval (-206701953824 / 1000000000000) (-206701937340 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2624190176321683 / 4000000000000) 4 (IntervalRat.scale (613 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-7401264531 / 1000000000000) (-7401264530 / 1000000000000), orderedInterval (-30253377265 / 1000000000000) (-30253377264 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1872745934004739 / 4000000000000) 4 (IntervalRat.scale (613 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-28286734350 / 1000000000000) (-28286734349 / 1000000000000), orderedInterval (-23626024220 / 1000000000000) (-23626024219 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2123494290078981 / 4000000000000) 4 (IntervalRat.scale (613 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-23082342252 / 1000000000000) (-23082342251 / 1000000000000), orderedInterval (-25792952535 / 1000000000000) (-25792952534 / 1000000000000)))) (orderedInterval (-10719696520 / 1000000000000) (-10719696230 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1770348153659189 / 4000000000000) 4 (IntervalRat.scale (613 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-15033909353 / 1000000000000) (-15033909352 / 1000000000000), orderedInterval (-34802378612 / 1000000000000) (-34802378611 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1564156283030969 / 4000000000000) 4 (IntervalRat.scale (613 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (30967630712 / 1000000000000) (30967675067 / 1000000000000), orderedInterval (-25905137246 / 1000000000000) (-25905092891 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (453353456741931 / 800000000000) 4 (IntervalRat.scale (613 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (30610562954 / 1000000000000) (30610621174 / 1000000000000), orderedInterval (-13679439484 / 1000000000000) (-13679381263 / 1000000000000)))) (orderedInterval (3706543572 / 1000000000000) (3706567968 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate435_chunkChecks4_2 :
    compactCertificate435.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1253999520033457 / 4000000000000) 4 (IntervalRat.scale (613 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (5645686239 / 1000000000000) (5645686240 / 1000000000000), orderedInterval (44699099978 / 1000000000000) (44699099979 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1063029280796777 / 4000000000000) 4 (IntervalRat.scale (613 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (23169134220 / 1000000000000) (23169136039 / 1000000000000), orderedInterval (-43156077056 / 1000000000000) (-43156075236 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (665194365890531 / 4000000000000) 4 (IntervalRat.scale (613 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-33846674707 / 1000000000000) (-33846674706 / 1000000000000), orderedInterval (-51691889483 / 1000000000000) (-51691889482 / 1000000000000)))) (orderedInterval (-1865939658 / 1000000000000) (-1865939533 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (357743742312477 / 4000000000000) 4 (IntervalRat.scale (613 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (65360833283 / 1000000000000) (65360904997 / 1000000000000), orderedInterval (-53714275874 / 1000000000000) (-53714204160 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (971343851448431 / 4000000000000) 4 (IntervalRat.scale (613 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-50646216178 / 1000000000000) (-50646215526 / 1000000000000), orderedInterval (7624896226 / 1000000000000) (7624896879 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1326286986412687 / 4000000000000) 4 (IntervalRat.scale (613 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-26589545819 / 1000000000000) (-26589538765 / 1000000000000), orderedInterval (34868283651 / 1000000000000) (34868290706 / 1000000000000)))) (orderedInterval (3212345325 / 1000000000000) (3212346122 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (560805634109469 / 4000000000000) 4 (IntervalRat.scale (613 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (25354107437 / 1000000000000) (25354108529 / 1000000000000), orderedInterval (-62523916467 / 1000000000000) (-62523915375 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2279643767657149 / 4000000000000) 4 (IntervalRat.scale (613 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-29377968002 / 1000000000000) (-29377855785 / 1000000000000), orderedInterval (15962758461 / 1000000000000) (15962870679 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1522696388839091 / 4000000000000) 4 (IntervalRat.scale (613 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-39679660348 / 1000000000000) (-39679660341 / 1000000000000), orderedInterval (-9840901504 / 1000000000000) (-9840901497 / 1000000000000)))) (orderedInterval (46276342552 / 1000000000000) (46276452568 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate435_chunkChecks4 :
    compactCertificate435.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate435.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate435_chunkChecks4_0
    compactCertificate435_chunkChecks4_1 compactCertificate435_chunkChecks4_2

theorem compactCertificate435_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate435.chunkCheck r b = true :=
  compactCertificate435.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate435_chunkChecks0
    · exact compactCertificate435_chunkChecks1
    · exact compactCertificate435_chunkChecks2
    · exact compactCertificate435_chunkChecks3
    · exact compactCertificate435_chunkChecks4)

theorem compactCertificate435_coefficient0 :
    compactCertificate435.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate435_coefficient1 :
    compactCertificate435.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate435_coefficient2 :
    compactCertificate435.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate435_coefficient3 :
    compactCertificate435.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate435_coefficient4 :
    compactCertificate435.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate435_coefficients : ∀ r : Fin 5,
    compactCertificate435.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate435_coefficient0
  · exact compactCertificate435_coefficient1
  · exact compactCertificate435_coefficient2
  · exact compactCertificate435_coefficient3
  · exact compactCertificate435_coefficient4

theorem compactCertificate435_lower : (1 : ℚ) ≤ compactCertificate435.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate435, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate435_proves {t : ℝ} (ht : t ∈ compactCertificate435.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate435.proves compactCertificate435_states compactCertificate435_chunks
    compactCertificate435_coefficients compactCertificate435_lower ht

end Erdos232
