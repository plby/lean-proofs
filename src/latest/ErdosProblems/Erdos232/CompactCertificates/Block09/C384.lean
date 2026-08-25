/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate384 : CompactCertificate where
  left := 255
  right := 256
  center := 511 / 2
  grid := fun i =>
    match i.val with
    | 0 => 81
    | 1 => 60
    | 2 => 97
    | 3 => 17
    | 4 => 47
    | 5 => 128
    | 6 => 94
    | 7 => 161
    | 8 => 119
    | 9 => 182
    | 10 => 105
    | 11 => 186
    | 12 => 174
    | 13 => 124
    | 14 => 141
    | 15 => 117
    | 16 => 104
    | 17 => 150
    | 18 => 83
    | 19 => 71
    | 20 => 44
    | 21 => 24
    | 22 => 64
    | 23 => 88
    | 24 => 37
    | 25 => 151
    | _ => 101
  point := fun i =>
    match i.val with
    | 0 => 511 / 2
    | 1 => 752800574377411 / 4000000000000
    | 2 => 243440238489763 / 800000000000
    | 3 => 219665330091977 / 4000000000000
    | 4 => 590051975111669 / 4000000000000
    | 5 => 1602105893883873 / 4000000000000
    | 6 => 1180103950223849 / 4000000000000
    | 7 => 2022128232936077 / 4000000000000
    | 8 => 1489490504127143 / 4000000000000
    | 9 => 2285261473004489 / 4000000000000
    | 10 => 1319396326607681 / 4000000000000
    | 11 => 2341291934759029 / 4000000000000
    | 12 => 2187538629853801 / 4000000000000
    | 13 => 1561130786747833 / 4000000000000
    | 14 => 1770155925335007 / 4000000000000
    | 15 => 1475771462511983 / 4000000000000
    | 16 => 1303888842787643 / 4000000000000
    | 17 => 377917808148657 / 800000000000
    | 18 => 1045340546063779 / 4000000000000
    | 19 => 886146757727819 / 4000000000000
    | 20 => 554509495872857 / 4000000000000
    | 21 => 298217051095719 / 4000000000000
    | 22 => 809717305204157 / 4000000000000
    | 23 => 1105599755394589 / 4000000000000
    | 24 => 467490504127143 / 4000000000000
    | 25 => 1900322944980103 / 4000000000000
    | _ => 1269327658559177 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-48424564524 / 1000000000000) (-48424562311 / 1000000000000), orderedInterval (12207564258 / 1000000000000) (12207566471 / 1000000000000))
    | 1 => (orderedInterval (27336926045 / 1000000000000) (27336926046 / 1000000000000), orderedInterval (51263260775 / 1000000000000) (51263260776 / 1000000000000))
    | 2 => (orderedInterval (-15718158288 / 1000000000000) (-15718158287 / 1000000000000), orderedInterval (-42927858214 / 1000000000000) (-42927858213 / 1000000000000))
    | 3 => (orderedInterval (-80831760839 / 1000000000000) (-80831675517 / 1000000000000), orderedInterval (71860466489 / 1000000000000) (71860551811 / 1000000000000))
    | 4 => (orderedInterval (-39373567597 / 1000000000000) (-39373567596 / 1000000000000), orderedInterval (-52453758977 / 1000000000000) (-52453758976 / 1000000000000))
    | 5 => (orderedInterval (-28939032477 / 1000000000000) (-28939008474 / 1000000000000), orderedInterval (27458557599 / 1000000000000) (27458581602 / 1000000000000))
    | 6 => (orderedInterval (22321587223 / 1000000000000) (22321587224 / 1000000000000), orderedInterval (40700253733 / 1000000000000) (40700253734 / 1000000000000))
    | 7 => (orderedInterval (-17657017988 / 1000000000000) (-17657017987 / 1000000000000), orderedInterval (-30764616373 / 1000000000000) (-30764616372 / 1000000000000))
    | 8 => (orderedInterval (26377866446 / 1000000000000) (26377875016 / 1000000000000), orderedInterval (-31876264171 / 1000000000000) (-31876255602 / 1000000000000))
    | 9 => (orderedInterval (10838566444 / 1000000000000) (10838566445 / 1000000000000), orderedInterval (31563147562 / 1000000000000) (31563147563 / 1000000000000))
    | 10 => (orderedInterval (-30483900365 / 1000000000000) (-30483900364 / 1000000000000), orderedInterval (-31588667333 / 1000000000000) (-31588667332 / 1000000000000))
    | 11 => (orderedInterval (32314482312 / 1000000000000) (32314490509 / 1000000000000), orderedInterval (-6616388441 / 1000000000000) (-6616380244 / 1000000000000))
    | 12 => (orderedInterval (29297313753 / 1000000000000) (29297313754 / 1000000000000), orderedInterval (17458961304 / 1000000000000) (17458961305 / 1000000000000))
    | 13 => (orderedInterval (40313884888 / 1000000000000) (40313885002 / 1000000000000), orderedInterval (2390762210 / 1000000000000) (2390762324 / 1000000000000))
    | 14 => (orderedInterval (-13344603977 / 1000000000000) (-13344603976 / 1000000000000), orderedInterval (-35488221967 / 1000000000000) (-35488221966 / 1000000000000))
    | 15 => (orderedInterval (-34498609105 / 1000000000000) (-34498502510 / 1000000000000), orderedInterval (23184825823 / 1000000000000) (23184932418 / 1000000000000))
    | 16 => (orderedInterval (1395786343 / 1000000000000) (1395786345 / 1000000000000), orderedInterval (44168459449 / 1000000000000) (44168459450 / 1000000000000))
    | 17 => (orderedInterval (34189912695 / 1000000000000) (34189937548 / 1000000000000), orderedInterval (-13403507034 / 1000000000000) (-13403482181 / 1000000000000))
    | 18 => (orderedInterval (-48343315948 / 1000000000000) (-48343315943 / 1000000000000), orderedInterval (-9854765606 / 1000000000000) (-9854765601 / 1000000000000))
    | 19 => (orderedInterval (35810544299 / 1000000000000) (35810570588 / 1000000000000), orderedInterval (-39971418578 / 1000000000000) (-39971392289 / 1000000000000))
    | 20 => (orderedInterval (62703384353 / 1000000000000) (62703384354 / 1000000000000), orderedInterval (25475470739 / 1000000000000) (25475470740 / 1000000000000))
    | 21 => (orderedInterval (-5563083915 / 1000000000000) (-5563083895 / 1000000000000), orderedInterval (92277510316 / 1000000000000) (92277510336 / 1000000000000))
    | 22 => (orderedInterval (46865744843 / 1000000000000) (46865792628 / 1000000000000), orderedInterval (-30913422710 / 1000000000000) (-30913374925 / 1000000000000))
    | 23 => (orderedInterval (31815679359 / 1000000000000) (31815679360 / 1000000000000), orderedInterval (35873197098 / 1000000000000) (35873197099 / 1000000000000))
    | 24 => (orderedInterval (-72944729925 / 1000000000000) (-72944729921 / 1000000000000), orderedInterval (-10919302252 / 1000000000000) (-10919302248 / 1000000000000))
    | 25 => (orderedInterval (-36472877558 / 1000000000000) (-36472877412 / 1000000000000), orderedInterval (-3084571633 / 1000000000000) (-3084571487 / 1000000000000))
    | _ => (orderedInterval (-32627540843 / 1000000000000) (-32627540842 / 1000000000000), orderedInterval (-30634208757 / 1000000000000) (-30634208756 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-19861434518 / 1000000000000) (-19861433622 / 1000000000000)
      | 1 => orderedInterval (1496632378 / 1000000000000) (1496635042 / 1000000000000)
      | 2 => orderedInterval (1182114061 / 1000000000000) (1182114284 / 1000000000000)
      | 3 => orderedInterval (409205449 / 1000000000000) (409206716 / 1000000000000)
      | 4 => orderedInterval (3350820937 / 1000000000000) (3350820979 / 1000000000000)
      | 5 => orderedInterval (397142035 / 1000000000000) (397143927 / 1000000000000)
      | 6 => orderedInterval (7744179759 / 1000000000000) (7744181312 / 1000000000000)
      | 7 => orderedInterval (-3398832505 / 1000000000000) (-3398831389 / 1000000000000)
      | _ => orderedInterval (8651014413 / 1000000000000) (8651014496 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (2190310423 / 1000000000000) (2190311321 / 1000000000000)
      | 1 => orderedInterval (-4333324521 / 1000000000000) (-4333321612 / 1000000000000)
      | 2 => orderedInterval (754718221 / 1000000000000) (754718549 / 1000000000000)
      | 3 => orderedInterval (-17716981623 / 1000000000000) (-17716978743 / 1000000000000)
      | 4 => orderedInterval (-18244778 / 1000000000000) (-18244712 / 1000000000000)
      | 5 => orderedInterval (-3472693625 / 1000000000000) (-3472690635 / 1000000000000)
      | 6 => orderedInterval (4023320983 / 1000000000000) (4023322334 / 1000000000000)
      | 7 => orderedInterval (-2915718453 / 1000000000000) (-2915717566 / 1000000000000)
      | _ => orderedInterval (7575545718 / 1000000000000) (7575545840 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (20355368229 / 1000000000000) (20355369133 / 1000000000000)
      | 1 => orderedInterval (-4599934418 / 1000000000000) (-4599930122 / 1000000000000)
      | 2 => orderedInterval (-3489147046 / 1000000000000) (-3489146560 / 1000000000000)
      | 3 => orderedInterval (-10645476344 / 1000000000000) (-10645469767 / 1000000000000)
      | 4 => orderedInterval (-6674449840 / 1000000000000) (-6674449732 / 1000000000000)
      | 5 => orderedInterval (-2018245390 / 1000000000000) (-2018240583 / 1000000000000)
      | 6 => orderedInterval (-7179680568 / 1000000000000) (-7179679386 / 1000000000000)
      | 7 => orderedInterval (3523621556 / 1000000000000) (3523622267 / 1000000000000)
      | _ => orderedInterval (-19645903281 / 1000000000000) (-19645903093 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-853481369 / 1000000000000) (-853480461 / 1000000000000)
      | 1 => orderedInterval (7914032732 / 1000000000000) (7914039404 / 1000000000000)
      | 2 => orderedInterval (-4951578494 / 1000000000000) (-4951577770 / 1000000000000)
      | 3 => orderedInterval (79089323680 / 1000000000000) (79089338702 / 1000000000000)
      | 4 => orderedInterval (1378046483 / 1000000000000) (1378046661 / 1000000000000)
      | 5 => orderedInterval (6619827613 / 1000000000000) (6619835441 / 1000000000000)
      | 6 => orderedInterval (-3265242158 / 1000000000000) (-3265241127 / 1000000000000)
      | 7 => orderedInterval (3160353977 / 1000000000000) (3160354548 / 1000000000000)
      | _ => orderedInterval (-12542977713 / 1000000000000) (-12542977409 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-20967685486 / 1000000000000) (-20967684570 / 1000000000000)
      | 1 => orderedInterval (12203827515 / 1000000000000) (12203837984 / 1000000000000)
      | 2 => orderedInterval (11261752513 / 1000000000000) (11261753603 / 1000000000000)
      | 3 => orderedInterval (71486062614 / 1000000000000) (71486097013 / 1000000000000)
      | 4 => orderedInterval (10250252259 / 1000000000000) (10250252559 / 1000000000000)
      | 5 => orderedInterval (8234324401 / 1000000000000) (8234337379 / 1000000000000)
      | 6 => orderedInterval (7517141934 / 1000000000000) (7517142838 / 1000000000000)
      | 7 => orderedInterval (-3782365012 / 1000000000000) (-3782364551 / 1000000000000)
      | _ => orderedInterval (50135950252 / 1000000000000) (50135950759 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-29157991 / 1000000000000) (-29148255 / 1000000000000)
    | 1 => orderedInterval (-13913067655 / 1000000000000) (-13913055224 / 1000000000000)
    | 2 => orderedInterval (-30373847102 / 1000000000000) (-30373827843 / 1000000000000)
    | 3 => orderedInterval (76548304751 / 1000000000000) (76548337989 / 1000000000000)
    | _ => orderedInterval (146339260990 / 1000000000000) (146339323014 / 1000000000000)

theorem compactCertificate384_stateChecks0 :
    compactCertificate384.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (511 / 2)) (orderedInterval (-48424564524 / 1000000000000) (-48424562311 / 1000000000000), orderedInterval (12207564258 / 1000000000000) (12207566471 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (752800574377411 / 4000000000000)) (orderedInterval (27336926045 / 1000000000000) (27336926046 / 1000000000000), orderedInterval (51263260775 / 1000000000000) (51263260776 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 97 12 (243440238489763 / 800000000000)) (orderedInterval (-15718158288 / 1000000000000) (-15718158287 / 1000000000000), orderedInterval (-42927858214 / 1000000000000) (-42927858213 / 1000000000000))) = true
  rfl'

theorem compactCertificate384_stateChecks1 :
    compactCertificate384.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 17 12 (219665330091977 / 4000000000000)) (orderedInterval (-80831760839 / 1000000000000) (-80831675517 / 1000000000000), orderedInterval (71860466489 / 1000000000000) (71860551811 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (590051975111669 / 4000000000000)) (orderedInterval (-39373567597 / 1000000000000) (-39373567596 / 1000000000000), orderedInterval (-52453758977 / 1000000000000) (-52453758976 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 128 12 (1602105893883873 / 4000000000000)) (orderedInterval (-28939032477 / 1000000000000) (-28939008474 / 1000000000000), orderedInterval (27458557599 / 1000000000000) (27458581602 / 1000000000000))) = true
  rfl'

theorem compactCertificate384_stateChecks2 :
    compactCertificate384.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 94 12 (1180103950223849 / 4000000000000)) (orderedInterval (22321587223 / 1000000000000) (22321587224 / 1000000000000), orderedInterval (40700253733 / 1000000000000) (40700253734 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 161 12 (2022128232936077 / 4000000000000)) (orderedInterval (-17657017988 / 1000000000000) (-17657017987 / 1000000000000), orderedInterval (-30764616373 / 1000000000000) (-30764616372 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 119 12 (1489490504127143 / 4000000000000)) (orderedInterval (26377866446 / 1000000000000) (26377875016 / 1000000000000), orderedInterval (-31876264171 / 1000000000000) (-31876255602 / 1000000000000))) = true
  rfl'

theorem compactCertificate384_stateChecks3 :
    compactCertificate384.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 182 12 (2285261473004489 / 4000000000000)) (orderedInterval (10838566444 / 1000000000000) (10838566445 / 1000000000000), orderedInterval (31563147562 / 1000000000000) (31563147563 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 105 12 (1319396326607681 / 4000000000000)) (orderedInterval (-30483900365 / 1000000000000) (-30483900364 / 1000000000000), orderedInterval (-31588667333 / 1000000000000) (-31588667332 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 186 12 (2341291934759029 / 4000000000000)) (orderedInterval (32314482312 / 1000000000000) (32314490509 / 1000000000000), orderedInterval (-6616388441 / 1000000000000) (-6616380244 / 1000000000000))) = true
  rfl'

theorem compactCertificate384_stateChecks4 :
    compactCertificate384.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 174 12 (2187538629853801 / 4000000000000)) (orderedInterval (29297313753 / 1000000000000) (29297313754 / 1000000000000), orderedInterval (17458961304 / 1000000000000) (17458961305 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 124 12 (1561130786747833 / 4000000000000)) (orderedInterval (40313884888 / 1000000000000) (40313885002 / 1000000000000), orderedInterval (2390762210 / 1000000000000) (2390762324 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 141 12 (1770155925335007 / 4000000000000)) (orderedInterval (-13344603977 / 1000000000000) (-13344603976 / 1000000000000), orderedInterval (-35488221967 / 1000000000000) (-35488221966 / 1000000000000))) = true
  rfl'

theorem compactCertificate384_stateChecks5 :
    compactCertificate384.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 117 12 (1475771462511983 / 4000000000000)) (orderedInterval (-34498609105 / 1000000000000) (-34498502510 / 1000000000000), orderedInterval (23184825823 / 1000000000000) (23184932418 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 104 12 (1303888842787643 / 4000000000000)) (orderedInterval (1395786343 / 1000000000000) (1395786345 / 1000000000000), orderedInterval (44168459449 / 1000000000000) (44168459450 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 150 12 (377917808148657 / 800000000000)) (orderedInterval (34189912695 / 1000000000000) (34189937548 / 1000000000000), orderedInterval (-13403507034 / 1000000000000) (-13403482181 / 1000000000000))) = true
  rfl'

theorem compactCertificate384_stateChecks6 :
    compactCertificate384.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (1045340546063779 / 4000000000000)) (orderedInterval (-48343315948 / 1000000000000) (-48343315943 / 1000000000000), orderedInterval (-9854765606 / 1000000000000) (-9854765601 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (886146757727819 / 4000000000000)) (orderedInterval (35810544299 / 1000000000000) (35810570588 / 1000000000000), orderedInterval (-39971418578 / 1000000000000) (-39971392289 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (554509495872857 / 4000000000000)) (orderedInterval (62703384353 / 1000000000000) (62703384354 / 1000000000000), orderedInterval (25475470739 / 1000000000000) (25475470740 / 1000000000000))) = true
  rfl'

theorem compactCertificate384_stateChecks7 :
    compactCertificate384.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 24 12 (298217051095719 / 4000000000000)) (orderedInterval (-5563083915 / 1000000000000) (-5563083895 / 1000000000000), orderedInterval (92277510316 / 1000000000000) (92277510336 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (809717305204157 / 4000000000000)) (orderedInterval (46865744843 / 1000000000000) (46865792628 / 1000000000000), orderedInterval (-30913422710 / 1000000000000) (-30913374925 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 88 12 (1105599755394589 / 4000000000000)) (orderedInterval (31815679359 / 1000000000000) (31815679360 / 1000000000000), orderedInterval (35873197098 / 1000000000000) (35873197099 / 1000000000000))) = true
  rfl'

theorem compactCertificate384_stateChecks8 :
    compactCertificate384.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (467490504127143 / 4000000000000)) (orderedInterval (-72944729925 / 1000000000000) (-72944729921 / 1000000000000), orderedInterval (-10919302252 / 1000000000000) (-10919302248 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 151 12 (1900322944980103 / 4000000000000)) (orderedInterval (-36472877558 / 1000000000000) (-36472877412 / 1000000000000), orderedInterval (-3084571633 / 1000000000000) (-3084571487 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 101 12 (1269327658559177 / 4000000000000)) (orderedInterval (-32627540843 / 1000000000000) (-32627540842 / 1000000000000), orderedInterval (-30634208757 / 1000000000000) (-30634208756 / 1000000000000))) = true
  rfl'

theorem compactCertificate384_states : ∀ j,
    BesselStateValid (compactCertificate384.point j) (compactCertificate384.state j) :=
  compactCertificate384.statesValid_of_checks3 compactCertificate384_stateChecks0
    compactCertificate384_stateChecks1 compactCertificate384_stateChecks2
    compactCertificate384_stateChecks3 compactCertificate384_stateChecks4
    compactCertificate384_stateChecks5 compactCertificate384_stateChecks6
    compactCertificate384_stateChecks7 compactCertificate384_stateChecks8

theorem compactCertificate384_chunkChecks0_0 :
    compactCertificate384.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (511 / 2) 0 (IntervalRat.scale (511 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-48424564524 / 1000000000000) (-48424562311 / 1000000000000), orderedInterval (12207564258 / 1000000000000) (12207566471 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (752800574377411 / 4000000000000) 0 (IntervalRat.scale (511 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (27336926045 / 1000000000000) (27336926046 / 1000000000000), orderedInterval (51263260775 / 1000000000000) (51263260776 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (243440238489763 / 800000000000) 0 (IntervalRat.scale (511 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-15718158288 / 1000000000000) (-15718158287 / 1000000000000), orderedInterval (-42927858214 / 1000000000000) (-42927858213 / 1000000000000)))) (orderedInterval (-19861434518 / 1000000000000) (-19861433622 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (219665330091977 / 4000000000000) 0 (IntervalRat.scale (511 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-80831760839 / 1000000000000) (-80831675517 / 1000000000000), orderedInterval (71860466489 / 1000000000000) (71860551811 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (590051975111669 / 4000000000000) 0 (IntervalRat.scale (511 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-39373567597 / 1000000000000) (-39373567596 / 1000000000000), orderedInterval (-52453758977 / 1000000000000) (-52453758976 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1602105893883873 / 4000000000000) 0 (IntervalRat.scale (511 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28939032477 / 1000000000000) (-28939008474 / 1000000000000), orderedInterval (27458557599 / 1000000000000) (27458581602 / 1000000000000)))) (orderedInterval (1496632378 / 1000000000000) (1496635042 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1180103950223849 / 4000000000000) 0 (IntervalRat.scale (511 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (22321587223 / 1000000000000) (22321587224 / 1000000000000), orderedInterval (40700253733 / 1000000000000) (40700253734 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2022128232936077 / 4000000000000) 0 (IntervalRat.scale (511 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-17657017988 / 1000000000000) (-17657017987 / 1000000000000), orderedInterval (-30764616373 / 1000000000000) (-30764616372 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1489490504127143 / 4000000000000) 0 (IntervalRat.scale (511 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (26377866446 / 1000000000000) (26377875016 / 1000000000000), orderedInterval (-31876264171 / 1000000000000) (-31876255602 / 1000000000000)))) (orderedInterval (1182114061 / 1000000000000) (1182114284 / 1000000000000))) = true
  rfl'

theorem compactCertificate384_chunkChecks0_1 :
    compactCertificate384.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2285261473004489 / 4000000000000) 0 (IntervalRat.scale (511 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (10838566444 / 1000000000000) (10838566445 / 1000000000000), orderedInterval (31563147562 / 1000000000000) (31563147563 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1319396326607681 / 4000000000000) 0 (IntervalRat.scale (511 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-30483900365 / 1000000000000) (-30483900364 / 1000000000000), orderedInterval (-31588667333 / 1000000000000) (-31588667332 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2341291934759029 / 4000000000000) 0 (IntervalRat.scale (511 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (32314482312 / 1000000000000) (32314490509 / 1000000000000), orderedInterval (-6616388441 / 1000000000000) (-6616380244 / 1000000000000)))) (orderedInterval (409205449 / 1000000000000) (409206716 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2187538629853801 / 4000000000000) 0 (IntervalRat.scale (511 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (29297313753 / 1000000000000) (29297313754 / 1000000000000), orderedInterval (17458961304 / 1000000000000) (17458961305 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1561130786747833 / 4000000000000) 0 (IntervalRat.scale (511 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (40313884888 / 1000000000000) (40313885002 / 1000000000000), orderedInterval (2390762210 / 1000000000000) (2390762324 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1770155925335007 / 4000000000000) 0 (IntervalRat.scale (511 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-13344603977 / 1000000000000) (-13344603976 / 1000000000000), orderedInterval (-35488221967 / 1000000000000) (-35488221966 / 1000000000000)))) (orderedInterval (3350820937 / 1000000000000) (3350820979 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1475771462511983 / 4000000000000) 0 (IntervalRat.scale (511 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-34498609105 / 1000000000000) (-34498502510 / 1000000000000), orderedInterval (23184825823 / 1000000000000) (23184932418 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1303888842787643 / 4000000000000) 0 (IntervalRat.scale (511 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (1395786343 / 1000000000000) (1395786345 / 1000000000000), orderedInterval (44168459449 / 1000000000000) (44168459450 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (377917808148657 / 800000000000) 0 (IntervalRat.scale (511 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (34189912695 / 1000000000000) (34189937548 / 1000000000000), orderedInterval (-13403507034 / 1000000000000) (-13403482181 / 1000000000000)))) (orderedInterval (397142035 / 1000000000000) (397143927 / 1000000000000))) = true
  rfl'

theorem compactCertificate384_chunkChecks0_2 :
    compactCertificate384.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1045340546063779 / 4000000000000) 0 (IntervalRat.scale (511 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-48343315948 / 1000000000000) (-48343315943 / 1000000000000), orderedInterval (-9854765606 / 1000000000000) (-9854765601 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (886146757727819 / 4000000000000) 0 (IntervalRat.scale (511 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (35810544299 / 1000000000000) (35810570588 / 1000000000000), orderedInterval (-39971418578 / 1000000000000) (-39971392289 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (554509495872857 / 4000000000000) 0 (IntervalRat.scale (511 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (62703384353 / 1000000000000) (62703384354 / 1000000000000), orderedInterval (25475470739 / 1000000000000) (25475470740 / 1000000000000)))) (orderedInterval (7744179759 / 1000000000000) (7744181312 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (298217051095719 / 4000000000000) 0 (IntervalRat.scale (511 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-5563083915 / 1000000000000) (-5563083895 / 1000000000000), orderedInterval (92277510316 / 1000000000000) (92277510336 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (809717305204157 / 4000000000000) 0 (IntervalRat.scale (511 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (46865744843 / 1000000000000) (46865792628 / 1000000000000), orderedInterval (-30913422710 / 1000000000000) (-30913374925 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1105599755394589 / 4000000000000) 0 (IntervalRat.scale (511 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (31815679359 / 1000000000000) (31815679360 / 1000000000000), orderedInterval (35873197098 / 1000000000000) (35873197099 / 1000000000000)))) (orderedInterval (-3398832505 / 1000000000000) (-3398831389 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (467490504127143 / 4000000000000) 0 (IntervalRat.scale (511 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-72944729925 / 1000000000000) (-72944729921 / 1000000000000), orderedInterval (-10919302252 / 1000000000000) (-10919302248 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1900322944980103 / 4000000000000) 0 (IntervalRat.scale (511 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-36472877558 / 1000000000000) (-36472877412 / 1000000000000), orderedInterval (-3084571633 / 1000000000000) (-3084571487 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1269327658559177 / 4000000000000) 0 (IntervalRat.scale (511 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-32627540843 / 1000000000000) (-32627540842 / 1000000000000), orderedInterval (-30634208757 / 1000000000000) (-30634208756 / 1000000000000)))) (orderedInterval (8651014413 / 1000000000000) (8651014496 / 1000000000000))) = true
  rfl'

theorem compactCertificate384_chunkChecks0 :
    compactCertificate384.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate384.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate384_chunkChecks0_0
    compactCertificate384_chunkChecks0_1 compactCertificate384_chunkChecks0_2

theorem compactCertificate384_chunkChecks1_0 :
    compactCertificate384.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (511 / 2) 1 (IntervalRat.scale (511 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-48424564524 / 1000000000000) (-48424562311 / 1000000000000), orderedInterval (12207564258 / 1000000000000) (12207566471 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (752800574377411 / 4000000000000) 1 (IntervalRat.scale (511 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (27336926045 / 1000000000000) (27336926046 / 1000000000000), orderedInterval (51263260775 / 1000000000000) (51263260776 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (243440238489763 / 800000000000) 1 (IntervalRat.scale (511 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-15718158288 / 1000000000000) (-15718158287 / 1000000000000), orderedInterval (-42927858214 / 1000000000000) (-42927858213 / 1000000000000)))) (orderedInterval (2190310423 / 1000000000000) (2190311321 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (219665330091977 / 4000000000000) 1 (IntervalRat.scale (511 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-80831760839 / 1000000000000) (-80831675517 / 1000000000000), orderedInterval (71860466489 / 1000000000000) (71860551811 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (590051975111669 / 4000000000000) 1 (IntervalRat.scale (511 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-39373567597 / 1000000000000) (-39373567596 / 1000000000000), orderedInterval (-52453758977 / 1000000000000) (-52453758976 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1602105893883873 / 4000000000000) 1 (IntervalRat.scale (511 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28939032477 / 1000000000000) (-28939008474 / 1000000000000), orderedInterval (27458557599 / 1000000000000) (27458581602 / 1000000000000)))) (orderedInterval (-4333324521 / 1000000000000) (-4333321612 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1180103950223849 / 4000000000000) 1 (IntervalRat.scale (511 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (22321587223 / 1000000000000) (22321587224 / 1000000000000), orderedInterval (40700253733 / 1000000000000) (40700253734 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2022128232936077 / 4000000000000) 1 (IntervalRat.scale (511 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-17657017988 / 1000000000000) (-17657017987 / 1000000000000), orderedInterval (-30764616373 / 1000000000000) (-30764616372 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1489490504127143 / 4000000000000) 1 (IntervalRat.scale (511 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (26377866446 / 1000000000000) (26377875016 / 1000000000000), orderedInterval (-31876264171 / 1000000000000) (-31876255602 / 1000000000000)))) (orderedInterval (754718221 / 1000000000000) (754718549 / 1000000000000))) = true
  rfl'

theorem compactCertificate384_chunkChecks1_1 :
    compactCertificate384.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2285261473004489 / 4000000000000) 1 (IntervalRat.scale (511 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (10838566444 / 1000000000000) (10838566445 / 1000000000000), orderedInterval (31563147562 / 1000000000000) (31563147563 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1319396326607681 / 4000000000000) 1 (IntervalRat.scale (511 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-30483900365 / 1000000000000) (-30483900364 / 1000000000000), orderedInterval (-31588667333 / 1000000000000) (-31588667332 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2341291934759029 / 4000000000000) 1 (IntervalRat.scale (511 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (32314482312 / 1000000000000) (32314490509 / 1000000000000), orderedInterval (-6616388441 / 1000000000000) (-6616380244 / 1000000000000)))) (orderedInterval (-17716981623 / 1000000000000) (-17716978743 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2187538629853801 / 4000000000000) 1 (IntervalRat.scale (511 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (29297313753 / 1000000000000) (29297313754 / 1000000000000), orderedInterval (17458961304 / 1000000000000) (17458961305 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1561130786747833 / 4000000000000) 1 (IntervalRat.scale (511 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (40313884888 / 1000000000000) (40313885002 / 1000000000000), orderedInterval (2390762210 / 1000000000000) (2390762324 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1770155925335007 / 4000000000000) 1 (IntervalRat.scale (511 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-13344603977 / 1000000000000) (-13344603976 / 1000000000000), orderedInterval (-35488221967 / 1000000000000) (-35488221966 / 1000000000000)))) (orderedInterval (-18244778 / 1000000000000) (-18244712 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1475771462511983 / 4000000000000) 1 (IntervalRat.scale (511 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-34498609105 / 1000000000000) (-34498502510 / 1000000000000), orderedInterval (23184825823 / 1000000000000) (23184932418 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1303888842787643 / 4000000000000) 1 (IntervalRat.scale (511 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (1395786343 / 1000000000000) (1395786345 / 1000000000000), orderedInterval (44168459449 / 1000000000000) (44168459450 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (377917808148657 / 800000000000) 1 (IntervalRat.scale (511 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (34189912695 / 1000000000000) (34189937548 / 1000000000000), orderedInterval (-13403507034 / 1000000000000) (-13403482181 / 1000000000000)))) (orderedInterval (-3472693625 / 1000000000000) (-3472690635 / 1000000000000))) = true
  rfl'

theorem compactCertificate384_chunkChecks1_2 :
    compactCertificate384.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1045340546063779 / 4000000000000) 1 (IntervalRat.scale (511 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-48343315948 / 1000000000000) (-48343315943 / 1000000000000), orderedInterval (-9854765606 / 1000000000000) (-9854765601 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (886146757727819 / 4000000000000) 1 (IntervalRat.scale (511 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (35810544299 / 1000000000000) (35810570588 / 1000000000000), orderedInterval (-39971418578 / 1000000000000) (-39971392289 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (554509495872857 / 4000000000000) 1 (IntervalRat.scale (511 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (62703384353 / 1000000000000) (62703384354 / 1000000000000), orderedInterval (25475470739 / 1000000000000) (25475470740 / 1000000000000)))) (orderedInterval (4023320983 / 1000000000000) (4023322334 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (298217051095719 / 4000000000000) 1 (IntervalRat.scale (511 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-5563083915 / 1000000000000) (-5563083895 / 1000000000000), orderedInterval (92277510316 / 1000000000000) (92277510336 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (809717305204157 / 4000000000000) 1 (IntervalRat.scale (511 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (46865744843 / 1000000000000) (46865792628 / 1000000000000), orderedInterval (-30913422710 / 1000000000000) (-30913374925 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1105599755394589 / 4000000000000) 1 (IntervalRat.scale (511 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (31815679359 / 1000000000000) (31815679360 / 1000000000000), orderedInterval (35873197098 / 1000000000000) (35873197099 / 1000000000000)))) (orderedInterval (-2915718453 / 1000000000000) (-2915717566 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (467490504127143 / 4000000000000) 1 (IntervalRat.scale (511 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-72944729925 / 1000000000000) (-72944729921 / 1000000000000), orderedInterval (-10919302252 / 1000000000000) (-10919302248 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1900322944980103 / 4000000000000) 1 (IntervalRat.scale (511 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-36472877558 / 1000000000000) (-36472877412 / 1000000000000), orderedInterval (-3084571633 / 1000000000000) (-3084571487 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1269327658559177 / 4000000000000) 1 (IntervalRat.scale (511 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-32627540843 / 1000000000000) (-32627540842 / 1000000000000), orderedInterval (-30634208757 / 1000000000000) (-30634208756 / 1000000000000)))) (orderedInterval (7575545718 / 1000000000000) (7575545840 / 1000000000000))) = true
  rfl'

theorem compactCertificate384_chunkChecks1 :
    compactCertificate384.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate384.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate384_chunkChecks1_0
    compactCertificate384_chunkChecks1_1 compactCertificate384_chunkChecks1_2

theorem compactCertificate384_chunkChecks2_0 :
    compactCertificate384.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (511 / 2) 2 (IntervalRat.scale (511 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-48424564524 / 1000000000000) (-48424562311 / 1000000000000), orderedInterval (12207564258 / 1000000000000) (12207566471 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (752800574377411 / 4000000000000) 2 (IntervalRat.scale (511 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (27336926045 / 1000000000000) (27336926046 / 1000000000000), orderedInterval (51263260775 / 1000000000000) (51263260776 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (243440238489763 / 800000000000) 2 (IntervalRat.scale (511 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-15718158288 / 1000000000000) (-15718158287 / 1000000000000), orderedInterval (-42927858214 / 1000000000000) (-42927858213 / 1000000000000)))) (orderedInterval (20355368229 / 1000000000000) (20355369133 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (219665330091977 / 4000000000000) 2 (IntervalRat.scale (511 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-80831760839 / 1000000000000) (-80831675517 / 1000000000000), orderedInterval (71860466489 / 1000000000000) (71860551811 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (590051975111669 / 4000000000000) 2 (IntervalRat.scale (511 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-39373567597 / 1000000000000) (-39373567596 / 1000000000000), orderedInterval (-52453758977 / 1000000000000) (-52453758976 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1602105893883873 / 4000000000000) 2 (IntervalRat.scale (511 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28939032477 / 1000000000000) (-28939008474 / 1000000000000), orderedInterval (27458557599 / 1000000000000) (27458581602 / 1000000000000)))) (orderedInterval (-4599934418 / 1000000000000) (-4599930122 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1180103950223849 / 4000000000000) 2 (IntervalRat.scale (511 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (22321587223 / 1000000000000) (22321587224 / 1000000000000), orderedInterval (40700253733 / 1000000000000) (40700253734 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2022128232936077 / 4000000000000) 2 (IntervalRat.scale (511 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-17657017988 / 1000000000000) (-17657017987 / 1000000000000), orderedInterval (-30764616373 / 1000000000000) (-30764616372 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1489490504127143 / 4000000000000) 2 (IntervalRat.scale (511 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (26377866446 / 1000000000000) (26377875016 / 1000000000000), orderedInterval (-31876264171 / 1000000000000) (-31876255602 / 1000000000000)))) (orderedInterval (-3489147046 / 1000000000000) (-3489146560 / 1000000000000))) = true
  rfl'

theorem compactCertificate384_chunkChecks2_1 :
    compactCertificate384.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2285261473004489 / 4000000000000) 2 (IntervalRat.scale (511 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (10838566444 / 1000000000000) (10838566445 / 1000000000000), orderedInterval (31563147562 / 1000000000000) (31563147563 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1319396326607681 / 4000000000000) 2 (IntervalRat.scale (511 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-30483900365 / 1000000000000) (-30483900364 / 1000000000000), orderedInterval (-31588667333 / 1000000000000) (-31588667332 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2341291934759029 / 4000000000000) 2 (IntervalRat.scale (511 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (32314482312 / 1000000000000) (32314490509 / 1000000000000), orderedInterval (-6616388441 / 1000000000000) (-6616380244 / 1000000000000)))) (orderedInterval (-10645476344 / 1000000000000) (-10645469767 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2187538629853801 / 4000000000000) 2 (IntervalRat.scale (511 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (29297313753 / 1000000000000) (29297313754 / 1000000000000), orderedInterval (17458961304 / 1000000000000) (17458961305 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1561130786747833 / 4000000000000) 2 (IntervalRat.scale (511 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (40313884888 / 1000000000000) (40313885002 / 1000000000000), orderedInterval (2390762210 / 1000000000000) (2390762324 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1770155925335007 / 4000000000000) 2 (IntervalRat.scale (511 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-13344603977 / 1000000000000) (-13344603976 / 1000000000000), orderedInterval (-35488221967 / 1000000000000) (-35488221966 / 1000000000000)))) (orderedInterval (-6674449840 / 1000000000000) (-6674449732 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1475771462511983 / 4000000000000) 2 (IntervalRat.scale (511 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-34498609105 / 1000000000000) (-34498502510 / 1000000000000), orderedInterval (23184825823 / 1000000000000) (23184932418 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1303888842787643 / 4000000000000) 2 (IntervalRat.scale (511 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (1395786343 / 1000000000000) (1395786345 / 1000000000000), orderedInterval (44168459449 / 1000000000000) (44168459450 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (377917808148657 / 800000000000) 2 (IntervalRat.scale (511 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (34189912695 / 1000000000000) (34189937548 / 1000000000000), orderedInterval (-13403507034 / 1000000000000) (-13403482181 / 1000000000000)))) (orderedInterval (-2018245390 / 1000000000000) (-2018240583 / 1000000000000))) = true
  rfl'

theorem compactCertificate384_chunkChecks2_2 :
    compactCertificate384.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1045340546063779 / 4000000000000) 2 (IntervalRat.scale (511 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-48343315948 / 1000000000000) (-48343315943 / 1000000000000), orderedInterval (-9854765606 / 1000000000000) (-9854765601 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (886146757727819 / 4000000000000) 2 (IntervalRat.scale (511 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (35810544299 / 1000000000000) (35810570588 / 1000000000000), orderedInterval (-39971418578 / 1000000000000) (-39971392289 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (554509495872857 / 4000000000000) 2 (IntervalRat.scale (511 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (62703384353 / 1000000000000) (62703384354 / 1000000000000), orderedInterval (25475470739 / 1000000000000) (25475470740 / 1000000000000)))) (orderedInterval (-7179680568 / 1000000000000) (-7179679386 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (298217051095719 / 4000000000000) 2 (IntervalRat.scale (511 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-5563083915 / 1000000000000) (-5563083895 / 1000000000000), orderedInterval (92277510316 / 1000000000000) (92277510336 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (809717305204157 / 4000000000000) 2 (IntervalRat.scale (511 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (46865744843 / 1000000000000) (46865792628 / 1000000000000), orderedInterval (-30913422710 / 1000000000000) (-30913374925 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1105599755394589 / 4000000000000) 2 (IntervalRat.scale (511 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (31815679359 / 1000000000000) (31815679360 / 1000000000000), orderedInterval (35873197098 / 1000000000000) (35873197099 / 1000000000000)))) (orderedInterval (3523621556 / 1000000000000) (3523622267 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (467490504127143 / 4000000000000) 2 (IntervalRat.scale (511 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-72944729925 / 1000000000000) (-72944729921 / 1000000000000), orderedInterval (-10919302252 / 1000000000000) (-10919302248 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1900322944980103 / 4000000000000) 2 (IntervalRat.scale (511 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-36472877558 / 1000000000000) (-36472877412 / 1000000000000), orderedInterval (-3084571633 / 1000000000000) (-3084571487 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1269327658559177 / 4000000000000) 2 (IntervalRat.scale (511 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-32627540843 / 1000000000000) (-32627540842 / 1000000000000), orderedInterval (-30634208757 / 1000000000000) (-30634208756 / 1000000000000)))) (orderedInterval (-19645903281 / 1000000000000) (-19645903093 / 1000000000000))) = true
  rfl'

theorem compactCertificate384_chunkChecks2 :
    compactCertificate384.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate384.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate384_chunkChecks2_0
    compactCertificate384_chunkChecks2_1 compactCertificate384_chunkChecks2_2

theorem compactCertificate384_chunkChecks3_0 :
    compactCertificate384.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (511 / 2) 3 (IntervalRat.scale (511 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-48424564524 / 1000000000000) (-48424562311 / 1000000000000), orderedInterval (12207564258 / 1000000000000) (12207566471 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (752800574377411 / 4000000000000) 3 (IntervalRat.scale (511 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (27336926045 / 1000000000000) (27336926046 / 1000000000000), orderedInterval (51263260775 / 1000000000000) (51263260776 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (243440238489763 / 800000000000) 3 (IntervalRat.scale (511 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-15718158288 / 1000000000000) (-15718158287 / 1000000000000), orderedInterval (-42927858214 / 1000000000000) (-42927858213 / 1000000000000)))) (orderedInterval (-853481369 / 1000000000000) (-853480461 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (219665330091977 / 4000000000000) 3 (IntervalRat.scale (511 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-80831760839 / 1000000000000) (-80831675517 / 1000000000000), orderedInterval (71860466489 / 1000000000000) (71860551811 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (590051975111669 / 4000000000000) 3 (IntervalRat.scale (511 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-39373567597 / 1000000000000) (-39373567596 / 1000000000000), orderedInterval (-52453758977 / 1000000000000) (-52453758976 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1602105893883873 / 4000000000000) 3 (IntervalRat.scale (511 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28939032477 / 1000000000000) (-28939008474 / 1000000000000), orderedInterval (27458557599 / 1000000000000) (27458581602 / 1000000000000)))) (orderedInterval (7914032732 / 1000000000000) (7914039404 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1180103950223849 / 4000000000000) 3 (IntervalRat.scale (511 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (22321587223 / 1000000000000) (22321587224 / 1000000000000), orderedInterval (40700253733 / 1000000000000) (40700253734 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2022128232936077 / 4000000000000) 3 (IntervalRat.scale (511 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-17657017988 / 1000000000000) (-17657017987 / 1000000000000), orderedInterval (-30764616373 / 1000000000000) (-30764616372 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1489490504127143 / 4000000000000) 3 (IntervalRat.scale (511 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (26377866446 / 1000000000000) (26377875016 / 1000000000000), orderedInterval (-31876264171 / 1000000000000) (-31876255602 / 1000000000000)))) (orderedInterval (-4951578494 / 1000000000000) (-4951577770 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate384_chunkChecks3_1 :
    compactCertificate384.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2285261473004489 / 4000000000000) 3 (IntervalRat.scale (511 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (10838566444 / 1000000000000) (10838566445 / 1000000000000), orderedInterval (31563147562 / 1000000000000) (31563147563 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1319396326607681 / 4000000000000) 3 (IntervalRat.scale (511 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-30483900365 / 1000000000000) (-30483900364 / 1000000000000), orderedInterval (-31588667333 / 1000000000000) (-31588667332 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2341291934759029 / 4000000000000) 3 (IntervalRat.scale (511 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (32314482312 / 1000000000000) (32314490509 / 1000000000000), orderedInterval (-6616388441 / 1000000000000) (-6616380244 / 1000000000000)))) (orderedInterval (79089323680 / 1000000000000) (79089338702 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2187538629853801 / 4000000000000) 3 (IntervalRat.scale (511 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (29297313753 / 1000000000000) (29297313754 / 1000000000000), orderedInterval (17458961304 / 1000000000000) (17458961305 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1561130786747833 / 4000000000000) 3 (IntervalRat.scale (511 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (40313884888 / 1000000000000) (40313885002 / 1000000000000), orderedInterval (2390762210 / 1000000000000) (2390762324 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1770155925335007 / 4000000000000) 3 (IntervalRat.scale (511 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-13344603977 / 1000000000000) (-13344603976 / 1000000000000), orderedInterval (-35488221967 / 1000000000000) (-35488221966 / 1000000000000)))) (orderedInterval (1378046483 / 1000000000000) (1378046661 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1475771462511983 / 4000000000000) 3 (IntervalRat.scale (511 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-34498609105 / 1000000000000) (-34498502510 / 1000000000000), orderedInterval (23184825823 / 1000000000000) (23184932418 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1303888842787643 / 4000000000000) 3 (IntervalRat.scale (511 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (1395786343 / 1000000000000) (1395786345 / 1000000000000), orderedInterval (44168459449 / 1000000000000) (44168459450 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (377917808148657 / 800000000000) 3 (IntervalRat.scale (511 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (34189912695 / 1000000000000) (34189937548 / 1000000000000), orderedInterval (-13403507034 / 1000000000000) (-13403482181 / 1000000000000)))) (orderedInterval (6619827613 / 1000000000000) (6619835441 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate384_chunkChecks3_2 :
    compactCertificate384.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1045340546063779 / 4000000000000) 3 (IntervalRat.scale (511 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-48343315948 / 1000000000000) (-48343315943 / 1000000000000), orderedInterval (-9854765606 / 1000000000000) (-9854765601 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (886146757727819 / 4000000000000) 3 (IntervalRat.scale (511 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (35810544299 / 1000000000000) (35810570588 / 1000000000000), orderedInterval (-39971418578 / 1000000000000) (-39971392289 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (554509495872857 / 4000000000000) 3 (IntervalRat.scale (511 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (62703384353 / 1000000000000) (62703384354 / 1000000000000), orderedInterval (25475470739 / 1000000000000) (25475470740 / 1000000000000)))) (orderedInterval (-3265242158 / 1000000000000) (-3265241127 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (298217051095719 / 4000000000000) 3 (IntervalRat.scale (511 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-5563083915 / 1000000000000) (-5563083895 / 1000000000000), orderedInterval (92277510316 / 1000000000000) (92277510336 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (809717305204157 / 4000000000000) 3 (IntervalRat.scale (511 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (46865744843 / 1000000000000) (46865792628 / 1000000000000), orderedInterval (-30913422710 / 1000000000000) (-30913374925 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1105599755394589 / 4000000000000) 3 (IntervalRat.scale (511 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (31815679359 / 1000000000000) (31815679360 / 1000000000000), orderedInterval (35873197098 / 1000000000000) (35873197099 / 1000000000000)))) (orderedInterval (3160353977 / 1000000000000) (3160354548 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (467490504127143 / 4000000000000) 3 (IntervalRat.scale (511 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-72944729925 / 1000000000000) (-72944729921 / 1000000000000), orderedInterval (-10919302252 / 1000000000000) (-10919302248 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1900322944980103 / 4000000000000) 3 (IntervalRat.scale (511 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-36472877558 / 1000000000000) (-36472877412 / 1000000000000), orderedInterval (-3084571633 / 1000000000000) (-3084571487 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1269327658559177 / 4000000000000) 3 (IntervalRat.scale (511 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-32627540843 / 1000000000000) (-32627540842 / 1000000000000), orderedInterval (-30634208757 / 1000000000000) (-30634208756 / 1000000000000)))) (orderedInterval (-12542977713 / 1000000000000) (-12542977409 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate384_chunkChecks3 :
    compactCertificate384.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate384.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate384_chunkChecks3_0
    compactCertificate384_chunkChecks3_1 compactCertificate384_chunkChecks3_2

theorem compactCertificate384_chunkChecks4_0 :
    compactCertificate384.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (511 / 2) 4 (IntervalRat.scale (511 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-48424564524 / 1000000000000) (-48424562311 / 1000000000000), orderedInterval (12207564258 / 1000000000000) (12207566471 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (752800574377411 / 4000000000000) 4 (IntervalRat.scale (511 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (27336926045 / 1000000000000) (27336926046 / 1000000000000), orderedInterval (51263260775 / 1000000000000) (51263260776 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (243440238489763 / 800000000000) 4 (IntervalRat.scale (511 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-15718158288 / 1000000000000) (-15718158287 / 1000000000000), orderedInterval (-42927858214 / 1000000000000) (-42927858213 / 1000000000000)))) (orderedInterval (-20967685486 / 1000000000000) (-20967684570 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (219665330091977 / 4000000000000) 4 (IntervalRat.scale (511 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-80831760839 / 1000000000000) (-80831675517 / 1000000000000), orderedInterval (71860466489 / 1000000000000) (71860551811 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (590051975111669 / 4000000000000) 4 (IntervalRat.scale (511 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-39373567597 / 1000000000000) (-39373567596 / 1000000000000), orderedInterval (-52453758977 / 1000000000000) (-52453758976 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1602105893883873 / 4000000000000) 4 (IntervalRat.scale (511 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28939032477 / 1000000000000) (-28939008474 / 1000000000000), orderedInterval (27458557599 / 1000000000000) (27458581602 / 1000000000000)))) (orderedInterval (12203827515 / 1000000000000) (12203837984 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1180103950223849 / 4000000000000) 4 (IntervalRat.scale (511 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (22321587223 / 1000000000000) (22321587224 / 1000000000000), orderedInterval (40700253733 / 1000000000000) (40700253734 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2022128232936077 / 4000000000000) 4 (IntervalRat.scale (511 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-17657017988 / 1000000000000) (-17657017987 / 1000000000000), orderedInterval (-30764616373 / 1000000000000) (-30764616372 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1489490504127143 / 4000000000000) 4 (IntervalRat.scale (511 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (26377866446 / 1000000000000) (26377875016 / 1000000000000), orderedInterval (-31876264171 / 1000000000000) (-31876255602 / 1000000000000)))) (orderedInterval (11261752513 / 1000000000000) (11261753603 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate384_chunkChecks4_1 :
    compactCertificate384.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2285261473004489 / 4000000000000) 4 (IntervalRat.scale (511 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (10838566444 / 1000000000000) (10838566445 / 1000000000000), orderedInterval (31563147562 / 1000000000000) (31563147563 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1319396326607681 / 4000000000000) 4 (IntervalRat.scale (511 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-30483900365 / 1000000000000) (-30483900364 / 1000000000000), orderedInterval (-31588667333 / 1000000000000) (-31588667332 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2341291934759029 / 4000000000000) 4 (IntervalRat.scale (511 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (32314482312 / 1000000000000) (32314490509 / 1000000000000), orderedInterval (-6616388441 / 1000000000000) (-6616380244 / 1000000000000)))) (orderedInterval (71486062614 / 1000000000000) (71486097013 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2187538629853801 / 4000000000000) 4 (IntervalRat.scale (511 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (29297313753 / 1000000000000) (29297313754 / 1000000000000), orderedInterval (17458961304 / 1000000000000) (17458961305 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1561130786747833 / 4000000000000) 4 (IntervalRat.scale (511 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (40313884888 / 1000000000000) (40313885002 / 1000000000000), orderedInterval (2390762210 / 1000000000000) (2390762324 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1770155925335007 / 4000000000000) 4 (IntervalRat.scale (511 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-13344603977 / 1000000000000) (-13344603976 / 1000000000000), orderedInterval (-35488221967 / 1000000000000) (-35488221966 / 1000000000000)))) (orderedInterval (10250252259 / 1000000000000) (10250252559 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1475771462511983 / 4000000000000) 4 (IntervalRat.scale (511 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-34498609105 / 1000000000000) (-34498502510 / 1000000000000), orderedInterval (23184825823 / 1000000000000) (23184932418 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1303888842787643 / 4000000000000) 4 (IntervalRat.scale (511 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (1395786343 / 1000000000000) (1395786345 / 1000000000000), orderedInterval (44168459449 / 1000000000000) (44168459450 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (377917808148657 / 800000000000) 4 (IntervalRat.scale (511 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (34189912695 / 1000000000000) (34189937548 / 1000000000000), orderedInterval (-13403507034 / 1000000000000) (-13403482181 / 1000000000000)))) (orderedInterval (8234324401 / 1000000000000) (8234337379 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate384_chunkChecks4_2 :
    compactCertificate384.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1045340546063779 / 4000000000000) 4 (IntervalRat.scale (511 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-48343315948 / 1000000000000) (-48343315943 / 1000000000000), orderedInterval (-9854765606 / 1000000000000) (-9854765601 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (886146757727819 / 4000000000000) 4 (IntervalRat.scale (511 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (35810544299 / 1000000000000) (35810570588 / 1000000000000), orderedInterval (-39971418578 / 1000000000000) (-39971392289 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (554509495872857 / 4000000000000) 4 (IntervalRat.scale (511 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (62703384353 / 1000000000000) (62703384354 / 1000000000000), orderedInterval (25475470739 / 1000000000000) (25475470740 / 1000000000000)))) (orderedInterval (7517141934 / 1000000000000) (7517142838 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (298217051095719 / 4000000000000) 4 (IntervalRat.scale (511 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-5563083915 / 1000000000000) (-5563083895 / 1000000000000), orderedInterval (92277510316 / 1000000000000) (92277510336 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (809717305204157 / 4000000000000) 4 (IntervalRat.scale (511 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (46865744843 / 1000000000000) (46865792628 / 1000000000000), orderedInterval (-30913422710 / 1000000000000) (-30913374925 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1105599755394589 / 4000000000000) 4 (IntervalRat.scale (511 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (31815679359 / 1000000000000) (31815679360 / 1000000000000), orderedInterval (35873197098 / 1000000000000) (35873197099 / 1000000000000)))) (orderedInterval (-3782365012 / 1000000000000) (-3782364551 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (467490504127143 / 4000000000000) 4 (IntervalRat.scale (511 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-72944729925 / 1000000000000) (-72944729921 / 1000000000000), orderedInterval (-10919302252 / 1000000000000) (-10919302248 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1900322944980103 / 4000000000000) 4 (IntervalRat.scale (511 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-36472877558 / 1000000000000) (-36472877412 / 1000000000000), orderedInterval (-3084571633 / 1000000000000) (-3084571487 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1269327658559177 / 4000000000000) 4 (IntervalRat.scale (511 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-32627540843 / 1000000000000) (-32627540842 / 1000000000000), orderedInterval (-30634208757 / 1000000000000) (-30634208756 / 1000000000000)))) (orderedInterval (50135950252 / 1000000000000) (50135950759 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate384_chunkChecks4 :
    compactCertificate384.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate384.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate384_chunkChecks4_0
    compactCertificate384_chunkChecks4_1 compactCertificate384_chunkChecks4_2

theorem compactCertificate384_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate384.chunkCheck r b = true :=
  compactCertificate384.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate384_chunkChecks0
    · exact compactCertificate384_chunkChecks1
    · exact compactCertificate384_chunkChecks2
    · exact compactCertificate384_chunkChecks3
    · exact compactCertificate384_chunkChecks4)

theorem compactCertificate384_coefficient0 :
    compactCertificate384.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate384_coefficient1 :
    compactCertificate384.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate384_coefficient2 :
    compactCertificate384.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate384_coefficient3 :
    compactCertificate384.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate384_coefficient4 :
    compactCertificate384.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate384_coefficients : ∀ r : Fin 5,
    compactCertificate384.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate384_coefficient0
  · exact compactCertificate384_coefficient1
  · exact compactCertificate384_coefficient2
  · exact compactCertificate384_coefficient3
  · exact compactCertificate384_coefficient4

theorem compactCertificate384_lower : (1 : ℚ) ≤ compactCertificate384.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate384, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate384_proves {t : ℝ} (ht : t ∈ compactCertificate384.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate384.proves compactCertificate384_states compactCertificate384_chunks
    compactCertificate384_coefficients compactCertificate384_lower ht

end Erdos232
