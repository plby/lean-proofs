/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate364 : CompactCertificate where
  left := 235
  right := 236
  center := 471 / 2
  grid := fun i =>
    match i.val with
    | 0 => 75
    | 1 => 55
    | 2 => 89
    | 3 => 16
    | 4 => 43
    | 5 => 118
    | 6 => 87
    | 7 => 148
    | 8 => 109
    | 9 => 168
    | 10 => 97
    | 11 => 172
    | 12 => 161
    | 13 => 115
    | 14 => 130
    | 15 => 108
    | 16 => 96
    | 17 => 139
    | 18 => 77
    | 19 => 65
    | 20 => 41
    | 21 => 22
    | 22 => 59
    | 23 => 81
    | 24 => 34
    | 25 => 139
    | _ => 93
  point := fun i =>
    match i.val with
    | 0 => 471 / 2
    | 1 => 693872936461371 / 4000000000000
    | 2 => 224384251132443 / 800000000000
    | 3 => 202470392315697 / 4000000000000
    | 4 => 543863953576509 / 4000000000000
    | 5 => 1476696430566153 / 4000000000000
    | 6 => 1087727907153489 / 4000000000000
    | 7 => 1863840308635797 / 4000000000000
    | 8 => 1372896335506623 / 4000000000000
    | 9 => 2106376034804529 / 4000000000000
    | 10 => 1216116770708841 / 4000000000000
    | 11 => 2158020550433469 / 4000000000000
    | 12 => 2016302729278161 / 4000000000000
    | 13 => 1438928768215713 / 4000000000000
    | 14 => 1631591860729527 / 4000000000000
    | 15 => 1360251191473863 / 4000000000000
    | 16 => 1201823179947123 / 4000000000000
    | 17 => 348335200857177 / 800000000000
    | 18 => 963513497448219 / 4000000000000
    | 19 => 816781062406659 / 4000000000000
    | 20 => 511103664493377 / 4000000000000
    | 21 => 274873250618559 / 4000000000000
    | 22 => 746334345892677 / 4000000000000
    | 23 => 1019055743230629 / 4000000000000
    | 24 => 430896335506623 / 4000000000000
    | 25 => 1751569681185183 / 4000000000000
    | _ => 1169967372174897 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-32099813456 / 1000000000000) (-32099813455 / 1000000000000), orderedInterval (-40832606957 / 1000000000000) (-40832606956 / 1000000000000))
    | 1 => (orderedInterval (-60243288980 / 1000000000000) (-60243288968 / 1000000000000), orderedInterval (-6204553581 / 1000000000000) (-6204553570 / 1000000000000))
    | 2 => (orderedInterval (-47437180924 / 1000000000000) (-47437180506 / 1000000000000), orderedInterval (4495781516 / 1000000000000) (4495781934 / 1000000000000))
    | 3 => (orderedInterval (101665112518 / 1000000000000) (101665112519 / 1000000000000), orderedInterval (46333515660 / 1000000000000) (46333515661 / 1000000000000))
    | 4 => (orderedInterval (-68142075508 / 1000000000000) (-68142075351 / 1000000000000), orderedInterval (6481561518 / 1000000000000) (6481561675 / 1000000000000))
    | 5 => (orderedInterval (-28268490120 / 1000000000000) (-28268474847 / 1000000000000), orderedInterval (30457617147 / 1000000000000) (30457632419 / 1000000000000))
    | 6 => (orderedInterval (27385825396 / 1000000000000) (27385831120 / 1000000000000), orderedInterval (-39939166887 / 1000000000000) (-39939161163 / 1000000000000))
    | 7 => (orderedInterval (36082431167 / 1000000000000) (36082436435 / 1000000000000), orderedInterval (-8058144343 / 1000000000000) (-8058139074 / 1000000000000))
    | 8 => (orderedInterval (-43067147963 / 1000000000000) (-43067147763 / 1000000000000), orderedInterval (266115734 / 1000000000000) (266115935 / 1000000000000))
    | 9 => (orderedInterval (-13808404407 / 1000000000000) (-13808404288 / 1000000000000), orderedInterval (31923404696 / 1000000000000) (31923404816 / 1000000000000))
    | 10 => (orderedInterval (-3642828266 / 1000000000000) (-3642828265 / 1000000000000), orderedInterval (-45608431244 / 1000000000000) (-45608431243 / 1000000000000))
    | 11 => (orderedInterval (-2184373718 / 1000000000000) (-2184373716 / 1000000000000), orderedInterval (34283738071 / 1000000000000) (34283738072 / 1000000000000))
    | 12 => (orderedInterval (28606093652 / 1000000000000) (28606139363 / 1000000000000), orderedInterval (-21114760051 / 1000000000000) (-21114714340 / 1000000000000))
    | 13 => (orderedInterval (29161202185 / 1000000000000) (29161221026 / 1000000000000), orderedInterval (-30360972108 / 1000000000000) (-30360953267 / 1000000000000))
    | 14 => (orderedInterval (10766229506 / 1000000000000) (10766229507 / 1000000000000), orderedInterval (37997619644 / 1000000000000) (37997619645 / 1000000000000))
    | 15 => (orderedInterval (43262495831 / 1000000000000) (43262495981 / 1000000000000), orderedInterval (584272143 / 1000000000000) (584272293 / 1000000000000))
    | 16 => (orderedInterval (-15875425966 / 1000000000000) (-15875425704 / 1000000000000), orderedInterval (43233128814 / 1000000000000) (43233129077 / 1000000000000))
    | 17 => (orderedInterval (17564379130 / 1000000000000) (17564379672 / 1000000000000), orderedInterval (-33984541550 / 1000000000000) (-33984541008 / 1000000000000))
    | 18 => (orderedInterval (12189171383 / 1000000000000) (12189171467 / 1000000000000), orderedInterval (-49968657066 / 1000000000000) (-49968656981 / 1000000000000))
    | 19 => (orderedInterval (-39130503943 / 1000000000000) (-39130503942 / 1000000000000), orderedInterval (-39735136618 / 1000000000000) (-39735136617 / 1000000000000))
    | 20 => (orderedInterval (17118345865 / 1000000000000) (17118346065 / 1000000000000), orderedInterval (-68545522924 / 1000000000000) (-68545522723 / 1000000000000))
    | 21 => (orderedInterval (36312632687 / 1000000000000) (36312632688 / 1000000000000), orderedInterval (88874803916 / 1000000000000) (88874803917 / 1000000000000))
    | 22 => (orderedInterval (-52759716920 / 1000000000000) (-52759704630 / 1000000000000), orderedInterval (25209020650 / 1000000000000) (25209032941 / 1000000000000))
    | 23 => (orderedInterval (-44083996604 / 1000000000000) (-44083996603 / 1000000000000), orderedInterval (-23481679905 / 1000000000000) (-23481679904 / 1000000000000))
    | 24 => (orderedInterval (76289998421 / 1000000000000) (76289998622 / 1000000000000), orderedInterval (-9814533841 / 1000000000000) (-9814533640 / 1000000000000))
    | 25 => (orderedInterval (-34731447994 / 1000000000000) (-34731413664 / 1000000000000), orderedInterval (15773486665 / 1000000000000) (15773520995 / 1000000000000))
    | _ => (orderedInterval (-41760282392 / 1000000000000) (-41760282391 / 1000000000000), orderedInterval (-20728022971 / 1000000000000) (-20728022970 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-16068260781 / 1000000000000) (-16068260739 / 1000000000000)
      | 1 => orderedInterval (-1581384829 / 1000000000000) (-1581383709 / 1000000000000)
      | 2 => orderedInterval (-2153774707 / 1000000000000) (-2153774526 / 1000000000000)
      | 3 => orderedInterval (1873161480 / 1000000000000) (1873161596 / 1000000000000)
      | 4 => orderedInterval (2186654424 / 1000000000000) (2186657059 / 1000000000000)
      | 5 => orderedInterval (1857796358 / 1000000000000) (1857796411 / 1000000000000)
      | 6 => orderedInterval (823120768 / 1000000000000) (823120848 / 1000000000000)
      | 7 => orderedInterval (3904982797 / 1000000000000) (3904983105 / 1000000000000)
      | _ => orderedInterval (11122436642 / 1000000000000) (11122439504 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-15912995273 / 1000000000000) (-15912995224 / 1000000000000)
      | 1 => orderedInterval (-3365655761 / 1000000000000) (-3365654023 / 1000000000000)
      | 2 => orderedInterval (501144815 / 1000000000000) (501145167 / 1000000000000)
      | 3 => orderedInterval (-5881447004 / 1000000000000) (-5881446762 / 1000000000000)
      | 4 => orderedInterval (-3902703537 / 1000000000000) (-3902699003 / 1000000000000)
      | 5 => orderedInterval (-4755560998 / 1000000000000) (-4755560917 / 1000000000000)
      | 6 => orderedInterval (8911366097 / 1000000000000) (8911366170 / 1000000000000)
      | 7 => orderedInterval (1014833703 / 1000000000000) (1014833950 / 1000000000000)
      | _ => orderedInterval (2415769587 / 1000000000000) (2415774876 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (17043961726 / 1000000000000) (17043961784 / 1000000000000)
      | 1 => orderedInterval (-4043861561 / 1000000000000) (-4043858839 / 1000000000000)
      | 2 => orderedInterval (6565675878 / 1000000000000) (6565676568 / 1000000000000)
      | 3 => orderedInterval (-10163444720 / 1000000000000) (-10163444198 / 1000000000000)
      | 4 => orderedInterval (-3888278020 / 1000000000000) (-3888269987 / 1000000000000)
      | 5 => orderedInterval (-4037634668 / 1000000000000) (-4037634544 / 1000000000000)
      | 6 => orderedInterval (171992139 / 1000000000000) (171992208 / 1000000000000)
      | 7 => orderedInterval (-4652452848 / 1000000000000) (-4652452646 / 1000000000000)
      | _ => orderedInterval (-21967909118 / 1000000000000) (-21967899298 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (15689365987 / 1000000000000) (15689366054 / 1000000000000)
      | 1 => orderedInterval (8317655970 / 1000000000000) (8317660232 / 1000000000000)
      | 2 => orderedInterval (-1972995374 / 1000000000000) (-1972994023 / 1000000000000)
      | 3 => orderedInterval (12137475093 / 1000000000000) (12137476243 / 1000000000000)
      | 4 => orderedInterval (7510455713 / 1000000000000) (7510470318 / 1000000000000)
      | 5 => orderedInterval (10634311838 / 1000000000000) (10634312038 / 1000000000000)
      | 6 => orderedInterval (-9659820739 / 1000000000000) (-9659820672 / 1000000000000)
      | 7 => orderedInterval (-1933365512 / 1000000000000) (-1933365346 / 1000000000000)
      | _ => orderedInterval (902390508 / 1000000000000) (902408724 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-18622401011 / 1000000000000) (-18622400932 / 1000000000000)
      | 1 => orderedInterval (11786336117 / 1000000000000) (11786342813 / 1000000000000)
      | 2 => orderedInterval (-21736004882 / 1000000000000) (-21736002221 / 1000000000000)
      | 3 => orderedInterval (51933830592 / 1000000000000) (51933833148 / 1000000000000)
      | 4 => orderedInterval (3619197568 / 1000000000000) (3619224935 / 1000000000000)
      | 5 => orderedInterval (9744144096 / 1000000000000) (9744144426 / 1000000000000)
      | 6 => orderedInterval (-751010321 / 1000000000000) (-751010256 / 1000000000000)
      | 7 => orderedInterval (5110309374 / 1000000000000) (5110309513 / 1000000000000)
      | _ => orderedInterval (52452277627 / 1000000000000) (52452311521 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (1964732152 / 1000000000000) (1964739549 / 1000000000000)
    | 1 => orderedInterval (-20975248371 / 1000000000000) (-20975235766 / 1000000000000)
    | 2 => orderedInterval (-24971951192 / 1000000000000) (-24971928952 / 1000000000000)
    | 3 => orderedInterval (41625473484 / 1000000000000) (41625513568 / 1000000000000)
    | _ => orderedInterval (93536679160 / 1000000000000) (93536752947 / 1000000000000)

theorem compactCertificate364_stateChecks0 :
    compactCertificate364.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (471 / 2)) (orderedInterval (-32099813456 / 1000000000000) (-32099813455 / 1000000000000), orderedInterval (-40832606957 / 1000000000000) (-40832606956 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (693872936461371 / 4000000000000)) (orderedInterval (-60243288980 / 1000000000000) (-60243288968 / 1000000000000), orderedInterval (-6204553581 / 1000000000000) (-6204553570 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (224384251132443 / 800000000000)) (orderedInterval (-47437180924 / 1000000000000) (-47437180506 / 1000000000000), orderedInterval (4495781516 / 1000000000000) (4495781934 / 1000000000000))) = true
  rfl'

theorem compactCertificate364_stateChecks1 :
    compactCertificate364.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 16 12 (202470392315697 / 4000000000000)) (orderedInterval (101665112518 / 1000000000000) (101665112519 / 1000000000000), orderedInterval (46333515660 / 1000000000000) (46333515661 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (543863953576509 / 4000000000000)) (orderedInterval (-68142075508 / 1000000000000) (-68142075351 / 1000000000000), orderedInterval (6481561518 / 1000000000000) (6481561675 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 118 12 (1476696430566153 / 4000000000000)) (orderedInterval (-28268490120 / 1000000000000) (-28268474847 / 1000000000000), orderedInterval (30457617147 / 1000000000000) (30457632419 / 1000000000000))) = true
  rfl'

theorem compactCertificate364_stateChecks2 :
    compactCertificate364.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (1087727907153489 / 4000000000000)) (orderedInterval (27385825396 / 1000000000000) (27385831120 / 1000000000000), orderedInterval (-39939166887 / 1000000000000) (-39939161163 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 148 12 (1863840308635797 / 4000000000000)) (orderedInterval (36082431167 / 1000000000000) (36082436435 / 1000000000000), orderedInterval (-8058144343 / 1000000000000) (-8058139074 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 109 12 (1372896335506623 / 4000000000000)) (orderedInterval (-43067147963 / 1000000000000) (-43067147763 / 1000000000000), orderedInterval (266115734 / 1000000000000) (266115935 / 1000000000000))) = true
  rfl'

theorem compactCertificate364_stateChecks3 :
    compactCertificate364.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 168 12 (2106376034804529 / 4000000000000)) (orderedInterval (-13808404407 / 1000000000000) (-13808404288 / 1000000000000), orderedInterval (31923404696 / 1000000000000) (31923404816 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 97 12 (1216116770708841 / 4000000000000)) (orderedInterval (-3642828266 / 1000000000000) (-3642828265 / 1000000000000), orderedInterval (-45608431244 / 1000000000000) (-45608431243 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 172 12 (2158020550433469 / 4000000000000)) (orderedInterval (-2184373718 / 1000000000000) (-2184373716 / 1000000000000), orderedInterval (34283738071 / 1000000000000) (34283738072 / 1000000000000))) = true
  rfl'

theorem compactCertificate364_stateChecks4 :
    compactCertificate364.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 161 12 (2016302729278161 / 4000000000000)) (orderedInterval (28606093652 / 1000000000000) (28606139363 / 1000000000000), orderedInterval (-21114760051 / 1000000000000) (-21114714340 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 115 12 (1438928768215713 / 4000000000000)) (orderedInterval (29161202185 / 1000000000000) (29161221026 / 1000000000000), orderedInterval (-30360972108 / 1000000000000) (-30360953267 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 130 12 (1631591860729527 / 4000000000000)) (orderedInterval (10766229506 / 1000000000000) (10766229507 / 1000000000000), orderedInterval (37997619644 / 1000000000000) (37997619645 / 1000000000000))) = true
  rfl'

theorem compactCertificate364_stateChecks5 :
    compactCertificate364.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 108 12 (1360251191473863 / 4000000000000)) (orderedInterval (43262495831 / 1000000000000) (43262495981 / 1000000000000), orderedInterval (584272143 / 1000000000000) (584272293 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 96 12 (1201823179947123 / 4000000000000)) (orderedInterval (-15875425966 / 1000000000000) (-15875425704 / 1000000000000), orderedInterval (43233128814 / 1000000000000) (43233129077 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 139 12 (348335200857177 / 800000000000)) (orderedInterval (17564379130 / 1000000000000) (17564379672 / 1000000000000), orderedInterval (-33984541550 / 1000000000000) (-33984541008 / 1000000000000))) = true
  rfl'

theorem compactCertificate364_stateChecks6 :
    compactCertificate364.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (963513497448219 / 4000000000000)) (orderedInterval (12189171383 / 1000000000000) (12189171467 / 1000000000000), orderedInterval (-49968657066 / 1000000000000) (-49968656981 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (816781062406659 / 4000000000000)) (orderedInterval (-39130503943 / 1000000000000) (-39130503942 / 1000000000000), orderedInterval (-39735136618 / 1000000000000) (-39735136617 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (511103664493377 / 4000000000000)) (orderedInterval (17118345865 / 1000000000000) (17118346065 / 1000000000000), orderedInterval (-68545522924 / 1000000000000) (-68545522723 / 1000000000000))) = true
  rfl'

theorem compactCertificate364_stateChecks7 :
    compactCertificate364.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 22 12 (274873250618559 / 4000000000000)) (orderedInterval (36312632687 / 1000000000000) (36312632688 / 1000000000000), orderedInterval (88874803916 / 1000000000000) (88874803917 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (746334345892677 / 4000000000000)) (orderedInterval (-52759716920 / 1000000000000) (-52759704630 / 1000000000000), orderedInterval (25209020650 / 1000000000000) (25209032941 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (1019055743230629 / 4000000000000)) (orderedInterval (-44083996604 / 1000000000000) (-44083996603 / 1000000000000), orderedInterval (-23481679905 / 1000000000000) (-23481679904 / 1000000000000))) = true
  rfl'

theorem compactCertificate364_stateChecks8 :
    compactCertificate364.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (430896335506623 / 4000000000000)) (orderedInterval (76289998421 / 1000000000000) (76289998622 / 1000000000000), orderedInterval (-9814533841 / 1000000000000) (-9814533640 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 139 12 (1751569681185183 / 4000000000000)) (orderedInterval (-34731447994 / 1000000000000) (-34731413664 / 1000000000000), orderedInterval (15773486665 / 1000000000000) (15773520995 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 93 12 (1169967372174897 / 4000000000000)) (orderedInterval (-41760282392 / 1000000000000) (-41760282391 / 1000000000000), orderedInterval (-20728022971 / 1000000000000) (-20728022970 / 1000000000000))) = true
  rfl'

theorem compactCertificate364_states : ∀ j,
    BesselStateValid (compactCertificate364.point j) (compactCertificate364.state j) :=
  compactCertificate364.statesValid_of_checks3 compactCertificate364_stateChecks0
    compactCertificate364_stateChecks1 compactCertificate364_stateChecks2
    compactCertificate364_stateChecks3 compactCertificate364_stateChecks4
    compactCertificate364_stateChecks5 compactCertificate364_stateChecks6
    compactCertificate364_stateChecks7 compactCertificate364_stateChecks8

theorem compactCertificate364_chunkChecks0_0 :
    compactCertificate364.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (471 / 2) 0 (IntervalRat.scale (471 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-32099813456 / 1000000000000) (-32099813455 / 1000000000000), orderedInterval (-40832606957 / 1000000000000) (-40832606956 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (693872936461371 / 4000000000000) 0 (IntervalRat.scale (471 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-60243288980 / 1000000000000) (-60243288968 / 1000000000000), orderedInterval (-6204553581 / 1000000000000) (-6204553570 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (224384251132443 / 800000000000) 0 (IntervalRat.scale (471 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-47437180924 / 1000000000000) (-47437180506 / 1000000000000), orderedInterval (4495781516 / 1000000000000) (4495781934 / 1000000000000)))) (orderedInterval (-16068260781 / 1000000000000) (-16068260739 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (202470392315697 / 4000000000000) 0 (IntervalRat.scale (471 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (101665112518 / 1000000000000) (101665112519 / 1000000000000), orderedInterval (46333515660 / 1000000000000) (46333515661 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (543863953576509 / 4000000000000) 0 (IntervalRat.scale (471 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-68142075508 / 1000000000000) (-68142075351 / 1000000000000), orderedInterval (6481561518 / 1000000000000) (6481561675 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1476696430566153 / 4000000000000) 0 (IntervalRat.scale (471 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28268490120 / 1000000000000) (-28268474847 / 1000000000000), orderedInterval (30457617147 / 1000000000000) (30457632419 / 1000000000000)))) (orderedInterval (-1581384829 / 1000000000000) (-1581383709 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1087727907153489 / 4000000000000) 0 (IntervalRat.scale (471 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (27385825396 / 1000000000000) (27385831120 / 1000000000000), orderedInterval (-39939166887 / 1000000000000) (-39939161163 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1863840308635797 / 4000000000000) 0 (IntervalRat.scale (471 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (36082431167 / 1000000000000) (36082436435 / 1000000000000), orderedInterval (-8058144343 / 1000000000000) (-8058139074 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1372896335506623 / 4000000000000) 0 (IntervalRat.scale (471 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-43067147963 / 1000000000000) (-43067147763 / 1000000000000), orderedInterval (266115734 / 1000000000000) (266115935 / 1000000000000)))) (orderedInterval (-2153774707 / 1000000000000) (-2153774526 / 1000000000000))) = true
  rfl'

theorem compactCertificate364_chunkChecks0_1 :
    compactCertificate364.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2106376034804529 / 4000000000000) 0 (IntervalRat.scale (471 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-13808404407 / 1000000000000) (-13808404288 / 1000000000000), orderedInterval (31923404696 / 1000000000000) (31923404816 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1216116770708841 / 4000000000000) 0 (IntervalRat.scale (471 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-3642828266 / 1000000000000) (-3642828265 / 1000000000000), orderedInterval (-45608431244 / 1000000000000) (-45608431243 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2158020550433469 / 4000000000000) 0 (IntervalRat.scale (471 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-2184373718 / 1000000000000) (-2184373716 / 1000000000000), orderedInterval (34283738071 / 1000000000000) (34283738072 / 1000000000000)))) (orderedInterval (1873161480 / 1000000000000) (1873161596 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2016302729278161 / 4000000000000) 0 (IntervalRat.scale (471 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (28606093652 / 1000000000000) (28606139363 / 1000000000000), orderedInterval (-21114760051 / 1000000000000) (-21114714340 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1438928768215713 / 4000000000000) 0 (IntervalRat.scale (471 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (29161202185 / 1000000000000) (29161221026 / 1000000000000), orderedInterval (-30360972108 / 1000000000000) (-30360953267 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1631591860729527 / 4000000000000) 0 (IntervalRat.scale (471 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (10766229506 / 1000000000000) (10766229507 / 1000000000000), orderedInterval (37997619644 / 1000000000000) (37997619645 / 1000000000000)))) (orderedInterval (2186654424 / 1000000000000) (2186657059 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1360251191473863 / 4000000000000) 0 (IntervalRat.scale (471 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (43262495831 / 1000000000000) (43262495981 / 1000000000000), orderedInterval (584272143 / 1000000000000) (584272293 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1201823179947123 / 4000000000000) 0 (IntervalRat.scale (471 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-15875425966 / 1000000000000) (-15875425704 / 1000000000000), orderedInterval (43233128814 / 1000000000000) (43233129077 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (348335200857177 / 800000000000) 0 (IntervalRat.scale (471 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (17564379130 / 1000000000000) (17564379672 / 1000000000000), orderedInterval (-33984541550 / 1000000000000) (-33984541008 / 1000000000000)))) (orderedInterval (1857796358 / 1000000000000) (1857796411 / 1000000000000))) = true
  rfl'

theorem compactCertificate364_chunkChecks0_2 :
    compactCertificate364.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (963513497448219 / 4000000000000) 0 (IntervalRat.scale (471 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (12189171383 / 1000000000000) (12189171467 / 1000000000000), orderedInterval (-49968657066 / 1000000000000) (-49968656981 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (816781062406659 / 4000000000000) 0 (IntervalRat.scale (471 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-39130503943 / 1000000000000) (-39130503942 / 1000000000000), orderedInterval (-39735136618 / 1000000000000) (-39735136617 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (511103664493377 / 4000000000000) 0 (IntervalRat.scale (471 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (17118345865 / 1000000000000) (17118346065 / 1000000000000), orderedInterval (-68545522924 / 1000000000000) (-68545522723 / 1000000000000)))) (orderedInterval (823120768 / 1000000000000) (823120848 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (274873250618559 / 4000000000000) 0 (IntervalRat.scale (471 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (36312632687 / 1000000000000) (36312632688 / 1000000000000), orderedInterval (88874803916 / 1000000000000) (88874803917 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (746334345892677 / 4000000000000) 0 (IntervalRat.scale (471 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-52759716920 / 1000000000000) (-52759704630 / 1000000000000), orderedInterval (25209020650 / 1000000000000) (25209032941 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1019055743230629 / 4000000000000) 0 (IntervalRat.scale (471 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-44083996604 / 1000000000000) (-44083996603 / 1000000000000), orderedInterval (-23481679905 / 1000000000000) (-23481679904 / 1000000000000)))) (orderedInterval (3904982797 / 1000000000000) (3904983105 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (430896335506623 / 4000000000000) 0 (IntervalRat.scale (471 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (76289998421 / 1000000000000) (76289998622 / 1000000000000), orderedInterval (-9814533841 / 1000000000000) (-9814533640 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1751569681185183 / 4000000000000) 0 (IntervalRat.scale (471 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-34731447994 / 1000000000000) (-34731413664 / 1000000000000), orderedInterval (15773486665 / 1000000000000) (15773520995 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1169967372174897 / 4000000000000) 0 (IntervalRat.scale (471 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-41760282392 / 1000000000000) (-41760282391 / 1000000000000), orderedInterval (-20728022971 / 1000000000000) (-20728022970 / 1000000000000)))) (orderedInterval (11122436642 / 1000000000000) (11122439504 / 1000000000000))) = true
  rfl'

theorem compactCertificate364_chunkChecks0 :
    compactCertificate364.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate364.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate364_chunkChecks0_0
    compactCertificate364_chunkChecks0_1 compactCertificate364_chunkChecks0_2

theorem compactCertificate364_chunkChecks1_0 :
    compactCertificate364.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (471 / 2) 1 (IntervalRat.scale (471 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-32099813456 / 1000000000000) (-32099813455 / 1000000000000), orderedInterval (-40832606957 / 1000000000000) (-40832606956 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (693872936461371 / 4000000000000) 1 (IntervalRat.scale (471 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-60243288980 / 1000000000000) (-60243288968 / 1000000000000), orderedInterval (-6204553581 / 1000000000000) (-6204553570 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (224384251132443 / 800000000000) 1 (IntervalRat.scale (471 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-47437180924 / 1000000000000) (-47437180506 / 1000000000000), orderedInterval (4495781516 / 1000000000000) (4495781934 / 1000000000000)))) (orderedInterval (-15912995273 / 1000000000000) (-15912995224 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (202470392315697 / 4000000000000) 1 (IntervalRat.scale (471 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (101665112518 / 1000000000000) (101665112519 / 1000000000000), orderedInterval (46333515660 / 1000000000000) (46333515661 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (543863953576509 / 4000000000000) 1 (IntervalRat.scale (471 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-68142075508 / 1000000000000) (-68142075351 / 1000000000000), orderedInterval (6481561518 / 1000000000000) (6481561675 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1476696430566153 / 4000000000000) 1 (IntervalRat.scale (471 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28268490120 / 1000000000000) (-28268474847 / 1000000000000), orderedInterval (30457617147 / 1000000000000) (30457632419 / 1000000000000)))) (orderedInterval (-3365655761 / 1000000000000) (-3365654023 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1087727907153489 / 4000000000000) 1 (IntervalRat.scale (471 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (27385825396 / 1000000000000) (27385831120 / 1000000000000), orderedInterval (-39939166887 / 1000000000000) (-39939161163 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1863840308635797 / 4000000000000) 1 (IntervalRat.scale (471 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (36082431167 / 1000000000000) (36082436435 / 1000000000000), orderedInterval (-8058144343 / 1000000000000) (-8058139074 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1372896335506623 / 4000000000000) 1 (IntervalRat.scale (471 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-43067147963 / 1000000000000) (-43067147763 / 1000000000000), orderedInterval (266115734 / 1000000000000) (266115935 / 1000000000000)))) (orderedInterval (501144815 / 1000000000000) (501145167 / 1000000000000))) = true
  rfl'

theorem compactCertificate364_chunkChecks1_1 :
    compactCertificate364.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2106376034804529 / 4000000000000) 1 (IntervalRat.scale (471 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-13808404407 / 1000000000000) (-13808404288 / 1000000000000), orderedInterval (31923404696 / 1000000000000) (31923404816 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1216116770708841 / 4000000000000) 1 (IntervalRat.scale (471 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-3642828266 / 1000000000000) (-3642828265 / 1000000000000), orderedInterval (-45608431244 / 1000000000000) (-45608431243 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2158020550433469 / 4000000000000) 1 (IntervalRat.scale (471 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-2184373718 / 1000000000000) (-2184373716 / 1000000000000), orderedInterval (34283738071 / 1000000000000) (34283738072 / 1000000000000)))) (orderedInterval (-5881447004 / 1000000000000) (-5881446762 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2016302729278161 / 4000000000000) 1 (IntervalRat.scale (471 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (28606093652 / 1000000000000) (28606139363 / 1000000000000), orderedInterval (-21114760051 / 1000000000000) (-21114714340 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1438928768215713 / 4000000000000) 1 (IntervalRat.scale (471 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (29161202185 / 1000000000000) (29161221026 / 1000000000000), orderedInterval (-30360972108 / 1000000000000) (-30360953267 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1631591860729527 / 4000000000000) 1 (IntervalRat.scale (471 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (10766229506 / 1000000000000) (10766229507 / 1000000000000), orderedInterval (37997619644 / 1000000000000) (37997619645 / 1000000000000)))) (orderedInterval (-3902703537 / 1000000000000) (-3902699003 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1360251191473863 / 4000000000000) 1 (IntervalRat.scale (471 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (43262495831 / 1000000000000) (43262495981 / 1000000000000), orderedInterval (584272143 / 1000000000000) (584272293 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1201823179947123 / 4000000000000) 1 (IntervalRat.scale (471 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-15875425966 / 1000000000000) (-15875425704 / 1000000000000), orderedInterval (43233128814 / 1000000000000) (43233129077 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (348335200857177 / 800000000000) 1 (IntervalRat.scale (471 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (17564379130 / 1000000000000) (17564379672 / 1000000000000), orderedInterval (-33984541550 / 1000000000000) (-33984541008 / 1000000000000)))) (orderedInterval (-4755560998 / 1000000000000) (-4755560917 / 1000000000000))) = true
  rfl'

theorem compactCertificate364_chunkChecks1_2 :
    compactCertificate364.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (963513497448219 / 4000000000000) 1 (IntervalRat.scale (471 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (12189171383 / 1000000000000) (12189171467 / 1000000000000), orderedInterval (-49968657066 / 1000000000000) (-49968656981 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (816781062406659 / 4000000000000) 1 (IntervalRat.scale (471 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-39130503943 / 1000000000000) (-39130503942 / 1000000000000), orderedInterval (-39735136618 / 1000000000000) (-39735136617 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (511103664493377 / 4000000000000) 1 (IntervalRat.scale (471 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (17118345865 / 1000000000000) (17118346065 / 1000000000000), orderedInterval (-68545522924 / 1000000000000) (-68545522723 / 1000000000000)))) (orderedInterval (8911366097 / 1000000000000) (8911366170 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (274873250618559 / 4000000000000) 1 (IntervalRat.scale (471 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (36312632687 / 1000000000000) (36312632688 / 1000000000000), orderedInterval (88874803916 / 1000000000000) (88874803917 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (746334345892677 / 4000000000000) 1 (IntervalRat.scale (471 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-52759716920 / 1000000000000) (-52759704630 / 1000000000000), orderedInterval (25209020650 / 1000000000000) (25209032941 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1019055743230629 / 4000000000000) 1 (IntervalRat.scale (471 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-44083996604 / 1000000000000) (-44083996603 / 1000000000000), orderedInterval (-23481679905 / 1000000000000) (-23481679904 / 1000000000000)))) (orderedInterval (1014833703 / 1000000000000) (1014833950 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (430896335506623 / 4000000000000) 1 (IntervalRat.scale (471 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (76289998421 / 1000000000000) (76289998622 / 1000000000000), orderedInterval (-9814533841 / 1000000000000) (-9814533640 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1751569681185183 / 4000000000000) 1 (IntervalRat.scale (471 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-34731447994 / 1000000000000) (-34731413664 / 1000000000000), orderedInterval (15773486665 / 1000000000000) (15773520995 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1169967372174897 / 4000000000000) 1 (IntervalRat.scale (471 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-41760282392 / 1000000000000) (-41760282391 / 1000000000000), orderedInterval (-20728022971 / 1000000000000) (-20728022970 / 1000000000000)))) (orderedInterval (2415769587 / 1000000000000) (2415774876 / 1000000000000))) = true
  rfl'

theorem compactCertificate364_chunkChecks1 :
    compactCertificate364.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate364.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate364_chunkChecks1_0
    compactCertificate364_chunkChecks1_1 compactCertificate364_chunkChecks1_2

theorem compactCertificate364_chunkChecks2_0 :
    compactCertificate364.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (471 / 2) 2 (IntervalRat.scale (471 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-32099813456 / 1000000000000) (-32099813455 / 1000000000000), orderedInterval (-40832606957 / 1000000000000) (-40832606956 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (693872936461371 / 4000000000000) 2 (IntervalRat.scale (471 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-60243288980 / 1000000000000) (-60243288968 / 1000000000000), orderedInterval (-6204553581 / 1000000000000) (-6204553570 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (224384251132443 / 800000000000) 2 (IntervalRat.scale (471 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-47437180924 / 1000000000000) (-47437180506 / 1000000000000), orderedInterval (4495781516 / 1000000000000) (4495781934 / 1000000000000)))) (orderedInterval (17043961726 / 1000000000000) (17043961784 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (202470392315697 / 4000000000000) 2 (IntervalRat.scale (471 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (101665112518 / 1000000000000) (101665112519 / 1000000000000), orderedInterval (46333515660 / 1000000000000) (46333515661 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (543863953576509 / 4000000000000) 2 (IntervalRat.scale (471 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-68142075508 / 1000000000000) (-68142075351 / 1000000000000), orderedInterval (6481561518 / 1000000000000) (6481561675 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1476696430566153 / 4000000000000) 2 (IntervalRat.scale (471 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28268490120 / 1000000000000) (-28268474847 / 1000000000000), orderedInterval (30457617147 / 1000000000000) (30457632419 / 1000000000000)))) (orderedInterval (-4043861561 / 1000000000000) (-4043858839 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1087727907153489 / 4000000000000) 2 (IntervalRat.scale (471 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (27385825396 / 1000000000000) (27385831120 / 1000000000000), orderedInterval (-39939166887 / 1000000000000) (-39939161163 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1863840308635797 / 4000000000000) 2 (IntervalRat.scale (471 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (36082431167 / 1000000000000) (36082436435 / 1000000000000), orderedInterval (-8058144343 / 1000000000000) (-8058139074 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1372896335506623 / 4000000000000) 2 (IntervalRat.scale (471 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-43067147963 / 1000000000000) (-43067147763 / 1000000000000), orderedInterval (266115734 / 1000000000000) (266115935 / 1000000000000)))) (orderedInterval (6565675878 / 1000000000000) (6565676568 / 1000000000000))) = true
  rfl'

theorem compactCertificate364_chunkChecks2_1 :
    compactCertificate364.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2106376034804529 / 4000000000000) 2 (IntervalRat.scale (471 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-13808404407 / 1000000000000) (-13808404288 / 1000000000000), orderedInterval (31923404696 / 1000000000000) (31923404816 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1216116770708841 / 4000000000000) 2 (IntervalRat.scale (471 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-3642828266 / 1000000000000) (-3642828265 / 1000000000000), orderedInterval (-45608431244 / 1000000000000) (-45608431243 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2158020550433469 / 4000000000000) 2 (IntervalRat.scale (471 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-2184373718 / 1000000000000) (-2184373716 / 1000000000000), orderedInterval (34283738071 / 1000000000000) (34283738072 / 1000000000000)))) (orderedInterval (-10163444720 / 1000000000000) (-10163444198 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2016302729278161 / 4000000000000) 2 (IntervalRat.scale (471 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (28606093652 / 1000000000000) (28606139363 / 1000000000000), orderedInterval (-21114760051 / 1000000000000) (-21114714340 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1438928768215713 / 4000000000000) 2 (IntervalRat.scale (471 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (29161202185 / 1000000000000) (29161221026 / 1000000000000), orderedInterval (-30360972108 / 1000000000000) (-30360953267 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1631591860729527 / 4000000000000) 2 (IntervalRat.scale (471 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (10766229506 / 1000000000000) (10766229507 / 1000000000000), orderedInterval (37997619644 / 1000000000000) (37997619645 / 1000000000000)))) (orderedInterval (-3888278020 / 1000000000000) (-3888269987 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1360251191473863 / 4000000000000) 2 (IntervalRat.scale (471 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (43262495831 / 1000000000000) (43262495981 / 1000000000000), orderedInterval (584272143 / 1000000000000) (584272293 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1201823179947123 / 4000000000000) 2 (IntervalRat.scale (471 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-15875425966 / 1000000000000) (-15875425704 / 1000000000000), orderedInterval (43233128814 / 1000000000000) (43233129077 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (348335200857177 / 800000000000) 2 (IntervalRat.scale (471 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (17564379130 / 1000000000000) (17564379672 / 1000000000000), orderedInterval (-33984541550 / 1000000000000) (-33984541008 / 1000000000000)))) (orderedInterval (-4037634668 / 1000000000000) (-4037634544 / 1000000000000))) = true
  rfl'

theorem compactCertificate364_chunkChecks2_2 :
    compactCertificate364.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (963513497448219 / 4000000000000) 2 (IntervalRat.scale (471 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (12189171383 / 1000000000000) (12189171467 / 1000000000000), orderedInterval (-49968657066 / 1000000000000) (-49968656981 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (816781062406659 / 4000000000000) 2 (IntervalRat.scale (471 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-39130503943 / 1000000000000) (-39130503942 / 1000000000000), orderedInterval (-39735136618 / 1000000000000) (-39735136617 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (511103664493377 / 4000000000000) 2 (IntervalRat.scale (471 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (17118345865 / 1000000000000) (17118346065 / 1000000000000), orderedInterval (-68545522924 / 1000000000000) (-68545522723 / 1000000000000)))) (orderedInterval (171992139 / 1000000000000) (171992208 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (274873250618559 / 4000000000000) 2 (IntervalRat.scale (471 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (36312632687 / 1000000000000) (36312632688 / 1000000000000), orderedInterval (88874803916 / 1000000000000) (88874803917 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (746334345892677 / 4000000000000) 2 (IntervalRat.scale (471 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-52759716920 / 1000000000000) (-52759704630 / 1000000000000), orderedInterval (25209020650 / 1000000000000) (25209032941 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1019055743230629 / 4000000000000) 2 (IntervalRat.scale (471 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-44083996604 / 1000000000000) (-44083996603 / 1000000000000), orderedInterval (-23481679905 / 1000000000000) (-23481679904 / 1000000000000)))) (orderedInterval (-4652452848 / 1000000000000) (-4652452646 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (430896335506623 / 4000000000000) 2 (IntervalRat.scale (471 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (76289998421 / 1000000000000) (76289998622 / 1000000000000), orderedInterval (-9814533841 / 1000000000000) (-9814533640 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1751569681185183 / 4000000000000) 2 (IntervalRat.scale (471 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-34731447994 / 1000000000000) (-34731413664 / 1000000000000), orderedInterval (15773486665 / 1000000000000) (15773520995 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1169967372174897 / 4000000000000) 2 (IntervalRat.scale (471 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-41760282392 / 1000000000000) (-41760282391 / 1000000000000), orderedInterval (-20728022971 / 1000000000000) (-20728022970 / 1000000000000)))) (orderedInterval (-21967909118 / 1000000000000) (-21967899298 / 1000000000000))) = true
  rfl'

theorem compactCertificate364_chunkChecks2 :
    compactCertificate364.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate364.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate364_chunkChecks2_0
    compactCertificate364_chunkChecks2_1 compactCertificate364_chunkChecks2_2

theorem compactCertificate364_chunkChecks3_0 :
    compactCertificate364.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (471 / 2) 3 (IntervalRat.scale (471 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-32099813456 / 1000000000000) (-32099813455 / 1000000000000), orderedInterval (-40832606957 / 1000000000000) (-40832606956 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (693872936461371 / 4000000000000) 3 (IntervalRat.scale (471 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-60243288980 / 1000000000000) (-60243288968 / 1000000000000), orderedInterval (-6204553581 / 1000000000000) (-6204553570 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (224384251132443 / 800000000000) 3 (IntervalRat.scale (471 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-47437180924 / 1000000000000) (-47437180506 / 1000000000000), orderedInterval (4495781516 / 1000000000000) (4495781934 / 1000000000000)))) (orderedInterval (15689365987 / 1000000000000) (15689366054 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (202470392315697 / 4000000000000) 3 (IntervalRat.scale (471 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (101665112518 / 1000000000000) (101665112519 / 1000000000000), orderedInterval (46333515660 / 1000000000000) (46333515661 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (543863953576509 / 4000000000000) 3 (IntervalRat.scale (471 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-68142075508 / 1000000000000) (-68142075351 / 1000000000000), orderedInterval (6481561518 / 1000000000000) (6481561675 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1476696430566153 / 4000000000000) 3 (IntervalRat.scale (471 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28268490120 / 1000000000000) (-28268474847 / 1000000000000), orderedInterval (30457617147 / 1000000000000) (30457632419 / 1000000000000)))) (orderedInterval (8317655970 / 1000000000000) (8317660232 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1087727907153489 / 4000000000000) 3 (IntervalRat.scale (471 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (27385825396 / 1000000000000) (27385831120 / 1000000000000), orderedInterval (-39939166887 / 1000000000000) (-39939161163 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1863840308635797 / 4000000000000) 3 (IntervalRat.scale (471 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (36082431167 / 1000000000000) (36082436435 / 1000000000000), orderedInterval (-8058144343 / 1000000000000) (-8058139074 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1372896335506623 / 4000000000000) 3 (IntervalRat.scale (471 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-43067147963 / 1000000000000) (-43067147763 / 1000000000000), orderedInterval (266115734 / 1000000000000) (266115935 / 1000000000000)))) (orderedInterval (-1972995374 / 1000000000000) (-1972994023 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate364_chunkChecks3_1 :
    compactCertificate364.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2106376034804529 / 4000000000000) 3 (IntervalRat.scale (471 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-13808404407 / 1000000000000) (-13808404288 / 1000000000000), orderedInterval (31923404696 / 1000000000000) (31923404816 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1216116770708841 / 4000000000000) 3 (IntervalRat.scale (471 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-3642828266 / 1000000000000) (-3642828265 / 1000000000000), orderedInterval (-45608431244 / 1000000000000) (-45608431243 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2158020550433469 / 4000000000000) 3 (IntervalRat.scale (471 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-2184373718 / 1000000000000) (-2184373716 / 1000000000000), orderedInterval (34283738071 / 1000000000000) (34283738072 / 1000000000000)))) (orderedInterval (12137475093 / 1000000000000) (12137476243 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2016302729278161 / 4000000000000) 3 (IntervalRat.scale (471 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (28606093652 / 1000000000000) (28606139363 / 1000000000000), orderedInterval (-21114760051 / 1000000000000) (-21114714340 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1438928768215713 / 4000000000000) 3 (IntervalRat.scale (471 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (29161202185 / 1000000000000) (29161221026 / 1000000000000), orderedInterval (-30360972108 / 1000000000000) (-30360953267 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1631591860729527 / 4000000000000) 3 (IntervalRat.scale (471 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (10766229506 / 1000000000000) (10766229507 / 1000000000000), orderedInterval (37997619644 / 1000000000000) (37997619645 / 1000000000000)))) (orderedInterval (7510455713 / 1000000000000) (7510470318 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1360251191473863 / 4000000000000) 3 (IntervalRat.scale (471 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (43262495831 / 1000000000000) (43262495981 / 1000000000000), orderedInterval (584272143 / 1000000000000) (584272293 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1201823179947123 / 4000000000000) 3 (IntervalRat.scale (471 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-15875425966 / 1000000000000) (-15875425704 / 1000000000000), orderedInterval (43233128814 / 1000000000000) (43233129077 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (348335200857177 / 800000000000) 3 (IntervalRat.scale (471 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (17564379130 / 1000000000000) (17564379672 / 1000000000000), orderedInterval (-33984541550 / 1000000000000) (-33984541008 / 1000000000000)))) (orderedInterval (10634311838 / 1000000000000) (10634312038 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate364_chunkChecks3_2 :
    compactCertificate364.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (963513497448219 / 4000000000000) 3 (IntervalRat.scale (471 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (12189171383 / 1000000000000) (12189171467 / 1000000000000), orderedInterval (-49968657066 / 1000000000000) (-49968656981 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (816781062406659 / 4000000000000) 3 (IntervalRat.scale (471 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-39130503943 / 1000000000000) (-39130503942 / 1000000000000), orderedInterval (-39735136618 / 1000000000000) (-39735136617 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (511103664493377 / 4000000000000) 3 (IntervalRat.scale (471 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (17118345865 / 1000000000000) (17118346065 / 1000000000000), orderedInterval (-68545522924 / 1000000000000) (-68545522723 / 1000000000000)))) (orderedInterval (-9659820739 / 1000000000000) (-9659820672 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (274873250618559 / 4000000000000) 3 (IntervalRat.scale (471 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (36312632687 / 1000000000000) (36312632688 / 1000000000000), orderedInterval (88874803916 / 1000000000000) (88874803917 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (746334345892677 / 4000000000000) 3 (IntervalRat.scale (471 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-52759716920 / 1000000000000) (-52759704630 / 1000000000000), orderedInterval (25209020650 / 1000000000000) (25209032941 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1019055743230629 / 4000000000000) 3 (IntervalRat.scale (471 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-44083996604 / 1000000000000) (-44083996603 / 1000000000000), orderedInterval (-23481679905 / 1000000000000) (-23481679904 / 1000000000000)))) (orderedInterval (-1933365512 / 1000000000000) (-1933365346 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (430896335506623 / 4000000000000) 3 (IntervalRat.scale (471 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (76289998421 / 1000000000000) (76289998622 / 1000000000000), orderedInterval (-9814533841 / 1000000000000) (-9814533640 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1751569681185183 / 4000000000000) 3 (IntervalRat.scale (471 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-34731447994 / 1000000000000) (-34731413664 / 1000000000000), orderedInterval (15773486665 / 1000000000000) (15773520995 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1169967372174897 / 4000000000000) 3 (IntervalRat.scale (471 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-41760282392 / 1000000000000) (-41760282391 / 1000000000000), orderedInterval (-20728022971 / 1000000000000) (-20728022970 / 1000000000000)))) (orderedInterval (902390508 / 1000000000000) (902408724 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate364_chunkChecks3 :
    compactCertificate364.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate364.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate364_chunkChecks3_0
    compactCertificate364_chunkChecks3_1 compactCertificate364_chunkChecks3_2

theorem compactCertificate364_chunkChecks4_0 :
    compactCertificate364.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (471 / 2) 4 (IntervalRat.scale (471 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-32099813456 / 1000000000000) (-32099813455 / 1000000000000), orderedInterval (-40832606957 / 1000000000000) (-40832606956 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (693872936461371 / 4000000000000) 4 (IntervalRat.scale (471 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-60243288980 / 1000000000000) (-60243288968 / 1000000000000), orderedInterval (-6204553581 / 1000000000000) (-6204553570 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (224384251132443 / 800000000000) 4 (IntervalRat.scale (471 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-47437180924 / 1000000000000) (-47437180506 / 1000000000000), orderedInterval (4495781516 / 1000000000000) (4495781934 / 1000000000000)))) (orderedInterval (-18622401011 / 1000000000000) (-18622400932 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (202470392315697 / 4000000000000) 4 (IntervalRat.scale (471 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (101665112518 / 1000000000000) (101665112519 / 1000000000000), orderedInterval (46333515660 / 1000000000000) (46333515661 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (543863953576509 / 4000000000000) 4 (IntervalRat.scale (471 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-68142075508 / 1000000000000) (-68142075351 / 1000000000000), orderedInterval (6481561518 / 1000000000000) (6481561675 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1476696430566153 / 4000000000000) 4 (IntervalRat.scale (471 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28268490120 / 1000000000000) (-28268474847 / 1000000000000), orderedInterval (30457617147 / 1000000000000) (30457632419 / 1000000000000)))) (orderedInterval (11786336117 / 1000000000000) (11786342813 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1087727907153489 / 4000000000000) 4 (IntervalRat.scale (471 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (27385825396 / 1000000000000) (27385831120 / 1000000000000), orderedInterval (-39939166887 / 1000000000000) (-39939161163 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1863840308635797 / 4000000000000) 4 (IntervalRat.scale (471 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (36082431167 / 1000000000000) (36082436435 / 1000000000000), orderedInterval (-8058144343 / 1000000000000) (-8058139074 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1372896335506623 / 4000000000000) 4 (IntervalRat.scale (471 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-43067147963 / 1000000000000) (-43067147763 / 1000000000000), orderedInterval (266115734 / 1000000000000) (266115935 / 1000000000000)))) (orderedInterval (-21736004882 / 1000000000000) (-21736002221 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate364_chunkChecks4_1 :
    compactCertificate364.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2106376034804529 / 4000000000000) 4 (IntervalRat.scale (471 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-13808404407 / 1000000000000) (-13808404288 / 1000000000000), orderedInterval (31923404696 / 1000000000000) (31923404816 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1216116770708841 / 4000000000000) 4 (IntervalRat.scale (471 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-3642828266 / 1000000000000) (-3642828265 / 1000000000000), orderedInterval (-45608431244 / 1000000000000) (-45608431243 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2158020550433469 / 4000000000000) 4 (IntervalRat.scale (471 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-2184373718 / 1000000000000) (-2184373716 / 1000000000000), orderedInterval (34283738071 / 1000000000000) (34283738072 / 1000000000000)))) (orderedInterval (51933830592 / 1000000000000) (51933833148 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2016302729278161 / 4000000000000) 4 (IntervalRat.scale (471 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (28606093652 / 1000000000000) (28606139363 / 1000000000000), orderedInterval (-21114760051 / 1000000000000) (-21114714340 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1438928768215713 / 4000000000000) 4 (IntervalRat.scale (471 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (29161202185 / 1000000000000) (29161221026 / 1000000000000), orderedInterval (-30360972108 / 1000000000000) (-30360953267 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1631591860729527 / 4000000000000) 4 (IntervalRat.scale (471 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (10766229506 / 1000000000000) (10766229507 / 1000000000000), orderedInterval (37997619644 / 1000000000000) (37997619645 / 1000000000000)))) (orderedInterval (3619197568 / 1000000000000) (3619224935 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1360251191473863 / 4000000000000) 4 (IntervalRat.scale (471 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (43262495831 / 1000000000000) (43262495981 / 1000000000000), orderedInterval (584272143 / 1000000000000) (584272293 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1201823179947123 / 4000000000000) 4 (IntervalRat.scale (471 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-15875425966 / 1000000000000) (-15875425704 / 1000000000000), orderedInterval (43233128814 / 1000000000000) (43233129077 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (348335200857177 / 800000000000) 4 (IntervalRat.scale (471 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (17564379130 / 1000000000000) (17564379672 / 1000000000000), orderedInterval (-33984541550 / 1000000000000) (-33984541008 / 1000000000000)))) (orderedInterval (9744144096 / 1000000000000) (9744144426 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate364_chunkChecks4_2 :
    compactCertificate364.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (963513497448219 / 4000000000000) 4 (IntervalRat.scale (471 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (12189171383 / 1000000000000) (12189171467 / 1000000000000), orderedInterval (-49968657066 / 1000000000000) (-49968656981 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (816781062406659 / 4000000000000) 4 (IntervalRat.scale (471 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-39130503943 / 1000000000000) (-39130503942 / 1000000000000), orderedInterval (-39735136618 / 1000000000000) (-39735136617 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (511103664493377 / 4000000000000) 4 (IntervalRat.scale (471 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (17118345865 / 1000000000000) (17118346065 / 1000000000000), orderedInterval (-68545522924 / 1000000000000) (-68545522723 / 1000000000000)))) (orderedInterval (-751010321 / 1000000000000) (-751010256 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (274873250618559 / 4000000000000) 4 (IntervalRat.scale (471 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (36312632687 / 1000000000000) (36312632688 / 1000000000000), orderedInterval (88874803916 / 1000000000000) (88874803917 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (746334345892677 / 4000000000000) 4 (IntervalRat.scale (471 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-52759716920 / 1000000000000) (-52759704630 / 1000000000000), orderedInterval (25209020650 / 1000000000000) (25209032941 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1019055743230629 / 4000000000000) 4 (IntervalRat.scale (471 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-44083996604 / 1000000000000) (-44083996603 / 1000000000000), orderedInterval (-23481679905 / 1000000000000) (-23481679904 / 1000000000000)))) (orderedInterval (5110309374 / 1000000000000) (5110309513 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (430896335506623 / 4000000000000) 4 (IntervalRat.scale (471 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (76289998421 / 1000000000000) (76289998622 / 1000000000000), orderedInterval (-9814533841 / 1000000000000) (-9814533640 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1751569681185183 / 4000000000000) 4 (IntervalRat.scale (471 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-34731447994 / 1000000000000) (-34731413664 / 1000000000000), orderedInterval (15773486665 / 1000000000000) (15773520995 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1169967372174897 / 4000000000000) 4 (IntervalRat.scale (471 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-41760282392 / 1000000000000) (-41760282391 / 1000000000000), orderedInterval (-20728022971 / 1000000000000) (-20728022970 / 1000000000000)))) (orderedInterval (52452277627 / 1000000000000) (52452311521 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate364_chunkChecks4 :
    compactCertificate364.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate364.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate364_chunkChecks4_0
    compactCertificate364_chunkChecks4_1 compactCertificate364_chunkChecks4_2

theorem compactCertificate364_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate364.chunkCheck r b = true :=
  compactCertificate364.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate364_chunkChecks0
    · exact compactCertificate364_chunkChecks1
    · exact compactCertificate364_chunkChecks2
    · exact compactCertificate364_chunkChecks3
    · exact compactCertificate364_chunkChecks4)

theorem compactCertificate364_coefficient0 :
    compactCertificate364.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate364_coefficient1 :
    compactCertificate364.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate364_coefficient2 :
    compactCertificate364.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate364_coefficient3 :
    compactCertificate364.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate364_coefficient4 :
    compactCertificate364.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate364_coefficients : ∀ r : Fin 5,
    compactCertificate364.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate364_coefficient0
  · exact compactCertificate364_coefficient1
  · exact compactCertificate364_coefficient2
  · exact compactCertificate364_coefficient3
  · exact compactCertificate364_coefficient4

theorem compactCertificate364_lower : (1 : ℚ) ≤ compactCertificate364.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate364, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate364_proves {t : ℝ} (ht : t ∈ compactCertificate364.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate364.proves compactCertificate364_states compactCertificate364_chunks
    compactCertificate364_coefficients compactCertificate364_lower ht

end Erdos232
