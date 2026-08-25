/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate465 : CompactCertificate where
  left := 336
  right := 337
  center := 673 / 2
  grid := fun i =>
    match i.val with
    | 0 => 107
    | 1 => 79
    | 2 => 128
    | 3 => 23
    | 4 => 62
    | 5 => 168
    | 6 => 124
    | 7 => 212
    | 8 => 156
    | 9 => 240
    | 10 => 138
    | 11 => 246
    | 12 => 229
    | 13 => 164
    | 14 => 186
    | 15 => 155
    | 16 => 137
    | 17 => 198
    | 18 => 110
    | 19 => 93
    | 20 => 58
    | 21 => 31
    | 22 => 85
    | 23 => 116
    | 24 => 49
    | 25 => 199
    | _ => 133
  point := fun i =>
    match i.val with
    | 0 => 673 / 2
    | 1 => 991457507937373 / 4000000000000
    | 2 => 320616987286909 / 800000000000
    | 3 => 289304828085911 / 4000000000000
    | 4 => 777113462329067 / 4000000000000
    | 5 => 2110014220320639 / 4000000000000
    | 6 => 1554226924658807 / 4000000000000
    | 7 => 2663194326352211 / 4000000000000
    | 8 => 1961696887040249 / 4000000000000
    | 9 => 3009747497714327 / 4000000000000
    | 10 => 1737678527997983 / 4000000000000
    | 11 => 3083541041277547 / 4000000000000
    | 12 => 2881044027185143 / 4000000000000
    | 13 => 2056048961802919 / 4000000000000
    | 14 => 2331340386987201 / 4000000000000
    | 15 => 1943628560216369 / 4000000000000
    | 16 => 1717254777291749 / 4000000000000
    | 17 => 497727367679151 / 800000000000
    | 18 => 1376740092956797 / 4000000000000
    | 19 => 1167077823778517 / 4000000000000
    | 20 => 730303112959751 / 4000000000000
    | 21 => 392759443028217 / 4000000000000
    | 22 => 1066418290415651 / 4000000000000
    | 23 => 1456103004658627 / 4000000000000
    | 24 => 615696887040249 / 4000000000000
    | 25 => 2502773663349529 / 4000000000000
    | _ => 1671736818415511 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-39423312850 / 1000000000000) (-39423312849 / 1000000000000), orderedInterval (-18317695962 / 1000000000000) (-18317695961 / 1000000000000))
    | 1 => (orderedInterval (-22655670966 / 1000000000000) (-22655670965 / 1000000000000), orderedInterval (-45287989058 / 1000000000000) (-45287989057 / 1000000000000))
    | 2 => (orderedInterval (-21424838995 / 1000000000000) (-21424837045 / 1000000000000), orderedInterval (33634220635 / 1000000000000) (33634222585 / 1000000000000))
    | 3 => (orderedInterval (-70684382603 / 1000000000000) (-70684382602 / 1000000000000), orderedInterval (-61202149176 / 1000000000000) (-61202149175 / 1000000000000))
    | 4 => (orderedInterval (16060179610 / 1000000000000) (16060179611 / 1000000000000), orderedInterval (54903395364 / 1000000000000) (54903395365 / 1000000000000))
    | 5 => (orderedInterval (16690209154 / 1000000000000) (16690209155 / 1000000000000), orderedInterval (30452051691 / 1000000000000) (30452051692 / 1000000000000))
    | 6 => (orderedInterval (-8662695330 / 1000000000000) (-8662695310 / 1000000000000), orderedInterval (39550755516 / 1000000000000) (39550755536 / 1000000000000))
    | 7 => (orderedInterval (16586174149 / 1000000000000) (16586174150 / 1000000000000), orderedInterval (26084932180 / 1000000000000) (26084932181 / 1000000000000))
    | 8 => (orderedInterval (32444140135 / 1000000000000) (32444140136 / 1000000000000), orderedInterval (15634645121 / 1000000000000) (15634645123 / 1000000000000))
    | 9 => (orderedInterval (-20041687268 / 1000000000000) (-20041684977 / 1000000000000), orderedInterval (21094306779 / 1000000000000) (21094309070 / 1000000000000))
    | 10 => (orderedInterval (38111592086 / 1000000000000) (38111593191 / 1000000000000), orderedInterval (-3643094932 / 1000000000000) (-3643093827 / 1000000000000))
    | 11 => (orderedInterval (-26361300689 / 1000000000000) (-26361201079 / 1000000000000), orderedInterval (11458802040 / 1000000000000) (11458901650 / 1000000000000))
    | 12 => (orderedInterval (-29691783427 / 1000000000000) (-29691779952 / 1000000000000), orderedInterval (1527793271 / 1000000000000) (1527796746 / 1000000000000))
    | 13 => (orderedInterval (-14472210541 / 1000000000000) (-14472210380 / 1000000000000), orderedInterval (32093446137 / 1000000000000) (32093446298 / 1000000000000))
    | 14 => (orderedInterval (-21691717306 / 1000000000000) (-21691713681 / 1000000000000), orderedInterval (24953535305 / 1000000000000) (24953538930 / 1000000000000))
    | 15 => (orderedInterval (9115632381 / 1000000000000) (9115632398 / 1000000000000), orderedInterval (-35038987667 / 1000000000000) (-35038987650 / 1000000000000))
    | 16 => (orderedInterval (11357572135 / 1000000000000) (11357572186 / 1000000000000), orderedInterval (-36808393659 / 1000000000000) (-36808393609 / 1000000000000))
    | 17 => (orderedInterval (25236332372 / 1000000000000) (25236332373 / 1000000000000), orderedInterval (19636015247 / 1000000000000) (19636015248 / 1000000000000))
    | 18 => (orderedInterval (-24465745326 / 1000000000000) (-24465741287 / 1000000000000), orderedInterval (35406037241 / 1000000000000) (35406041279 / 1000000000000))
    | 19 => (orderedInterval (-17599419499 / 1000000000000) (-17599419498 / 1000000000000), orderedInterval (-43238652774 / 1000000000000) (-43238652773 / 1000000000000))
    | 20 => (orderedInterval (53852938614 / 1000000000000) (53852938615 / 1000000000000), orderedInterval (24075071815 / 1000000000000) (24075071816 / 1000000000000))
    | 21 => (orderedInterval (-80512343079 / 1000000000000) (-80512343039 / 1000000000000), orderedInterval (1522525362 / 1000000000000) (1522525401 / 1000000000000))
    | 22 => (orderedInterval (-16945279381 / 1000000000000) (-16945279380 / 1000000000000), orderedInterval (-45802060071 / 1000000000000) (-45802060070 / 1000000000000))
    | 23 => (orderedInterval (15746515333 / 1000000000000) (15746515334 / 1000000000000), orderedInterval (38719566022 / 1000000000000) (38719566023 / 1000000000000))
    | 24 => (orderedInterval (-44804607923 / 1000000000000) (-44804607922 / 1000000000000), orderedInterval (-45989886342 / 1000000000000) (-45989886341 / 1000000000000))
    | 25 => (orderedInterval (-30749536749 / 1000000000000) (-30749536718 / 1000000000000), orderedInterval (-8456495274 / 1000000000000) (-8456495243 / 1000000000000))
    | _ => (orderedInterval (-30266248027 / 1000000000000) (-30266248026 / 1000000000000), orderedInterval (-24605373184 / 1000000000000) (-24605373183 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-17094362012 / 1000000000000) (-17094361873 / 1000000000000)
      | 1 => orderedInterval (166759637 / 1000000000000) (166759678 / 1000000000000)
      | 2 => orderedInterval (272526873 / 1000000000000) (272526893 / 1000000000000)
      | 3 => orderedInterval (2637506510 / 1000000000000) (2637521293 / 1000000000000)
      | 4 => orderedInterval (-722732904 / 1000000000000) (-722732767 / 1000000000000)
      | 5 => orderedInterval (101457975 / 1000000000000) (101458011 / 1000000000000)
      | 6 => orderedInterval (6661210457 / 1000000000000) (6661211188 / 1000000000000)
      | 7 => orderedInterval (664309887 / 1000000000000) (664309929 / 1000000000000)
      | _ => orderedInterval (7911721014 / 1000000000000) (7911721110 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-5220665453 / 1000000000000) (-5220665289 / 1000000000000)
      | 1 => orderedInterval (-2093534767 / 1000000000000) (-2093534720 / 1000000000000)
      | 2 => orderedInterval (-1041207683 / 1000000000000) (-1041207650 / 1000000000000)
      | 3 => orderedInterval (-4997991232 / 1000000000000) (-4997957500 / 1000000000000)
      | 4 => orderedInterval (4358048437 / 1000000000000) (4358048692 / 1000000000000)
      | 5 => orderedInterval (3032704938 / 1000000000000) (3032704989 / 1000000000000)
      | 6 => orderedInterval (-3243207571 / 1000000000000) (-3243206833 / 1000000000000)
      | 7 => orderedInterval (-2395093616 / 1000000000000) (-2395093579 / 1000000000000)
      | _ => orderedInterval (6887014336 / 1000000000000) (6887014472 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (17539436575 / 1000000000000) (17539436769 / 1000000000000)
      | 1 => orderedInterval (2691071445 / 1000000000000) (2691071510 / 1000000000000)
      | 2 => orderedInterval (340345883 / 1000000000000) (340345942 / 1000000000000)
      | 3 => orderedInterval (-2830177503 / 1000000000000) (-2830100324 / 1000000000000)
      | 4 => orderedInterval (395151422 / 1000000000000) (395151909 / 1000000000000)
      | 5 => orderedInterval (-1379407842 / 1000000000000) (-1379407767 / 1000000000000)
      | 6 => orderedInterval (-5347986043 / 1000000000000) (-5347985290 / 1000000000000)
      | 7 => orderedInterval (1051518991 / 1000000000000) (1051519027 / 1000000000000)
      | _ => orderedInterval (-17378010583 / 1000000000000) (-17378010380 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (4042603442 / 1000000000000) (4042603672 / 1000000000000)
      | 1 => orderedInterval (7939175504 / 1000000000000) (7939175600 / 1000000000000)
      | 2 => orderedInterval (5061329573 / 1000000000000) (5061329680 / 1000000000000)
      | 3 => orderedInterval (22910415120 / 1000000000000) (22910591621 / 1000000000000)
      | 4 => orderedInterval (-9891376167 / 1000000000000) (-9891375218 / 1000000000000)
      | 5 => orderedInterval (-6329620095 / 1000000000000) (-6329619981 / 1000000000000)
      | 6 => orderedInterval (4353292668 / 1000000000000) (4353293433 / 1000000000000)
      | 7 => orderedInterval (3237593482 / 1000000000000) (3237593520 / 1000000000000)
      | _ => orderedInterval (-13192070104 / 1000000000000) (-13192069789 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-18241699368 / 1000000000000) (-18241699095 / 1000000000000)
      | 1 => orderedInterval (-7145590118 / 1000000000000) (-7145589970 / 1000000000000)
      | 2 => orderedInterval (-4332926698 / 1000000000000) (-4332926501 / 1000000000000)
      | 3 => orderedInterval (-6480095957 / 1000000000000) (-6479691612 / 1000000000000)
      | 4 => orderedInterval (4847252253 / 1000000000000) (4847254140 / 1000000000000)
      | 5 => orderedInterval (6324147784 / 1000000000000) (6324147962 / 1000000000000)
      | 6 => orderedInterval (4970725328 / 1000000000000) (4970726110 / 1000000000000)
      | 7 => orderedInterval (-1509781402 / 1000000000000) (-1509781363 / 1000000000000)
      | _ => orderedInterval (43500360267 / 1000000000000) (43500360777 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (598397437 / 1000000000000) (598413462 / 1000000000000)
    | 1 => orderedInterval (-4713932611 / 1000000000000) (-4713897418 / 1000000000000)
    | 2 => orderedInterval (-4918057655 / 1000000000000) (-4917978604 / 1000000000000)
    | 3 => orderedInterval (18131343423 / 1000000000000) (18131522538 / 1000000000000)
    | _ => orderedInterval (21932392089 / 1000000000000) (21932800448 / 1000000000000)

theorem compactCertificate465_stateChecks0 :
    compactCertificate465.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 107 12 (673 / 2)) (orderedInterval (-39423312850 / 1000000000000) (-39423312849 / 1000000000000), orderedInterval (-18317695962 / 1000000000000) (-18317695961 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (991457507937373 / 4000000000000)) (orderedInterval (-22655670966 / 1000000000000) (-22655670965 / 1000000000000), orderedInterval (-45287989058 / 1000000000000) (-45287989057 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 128 12 (320616987286909 / 800000000000)) (orderedInterval (-21424838995 / 1000000000000) (-21424837045 / 1000000000000), orderedInterval (33634220635 / 1000000000000) (33634222585 / 1000000000000))) = true
  rfl'

theorem compactCertificate465_stateChecks1 :
    compactCertificate465.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (289304828085911 / 4000000000000)) (orderedInterval (-70684382603 / 1000000000000) (-70684382602 / 1000000000000), orderedInterval (-61202149176 / 1000000000000) (-61202149175 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (777113462329067 / 4000000000000)) (orderedInterval (16060179610 / 1000000000000) (16060179611 / 1000000000000), orderedInterval (54903395364 / 1000000000000) (54903395365 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 168 12 (2110014220320639 / 4000000000000)) (orderedInterval (16690209154 / 1000000000000) (16690209155 / 1000000000000), orderedInterval (30452051691 / 1000000000000) (30452051692 / 1000000000000))) = true
  rfl'

theorem compactCertificate465_stateChecks2 :
    compactCertificate465.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 124 12 (1554226924658807 / 4000000000000)) (orderedInterval (-8662695330 / 1000000000000) (-8662695310 / 1000000000000), orderedInterval (39550755516 / 1000000000000) (39550755536 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 212 12 (2663194326352211 / 4000000000000)) (orderedInterval (16586174149 / 1000000000000) (16586174150 / 1000000000000), orderedInterval (26084932180 / 1000000000000) (26084932181 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 156 12 (1961696887040249 / 4000000000000)) (orderedInterval (32444140135 / 1000000000000) (32444140136 / 1000000000000), orderedInterval (15634645121 / 1000000000000) (15634645123 / 1000000000000))) = true
  rfl'

theorem compactCertificate465_stateChecks3 :
    compactCertificate465.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 240 12 (3009747497714327 / 4000000000000)) (orderedInterval (-20041687268 / 1000000000000) (-20041684977 / 1000000000000), orderedInterval (21094306779 / 1000000000000) (21094309070 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 138 12 (1737678527997983 / 4000000000000)) (orderedInterval (38111592086 / 1000000000000) (38111593191 / 1000000000000), orderedInterval (-3643094932 / 1000000000000) (-3643093827 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 246 12 (3083541041277547 / 4000000000000)) (orderedInterval (-26361300689 / 1000000000000) (-26361201079 / 1000000000000), orderedInterval (11458802040 / 1000000000000) (11458901650 / 1000000000000))) = true
  rfl'

theorem compactCertificate465_stateChecks4 :
    compactCertificate465.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 229 12 (2881044027185143 / 4000000000000)) (orderedInterval (-29691783427 / 1000000000000) (-29691779952 / 1000000000000), orderedInterval (1527793271 / 1000000000000) (1527796746 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 164 12 (2056048961802919 / 4000000000000)) (orderedInterval (-14472210541 / 1000000000000) (-14472210380 / 1000000000000), orderedInterval (32093446137 / 1000000000000) (32093446298 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 186 12 (2331340386987201 / 4000000000000)) (orderedInterval (-21691717306 / 1000000000000) (-21691713681 / 1000000000000), orderedInterval (24953535305 / 1000000000000) (24953538930 / 1000000000000))) = true
  rfl'

theorem compactCertificate465_stateChecks5 :
    compactCertificate465.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 155 12 (1943628560216369 / 4000000000000)) (orderedInterval (9115632381 / 1000000000000) (9115632398 / 1000000000000), orderedInterval (-35038987667 / 1000000000000) (-35038987650 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 137 12 (1717254777291749 / 4000000000000)) (orderedInterval (11357572135 / 1000000000000) (11357572186 / 1000000000000), orderedInterval (-36808393659 / 1000000000000) (-36808393609 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 198 12 (497727367679151 / 800000000000)) (orderedInterval (25236332372 / 1000000000000) (25236332373 / 1000000000000), orderedInterval (19636015247 / 1000000000000) (19636015248 / 1000000000000))) = true
  rfl'

theorem compactCertificate465_stateChecks6 :
    compactCertificate465.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 110 12 (1376740092956797 / 4000000000000)) (orderedInterval (-24465745326 / 1000000000000) (-24465741287 / 1000000000000), orderedInterval (35406037241 / 1000000000000) (35406041279 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 93 12 (1167077823778517 / 4000000000000)) (orderedInterval (-17599419499 / 1000000000000) (-17599419498 / 1000000000000), orderedInterval (-43238652774 / 1000000000000) (-43238652773 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (730303112959751 / 4000000000000)) (orderedInterval (53852938614 / 1000000000000) (53852938615 / 1000000000000), orderedInterval (24075071815 / 1000000000000) (24075071816 / 1000000000000))) = true
  rfl'

theorem compactCertificate465_stateChecks7 :
    compactCertificate465.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (392759443028217 / 4000000000000)) (orderedInterval (-80512343079 / 1000000000000) (-80512343039 / 1000000000000), orderedInterval (1522525362 / 1000000000000) (1522525401 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (1066418290415651 / 4000000000000)) (orderedInterval (-16945279381 / 1000000000000) (-16945279380 / 1000000000000), orderedInterval (-45802060071 / 1000000000000) (-45802060070 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 116 12 (1456103004658627 / 4000000000000)) (orderedInterval (15746515333 / 1000000000000) (15746515334 / 1000000000000), orderedInterval (38719566022 / 1000000000000) (38719566023 / 1000000000000))) = true
  rfl'

theorem compactCertificate465_stateChecks8 :
    compactCertificate465.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (615696887040249 / 4000000000000)) (orderedInterval (-44804607923 / 1000000000000) (-44804607922 / 1000000000000), orderedInterval (-45989886342 / 1000000000000) (-45989886341 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 199 12 (2502773663349529 / 4000000000000)) (orderedInterval (-30749536749 / 1000000000000) (-30749536718 / 1000000000000), orderedInterval (-8456495274 / 1000000000000) (-8456495243 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 133 12 (1671736818415511 / 4000000000000)) (orderedInterval (-30266248027 / 1000000000000) (-30266248026 / 1000000000000), orderedInterval (-24605373184 / 1000000000000) (-24605373183 / 1000000000000))) = true
  rfl'

theorem compactCertificate465_states : ∀ j,
    BesselStateValid (compactCertificate465.point j) (compactCertificate465.state j) :=
  compactCertificate465.statesValid_of_checks3 compactCertificate465_stateChecks0
    compactCertificate465_stateChecks1 compactCertificate465_stateChecks2
    compactCertificate465_stateChecks3 compactCertificate465_stateChecks4
    compactCertificate465_stateChecks5 compactCertificate465_stateChecks6
    compactCertificate465_stateChecks7 compactCertificate465_stateChecks8

theorem compactCertificate465_chunkChecks0_0 :
    compactCertificate465.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (673 / 2) 0 (IntervalRat.scale (673 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-39423312850 / 1000000000000) (-39423312849 / 1000000000000), orderedInterval (-18317695962 / 1000000000000) (-18317695961 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (991457507937373 / 4000000000000) 0 (IntervalRat.scale (673 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-22655670966 / 1000000000000) (-22655670965 / 1000000000000), orderedInterval (-45287989058 / 1000000000000) (-45287989057 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (320616987286909 / 800000000000) 0 (IntervalRat.scale (673 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-21424838995 / 1000000000000) (-21424837045 / 1000000000000), orderedInterval (33634220635 / 1000000000000) (33634222585 / 1000000000000)))) (orderedInterval (-17094362012 / 1000000000000) (-17094361873 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (289304828085911 / 4000000000000) 0 (IntervalRat.scale (673 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-70684382603 / 1000000000000) (-70684382602 / 1000000000000), orderedInterval (-61202149176 / 1000000000000) (-61202149175 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (777113462329067 / 4000000000000) 0 (IntervalRat.scale (673 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (16060179610 / 1000000000000) (16060179611 / 1000000000000), orderedInterval (54903395364 / 1000000000000) (54903395365 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2110014220320639 / 4000000000000) 0 (IntervalRat.scale (673 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (16690209154 / 1000000000000) (16690209155 / 1000000000000), orderedInterval (30452051691 / 1000000000000) (30452051692 / 1000000000000)))) (orderedInterval (166759637 / 1000000000000) (166759678 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1554226924658807 / 4000000000000) 0 (IntervalRat.scale (673 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-8662695330 / 1000000000000) (-8662695310 / 1000000000000), orderedInterval (39550755516 / 1000000000000) (39550755536 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2663194326352211 / 4000000000000) 0 (IntervalRat.scale (673 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (16586174149 / 1000000000000) (16586174150 / 1000000000000), orderedInterval (26084932180 / 1000000000000) (26084932181 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1961696887040249 / 4000000000000) 0 (IntervalRat.scale (673 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (32444140135 / 1000000000000) (32444140136 / 1000000000000), orderedInterval (15634645121 / 1000000000000) (15634645123 / 1000000000000)))) (orderedInterval (272526873 / 1000000000000) (272526893 / 1000000000000))) = true
  rfl'

theorem compactCertificate465_chunkChecks0_1 :
    compactCertificate465.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3009747497714327 / 4000000000000) 0 (IntervalRat.scale (673 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-20041687268 / 1000000000000) (-20041684977 / 1000000000000), orderedInterval (21094306779 / 1000000000000) (21094309070 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1737678527997983 / 4000000000000) 0 (IntervalRat.scale (673 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (38111592086 / 1000000000000) (38111593191 / 1000000000000), orderedInterval (-3643094932 / 1000000000000) (-3643093827 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3083541041277547 / 4000000000000) 0 (IntervalRat.scale (673 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-26361300689 / 1000000000000) (-26361201079 / 1000000000000), orderedInterval (11458802040 / 1000000000000) (11458901650 / 1000000000000)))) (orderedInterval (2637506510 / 1000000000000) (2637521293 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2881044027185143 / 4000000000000) 0 (IntervalRat.scale (673 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-29691783427 / 1000000000000) (-29691779952 / 1000000000000), orderedInterval (1527793271 / 1000000000000) (1527796746 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2056048961802919 / 4000000000000) 0 (IntervalRat.scale (673 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14472210541 / 1000000000000) (-14472210380 / 1000000000000), orderedInterval (32093446137 / 1000000000000) (32093446298 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2331340386987201 / 4000000000000) 0 (IntervalRat.scale (673 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-21691717306 / 1000000000000) (-21691713681 / 1000000000000), orderedInterval (24953535305 / 1000000000000) (24953538930 / 1000000000000)))) (orderedInterval (-722732904 / 1000000000000) (-722732767 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1943628560216369 / 4000000000000) 0 (IntervalRat.scale (673 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (9115632381 / 1000000000000) (9115632398 / 1000000000000), orderedInterval (-35038987667 / 1000000000000) (-35038987650 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1717254777291749 / 4000000000000) 0 (IntervalRat.scale (673 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (11357572135 / 1000000000000) (11357572186 / 1000000000000), orderedInterval (-36808393659 / 1000000000000) (-36808393609 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (497727367679151 / 800000000000) 0 (IntervalRat.scale (673 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (25236332372 / 1000000000000) (25236332373 / 1000000000000), orderedInterval (19636015247 / 1000000000000) (19636015248 / 1000000000000)))) (orderedInterval (101457975 / 1000000000000) (101458011 / 1000000000000))) = true
  rfl'

theorem compactCertificate465_chunkChecks0_2 :
    compactCertificate465.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1376740092956797 / 4000000000000) 0 (IntervalRat.scale (673 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-24465745326 / 1000000000000) (-24465741287 / 1000000000000), orderedInterval (35406037241 / 1000000000000) (35406041279 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1167077823778517 / 4000000000000) 0 (IntervalRat.scale (673 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-17599419499 / 1000000000000) (-17599419498 / 1000000000000), orderedInterval (-43238652774 / 1000000000000) (-43238652773 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (730303112959751 / 4000000000000) 0 (IntervalRat.scale (673 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (53852938614 / 1000000000000) (53852938615 / 1000000000000), orderedInterval (24075071815 / 1000000000000) (24075071816 / 1000000000000)))) (orderedInterval (6661210457 / 1000000000000) (6661211188 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (392759443028217 / 4000000000000) 0 (IntervalRat.scale (673 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-80512343079 / 1000000000000) (-80512343039 / 1000000000000), orderedInterval (1522525362 / 1000000000000) (1522525401 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1066418290415651 / 4000000000000) 0 (IntervalRat.scale (673 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-16945279381 / 1000000000000) (-16945279380 / 1000000000000), orderedInterval (-45802060071 / 1000000000000) (-45802060070 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1456103004658627 / 4000000000000) 0 (IntervalRat.scale (673 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (15746515333 / 1000000000000) (15746515334 / 1000000000000), orderedInterval (38719566022 / 1000000000000) (38719566023 / 1000000000000)))) (orderedInterval (664309887 / 1000000000000) (664309929 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (615696887040249 / 4000000000000) 0 (IntervalRat.scale (673 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-44804607923 / 1000000000000) (-44804607922 / 1000000000000), orderedInterval (-45989886342 / 1000000000000) (-45989886341 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2502773663349529 / 4000000000000) 0 (IntervalRat.scale (673 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-30749536749 / 1000000000000) (-30749536718 / 1000000000000), orderedInterval (-8456495274 / 1000000000000) (-8456495243 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1671736818415511 / 4000000000000) 0 (IntervalRat.scale (673 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-30266248027 / 1000000000000) (-30266248026 / 1000000000000), orderedInterval (-24605373184 / 1000000000000) (-24605373183 / 1000000000000)))) (orderedInterval (7911721014 / 1000000000000) (7911721110 / 1000000000000))) = true
  rfl'

theorem compactCertificate465_chunkChecks0 :
    compactCertificate465.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate465.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate465_chunkChecks0_0
    compactCertificate465_chunkChecks0_1 compactCertificate465_chunkChecks0_2

theorem compactCertificate465_chunkChecks1_0 :
    compactCertificate465.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (673 / 2) 1 (IntervalRat.scale (673 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-39423312850 / 1000000000000) (-39423312849 / 1000000000000), orderedInterval (-18317695962 / 1000000000000) (-18317695961 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (991457507937373 / 4000000000000) 1 (IntervalRat.scale (673 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-22655670966 / 1000000000000) (-22655670965 / 1000000000000), orderedInterval (-45287989058 / 1000000000000) (-45287989057 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (320616987286909 / 800000000000) 1 (IntervalRat.scale (673 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-21424838995 / 1000000000000) (-21424837045 / 1000000000000), orderedInterval (33634220635 / 1000000000000) (33634222585 / 1000000000000)))) (orderedInterval (-5220665453 / 1000000000000) (-5220665289 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (289304828085911 / 4000000000000) 1 (IntervalRat.scale (673 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-70684382603 / 1000000000000) (-70684382602 / 1000000000000), orderedInterval (-61202149176 / 1000000000000) (-61202149175 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (777113462329067 / 4000000000000) 1 (IntervalRat.scale (673 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (16060179610 / 1000000000000) (16060179611 / 1000000000000), orderedInterval (54903395364 / 1000000000000) (54903395365 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2110014220320639 / 4000000000000) 1 (IntervalRat.scale (673 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (16690209154 / 1000000000000) (16690209155 / 1000000000000), orderedInterval (30452051691 / 1000000000000) (30452051692 / 1000000000000)))) (orderedInterval (-2093534767 / 1000000000000) (-2093534720 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1554226924658807 / 4000000000000) 1 (IntervalRat.scale (673 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-8662695330 / 1000000000000) (-8662695310 / 1000000000000), orderedInterval (39550755516 / 1000000000000) (39550755536 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2663194326352211 / 4000000000000) 1 (IntervalRat.scale (673 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (16586174149 / 1000000000000) (16586174150 / 1000000000000), orderedInterval (26084932180 / 1000000000000) (26084932181 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1961696887040249 / 4000000000000) 1 (IntervalRat.scale (673 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (32444140135 / 1000000000000) (32444140136 / 1000000000000), orderedInterval (15634645121 / 1000000000000) (15634645123 / 1000000000000)))) (orderedInterval (-1041207683 / 1000000000000) (-1041207650 / 1000000000000))) = true
  rfl'

theorem compactCertificate465_chunkChecks1_1 :
    compactCertificate465.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3009747497714327 / 4000000000000) 1 (IntervalRat.scale (673 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-20041687268 / 1000000000000) (-20041684977 / 1000000000000), orderedInterval (21094306779 / 1000000000000) (21094309070 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1737678527997983 / 4000000000000) 1 (IntervalRat.scale (673 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (38111592086 / 1000000000000) (38111593191 / 1000000000000), orderedInterval (-3643094932 / 1000000000000) (-3643093827 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3083541041277547 / 4000000000000) 1 (IntervalRat.scale (673 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-26361300689 / 1000000000000) (-26361201079 / 1000000000000), orderedInterval (11458802040 / 1000000000000) (11458901650 / 1000000000000)))) (orderedInterval (-4997991232 / 1000000000000) (-4997957500 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2881044027185143 / 4000000000000) 1 (IntervalRat.scale (673 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-29691783427 / 1000000000000) (-29691779952 / 1000000000000), orderedInterval (1527793271 / 1000000000000) (1527796746 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2056048961802919 / 4000000000000) 1 (IntervalRat.scale (673 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14472210541 / 1000000000000) (-14472210380 / 1000000000000), orderedInterval (32093446137 / 1000000000000) (32093446298 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2331340386987201 / 4000000000000) 1 (IntervalRat.scale (673 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-21691717306 / 1000000000000) (-21691713681 / 1000000000000), orderedInterval (24953535305 / 1000000000000) (24953538930 / 1000000000000)))) (orderedInterval (4358048437 / 1000000000000) (4358048692 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1943628560216369 / 4000000000000) 1 (IntervalRat.scale (673 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (9115632381 / 1000000000000) (9115632398 / 1000000000000), orderedInterval (-35038987667 / 1000000000000) (-35038987650 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1717254777291749 / 4000000000000) 1 (IntervalRat.scale (673 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (11357572135 / 1000000000000) (11357572186 / 1000000000000), orderedInterval (-36808393659 / 1000000000000) (-36808393609 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (497727367679151 / 800000000000) 1 (IntervalRat.scale (673 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (25236332372 / 1000000000000) (25236332373 / 1000000000000), orderedInterval (19636015247 / 1000000000000) (19636015248 / 1000000000000)))) (orderedInterval (3032704938 / 1000000000000) (3032704989 / 1000000000000))) = true
  rfl'

theorem compactCertificate465_chunkChecks1_2 :
    compactCertificate465.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1376740092956797 / 4000000000000) 1 (IntervalRat.scale (673 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-24465745326 / 1000000000000) (-24465741287 / 1000000000000), orderedInterval (35406037241 / 1000000000000) (35406041279 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1167077823778517 / 4000000000000) 1 (IntervalRat.scale (673 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-17599419499 / 1000000000000) (-17599419498 / 1000000000000), orderedInterval (-43238652774 / 1000000000000) (-43238652773 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (730303112959751 / 4000000000000) 1 (IntervalRat.scale (673 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (53852938614 / 1000000000000) (53852938615 / 1000000000000), orderedInterval (24075071815 / 1000000000000) (24075071816 / 1000000000000)))) (orderedInterval (-3243207571 / 1000000000000) (-3243206833 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (392759443028217 / 4000000000000) 1 (IntervalRat.scale (673 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-80512343079 / 1000000000000) (-80512343039 / 1000000000000), orderedInterval (1522525362 / 1000000000000) (1522525401 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1066418290415651 / 4000000000000) 1 (IntervalRat.scale (673 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-16945279381 / 1000000000000) (-16945279380 / 1000000000000), orderedInterval (-45802060071 / 1000000000000) (-45802060070 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1456103004658627 / 4000000000000) 1 (IntervalRat.scale (673 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (15746515333 / 1000000000000) (15746515334 / 1000000000000), orderedInterval (38719566022 / 1000000000000) (38719566023 / 1000000000000)))) (orderedInterval (-2395093616 / 1000000000000) (-2395093579 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (615696887040249 / 4000000000000) 1 (IntervalRat.scale (673 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-44804607923 / 1000000000000) (-44804607922 / 1000000000000), orderedInterval (-45989886342 / 1000000000000) (-45989886341 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2502773663349529 / 4000000000000) 1 (IntervalRat.scale (673 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-30749536749 / 1000000000000) (-30749536718 / 1000000000000), orderedInterval (-8456495274 / 1000000000000) (-8456495243 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1671736818415511 / 4000000000000) 1 (IntervalRat.scale (673 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-30266248027 / 1000000000000) (-30266248026 / 1000000000000), orderedInterval (-24605373184 / 1000000000000) (-24605373183 / 1000000000000)))) (orderedInterval (6887014336 / 1000000000000) (6887014472 / 1000000000000))) = true
  rfl'

theorem compactCertificate465_chunkChecks1 :
    compactCertificate465.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate465.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate465_chunkChecks1_0
    compactCertificate465_chunkChecks1_1 compactCertificate465_chunkChecks1_2

theorem compactCertificate465_chunkChecks2_0 :
    compactCertificate465.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (673 / 2) 2 (IntervalRat.scale (673 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-39423312850 / 1000000000000) (-39423312849 / 1000000000000), orderedInterval (-18317695962 / 1000000000000) (-18317695961 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (991457507937373 / 4000000000000) 2 (IntervalRat.scale (673 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-22655670966 / 1000000000000) (-22655670965 / 1000000000000), orderedInterval (-45287989058 / 1000000000000) (-45287989057 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (320616987286909 / 800000000000) 2 (IntervalRat.scale (673 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-21424838995 / 1000000000000) (-21424837045 / 1000000000000), orderedInterval (33634220635 / 1000000000000) (33634222585 / 1000000000000)))) (orderedInterval (17539436575 / 1000000000000) (17539436769 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (289304828085911 / 4000000000000) 2 (IntervalRat.scale (673 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-70684382603 / 1000000000000) (-70684382602 / 1000000000000), orderedInterval (-61202149176 / 1000000000000) (-61202149175 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (777113462329067 / 4000000000000) 2 (IntervalRat.scale (673 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (16060179610 / 1000000000000) (16060179611 / 1000000000000), orderedInterval (54903395364 / 1000000000000) (54903395365 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2110014220320639 / 4000000000000) 2 (IntervalRat.scale (673 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (16690209154 / 1000000000000) (16690209155 / 1000000000000), orderedInterval (30452051691 / 1000000000000) (30452051692 / 1000000000000)))) (orderedInterval (2691071445 / 1000000000000) (2691071510 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1554226924658807 / 4000000000000) 2 (IntervalRat.scale (673 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-8662695330 / 1000000000000) (-8662695310 / 1000000000000), orderedInterval (39550755516 / 1000000000000) (39550755536 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2663194326352211 / 4000000000000) 2 (IntervalRat.scale (673 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (16586174149 / 1000000000000) (16586174150 / 1000000000000), orderedInterval (26084932180 / 1000000000000) (26084932181 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1961696887040249 / 4000000000000) 2 (IntervalRat.scale (673 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (32444140135 / 1000000000000) (32444140136 / 1000000000000), orderedInterval (15634645121 / 1000000000000) (15634645123 / 1000000000000)))) (orderedInterval (340345883 / 1000000000000) (340345942 / 1000000000000))) = true
  rfl'

theorem compactCertificate465_chunkChecks2_1 :
    compactCertificate465.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3009747497714327 / 4000000000000) 2 (IntervalRat.scale (673 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-20041687268 / 1000000000000) (-20041684977 / 1000000000000), orderedInterval (21094306779 / 1000000000000) (21094309070 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1737678527997983 / 4000000000000) 2 (IntervalRat.scale (673 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (38111592086 / 1000000000000) (38111593191 / 1000000000000), orderedInterval (-3643094932 / 1000000000000) (-3643093827 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3083541041277547 / 4000000000000) 2 (IntervalRat.scale (673 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-26361300689 / 1000000000000) (-26361201079 / 1000000000000), orderedInterval (11458802040 / 1000000000000) (11458901650 / 1000000000000)))) (orderedInterval (-2830177503 / 1000000000000) (-2830100324 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2881044027185143 / 4000000000000) 2 (IntervalRat.scale (673 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-29691783427 / 1000000000000) (-29691779952 / 1000000000000), orderedInterval (1527793271 / 1000000000000) (1527796746 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2056048961802919 / 4000000000000) 2 (IntervalRat.scale (673 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14472210541 / 1000000000000) (-14472210380 / 1000000000000), orderedInterval (32093446137 / 1000000000000) (32093446298 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2331340386987201 / 4000000000000) 2 (IntervalRat.scale (673 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-21691717306 / 1000000000000) (-21691713681 / 1000000000000), orderedInterval (24953535305 / 1000000000000) (24953538930 / 1000000000000)))) (orderedInterval (395151422 / 1000000000000) (395151909 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1943628560216369 / 4000000000000) 2 (IntervalRat.scale (673 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (9115632381 / 1000000000000) (9115632398 / 1000000000000), orderedInterval (-35038987667 / 1000000000000) (-35038987650 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1717254777291749 / 4000000000000) 2 (IntervalRat.scale (673 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (11357572135 / 1000000000000) (11357572186 / 1000000000000), orderedInterval (-36808393659 / 1000000000000) (-36808393609 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (497727367679151 / 800000000000) 2 (IntervalRat.scale (673 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (25236332372 / 1000000000000) (25236332373 / 1000000000000), orderedInterval (19636015247 / 1000000000000) (19636015248 / 1000000000000)))) (orderedInterval (-1379407842 / 1000000000000) (-1379407767 / 1000000000000))) = true
  rfl'

theorem compactCertificate465_chunkChecks2_2 :
    compactCertificate465.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1376740092956797 / 4000000000000) 2 (IntervalRat.scale (673 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-24465745326 / 1000000000000) (-24465741287 / 1000000000000), orderedInterval (35406037241 / 1000000000000) (35406041279 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1167077823778517 / 4000000000000) 2 (IntervalRat.scale (673 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-17599419499 / 1000000000000) (-17599419498 / 1000000000000), orderedInterval (-43238652774 / 1000000000000) (-43238652773 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (730303112959751 / 4000000000000) 2 (IntervalRat.scale (673 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (53852938614 / 1000000000000) (53852938615 / 1000000000000), orderedInterval (24075071815 / 1000000000000) (24075071816 / 1000000000000)))) (orderedInterval (-5347986043 / 1000000000000) (-5347985290 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (392759443028217 / 4000000000000) 2 (IntervalRat.scale (673 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-80512343079 / 1000000000000) (-80512343039 / 1000000000000), orderedInterval (1522525362 / 1000000000000) (1522525401 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1066418290415651 / 4000000000000) 2 (IntervalRat.scale (673 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-16945279381 / 1000000000000) (-16945279380 / 1000000000000), orderedInterval (-45802060071 / 1000000000000) (-45802060070 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1456103004658627 / 4000000000000) 2 (IntervalRat.scale (673 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (15746515333 / 1000000000000) (15746515334 / 1000000000000), orderedInterval (38719566022 / 1000000000000) (38719566023 / 1000000000000)))) (orderedInterval (1051518991 / 1000000000000) (1051519027 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (615696887040249 / 4000000000000) 2 (IntervalRat.scale (673 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-44804607923 / 1000000000000) (-44804607922 / 1000000000000), orderedInterval (-45989886342 / 1000000000000) (-45989886341 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2502773663349529 / 4000000000000) 2 (IntervalRat.scale (673 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-30749536749 / 1000000000000) (-30749536718 / 1000000000000), orderedInterval (-8456495274 / 1000000000000) (-8456495243 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1671736818415511 / 4000000000000) 2 (IntervalRat.scale (673 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-30266248027 / 1000000000000) (-30266248026 / 1000000000000), orderedInterval (-24605373184 / 1000000000000) (-24605373183 / 1000000000000)))) (orderedInterval (-17378010583 / 1000000000000) (-17378010380 / 1000000000000))) = true
  rfl'

theorem compactCertificate465_chunkChecks2 :
    compactCertificate465.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate465.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate465_chunkChecks2_0
    compactCertificate465_chunkChecks2_1 compactCertificate465_chunkChecks2_2

theorem compactCertificate465_chunkChecks3_0 :
    compactCertificate465.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (673 / 2) 3 (IntervalRat.scale (673 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-39423312850 / 1000000000000) (-39423312849 / 1000000000000), orderedInterval (-18317695962 / 1000000000000) (-18317695961 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (991457507937373 / 4000000000000) 3 (IntervalRat.scale (673 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-22655670966 / 1000000000000) (-22655670965 / 1000000000000), orderedInterval (-45287989058 / 1000000000000) (-45287989057 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (320616987286909 / 800000000000) 3 (IntervalRat.scale (673 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-21424838995 / 1000000000000) (-21424837045 / 1000000000000), orderedInterval (33634220635 / 1000000000000) (33634222585 / 1000000000000)))) (orderedInterval (4042603442 / 1000000000000) (4042603672 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (289304828085911 / 4000000000000) 3 (IntervalRat.scale (673 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-70684382603 / 1000000000000) (-70684382602 / 1000000000000), orderedInterval (-61202149176 / 1000000000000) (-61202149175 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (777113462329067 / 4000000000000) 3 (IntervalRat.scale (673 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (16060179610 / 1000000000000) (16060179611 / 1000000000000), orderedInterval (54903395364 / 1000000000000) (54903395365 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2110014220320639 / 4000000000000) 3 (IntervalRat.scale (673 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (16690209154 / 1000000000000) (16690209155 / 1000000000000), orderedInterval (30452051691 / 1000000000000) (30452051692 / 1000000000000)))) (orderedInterval (7939175504 / 1000000000000) (7939175600 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1554226924658807 / 4000000000000) 3 (IntervalRat.scale (673 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-8662695330 / 1000000000000) (-8662695310 / 1000000000000), orderedInterval (39550755516 / 1000000000000) (39550755536 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2663194326352211 / 4000000000000) 3 (IntervalRat.scale (673 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (16586174149 / 1000000000000) (16586174150 / 1000000000000), orderedInterval (26084932180 / 1000000000000) (26084932181 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1961696887040249 / 4000000000000) 3 (IntervalRat.scale (673 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (32444140135 / 1000000000000) (32444140136 / 1000000000000), orderedInterval (15634645121 / 1000000000000) (15634645123 / 1000000000000)))) (orderedInterval (5061329573 / 1000000000000) (5061329680 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate465_chunkChecks3_1 :
    compactCertificate465.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3009747497714327 / 4000000000000) 3 (IntervalRat.scale (673 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-20041687268 / 1000000000000) (-20041684977 / 1000000000000), orderedInterval (21094306779 / 1000000000000) (21094309070 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1737678527997983 / 4000000000000) 3 (IntervalRat.scale (673 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (38111592086 / 1000000000000) (38111593191 / 1000000000000), orderedInterval (-3643094932 / 1000000000000) (-3643093827 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3083541041277547 / 4000000000000) 3 (IntervalRat.scale (673 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-26361300689 / 1000000000000) (-26361201079 / 1000000000000), orderedInterval (11458802040 / 1000000000000) (11458901650 / 1000000000000)))) (orderedInterval (22910415120 / 1000000000000) (22910591621 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2881044027185143 / 4000000000000) 3 (IntervalRat.scale (673 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-29691783427 / 1000000000000) (-29691779952 / 1000000000000), orderedInterval (1527793271 / 1000000000000) (1527796746 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2056048961802919 / 4000000000000) 3 (IntervalRat.scale (673 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14472210541 / 1000000000000) (-14472210380 / 1000000000000), orderedInterval (32093446137 / 1000000000000) (32093446298 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2331340386987201 / 4000000000000) 3 (IntervalRat.scale (673 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-21691717306 / 1000000000000) (-21691713681 / 1000000000000), orderedInterval (24953535305 / 1000000000000) (24953538930 / 1000000000000)))) (orderedInterval (-9891376167 / 1000000000000) (-9891375218 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1943628560216369 / 4000000000000) 3 (IntervalRat.scale (673 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (9115632381 / 1000000000000) (9115632398 / 1000000000000), orderedInterval (-35038987667 / 1000000000000) (-35038987650 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1717254777291749 / 4000000000000) 3 (IntervalRat.scale (673 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (11357572135 / 1000000000000) (11357572186 / 1000000000000), orderedInterval (-36808393659 / 1000000000000) (-36808393609 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (497727367679151 / 800000000000) 3 (IntervalRat.scale (673 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (25236332372 / 1000000000000) (25236332373 / 1000000000000), orderedInterval (19636015247 / 1000000000000) (19636015248 / 1000000000000)))) (orderedInterval (-6329620095 / 1000000000000) (-6329619981 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate465_chunkChecks3_2 :
    compactCertificate465.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1376740092956797 / 4000000000000) 3 (IntervalRat.scale (673 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-24465745326 / 1000000000000) (-24465741287 / 1000000000000), orderedInterval (35406037241 / 1000000000000) (35406041279 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1167077823778517 / 4000000000000) 3 (IntervalRat.scale (673 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-17599419499 / 1000000000000) (-17599419498 / 1000000000000), orderedInterval (-43238652774 / 1000000000000) (-43238652773 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (730303112959751 / 4000000000000) 3 (IntervalRat.scale (673 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (53852938614 / 1000000000000) (53852938615 / 1000000000000), orderedInterval (24075071815 / 1000000000000) (24075071816 / 1000000000000)))) (orderedInterval (4353292668 / 1000000000000) (4353293433 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (392759443028217 / 4000000000000) 3 (IntervalRat.scale (673 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-80512343079 / 1000000000000) (-80512343039 / 1000000000000), orderedInterval (1522525362 / 1000000000000) (1522525401 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1066418290415651 / 4000000000000) 3 (IntervalRat.scale (673 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-16945279381 / 1000000000000) (-16945279380 / 1000000000000), orderedInterval (-45802060071 / 1000000000000) (-45802060070 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1456103004658627 / 4000000000000) 3 (IntervalRat.scale (673 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (15746515333 / 1000000000000) (15746515334 / 1000000000000), orderedInterval (38719566022 / 1000000000000) (38719566023 / 1000000000000)))) (orderedInterval (3237593482 / 1000000000000) (3237593520 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (615696887040249 / 4000000000000) 3 (IntervalRat.scale (673 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-44804607923 / 1000000000000) (-44804607922 / 1000000000000), orderedInterval (-45989886342 / 1000000000000) (-45989886341 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2502773663349529 / 4000000000000) 3 (IntervalRat.scale (673 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-30749536749 / 1000000000000) (-30749536718 / 1000000000000), orderedInterval (-8456495274 / 1000000000000) (-8456495243 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1671736818415511 / 4000000000000) 3 (IntervalRat.scale (673 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-30266248027 / 1000000000000) (-30266248026 / 1000000000000), orderedInterval (-24605373184 / 1000000000000) (-24605373183 / 1000000000000)))) (orderedInterval (-13192070104 / 1000000000000) (-13192069789 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate465_chunkChecks3 :
    compactCertificate465.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate465.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate465_chunkChecks3_0
    compactCertificate465_chunkChecks3_1 compactCertificate465_chunkChecks3_2

theorem compactCertificate465_chunkChecks4_0 :
    compactCertificate465.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (673 / 2) 4 (IntervalRat.scale (673 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-39423312850 / 1000000000000) (-39423312849 / 1000000000000), orderedInterval (-18317695962 / 1000000000000) (-18317695961 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (991457507937373 / 4000000000000) 4 (IntervalRat.scale (673 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-22655670966 / 1000000000000) (-22655670965 / 1000000000000), orderedInterval (-45287989058 / 1000000000000) (-45287989057 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (320616987286909 / 800000000000) 4 (IntervalRat.scale (673 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-21424838995 / 1000000000000) (-21424837045 / 1000000000000), orderedInterval (33634220635 / 1000000000000) (33634222585 / 1000000000000)))) (orderedInterval (-18241699368 / 1000000000000) (-18241699095 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (289304828085911 / 4000000000000) 4 (IntervalRat.scale (673 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-70684382603 / 1000000000000) (-70684382602 / 1000000000000), orderedInterval (-61202149176 / 1000000000000) (-61202149175 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (777113462329067 / 4000000000000) 4 (IntervalRat.scale (673 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (16060179610 / 1000000000000) (16060179611 / 1000000000000), orderedInterval (54903395364 / 1000000000000) (54903395365 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2110014220320639 / 4000000000000) 4 (IntervalRat.scale (673 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (16690209154 / 1000000000000) (16690209155 / 1000000000000), orderedInterval (30452051691 / 1000000000000) (30452051692 / 1000000000000)))) (orderedInterval (-7145590118 / 1000000000000) (-7145589970 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1554226924658807 / 4000000000000) 4 (IntervalRat.scale (673 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-8662695330 / 1000000000000) (-8662695310 / 1000000000000), orderedInterval (39550755516 / 1000000000000) (39550755536 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2663194326352211 / 4000000000000) 4 (IntervalRat.scale (673 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (16586174149 / 1000000000000) (16586174150 / 1000000000000), orderedInterval (26084932180 / 1000000000000) (26084932181 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1961696887040249 / 4000000000000) 4 (IntervalRat.scale (673 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (32444140135 / 1000000000000) (32444140136 / 1000000000000), orderedInterval (15634645121 / 1000000000000) (15634645123 / 1000000000000)))) (orderedInterval (-4332926698 / 1000000000000) (-4332926501 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate465_chunkChecks4_1 :
    compactCertificate465.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3009747497714327 / 4000000000000) 4 (IntervalRat.scale (673 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-20041687268 / 1000000000000) (-20041684977 / 1000000000000), orderedInterval (21094306779 / 1000000000000) (21094309070 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1737678527997983 / 4000000000000) 4 (IntervalRat.scale (673 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (38111592086 / 1000000000000) (38111593191 / 1000000000000), orderedInterval (-3643094932 / 1000000000000) (-3643093827 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3083541041277547 / 4000000000000) 4 (IntervalRat.scale (673 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-26361300689 / 1000000000000) (-26361201079 / 1000000000000), orderedInterval (11458802040 / 1000000000000) (11458901650 / 1000000000000)))) (orderedInterval (-6480095957 / 1000000000000) (-6479691612 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2881044027185143 / 4000000000000) 4 (IntervalRat.scale (673 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-29691783427 / 1000000000000) (-29691779952 / 1000000000000), orderedInterval (1527793271 / 1000000000000) (1527796746 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2056048961802919 / 4000000000000) 4 (IntervalRat.scale (673 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14472210541 / 1000000000000) (-14472210380 / 1000000000000), orderedInterval (32093446137 / 1000000000000) (32093446298 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2331340386987201 / 4000000000000) 4 (IntervalRat.scale (673 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-21691717306 / 1000000000000) (-21691713681 / 1000000000000), orderedInterval (24953535305 / 1000000000000) (24953538930 / 1000000000000)))) (orderedInterval (4847252253 / 1000000000000) (4847254140 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1943628560216369 / 4000000000000) 4 (IntervalRat.scale (673 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (9115632381 / 1000000000000) (9115632398 / 1000000000000), orderedInterval (-35038987667 / 1000000000000) (-35038987650 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1717254777291749 / 4000000000000) 4 (IntervalRat.scale (673 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (11357572135 / 1000000000000) (11357572186 / 1000000000000), orderedInterval (-36808393659 / 1000000000000) (-36808393609 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (497727367679151 / 800000000000) 4 (IntervalRat.scale (673 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (25236332372 / 1000000000000) (25236332373 / 1000000000000), orderedInterval (19636015247 / 1000000000000) (19636015248 / 1000000000000)))) (orderedInterval (6324147784 / 1000000000000) (6324147962 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate465_chunkChecks4_2 :
    compactCertificate465.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1376740092956797 / 4000000000000) 4 (IntervalRat.scale (673 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-24465745326 / 1000000000000) (-24465741287 / 1000000000000), orderedInterval (35406037241 / 1000000000000) (35406041279 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1167077823778517 / 4000000000000) 4 (IntervalRat.scale (673 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-17599419499 / 1000000000000) (-17599419498 / 1000000000000), orderedInterval (-43238652774 / 1000000000000) (-43238652773 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (730303112959751 / 4000000000000) 4 (IntervalRat.scale (673 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (53852938614 / 1000000000000) (53852938615 / 1000000000000), orderedInterval (24075071815 / 1000000000000) (24075071816 / 1000000000000)))) (orderedInterval (4970725328 / 1000000000000) (4970726110 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (392759443028217 / 4000000000000) 4 (IntervalRat.scale (673 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-80512343079 / 1000000000000) (-80512343039 / 1000000000000), orderedInterval (1522525362 / 1000000000000) (1522525401 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1066418290415651 / 4000000000000) 4 (IntervalRat.scale (673 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-16945279381 / 1000000000000) (-16945279380 / 1000000000000), orderedInterval (-45802060071 / 1000000000000) (-45802060070 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1456103004658627 / 4000000000000) 4 (IntervalRat.scale (673 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (15746515333 / 1000000000000) (15746515334 / 1000000000000), orderedInterval (38719566022 / 1000000000000) (38719566023 / 1000000000000)))) (orderedInterval (-1509781402 / 1000000000000) (-1509781363 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (615696887040249 / 4000000000000) 4 (IntervalRat.scale (673 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-44804607923 / 1000000000000) (-44804607922 / 1000000000000), orderedInterval (-45989886342 / 1000000000000) (-45989886341 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2502773663349529 / 4000000000000) 4 (IntervalRat.scale (673 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-30749536749 / 1000000000000) (-30749536718 / 1000000000000), orderedInterval (-8456495274 / 1000000000000) (-8456495243 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1671736818415511 / 4000000000000) 4 (IntervalRat.scale (673 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-30266248027 / 1000000000000) (-30266248026 / 1000000000000), orderedInterval (-24605373184 / 1000000000000) (-24605373183 / 1000000000000)))) (orderedInterval (43500360267 / 1000000000000) (43500360777 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate465_chunkChecks4 :
    compactCertificate465.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate465.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate465_chunkChecks4_0
    compactCertificate465_chunkChecks4_1 compactCertificate465_chunkChecks4_2

theorem compactCertificate465_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate465.chunkCheck r b = true :=
  compactCertificate465.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate465_chunkChecks0
    · exact compactCertificate465_chunkChecks1
    · exact compactCertificate465_chunkChecks2
    · exact compactCertificate465_chunkChecks3
    · exact compactCertificate465_chunkChecks4)

theorem compactCertificate465_coefficient0 :
    compactCertificate465.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate465_coefficient1 :
    compactCertificate465.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate465_coefficient2 :
    compactCertificate465.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate465_coefficient3 :
    compactCertificate465.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate465_coefficient4 :
    compactCertificate465.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate465_coefficients : ∀ r : Fin 5,
    compactCertificate465.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate465_coefficient0
  · exact compactCertificate465_coefficient1
  · exact compactCertificate465_coefficient2
  · exact compactCertificate465_coefficient3
  · exact compactCertificate465_coefficient4

theorem compactCertificate465_lower : (1 : ℚ) ≤ compactCertificate465.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate465, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate465_proves {t : ℝ} (ht : t ∈ compactCertificate465.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate465.proves compactCertificate465_states compactCertificate465_chunks
    compactCertificate465_coefficients compactCertificate465_lower ht

end Erdos232
