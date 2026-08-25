/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate519 : CompactCertificate where
  left := 390
  right := 391
  center := 781 / 2
  grid := fun i =>
    match i.val with
    | 0 => 124
    | 1 => 92
    | 2 => 148
    | 3 => 27
    | 4 => 72
    | 5 => 195
    | 6 => 144
    | 7 => 246
    | 8 => 181
    | 9 => 278
    | 10 => 161
    | 11 => 285
    | 12 => 266
    | 13 => 190
    | 14 => 215
    | 15 => 180
    | 16 => 159
    | 17 => 230
    | 18 => 127
    | 19 => 108
    | 20 => 67
    | 21 => 36
    | 22 => 99
    | 23 => 135
    | 24 => 57
    | 25 => 231
    | _ => 154
  point := fun i =>
    match i.val with
    | 0 => 781 / 2
    | 1 => 1150562130310681 / 4000000000000
    | 2 => 372068153151673 / 800000000000
    | 3 => 335731160081867 / 4000000000000
    | 4 => 901821120473999 / 4000000000000
    | 5 => 2448619771278483 / 4000000000000
    | 6 => 1803642240948779 / 4000000000000
    | 7 => 3090571721962967 / 4000000000000
    | 8 => 2276501142315653 / 4000000000000
    | 9 => 3492738180854219 / 4000000000000
    | 10 => 2016533328924851 / 4000000000000
    | 11 => 3578373778956559 / 4000000000000
    | 12 => 3343380958739371 / 4000000000000
    | 13 => 2385994411839643 / 4000000000000
    | 14 => 2705463361421997 / 4000000000000
    | 15 => 2255533292019293 / 4000000000000
    | 16 => 1992832066961153 / 4000000000000
    | 17 => 577600407366147 / 800000000000
    | 18 => 1597673124218809 / 4000000000000
    | 19 => 1354365201145649 / 4000000000000
    | 20 => 847498857684347 / 4000000000000
    | 21 => 455787704316549 / 4000000000000
    | 22 => 1237552280556647 / 4000000000000
    | 23 => 1689771837501319 / 4000000000000
    | 24 => 714501142315653 / 4000000000000
    | 25 => 2904407475595813 / 4000000000000
    | _ => 1940009591653067 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (39881271922 / 1000000000000) (39881273687 / 1000000000000), orderedInterval (-6355913219 / 1000000000000) (-6355911454 / 1000000000000))
    | 1 => (orderedInterval (-26603581685 / 1000000000000) (-26603576450 / 1000000000000), orderedInterval (38846996404 / 1000000000000) (38847001638 / 1000000000000))
    | 2 => (orderedInterval (29314078445 / 1000000000000) (29314078446 / 1000000000000), orderedInterval (22540782549 / 1000000000000) (22540782550 / 1000000000000))
    | 3 => (orderedInterval (9240515085 / 1000000000000) (9240515124 / 1000000000000), orderedInterval (-86655391718 / 1000000000000) (-86655391680 / 1000000000000))
    | 4 => (orderedInterval (2414461980 / 1000000000000) (2414461982 / 1000000000000), orderedInterval (53078398265 / 1000000000000) (53078398267 / 1000000000000))
    | 5 => (orderedInterval (-10436756716 / 1000000000000) (-10436756715 / 1000000000000), orderedInterval (-30504414904 / 1000000000000) (-30504414903 / 1000000000000))
    | 6 => (orderedInterval (-24023583260 / 1000000000000) (-24023577451 / 1000000000000), orderedInterval (28918183289 / 1000000000000) (28918189098 / 1000000000000))
    | 7 => (orderedInterval (16121795338 / 1000000000000) (16121795339 / 1000000000000), orderedInterval (23739063823 / 1000000000000) (23739063824 / 1000000000000))
    | 8 => (orderedInterval (-32062157250 / 1000000000000) (-32062157236 / 1000000000000), orderedInterval (-9490817518 / 1000000000000) (-9490817503 / 1000000000000))
    | 9 => (orderedInterval (15402727746 / 1000000000000) (15402727747 / 1000000000000), orderedInterval (22168514726 / 1000000000000) (22168514727 / 1000000000000))
    | 10 => (orderedInterval (27342062793 / 1000000000000) (27342089911 / 1000000000000), orderedInterval (-22725393726 / 1000000000000) (-22725366608 / 1000000000000))
    | 11 => (orderedInterval (-661424194 / 1000000000000) (-661424193 / 1000000000000), orderedInterval (-26667830421 / 1000000000000) (-26667830420 / 1000000000000))
    | 12 => (orderedInterval (22715793626 / 1000000000000) (22715793627 / 1000000000000), orderedInterval (15659336312 / 1000000000000) (15659336313 / 1000000000000))
    | 13 => (orderedInterval (12153599824 / 1000000000000) (12153599825 / 1000000000000), orderedInterval (30313918666 / 1000000000000) (30313918667 / 1000000000000))
    | 14 => (orderedInterval (-30388586987 / 1000000000000) (-30388580104 / 1000000000000), orderedInterval (4237859159 / 1000000000000) (4237866041 / 1000000000000))
    | 15 => (orderedInterval (-24525046182 / 1000000000000) (-24525034700 / 1000000000000), orderedInterval (22989421808 / 1000000000000) (22989433290 / 1000000000000))
    | 16 => (orderedInterval (17763876127 / 1000000000000) (17763876749 / 1000000000000), orderedInterval (-31038212086 / 1000000000000) (-31038211464 / 1000000000000))
    | 17 => (orderedInterval (6463453405 / 1000000000000) (6463453406 / 1000000000000), orderedInterval (28977728412 / 1000000000000) (28977728413 / 1000000000000))
    | 18 => (orderedInterval (-37506959871 / 1000000000000) (-37506959869 / 1000000000000), orderedInterval (-13631293365 / 1000000000000) (-13631293363 / 1000000000000))
    | 19 => (orderedInterval (3652006830 / 1000000000000) (3652006832 / 1000000000000), orderedInterval (43201852719 / 1000000000000) (43201852720 / 1000000000000))
    | 20 => (orderedInterval (-45178283152 / 1000000000000) (-45178223447 / 1000000000000), orderedInterval (31148836808 / 1000000000000) (31148896514 / 1000000000000))
    | 21 => (orderedInterval (74597044192 / 1000000000000) (74597044283 / 1000000000000), orderedInterval (-5040359845 / 1000000000000) (-5040359753 / 1000000000000))
    | 22 => (orderedInterval (33917320096 / 1000000000000) (33917368994 / 1000000000000), orderedInterval (-30176047593 / 1000000000000) (-30175998695 / 1000000000000))
    | 23 => (orderedInterval (30091179886 / 1000000000000) (30091222730 / 1000000000000), orderedInterval (-24561442750 / 1000000000000) (-24561399906 / 1000000000000))
    | 24 => (orderedInterval (-19863998306 / 1000000000000) (-19863998305 / 1000000000000), orderedInterval (-56242073526 / 1000000000000) (-56242073525 / 1000000000000))
    | 25 => (orderedInterval (-27368638785 / 1000000000000) (-27368638774 / 1000000000000), orderedInterval (-11282533273 / 1000000000000) (-11282533262 / 1000000000000))
    | _ => (orderedInterval (33205928934 / 1000000000000) (33205966506 / 1000000000000), orderedInterval (-14524804010 / 1000000000000) (-14524766438 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (17279829823 / 1000000000000) (17279830599 / 1000000000000)
      | 1 => orderedInterval (729848449 / 1000000000000) (729848497 / 1000000000000)
      | 2 => orderedInterval (-1272139765 / 1000000000000) (-1272139742 / 1000000000000)
      | 3 => orderedInterval (-805082317 / 1000000000000) (-805080152 / 1000000000000)
      | 4 => orderedInterval (892972751 / 1000000000000) (892972833 / 1000000000000)
      | 5 => orderedInterval (-1134284858 / 1000000000000) (-1134284652 / 1000000000000)
      | 6 => orderedInterval (4319584679 / 1000000000000) (4319586721 / 1000000000000)
      | 7 => orderedInterval (-4453079151 / 1000000000000) (-4453074709 / 1000000000000)
      | _ => orderedInterval (-4122211092 / 1000000000000) (-4122203933 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-677272618 / 1000000000000) (-677271852 / 1000000000000)
      | 1 => orderedInterval (4720424158 / 1000000000000) (4720424212 / 1000000000000)
      | 2 => orderedInterval (-1783041870 / 1000000000000) (-1783041831 / 1000000000000)
      | 3 => orderedInterval (-19666523876 / 1000000000000) (-19666520961 / 1000000000000)
      | 4 => orderedInterval (3736510438 / 1000000000000) (3736510575 / 1000000000000)
      | 5 => orderedInterval (4021266505 / 1000000000000) (4021266797 / 1000000000000)
      | 6 => orderedInterval (659335766 / 1000000000000) (659336912 / 1000000000000)
      | 7 => orderedInterval (2605891574 / 1000000000000) (2605896048 / 1000000000000)
      | _ => orderedInterval (4937379917 / 1000000000000) (4937388826 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-18111350431 / 1000000000000) (-18111349668 / 1000000000000)
      | 1 => orderedInterval (-1860118593 / 1000000000000) (-1860118519 / 1000000000000)
      | 2 => orderedInterval (3597184884 / 1000000000000) (3597184953 / 1000000000000)
      | 3 => orderedInterval (10851845350 / 1000000000000) (10851849394 / 1000000000000)
      | 4 => orderedInterval (-1273734690 / 1000000000000) (-1273734459 / 1000000000000)
      | 5 => orderedInterval (1669192293 / 1000000000000) (1669192709 / 1000000000000)
      | 6 => orderedInterval (-5687438709 / 1000000000000) (-5687438047 / 1000000000000)
      | 7 => orderedInterval (3292498274 / 1000000000000) (3292502866 / 1000000000000)
      | _ => orderedInterval (1920474862 / 1000000000000) (1920485986 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (186357911 / 1000000000000) (186358673 / 1000000000000)
      | 1 => orderedInterval (-8731420125 / 1000000000000) (-8731420014 / 1000000000000)
      | 2 => orderedInterval (6372480691 / 1000000000000) (6372480816 / 1000000000000)
      | 3 => orderedInterval (93214371765 / 1000000000000) (93214377607 / 1000000000000)
      | 4 => orderedInterval (-7330088598 / 1000000000000) (-7330088204 / 1000000000000)
      | 5 => orderedInterval (-9181640096 / 1000000000000) (-9181639497 / 1000000000000)
      | 6 => orderedInterval (-885729985 / 1000000000000) (-885729589 / 1000000000000)
      | 7 => orderedInterval (-2734311089 / 1000000000000) (-2734306325 / 1000000000000)
      | _ => orderedInterval (-11097990315 / 1000000000000) (-11097976430 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (19194642602 / 1000000000000) (19194643368 / 1000000000000)
      | 1 => orderedInterval (4534856996 / 1000000000000) (4534857167 / 1000000000000)
      | 2 => orderedInterval (-11149752205 / 1000000000000) (-11149751974 / 1000000000000)
      | 3 => orderedInterval (-65861810875 / 1000000000000) (-65861801918 / 1000000000000)
      | 4 => orderedInterval (-929155730 / 1000000000000) (-929155047 / 1000000000000)
      | 5 => orderedInterval (-1943749699 / 1000000000000) (-1943748829 / 1000000000000)
      | 6 => orderedInterval (6324185210 / 1000000000000) (6324185464 / 1000000000000)
      | 7 => orderedInterval (-3457631145 / 1000000000000) (-3457626141 / 1000000000000)
      | _ => orderedInterval (11857716563 / 1000000000000) (11857733972 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (11435438519 / 1000000000000) (11435455462 / 1000000000000)
    | 1 => orderedInterval (-1446030006 / 1000000000000) (-1446011274 / 1000000000000)
    | 2 => orderedInterval (-5601446760 / 1000000000000) (-5601424785 / 1000000000000)
    | 3 => orderedInterval (59812030159 / 1000000000000) (59812057037 / 1000000000000)
    | _ => orderedInterval (-41430698283 / 1000000000000) (-41430663938 / 1000000000000)

theorem compactCertificate519_stateChecks0 :
    compactCertificate519.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 124 12 (781 / 2)) (orderedInterval (39881271922 / 1000000000000) (39881273687 / 1000000000000), orderedInterval (-6355913219 / 1000000000000) (-6355911454 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 92 12 (1150562130310681 / 4000000000000)) (orderedInterval (-26603581685 / 1000000000000) (-26603576450 / 1000000000000), orderedInterval (38846996404 / 1000000000000) (38847001638 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 148 12 (372068153151673 / 800000000000)) (orderedInterval (29314078445 / 1000000000000) (29314078446 / 1000000000000), orderedInterval (22540782549 / 1000000000000) (22540782550 / 1000000000000))) = true
  rfl'

theorem compactCertificate519_stateChecks1 :
    compactCertificate519.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (335731160081867 / 4000000000000)) (orderedInterval (9240515085 / 1000000000000) (9240515124 / 1000000000000), orderedInterval (-86655391718 / 1000000000000) (-86655391680 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (901821120473999 / 4000000000000)) (orderedInterval (2414461980 / 1000000000000) (2414461982 / 1000000000000), orderedInterval (53078398265 / 1000000000000) (53078398267 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 195 12 (2448619771278483 / 4000000000000)) (orderedInterval (-10436756716 / 1000000000000) (-10436756715 / 1000000000000), orderedInterval (-30504414904 / 1000000000000) (-30504414903 / 1000000000000))) = true
  rfl'

theorem compactCertificate519_stateChecks2 :
    compactCertificate519.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 144 12 (1803642240948779 / 4000000000000)) (orderedInterval (-24023583260 / 1000000000000) (-24023577451 / 1000000000000), orderedInterval (28918183289 / 1000000000000) (28918189098 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 246 12 (3090571721962967 / 4000000000000)) (orderedInterval (16121795338 / 1000000000000) (16121795339 / 1000000000000), orderedInterval (23739063823 / 1000000000000) (23739063824 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 181 12 (2276501142315653 / 4000000000000)) (orderedInterval (-32062157250 / 1000000000000) (-32062157236 / 1000000000000), orderedInterval (-9490817518 / 1000000000000) (-9490817503 / 1000000000000))) = true
  rfl'

theorem compactCertificate519_stateChecks3 :
    compactCertificate519.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 278 12 (3492738180854219 / 4000000000000)) (orderedInterval (15402727746 / 1000000000000) (15402727747 / 1000000000000), orderedInterval (22168514726 / 1000000000000) (22168514727 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 161 12 (2016533328924851 / 4000000000000)) (orderedInterval (27342062793 / 1000000000000) (27342089911 / 1000000000000), orderedInterval (-22725393726 / 1000000000000) (-22725366608 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 285 12 (3578373778956559 / 4000000000000)) (orderedInterval (-661424194 / 1000000000000) (-661424193 / 1000000000000), orderedInterval (-26667830421 / 1000000000000) (-26667830420 / 1000000000000))) = true
  rfl'

theorem compactCertificate519_stateChecks4 :
    compactCertificate519.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 266 12 (3343380958739371 / 4000000000000)) (orderedInterval (22715793626 / 1000000000000) (22715793627 / 1000000000000), orderedInterval (15659336312 / 1000000000000) (15659336313 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 190 12 (2385994411839643 / 4000000000000)) (orderedInterval (12153599824 / 1000000000000) (12153599825 / 1000000000000), orderedInterval (30313918666 / 1000000000000) (30313918667 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 215 12 (2705463361421997 / 4000000000000)) (orderedInterval (-30388586987 / 1000000000000) (-30388580104 / 1000000000000), orderedInterval (4237859159 / 1000000000000) (4237866041 / 1000000000000))) = true
  rfl'

theorem compactCertificate519_stateChecks5 :
    compactCertificate519.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 180 12 (2255533292019293 / 4000000000000)) (orderedInterval (-24525046182 / 1000000000000) (-24525034700 / 1000000000000), orderedInterval (22989421808 / 1000000000000) (22989433290 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 159 12 (1992832066961153 / 4000000000000)) (orderedInterval (17763876127 / 1000000000000) (17763876749 / 1000000000000), orderedInterval (-31038212086 / 1000000000000) (-31038211464 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 230 12 (577600407366147 / 800000000000)) (orderedInterval (6463453405 / 1000000000000) (6463453406 / 1000000000000), orderedInterval (28977728412 / 1000000000000) (28977728413 / 1000000000000))) = true
  rfl'

theorem compactCertificate519_stateChecks6 :
    compactCertificate519.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 127 12 (1597673124218809 / 4000000000000)) (orderedInterval (-37506959871 / 1000000000000) (-37506959869 / 1000000000000), orderedInterval (-13631293365 / 1000000000000) (-13631293363 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 108 12 (1354365201145649 / 4000000000000)) (orderedInterval (3652006830 / 1000000000000) (3652006832 / 1000000000000), orderedInterval (43201852719 / 1000000000000) (43201852720 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (847498857684347 / 4000000000000)) (orderedInterval (-45178283152 / 1000000000000) (-45178223447 / 1000000000000), orderedInterval (31148836808 / 1000000000000) (31148896514 / 1000000000000))) = true
  rfl'

theorem compactCertificate519_stateChecks7 :
    compactCertificate519.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (455787704316549 / 4000000000000)) (orderedInterval (74597044192 / 1000000000000) (74597044283 / 1000000000000), orderedInterval (-5040359845 / 1000000000000) (-5040359753 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 99 12 (1237552280556647 / 4000000000000)) (orderedInterval (33917320096 / 1000000000000) (33917368994 / 1000000000000), orderedInterval (-30176047593 / 1000000000000) (-30175998695 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 135 12 (1689771837501319 / 4000000000000)) (orderedInterval (30091179886 / 1000000000000) (30091222730 / 1000000000000), orderedInterval (-24561442750 / 1000000000000) (-24561399906 / 1000000000000))) = true
  rfl'

theorem compactCertificate519_stateChecks8 :
    compactCertificate519.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (714501142315653 / 4000000000000)) (orderedInterval (-19863998306 / 1000000000000) (-19863998305 / 1000000000000), orderedInterval (-56242073526 / 1000000000000) (-56242073525 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 231 12 (2904407475595813 / 4000000000000)) (orderedInterval (-27368638785 / 1000000000000) (-27368638774 / 1000000000000), orderedInterval (-11282533273 / 1000000000000) (-11282533262 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 154 12 (1940009591653067 / 4000000000000)) (orderedInterval (33205928934 / 1000000000000) (33205966506 / 1000000000000), orderedInterval (-14524804010 / 1000000000000) (-14524766438 / 1000000000000))) = true
  rfl'

theorem compactCertificate519_states : ∀ j,
    BesselStateValid (compactCertificate519.point j) (compactCertificate519.state j) :=
  compactCertificate519.statesValid_of_checks3 compactCertificate519_stateChecks0
    compactCertificate519_stateChecks1 compactCertificate519_stateChecks2
    compactCertificate519_stateChecks3 compactCertificate519_stateChecks4
    compactCertificate519_stateChecks5 compactCertificate519_stateChecks6
    compactCertificate519_stateChecks7 compactCertificate519_stateChecks8

theorem compactCertificate519_chunkChecks0_0 :
    compactCertificate519.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (781 / 2) 0 (IntervalRat.scale (781 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (39881271922 / 1000000000000) (39881273687 / 1000000000000), orderedInterval (-6355913219 / 1000000000000) (-6355911454 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1150562130310681 / 4000000000000) 0 (IntervalRat.scale (781 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-26603581685 / 1000000000000) (-26603576450 / 1000000000000), orderedInterval (38846996404 / 1000000000000) (38847001638 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (372068153151673 / 800000000000) 0 (IntervalRat.scale (781 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (29314078445 / 1000000000000) (29314078446 / 1000000000000), orderedInterval (22540782549 / 1000000000000) (22540782550 / 1000000000000)))) (orderedInterval (17279829823 / 1000000000000) (17279830599 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (335731160081867 / 4000000000000) 0 (IntervalRat.scale (781 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (9240515085 / 1000000000000) (9240515124 / 1000000000000), orderedInterval (-86655391718 / 1000000000000) (-86655391680 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (901821120473999 / 4000000000000) 0 (IntervalRat.scale (781 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (2414461980 / 1000000000000) (2414461982 / 1000000000000), orderedInterval (53078398265 / 1000000000000) (53078398267 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2448619771278483 / 4000000000000) 0 (IntervalRat.scale (781 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-10436756716 / 1000000000000) (-10436756715 / 1000000000000), orderedInterval (-30504414904 / 1000000000000) (-30504414903 / 1000000000000)))) (orderedInterval (729848449 / 1000000000000) (729848497 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1803642240948779 / 4000000000000) 0 (IntervalRat.scale (781 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-24023583260 / 1000000000000) (-24023577451 / 1000000000000), orderedInterval (28918183289 / 1000000000000) (28918189098 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3090571721962967 / 4000000000000) 0 (IntervalRat.scale (781 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (16121795338 / 1000000000000) (16121795339 / 1000000000000), orderedInterval (23739063823 / 1000000000000) (23739063824 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2276501142315653 / 4000000000000) 0 (IntervalRat.scale (781 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-32062157250 / 1000000000000) (-32062157236 / 1000000000000), orderedInterval (-9490817518 / 1000000000000) (-9490817503 / 1000000000000)))) (orderedInterval (-1272139765 / 1000000000000) (-1272139742 / 1000000000000))) = true
  rfl'

theorem compactCertificate519_chunkChecks0_1 :
    compactCertificate519.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3492738180854219 / 4000000000000) 0 (IntervalRat.scale (781 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (15402727746 / 1000000000000) (15402727747 / 1000000000000), orderedInterval (22168514726 / 1000000000000) (22168514727 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2016533328924851 / 4000000000000) 0 (IntervalRat.scale (781 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (27342062793 / 1000000000000) (27342089911 / 1000000000000), orderedInterval (-22725393726 / 1000000000000) (-22725366608 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3578373778956559 / 4000000000000) 0 (IntervalRat.scale (781 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-661424194 / 1000000000000) (-661424193 / 1000000000000), orderedInterval (-26667830421 / 1000000000000) (-26667830420 / 1000000000000)))) (orderedInterval (-805082317 / 1000000000000) (-805080152 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3343380958739371 / 4000000000000) 0 (IntervalRat.scale (781 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (22715793626 / 1000000000000) (22715793627 / 1000000000000), orderedInterval (15659336312 / 1000000000000) (15659336313 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2385994411839643 / 4000000000000) 0 (IntervalRat.scale (781 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (12153599824 / 1000000000000) (12153599825 / 1000000000000), orderedInterval (30313918666 / 1000000000000) (30313918667 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2705463361421997 / 4000000000000) 0 (IntervalRat.scale (781 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-30388586987 / 1000000000000) (-30388580104 / 1000000000000), orderedInterval (4237859159 / 1000000000000) (4237866041 / 1000000000000)))) (orderedInterval (892972751 / 1000000000000) (892972833 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2255533292019293 / 4000000000000) 0 (IntervalRat.scale (781 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-24525046182 / 1000000000000) (-24525034700 / 1000000000000), orderedInterval (22989421808 / 1000000000000) (22989433290 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1992832066961153 / 4000000000000) 0 (IntervalRat.scale (781 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (17763876127 / 1000000000000) (17763876749 / 1000000000000), orderedInterval (-31038212086 / 1000000000000) (-31038211464 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (577600407366147 / 800000000000) 0 (IntervalRat.scale (781 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (6463453405 / 1000000000000) (6463453406 / 1000000000000), orderedInterval (28977728412 / 1000000000000) (28977728413 / 1000000000000)))) (orderedInterval (-1134284858 / 1000000000000) (-1134284652 / 1000000000000))) = true
  rfl'

theorem compactCertificate519_chunkChecks0_2 :
    compactCertificate519.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1597673124218809 / 4000000000000) 0 (IntervalRat.scale (781 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-37506959871 / 1000000000000) (-37506959869 / 1000000000000), orderedInterval (-13631293365 / 1000000000000) (-13631293363 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1354365201145649 / 4000000000000) 0 (IntervalRat.scale (781 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (3652006830 / 1000000000000) (3652006832 / 1000000000000), orderedInterval (43201852719 / 1000000000000) (43201852720 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (847498857684347 / 4000000000000) 0 (IntervalRat.scale (781 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-45178283152 / 1000000000000) (-45178223447 / 1000000000000), orderedInterval (31148836808 / 1000000000000) (31148896514 / 1000000000000)))) (orderedInterval (4319584679 / 1000000000000) (4319586721 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (455787704316549 / 4000000000000) 0 (IntervalRat.scale (781 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (74597044192 / 1000000000000) (74597044283 / 1000000000000), orderedInterval (-5040359845 / 1000000000000) (-5040359753 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1237552280556647 / 4000000000000) 0 (IntervalRat.scale (781 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (33917320096 / 1000000000000) (33917368994 / 1000000000000), orderedInterval (-30176047593 / 1000000000000) (-30175998695 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1689771837501319 / 4000000000000) 0 (IntervalRat.scale (781 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (30091179886 / 1000000000000) (30091222730 / 1000000000000), orderedInterval (-24561442750 / 1000000000000) (-24561399906 / 1000000000000)))) (orderedInterval (-4453079151 / 1000000000000) (-4453074709 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (714501142315653 / 4000000000000) 0 (IntervalRat.scale (781 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-19863998306 / 1000000000000) (-19863998305 / 1000000000000), orderedInterval (-56242073526 / 1000000000000) (-56242073525 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2904407475595813 / 4000000000000) 0 (IntervalRat.scale (781 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-27368638785 / 1000000000000) (-27368638774 / 1000000000000), orderedInterval (-11282533273 / 1000000000000) (-11282533262 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1940009591653067 / 4000000000000) 0 (IntervalRat.scale (781 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (33205928934 / 1000000000000) (33205966506 / 1000000000000), orderedInterval (-14524804010 / 1000000000000) (-14524766438 / 1000000000000)))) (orderedInterval (-4122211092 / 1000000000000) (-4122203933 / 1000000000000))) = true
  rfl'

theorem compactCertificate519_chunkChecks0 :
    compactCertificate519.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate519.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate519_chunkChecks0_0
    compactCertificate519_chunkChecks0_1 compactCertificate519_chunkChecks0_2

theorem compactCertificate519_chunkChecks1_0 :
    compactCertificate519.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (781 / 2) 1 (IntervalRat.scale (781 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (39881271922 / 1000000000000) (39881273687 / 1000000000000), orderedInterval (-6355913219 / 1000000000000) (-6355911454 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1150562130310681 / 4000000000000) 1 (IntervalRat.scale (781 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-26603581685 / 1000000000000) (-26603576450 / 1000000000000), orderedInterval (38846996404 / 1000000000000) (38847001638 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (372068153151673 / 800000000000) 1 (IntervalRat.scale (781 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (29314078445 / 1000000000000) (29314078446 / 1000000000000), orderedInterval (22540782549 / 1000000000000) (22540782550 / 1000000000000)))) (orderedInterval (-677272618 / 1000000000000) (-677271852 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (335731160081867 / 4000000000000) 1 (IntervalRat.scale (781 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (9240515085 / 1000000000000) (9240515124 / 1000000000000), orderedInterval (-86655391718 / 1000000000000) (-86655391680 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (901821120473999 / 4000000000000) 1 (IntervalRat.scale (781 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (2414461980 / 1000000000000) (2414461982 / 1000000000000), orderedInterval (53078398265 / 1000000000000) (53078398267 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2448619771278483 / 4000000000000) 1 (IntervalRat.scale (781 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-10436756716 / 1000000000000) (-10436756715 / 1000000000000), orderedInterval (-30504414904 / 1000000000000) (-30504414903 / 1000000000000)))) (orderedInterval (4720424158 / 1000000000000) (4720424212 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1803642240948779 / 4000000000000) 1 (IntervalRat.scale (781 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-24023583260 / 1000000000000) (-24023577451 / 1000000000000), orderedInterval (28918183289 / 1000000000000) (28918189098 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3090571721962967 / 4000000000000) 1 (IntervalRat.scale (781 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (16121795338 / 1000000000000) (16121795339 / 1000000000000), orderedInterval (23739063823 / 1000000000000) (23739063824 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2276501142315653 / 4000000000000) 1 (IntervalRat.scale (781 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-32062157250 / 1000000000000) (-32062157236 / 1000000000000), orderedInterval (-9490817518 / 1000000000000) (-9490817503 / 1000000000000)))) (orderedInterval (-1783041870 / 1000000000000) (-1783041831 / 1000000000000))) = true
  rfl'

theorem compactCertificate519_chunkChecks1_1 :
    compactCertificate519.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3492738180854219 / 4000000000000) 1 (IntervalRat.scale (781 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (15402727746 / 1000000000000) (15402727747 / 1000000000000), orderedInterval (22168514726 / 1000000000000) (22168514727 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2016533328924851 / 4000000000000) 1 (IntervalRat.scale (781 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (27342062793 / 1000000000000) (27342089911 / 1000000000000), orderedInterval (-22725393726 / 1000000000000) (-22725366608 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3578373778956559 / 4000000000000) 1 (IntervalRat.scale (781 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-661424194 / 1000000000000) (-661424193 / 1000000000000), orderedInterval (-26667830421 / 1000000000000) (-26667830420 / 1000000000000)))) (orderedInterval (-19666523876 / 1000000000000) (-19666520961 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3343380958739371 / 4000000000000) 1 (IntervalRat.scale (781 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (22715793626 / 1000000000000) (22715793627 / 1000000000000), orderedInterval (15659336312 / 1000000000000) (15659336313 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2385994411839643 / 4000000000000) 1 (IntervalRat.scale (781 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (12153599824 / 1000000000000) (12153599825 / 1000000000000), orderedInterval (30313918666 / 1000000000000) (30313918667 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2705463361421997 / 4000000000000) 1 (IntervalRat.scale (781 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-30388586987 / 1000000000000) (-30388580104 / 1000000000000), orderedInterval (4237859159 / 1000000000000) (4237866041 / 1000000000000)))) (orderedInterval (3736510438 / 1000000000000) (3736510575 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2255533292019293 / 4000000000000) 1 (IntervalRat.scale (781 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-24525046182 / 1000000000000) (-24525034700 / 1000000000000), orderedInterval (22989421808 / 1000000000000) (22989433290 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1992832066961153 / 4000000000000) 1 (IntervalRat.scale (781 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (17763876127 / 1000000000000) (17763876749 / 1000000000000), orderedInterval (-31038212086 / 1000000000000) (-31038211464 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (577600407366147 / 800000000000) 1 (IntervalRat.scale (781 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (6463453405 / 1000000000000) (6463453406 / 1000000000000), orderedInterval (28977728412 / 1000000000000) (28977728413 / 1000000000000)))) (orderedInterval (4021266505 / 1000000000000) (4021266797 / 1000000000000))) = true
  rfl'

theorem compactCertificate519_chunkChecks1_2 :
    compactCertificate519.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1597673124218809 / 4000000000000) 1 (IntervalRat.scale (781 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-37506959871 / 1000000000000) (-37506959869 / 1000000000000), orderedInterval (-13631293365 / 1000000000000) (-13631293363 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1354365201145649 / 4000000000000) 1 (IntervalRat.scale (781 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (3652006830 / 1000000000000) (3652006832 / 1000000000000), orderedInterval (43201852719 / 1000000000000) (43201852720 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (847498857684347 / 4000000000000) 1 (IntervalRat.scale (781 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-45178283152 / 1000000000000) (-45178223447 / 1000000000000), orderedInterval (31148836808 / 1000000000000) (31148896514 / 1000000000000)))) (orderedInterval (659335766 / 1000000000000) (659336912 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (455787704316549 / 4000000000000) 1 (IntervalRat.scale (781 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (74597044192 / 1000000000000) (74597044283 / 1000000000000), orderedInterval (-5040359845 / 1000000000000) (-5040359753 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1237552280556647 / 4000000000000) 1 (IntervalRat.scale (781 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (33917320096 / 1000000000000) (33917368994 / 1000000000000), orderedInterval (-30176047593 / 1000000000000) (-30175998695 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1689771837501319 / 4000000000000) 1 (IntervalRat.scale (781 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (30091179886 / 1000000000000) (30091222730 / 1000000000000), orderedInterval (-24561442750 / 1000000000000) (-24561399906 / 1000000000000)))) (orderedInterval (2605891574 / 1000000000000) (2605896048 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (714501142315653 / 4000000000000) 1 (IntervalRat.scale (781 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-19863998306 / 1000000000000) (-19863998305 / 1000000000000), orderedInterval (-56242073526 / 1000000000000) (-56242073525 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2904407475595813 / 4000000000000) 1 (IntervalRat.scale (781 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-27368638785 / 1000000000000) (-27368638774 / 1000000000000), orderedInterval (-11282533273 / 1000000000000) (-11282533262 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1940009591653067 / 4000000000000) 1 (IntervalRat.scale (781 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (33205928934 / 1000000000000) (33205966506 / 1000000000000), orderedInterval (-14524804010 / 1000000000000) (-14524766438 / 1000000000000)))) (orderedInterval (4937379917 / 1000000000000) (4937388826 / 1000000000000))) = true
  rfl'

theorem compactCertificate519_chunkChecks1 :
    compactCertificate519.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate519.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate519_chunkChecks1_0
    compactCertificate519_chunkChecks1_1 compactCertificate519_chunkChecks1_2

theorem compactCertificate519_chunkChecks2_0 :
    compactCertificate519.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (781 / 2) 2 (IntervalRat.scale (781 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (39881271922 / 1000000000000) (39881273687 / 1000000000000), orderedInterval (-6355913219 / 1000000000000) (-6355911454 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1150562130310681 / 4000000000000) 2 (IntervalRat.scale (781 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-26603581685 / 1000000000000) (-26603576450 / 1000000000000), orderedInterval (38846996404 / 1000000000000) (38847001638 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (372068153151673 / 800000000000) 2 (IntervalRat.scale (781 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (29314078445 / 1000000000000) (29314078446 / 1000000000000), orderedInterval (22540782549 / 1000000000000) (22540782550 / 1000000000000)))) (orderedInterval (-18111350431 / 1000000000000) (-18111349668 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (335731160081867 / 4000000000000) 2 (IntervalRat.scale (781 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (9240515085 / 1000000000000) (9240515124 / 1000000000000), orderedInterval (-86655391718 / 1000000000000) (-86655391680 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (901821120473999 / 4000000000000) 2 (IntervalRat.scale (781 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (2414461980 / 1000000000000) (2414461982 / 1000000000000), orderedInterval (53078398265 / 1000000000000) (53078398267 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2448619771278483 / 4000000000000) 2 (IntervalRat.scale (781 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-10436756716 / 1000000000000) (-10436756715 / 1000000000000), orderedInterval (-30504414904 / 1000000000000) (-30504414903 / 1000000000000)))) (orderedInterval (-1860118593 / 1000000000000) (-1860118519 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1803642240948779 / 4000000000000) 2 (IntervalRat.scale (781 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-24023583260 / 1000000000000) (-24023577451 / 1000000000000), orderedInterval (28918183289 / 1000000000000) (28918189098 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3090571721962967 / 4000000000000) 2 (IntervalRat.scale (781 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (16121795338 / 1000000000000) (16121795339 / 1000000000000), orderedInterval (23739063823 / 1000000000000) (23739063824 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2276501142315653 / 4000000000000) 2 (IntervalRat.scale (781 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-32062157250 / 1000000000000) (-32062157236 / 1000000000000), orderedInterval (-9490817518 / 1000000000000) (-9490817503 / 1000000000000)))) (orderedInterval (3597184884 / 1000000000000) (3597184953 / 1000000000000))) = true
  rfl'

theorem compactCertificate519_chunkChecks2_1 :
    compactCertificate519.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3492738180854219 / 4000000000000) 2 (IntervalRat.scale (781 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (15402727746 / 1000000000000) (15402727747 / 1000000000000), orderedInterval (22168514726 / 1000000000000) (22168514727 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2016533328924851 / 4000000000000) 2 (IntervalRat.scale (781 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (27342062793 / 1000000000000) (27342089911 / 1000000000000), orderedInterval (-22725393726 / 1000000000000) (-22725366608 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3578373778956559 / 4000000000000) 2 (IntervalRat.scale (781 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-661424194 / 1000000000000) (-661424193 / 1000000000000), orderedInterval (-26667830421 / 1000000000000) (-26667830420 / 1000000000000)))) (orderedInterval (10851845350 / 1000000000000) (10851849394 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3343380958739371 / 4000000000000) 2 (IntervalRat.scale (781 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (22715793626 / 1000000000000) (22715793627 / 1000000000000), orderedInterval (15659336312 / 1000000000000) (15659336313 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2385994411839643 / 4000000000000) 2 (IntervalRat.scale (781 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (12153599824 / 1000000000000) (12153599825 / 1000000000000), orderedInterval (30313918666 / 1000000000000) (30313918667 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2705463361421997 / 4000000000000) 2 (IntervalRat.scale (781 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-30388586987 / 1000000000000) (-30388580104 / 1000000000000), orderedInterval (4237859159 / 1000000000000) (4237866041 / 1000000000000)))) (orderedInterval (-1273734690 / 1000000000000) (-1273734459 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2255533292019293 / 4000000000000) 2 (IntervalRat.scale (781 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-24525046182 / 1000000000000) (-24525034700 / 1000000000000), orderedInterval (22989421808 / 1000000000000) (22989433290 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1992832066961153 / 4000000000000) 2 (IntervalRat.scale (781 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (17763876127 / 1000000000000) (17763876749 / 1000000000000), orderedInterval (-31038212086 / 1000000000000) (-31038211464 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (577600407366147 / 800000000000) 2 (IntervalRat.scale (781 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (6463453405 / 1000000000000) (6463453406 / 1000000000000), orderedInterval (28977728412 / 1000000000000) (28977728413 / 1000000000000)))) (orderedInterval (1669192293 / 1000000000000) (1669192709 / 1000000000000))) = true
  rfl'

theorem compactCertificate519_chunkChecks2_2 :
    compactCertificate519.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1597673124218809 / 4000000000000) 2 (IntervalRat.scale (781 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-37506959871 / 1000000000000) (-37506959869 / 1000000000000), orderedInterval (-13631293365 / 1000000000000) (-13631293363 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1354365201145649 / 4000000000000) 2 (IntervalRat.scale (781 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (3652006830 / 1000000000000) (3652006832 / 1000000000000), orderedInterval (43201852719 / 1000000000000) (43201852720 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (847498857684347 / 4000000000000) 2 (IntervalRat.scale (781 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-45178283152 / 1000000000000) (-45178223447 / 1000000000000), orderedInterval (31148836808 / 1000000000000) (31148896514 / 1000000000000)))) (orderedInterval (-5687438709 / 1000000000000) (-5687438047 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (455787704316549 / 4000000000000) 2 (IntervalRat.scale (781 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (74597044192 / 1000000000000) (74597044283 / 1000000000000), orderedInterval (-5040359845 / 1000000000000) (-5040359753 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1237552280556647 / 4000000000000) 2 (IntervalRat.scale (781 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (33917320096 / 1000000000000) (33917368994 / 1000000000000), orderedInterval (-30176047593 / 1000000000000) (-30175998695 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1689771837501319 / 4000000000000) 2 (IntervalRat.scale (781 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (30091179886 / 1000000000000) (30091222730 / 1000000000000), orderedInterval (-24561442750 / 1000000000000) (-24561399906 / 1000000000000)))) (orderedInterval (3292498274 / 1000000000000) (3292502866 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (714501142315653 / 4000000000000) 2 (IntervalRat.scale (781 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-19863998306 / 1000000000000) (-19863998305 / 1000000000000), orderedInterval (-56242073526 / 1000000000000) (-56242073525 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2904407475595813 / 4000000000000) 2 (IntervalRat.scale (781 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-27368638785 / 1000000000000) (-27368638774 / 1000000000000), orderedInterval (-11282533273 / 1000000000000) (-11282533262 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1940009591653067 / 4000000000000) 2 (IntervalRat.scale (781 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (33205928934 / 1000000000000) (33205966506 / 1000000000000), orderedInterval (-14524804010 / 1000000000000) (-14524766438 / 1000000000000)))) (orderedInterval (1920474862 / 1000000000000) (1920485986 / 1000000000000))) = true
  rfl'

theorem compactCertificate519_chunkChecks2 :
    compactCertificate519.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate519.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate519_chunkChecks2_0
    compactCertificate519_chunkChecks2_1 compactCertificate519_chunkChecks2_2

theorem compactCertificate519_chunkChecks3_0 :
    compactCertificate519.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (781 / 2) 3 (IntervalRat.scale (781 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (39881271922 / 1000000000000) (39881273687 / 1000000000000), orderedInterval (-6355913219 / 1000000000000) (-6355911454 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1150562130310681 / 4000000000000) 3 (IntervalRat.scale (781 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-26603581685 / 1000000000000) (-26603576450 / 1000000000000), orderedInterval (38846996404 / 1000000000000) (38847001638 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (372068153151673 / 800000000000) 3 (IntervalRat.scale (781 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (29314078445 / 1000000000000) (29314078446 / 1000000000000), orderedInterval (22540782549 / 1000000000000) (22540782550 / 1000000000000)))) (orderedInterval (186357911 / 1000000000000) (186358673 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (335731160081867 / 4000000000000) 3 (IntervalRat.scale (781 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (9240515085 / 1000000000000) (9240515124 / 1000000000000), orderedInterval (-86655391718 / 1000000000000) (-86655391680 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (901821120473999 / 4000000000000) 3 (IntervalRat.scale (781 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (2414461980 / 1000000000000) (2414461982 / 1000000000000), orderedInterval (53078398265 / 1000000000000) (53078398267 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2448619771278483 / 4000000000000) 3 (IntervalRat.scale (781 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-10436756716 / 1000000000000) (-10436756715 / 1000000000000), orderedInterval (-30504414904 / 1000000000000) (-30504414903 / 1000000000000)))) (orderedInterval (-8731420125 / 1000000000000) (-8731420014 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1803642240948779 / 4000000000000) 3 (IntervalRat.scale (781 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-24023583260 / 1000000000000) (-24023577451 / 1000000000000), orderedInterval (28918183289 / 1000000000000) (28918189098 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3090571721962967 / 4000000000000) 3 (IntervalRat.scale (781 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (16121795338 / 1000000000000) (16121795339 / 1000000000000), orderedInterval (23739063823 / 1000000000000) (23739063824 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2276501142315653 / 4000000000000) 3 (IntervalRat.scale (781 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-32062157250 / 1000000000000) (-32062157236 / 1000000000000), orderedInterval (-9490817518 / 1000000000000) (-9490817503 / 1000000000000)))) (orderedInterval (6372480691 / 1000000000000) (6372480816 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate519_chunkChecks3_1 :
    compactCertificate519.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3492738180854219 / 4000000000000) 3 (IntervalRat.scale (781 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (15402727746 / 1000000000000) (15402727747 / 1000000000000), orderedInterval (22168514726 / 1000000000000) (22168514727 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2016533328924851 / 4000000000000) 3 (IntervalRat.scale (781 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (27342062793 / 1000000000000) (27342089911 / 1000000000000), orderedInterval (-22725393726 / 1000000000000) (-22725366608 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3578373778956559 / 4000000000000) 3 (IntervalRat.scale (781 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-661424194 / 1000000000000) (-661424193 / 1000000000000), orderedInterval (-26667830421 / 1000000000000) (-26667830420 / 1000000000000)))) (orderedInterval (93214371765 / 1000000000000) (93214377607 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3343380958739371 / 4000000000000) 3 (IntervalRat.scale (781 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (22715793626 / 1000000000000) (22715793627 / 1000000000000), orderedInterval (15659336312 / 1000000000000) (15659336313 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2385994411839643 / 4000000000000) 3 (IntervalRat.scale (781 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (12153599824 / 1000000000000) (12153599825 / 1000000000000), orderedInterval (30313918666 / 1000000000000) (30313918667 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2705463361421997 / 4000000000000) 3 (IntervalRat.scale (781 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-30388586987 / 1000000000000) (-30388580104 / 1000000000000), orderedInterval (4237859159 / 1000000000000) (4237866041 / 1000000000000)))) (orderedInterval (-7330088598 / 1000000000000) (-7330088204 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2255533292019293 / 4000000000000) 3 (IntervalRat.scale (781 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-24525046182 / 1000000000000) (-24525034700 / 1000000000000), orderedInterval (22989421808 / 1000000000000) (22989433290 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1992832066961153 / 4000000000000) 3 (IntervalRat.scale (781 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (17763876127 / 1000000000000) (17763876749 / 1000000000000), orderedInterval (-31038212086 / 1000000000000) (-31038211464 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (577600407366147 / 800000000000) 3 (IntervalRat.scale (781 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (6463453405 / 1000000000000) (6463453406 / 1000000000000), orderedInterval (28977728412 / 1000000000000) (28977728413 / 1000000000000)))) (orderedInterval (-9181640096 / 1000000000000) (-9181639497 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate519_chunkChecks3_2 :
    compactCertificate519.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1597673124218809 / 4000000000000) 3 (IntervalRat.scale (781 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-37506959871 / 1000000000000) (-37506959869 / 1000000000000), orderedInterval (-13631293365 / 1000000000000) (-13631293363 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1354365201145649 / 4000000000000) 3 (IntervalRat.scale (781 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (3652006830 / 1000000000000) (3652006832 / 1000000000000), orderedInterval (43201852719 / 1000000000000) (43201852720 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (847498857684347 / 4000000000000) 3 (IntervalRat.scale (781 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-45178283152 / 1000000000000) (-45178223447 / 1000000000000), orderedInterval (31148836808 / 1000000000000) (31148896514 / 1000000000000)))) (orderedInterval (-885729985 / 1000000000000) (-885729589 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (455787704316549 / 4000000000000) 3 (IntervalRat.scale (781 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (74597044192 / 1000000000000) (74597044283 / 1000000000000), orderedInterval (-5040359845 / 1000000000000) (-5040359753 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1237552280556647 / 4000000000000) 3 (IntervalRat.scale (781 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (33917320096 / 1000000000000) (33917368994 / 1000000000000), orderedInterval (-30176047593 / 1000000000000) (-30175998695 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1689771837501319 / 4000000000000) 3 (IntervalRat.scale (781 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (30091179886 / 1000000000000) (30091222730 / 1000000000000), orderedInterval (-24561442750 / 1000000000000) (-24561399906 / 1000000000000)))) (orderedInterval (-2734311089 / 1000000000000) (-2734306325 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (714501142315653 / 4000000000000) 3 (IntervalRat.scale (781 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-19863998306 / 1000000000000) (-19863998305 / 1000000000000), orderedInterval (-56242073526 / 1000000000000) (-56242073525 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2904407475595813 / 4000000000000) 3 (IntervalRat.scale (781 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-27368638785 / 1000000000000) (-27368638774 / 1000000000000), orderedInterval (-11282533273 / 1000000000000) (-11282533262 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1940009591653067 / 4000000000000) 3 (IntervalRat.scale (781 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (33205928934 / 1000000000000) (33205966506 / 1000000000000), orderedInterval (-14524804010 / 1000000000000) (-14524766438 / 1000000000000)))) (orderedInterval (-11097990315 / 1000000000000) (-11097976430 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate519_chunkChecks3 :
    compactCertificate519.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate519.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate519_chunkChecks3_0
    compactCertificate519_chunkChecks3_1 compactCertificate519_chunkChecks3_2

theorem compactCertificate519_chunkChecks4_0 :
    compactCertificate519.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (781 / 2) 4 (IntervalRat.scale (781 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (39881271922 / 1000000000000) (39881273687 / 1000000000000), orderedInterval (-6355913219 / 1000000000000) (-6355911454 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1150562130310681 / 4000000000000) 4 (IntervalRat.scale (781 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-26603581685 / 1000000000000) (-26603576450 / 1000000000000), orderedInterval (38846996404 / 1000000000000) (38847001638 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (372068153151673 / 800000000000) 4 (IntervalRat.scale (781 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (29314078445 / 1000000000000) (29314078446 / 1000000000000), orderedInterval (22540782549 / 1000000000000) (22540782550 / 1000000000000)))) (orderedInterval (19194642602 / 1000000000000) (19194643368 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (335731160081867 / 4000000000000) 4 (IntervalRat.scale (781 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (9240515085 / 1000000000000) (9240515124 / 1000000000000), orderedInterval (-86655391718 / 1000000000000) (-86655391680 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (901821120473999 / 4000000000000) 4 (IntervalRat.scale (781 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (2414461980 / 1000000000000) (2414461982 / 1000000000000), orderedInterval (53078398265 / 1000000000000) (53078398267 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2448619771278483 / 4000000000000) 4 (IntervalRat.scale (781 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-10436756716 / 1000000000000) (-10436756715 / 1000000000000), orderedInterval (-30504414904 / 1000000000000) (-30504414903 / 1000000000000)))) (orderedInterval (4534856996 / 1000000000000) (4534857167 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1803642240948779 / 4000000000000) 4 (IntervalRat.scale (781 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-24023583260 / 1000000000000) (-24023577451 / 1000000000000), orderedInterval (28918183289 / 1000000000000) (28918189098 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3090571721962967 / 4000000000000) 4 (IntervalRat.scale (781 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (16121795338 / 1000000000000) (16121795339 / 1000000000000), orderedInterval (23739063823 / 1000000000000) (23739063824 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2276501142315653 / 4000000000000) 4 (IntervalRat.scale (781 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-32062157250 / 1000000000000) (-32062157236 / 1000000000000), orderedInterval (-9490817518 / 1000000000000) (-9490817503 / 1000000000000)))) (orderedInterval (-11149752205 / 1000000000000) (-11149751974 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate519_chunkChecks4_1 :
    compactCertificate519.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3492738180854219 / 4000000000000) 4 (IntervalRat.scale (781 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (15402727746 / 1000000000000) (15402727747 / 1000000000000), orderedInterval (22168514726 / 1000000000000) (22168514727 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2016533328924851 / 4000000000000) 4 (IntervalRat.scale (781 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (27342062793 / 1000000000000) (27342089911 / 1000000000000), orderedInterval (-22725393726 / 1000000000000) (-22725366608 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3578373778956559 / 4000000000000) 4 (IntervalRat.scale (781 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-661424194 / 1000000000000) (-661424193 / 1000000000000), orderedInterval (-26667830421 / 1000000000000) (-26667830420 / 1000000000000)))) (orderedInterval (-65861810875 / 1000000000000) (-65861801918 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3343380958739371 / 4000000000000) 4 (IntervalRat.scale (781 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (22715793626 / 1000000000000) (22715793627 / 1000000000000), orderedInterval (15659336312 / 1000000000000) (15659336313 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2385994411839643 / 4000000000000) 4 (IntervalRat.scale (781 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (12153599824 / 1000000000000) (12153599825 / 1000000000000), orderedInterval (30313918666 / 1000000000000) (30313918667 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2705463361421997 / 4000000000000) 4 (IntervalRat.scale (781 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-30388586987 / 1000000000000) (-30388580104 / 1000000000000), orderedInterval (4237859159 / 1000000000000) (4237866041 / 1000000000000)))) (orderedInterval (-929155730 / 1000000000000) (-929155047 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2255533292019293 / 4000000000000) 4 (IntervalRat.scale (781 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-24525046182 / 1000000000000) (-24525034700 / 1000000000000), orderedInterval (22989421808 / 1000000000000) (22989433290 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1992832066961153 / 4000000000000) 4 (IntervalRat.scale (781 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (17763876127 / 1000000000000) (17763876749 / 1000000000000), orderedInterval (-31038212086 / 1000000000000) (-31038211464 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (577600407366147 / 800000000000) 4 (IntervalRat.scale (781 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (6463453405 / 1000000000000) (6463453406 / 1000000000000), orderedInterval (28977728412 / 1000000000000) (28977728413 / 1000000000000)))) (orderedInterval (-1943749699 / 1000000000000) (-1943748829 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate519_chunkChecks4_2 :
    compactCertificate519.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1597673124218809 / 4000000000000) 4 (IntervalRat.scale (781 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-37506959871 / 1000000000000) (-37506959869 / 1000000000000), orderedInterval (-13631293365 / 1000000000000) (-13631293363 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1354365201145649 / 4000000000000) 4 (IntervalRat.scale (781 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (3652006830 / 1000000000000) (3652006832 / 1000000000000), orderedInterval (43201852719 / 1000000000000) (43201852720 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (847498857684347 / 4000000000000) 4 (IntervalRat.scale (781 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-45178283152 / 1000000000000) (-45178223447 / 1000000000000), orderedInterval (31148836808 / 1000000000000) (31148896514 / 1000000000000)))) (orderedInterval (6324185210 / 1000000000000) (6324185464 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (455787704316549 / 4000000000000) 4 (IntervalRat.scale (781 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (74597044192 / 1000000000000) (74597044283 / 1000000000000), orderedInterval (-5040359845 / 1000000000000) (-5040359753 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1237552280556647 / 4000000000000) 4 (IntervalRat.scale (781 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (33917320096 / 1000000000000) (33917368994 / 1000000000000), orderedInterval (-30176047593 / 1000000000000) (-30175998695 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1689771837501319 / 4000000000000) 4 (IntervalRat.scale (781 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (30091179886 / 1000000000000) (30091222730 / 1000000000000), orderedInterval (-24561442750 / 1000000000000) (-24561399906 / 1000000000000)))) (orderedInterval (-3457631145 / 1000000000000) (-3457626141 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (714501142315653 / 4000000000000) 4 (IntervalRat.scale (781 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-19863998306 / 1000000000000) (-19863998305 / 1000000000000), orderedInterval (-56242073526 / 1000000000000) (-56242073525 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2904407475595813 / 4000000000000) 4 (IntervalRat.scale (781 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-27368638785 / 1000000000000) (-27368638774 / 1000000000000), orderedInterval (-11282533273 / 1000000000000) (-11282533262 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1940009591653067 / 4000000000000) 4 (IntervalRat.scale (781 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (33205928934 / 1000000000000) (33205966506 / 1000000000000), orderedInterval (-14524804010 / 1000000000000) (-14524766438 / 1000000000000)))) (orderedInterval (11857716563 / 1000000000000) (11857733972 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate519_chunkChecks4 :
    compactCertificate519.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate519.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate519_chunkChecks4_0
    compactCertificate519_chunkChecks4_1 compactCertificate519_chunkChecks4_2

theorem compactCertificate519_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate519.chunkCheck r b = true :=
  compactCertificate519.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate519_chunkChecks0
    · exact compactCertificate519_chunkChecks1
    · exact compactCertificate519_chunkChecks2
    · exact compactCertificate519_chunkChecks3
    · exact compactCertificate519_chunkChecks4)

theorem compactCertificate519_coefficient0 :
    compactCertificate519.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate519_coefficient1 :
    compactCertificate519.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate519_coefficient2 :
    compactCertificate519.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate519_coefficient3 :
    compactCertificate519.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate519_coefficient4 :
    compactCertificate519.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate519_coefficients : ∀ r : Fin 5,
    compactCertificate519.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate519_coefficient0
  · exact compactCertificate519_coefficient1
  · exact compactCertificate519_coefficient2
  · exact compactCertificate519_coefficient3
  · exact compactCertificate519_coefficient4

theorem compactCertificate519_lower : (1 : ℚ) ≤ compactCertificate519.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate519, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate519_proves {t : ℝ} (ht : t ∈ compactCertificate519.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate519.proves compactCertificate519_states compactCertificate519_chunks
    compactCertificate519_coefficients compactCertificate519_lower ht

end Erdos232
