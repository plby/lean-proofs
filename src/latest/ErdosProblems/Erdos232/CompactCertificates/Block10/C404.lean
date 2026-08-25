/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate404 : CompactCertificate where
  left := 275
  right := 276
  center := 551 / 2
  grid := fun i =>
    match i.val with
    | 0 => 88
    | 1 => 65
    | 2 => 104
    | 3 => 19
    | 4 => 51
    | 5 => 138
    | 6 => 101
    | 7 => 174
    | 8 => 128
    | 9 => 196
    | 10 => 113
    | 11 => 201
    | 12 => 188
    | 13 => 134
    | 14 => 152
    | 15 => 127
    | 16 => 112
    | 17 => 162
    | 18 => 90
    | 19 => 76
    | 20 => 48
    | 21 => 26
    | 22 => 70
    | 23 => 95
    | 24 => 40
    | 25 => 163
    | _ => 109
  point := fun i =>
    match i.val with
    | 0 => 551 / 2
    | 1 => 811728212293451 / 4000000000000
    | 2 => 262496225847083 / 800000000000
    | 3 => 236860267868257 / 4000000000000
    | 4 => 636239996646829 / 4000000000000
    | 5 => 1727515357201593 / 4000000000000
    | 6 => 1272479993294209 / 4000000000000
    | 7 => 2180416157236357 / 4000000000000
    | 8 => 1606084672747663 / 4000000000000
    | 9 => 2464146911204449 / 4000000000000
    | 10 => 1422675882506521 / 4000000000000
    | 11 => 2524563319084589 / 4000000000000
    | 12 => 2358774530429441 / 4000000000000
    | 13 => 1683332805279953 / 4000000000000
    | 14 => 1908719989940487 / 4000000000000
    | 15 => 1591291733550103 / 4000000000000
    | 16 => 1405954505628163 / 4000000000000
    | 17 => 407500415440137 / 800000000000
    | 18 => 1127167594679339 / 4000000000000
    | 19 => 955512453048979 / 4000000000000
    | 20 => 597915327252337 / 4000000000000
    | 21 => 321560851572879 / 4000000000000
    | 22 => 873100264515637 / 4000000000000
    | 23 => 1192143767558549 / 4000000000000
    | 24 => 504084672747663 / 4000000000000
    | 25 => 2049076208775023 / 4000000000000
    | _ => 1368687944943457 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-8379366724 / 1000000000000) (-8379366699 / 1000000000000), orderedInterval (47349860353 / 1000000000000) (47349860378 / 1000000000000))
    | 1 => (orderedInterval (26195803844 / 1000000000000) (26195806262 / 1000000000000), orderedInterval (-49571040376 / 1000000000000) (-49571037958 / 1000000000000))
    | 2 => (orderedInterval (36132119990 / 1000000000000) (36132224317 / 1000000000000), orderedInterval (-25247721343 / 1000000000000) (-25247617016 / 1000000000000))
    | 3 => (orderedInterval (-31441771565 / 1000000000000) (-31441771564 / 1000000000000), orderedInterval (-98540926425 / 1000000000000) (-98540926424 / 1000000000000))
    | 4 => (orderedInterval (23266937932 / 1000000000000) (23266938807 / 1000000000000), orderedInterval (-58903841676 / 1000000000000) (-58903840802 / 1000000000000))
    | 5 => (orderedInterval (-29489401126 / 1000000000000) (-29489363970 / 1000000000000), orderedInterval (24619613657 / 1000000000000) (24619650812 / 1000000000000))
    | 6 => (orderedInterval (-44709803302 / 1000000000000) (-44709803054 / 1000000000000), orderedInterval (1561863354 / 1000000000000) (1561863602 / 1000000000000))
    | 7 => (orderedInterval (-23242343011 / 1000000000000) (-23242336795 / 1000000000000), orderedInterval (25074866559 / 1000000000000) (25074872775 / 1000000000000))
    | 8 => (orderedInterval (7222520680 / 1000000000000) (7222520681 / 1000000000000), orderedInterval (39149098059 / 1000000000000) (39149098060 / 1000000000000))
    | 9 => (orderedInterval (28195460775 / 1000000000000) (28195460777 / 1000000000000), orderedInterval (15418224531 / 1000000000000) (15418224533 / 1000000000000))
    | 10 => (orderedInterval (-42019446706 / 1000000000000) (-42019446667 / 1000000000000), orderedInterval (-4869066719 / 1000000000000) (-4869066680 / 1000000000000))
    | 11 => (orderedInterval (-14267516559 / 1000000000000) (-14267516558 / 1000000000000), orderedInterval (-28363319063 / 1000000000000) (-28363319062 / 1000000000000))
    | 12 => (orderedInterval (-4604479031 / 1000000000000) (-4604479030 / 1000000000000), orderedInterval (32536599948 / 1000000000000) (32536599950 / 1000000000000))
    | 13 => (orderedInterval (23379619763 / 1000000000000) (23379619764 / 1000000000000), orderedInterval (31055240224 / 1000000000000) (31055240225 / 1000000000000))
    | 14 => (orderedInterval (15658478543 / 1000000000000) (15658478544 / 1000000000000), orderedInterval (32982709689 / 1000000000000) (32982709690 / 1000000000000))
    | 15 => (orderedInterval (14624147431 / 1000000000000) (14624147614 / 1000000000000), orderedInterval (-37252697019 / 1000000000000) (-37252696836 / 1000000000000))
    | 16 => (orderedInterval (17170436620 / 1000000000000) (17170436621 / 1000000000000), orderedInterval (38916395293 / 1000000000000) (38916395294 / 1000000000000))
    | 17 => (orderedInterval (33231795045 / 1000000000000) (33231795048 / 1000000000000), orderedInterval (12027717783 / 1000000000000) (12027717787 / 1000000000000))
    | 18 => (orderedInterval (-7876693942 / 1000000000000) (-7876693921 / 1000000000000), orderedInterval (46887690808 / 1000000000000) (46887690829 / 1000000000000))
    | 19 => (orderedInterval (40500831232 / 1000000000000) (40500831233 / 1000000000000), orderedInterval (31926498991 / 1000000000000) (31926498992 / 1000000000000))
    | 20 => (orderedInterval (-33163040916 / 1000000000000) (-33163035587 / 1000000000000), orderedInterval (56317273947 / 1000000000000) (56317279276 / 1000000000000))
    | 21 => (orderedInterval (-43236451784 / 1000000000000) (-43236445954 / 1000000000000), orderedInterval (78049431552 / 1000000000000) (78049437383 / 1000000000000))
    | 22 => (orderedInterval (-40630025551 / 1000000000000) (-40629948101 / 1000000000000), orderedInterval (35671073065 / 1000000000000) (35671150515 / 1000000000000))
    | 23 => (orderedInterval (-16696484469 / 1000000000000) (-16696484468 / 1000000000000), orderedInterval (-43068160269 / 1000000000000) (-43068160268 / 1000000000000))
    | 24 => (orderedInterval (64636426730 / 1000000000000) (64636426731 / 1000000000000), orderedInterval (29303585851 / 1000000000000) (29303585852 / 1000000000000))
    | 25 => (orderedInterval (-29170786490 / 1000000000000) (-29170786489 / 1000000000000), orderedInterval (-19765717358 / 1000000000000) (-19765717357 / 1000000000000))
    | _ => (orderedInterval (-21560209995 / 1000000000000) (-21560209994 / 1000000000000), orderedInterval (-37327349955 / 1000000000000) (-37327349954 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-956919579 / 1000000000000) (-956913405 / 1000000000000)
      | 1 => orderedInterval (3287025738 / 1000000000000) (3287028445 / 1000000000000)
      | 2 => orderedInterval (891440726 / 1000000000000) (891440934 / 1000000000000)
      | 3 => orderedInterval (-10151499769 / 1000000000000) (-10151499656 / 1000000000000)
      | 4 => orderedInterval (2214727969 / 1000000000000) (2214728003 / 1000000000000)
      | 5 => orderedInterval (37133003 / 1000000000000) (37133033 / 1000000000000)
      | 6 => orderedInterval (-2112553259 / 1000000000000) (-2112553012 / 1000000000000)
      | 7 => orderedInterval (2999731745 / 1000000000000) (2999733643 / 1000000000000)
      | _ => orderedInterval (6809470722 / 1000000000000) (6809470799 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (16663046411 / 1000000000000) (16663053751 / 1000000000000)
      | 1 => orderedInterval (-3755557122 / 1000000000000) (-3755552925 / 1000000000000)
      | 2 => orderedInterval (-151313051 / 1000000000000) (-151312644 / 1000000000000)
      | 3 => orderedInterval (-15828647917 / 1000000000000) (-15828647685 / 1000000000000)
      | 4 => orderedInterval (2939472417 / 1000000000000) (2939472471 / 1000000000000)
      | 5 => orderedInterval (-2893122541 / 1000000000000) (-2893122499 / 1000000000000)
      | 6 => orderedInterval (-8240269171 / 1000000000000) (-8240269009 / 1000000000000)
      | 7 => orderedInterval (2508984960 / 1000000000000) (2508986413 / 1000000000000)
      | _ => orderedInterval (11771036784 / 1000000000000) (11771036892 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (120792753 / 1000000000000) (120801511 / 1000000000000)
      | 1 => orderedInterval (-5437027399 / 1000000000000) (-5437020830 / 1000000000000)
      | 2 => orderedInterval (-3176727530 / 1000000000000) (-3176726729 / 1000000000000)
      | 3 => orderedInterval (40940678686 / 1000000000000) (40940679178 / 1000000000000)
      | 4 => orderedInterval (-5312421705 / 1000000000000) (-5312421616 / 1000000000000)
      | 5 => orderedInterval (-1650884485 / 1000000000000) (-1650884423 / 1000000000000)
      | 6 => orderedInterval (753545205 / 1000000000000) (753545321 / 1000000000000)
      | 7 => orderedInterval (-2153200152 / 1000000000000) (-2153199004 / 1000000000000)
      | _ => orderedInterval (-14574222860 / 1000000000000) (-14574222700 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-16080485415 / 1000000000000) (-16080474992 / 1000000000000)
      | 1 => orderedInterval (7165275781 / 1000000000000) (7165286064 / 1000000000000)
      | 2 => orderedInterval (3073272130 / 1000000000000) (3073273705 / 1000000000000)
      | 3 => orderedInterval (79734456035 / 1000000000000) (79734457110 / 1000000000000)
      | 4 => orderedInterval (-3820136623 / 1000000000000) (-3820136472 / 1000000000000)
      | 5 => orderedInterval (3979656495 / 1000000000000) (3979656590 / 1000000000000)
      | 6 => orderedInterval (8904733139 / 1000000000000) (8904733231 / 1000000000000)
      | 7 => orderedInterval (-3732621475 / 1000000000000) (-3732620563 / 1000000000000)
      | _ => orderedInterval (-23725620601 / 1000000000000) (-23725620356 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (1133474793 / 1000000000000) (1133487237 / 1000000000000)
      | 1 => orderedInterval (12703010546 / 1000000000000) (12703026695 / 1000000000000)
      | 2 => orderedInterval (11752260977 / 1000000000000) (11752264088 / 1000000000000)
      | 3 => orderedInterval (-190340150498 / 1000000000000) (-190340148117 / 1000000000000)
      | 4 => orderedInterval (13096133014 / 1000000000000) (13096133275 / 1000000000000)
      | 5 => orderedInterval (8045151962 / 1000000000000) (8045152112 / 1000000000000)
      | 6 => orderedInterval (-75404654 / 1000000000000) (-75404577 / 1000000000000)
      | 7 => orderedInterval (2148577879 / 1000000000000) (2148578611 / 1000000000000)
      | _ => orderedInterval (38199889999 / 1000000000000) (38199890393 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (3018557296 / 1000000000000) (3018568784 / 1000000000000)
    | 1 => orderedInterval (3013630770 / 1000000000000) (3013644765 / 1000000000000)
    | 2 => orderedInterval (9510532513 / 1000000000000) (9510550708 / 1000000000000)
    | 3 => orderedInterval (55498529466 / 1000000000000) (55498554317 / 1000000000000)
    | _ => orderedInterval (-103337055982 / 1000000000000) (-103337020283 / 1000000000000)

theorem compactCertificate404_stateChecks0 :
    compactCertificate404.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 88 12 (551 / 2)) (orderedInterval (-8379366724 / 1000000000000) (-8379366699 / 1000000000000), orderedInterval (47349860353 / 1000000000000) (47349860378 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (811728212293451 / 4000000000000)) (orderedInterval (26195803844 / 1000000000000) (26195806262 / 1000000000000), orderedInterval (-49571040376 / 1000000000000) (-49571037958 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 104 12 (262496225847083 / 800000000000)) (orderedInterval (36132119990 / 1000000000000) (36132224317 / 1000000000000), orderedInterval (-25247721343 / 1000000000000) (-25247617016 / 1000000000000))) = true
  rfl'

theorem compactCertificate404_stateChecks1 :
    compactCertificate404.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 19 12 (236860267868257 / 4000000000000)) (orderedInterval (-31441771565 / 1000000000000) (-31441771564 / 1000000000000), orderedInterval (-98540926425 / 1000000000000) (-98540926424 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (636239996646829 / 4000000000000)) (orderedInterval (23266937932 / 1000000000000) (23266938807 / 1000000000000), orderedInterval (-58903841676 / 1000000000000) (-58903840802 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 138 12 (1727515357201593 / 4000000000000)) (orderedInterval (-29489401126 / 1000000000000) (-29489363970 / 1000000000000), orderedInterval (24619613657 / 1000000000000) (24619650812 / 1000000000000))) = true
  rfl'

theorem compactCertificate404_stateChecks2 :
    compactCertificate404.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 101 12 (1272479993294209 / 4000000000000)) (orderedInterval (-44709803302 / 1000000000000) (-44709803054 / 1000000000000), orderedInterval (1561863354 / 1000000000000) (1561863602 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 174 12 (2180416157236357 / 4000000000000)) (orderedInterval (-23242343011 / 1000000000000) (-23242336795 / 1000000000000), orderedInterval (25074866559 / 1000000000000) (25074872775 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 128 12 (1606084672747663 / 4000000000000)) (orderedInterval (7222520680 / 1000000000000) (7222520681 / 1000000000000), orderedInterval (39149098059 / 1000000000000) (39149098060 / 1000000000000))) = true
  rfl'

theorem compactCertificate404_stateChecks3 :
    compactCertificate404.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 196 12 (2464146911204449 / 4000000000000)) (orderedInterval (28195460775 / 1000000000000) (28195460777 / 1000000000000), orderedInterval (15418224531 / 1000000000000) (15418224533 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 113 12 (1422675882506521 / 4000000000000)) (orderedInterval (-42019446706 / 1000000000000) (-42019446667 / 1000000000000), orderedInterval (-4869066719 / 1000000000000) (-4869066680 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 201 12 (2524563319084589 / 4000000000000)) (orderedInterval (-14267516559 / 1000000000000) (-14267516558 / 1000000000000), orderedInterval (-28363319063 / 1000000000000) (-28363319062 / 1000000000000))) = true
  rfl'

theorem compactCertificate404_stateChecks4 :
    compactCertificate404.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 188 12 (2358774530429441 / 4000000000000)) (orderedInterval (-4604479031 / 1000000000000) (-4604479030 / 1000000000000), orderedInterval (32536599948 / 1000000000000) (32536599950 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 134 12 (1683332805279953 / 4000000000000)) (orderedInterval (23379619763 / 1000000000000) (23379619764 / 1000000000000), orderedInterval (31055240224 / 1000000000000) (31055240225 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 152 12 (1908719989940487 / 4000000000000)) (orderedInterval (15658478543 / 1000000000000) (15658478544 / 1000000000000), orderedInterval (32982709689 / 1000000000000) (32982709690 / 1000000000000))) = true
  rfl'

theorem compactCertificate404_stateChecks5 :
    compactCertificate404.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 127 12 (1591291733550103 / 4000000000000)) (orderedInterval (14624147431 / 1000000000000) (14624147614 / 1000000000000), orderedInterval (-37252697019 / 1000000000000) (-37252696836 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 112 12 (1405954505628163 / 4000000000000)) (orderedInterval (17170436620 / 1000000000000) (17170436621 / 1000000000000), orderedInterval (38916395293 / 1000000000000) (38916395294 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 162 12 (407500415440137 / 800000000000)) (orderedInterval (33231795045 / 1000000000000) (33231795048 / 1000000000000), orderedInterval (12027717783 / 1000000000000) (12027717787 / 1000000000000))) = true
  rfl'

theorem compactCertificate404_stateChecks6 :
    compactCertificate404.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (1127167594679339 / 4000000000000)) (orderedInterval (-7876693942 / 1000000000000) (-7876693921 / 1000000000000), orderedInterval (46887690808 / 1000000000000) (46887690829 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (955512453048979 / 4000000000000)) (orderedInterval (40500831232 / 1000000000000) (40500831233 / 1000000000000), orderedInterval (31926498991 / 1000000000000) (31926498992 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (597915327252337 / 4000000000000)) (orderedInterval (-33163040916 / 1000000000000) (-33163035587 / 1000000000000), orderedInterval (56317273947 / 1000000000000) (56317279276 / 1000000000000))) = true
  rfl'

theorem compactCertificate404_stateChecks7 :
    compactCertificate404.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (321560851572879 / 4000000000000)) (orderedInterval (-43236451784 / 1000000000000) (-43236445954 / 1000000000000), orderedInterval (78049431552 / 1000000000000) (78049437383 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (873100264515637 / 4000000000000)) (orderedInterval (-40630025551 / 1000000000000) (-40629948101 / 1000000000000), orderedInterval (35671073065 / 1000000000000) (35671150515 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 95 12 (1192143767558549 / 4000000000000)) (orderedInterval (-16696484469 / 1000000000000) (-16696484468 / 1000000000000), orderedInterval (-43068160269 / 1000000000000) (-43068160268 / 1000000000000))) = true
  rfl'

theorem compactCertificate404_stateChecks8 :
    compactCertificate404.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (504084672747663 / 4000000000000)) (orderedInterval (64636426730 / 1000000000000) (64636426731 / 1000000000000), orderedInterval (29303585851 / 1000000000000) (29303585852 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 163 12 (2049076208775023 / 4000000000000)) (orderedInterval (-29170786490 / 1000000000000) (-29170786489 / 1000000000000), orderedInterval (-19765717358 / 1000000000000) (-19765717357 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 109 12 (1368687944943457 / 4000000000000)) (orderedInterval (-21560209995 / 1000000000000) (-21560209994 / 1000000000000), orderedInterval (-37327349955 / 1000000000000) (-37327349954 / 1000000000000))) = true
  rfl'

theorem compactCertificate404_states : ∀ j,
    BesselStateValid (compactCertificate404.point j) (compactCertificate404.state j) :=
  compactCertificate404.statesValid_of_checks3 compactCertificate404_stateChecks0
    compactCertificate404_stateChecks1 compactCertificate404_stateChecks2
    compactCertificate404_stateChecks3 compactCertificate404_stateChecks4
    compactCertificate404_stateChecks5 compactCertificate404_stateChecks6
    compactCertificate404_stateChecks7 compactCertificate404_stateChecks8

theorem compactCertificate404_chunkChecks0_0 :
    compactCertificate404.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (551 / 2) 0 (IntervalRat.scale (551 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-8379366724 / 1000000000000) (-8379366699 / 1000000000000), orderedInterval (47349860353 / 1000000000000) (47349860378 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (811728212293451 / 4000000000000) 0 (IntervalRat.scale (551 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (26195803844 / 1000000000000) (26195806262 / 1000000000000), orderedInterval (-49571040376 / 1000000000000) (-49571037958 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (262496225847083 / 800000000000) 0 (IntervalRat.scale (551 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (36132119990 / 1000000000000) (36132224317 / 1000000000000), orderedInterval (-25247721343 / 1000000000000) (-25247617016 / 1000000000000)))) (orderedInterval (-956919579 / 1000000000000) (-956913405 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (236860267868257 / 4000000000000) 0 (IntervalRat.scale (551 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-31441771565 / 1000000000000) (-31441771564 / 1000000000000), orderedInterval (-98540926425 / 1000000000000) (-98540926424 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (636239996646829 / 4000000000000) 0 (IntervalRat.scale (551 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (23266937932 / 1000000000000) (23266938807 / 1000000000000), orderedInterval (-58903841676 / 1000000000000) (-58903840802 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1727515357201593 / 4000000000000) 0 (IntervalRat.scale (551 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29489401126 / 1000000000000) (-29489363970 / 1000000000000), orderedInterval (24619613657 / 1000000000000) (24619650812 / 1000000000000)))) (orderedInterval (3287025738 / 1000000000000) (3287028445 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1272479993294209 / 4000000000000) 0 (IntervalRat.scale (551 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-44709803302 / 1000000000000) (-44709803054 / 1000000000000), orderedInterval (1561863354 / 1000000000000) (1561863602 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2180416157236357 / 4000000000000) 0 (IntervalRat.scale (551 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-23242343011 / 1000000000000) (-23242336795 / 1000000000000), orderedInterval (25074866559 / 1000000000000) (25074872775 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1606084672747663 / 4000000000000) 0 (IntervalRat.scale (551 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (7222520680 / 1000000000000) (7222520681 / 1000000000000), orderedInterval (39149098059 / 1000000000000) (39149098060 / 1000000000000)))) (orderedInterval (891440726 / 1000000000000) (891440934 / 1000000000000))) = true
  rfl'

theorem compactCertificate404_chunkChecks0_1 :
    compactCertificate404.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2464146911204449 / 4000000000000) 0 (IntervalRat.scale (551 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (28195460775 / 1000000000000) (28195460777 / 1000000000000), orderedInterval (15418224531 / 1000000000000) (15418224533 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1422675882506521 / 4000000000000) 0 (IntervalRat.scale (551 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-42019446706 / 1000000000000) (-42019446667 / 1000000000000), orderedInterval (-4869066719 / 1000000000000) (-4869066680 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2524563319084589 / 4000000000000) 0 (IntervalRat.scale (551 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-14267516559 / 1000000000000) (-14267516558 / 1000000000000), orderedInterval (-28363319063 / 1000000000000) (-28363319062 / 1000000000000)))) (orderedInterval (-10151499769 / 1000000000000) (-10151499656 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2358774530429441 / 4000000000000) 0 (IntervalRat.scale (551 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-4604479031 / 1000000000000) (-4604479030 / 1000000000000), orderedInterval (32536599948 / 1000000000000) (32536599950 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1683332805279953 / 4000000000000) 0 (IntervalRat.scale (551 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (23379619763 / 1000000000000) (23379619764 / 1000000000000), orderedInterval (31055240224 / 1000000000000) (31055240225 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1908719989940487 / 4000000000000) 0 (IntervalRat.scale (551 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (15658478543 / 1000000000000) (15658478544 / 1000000000000), orderedInterval (32982709689 / 1000000000000) (32982709690 / 1000000000000)))) (orderedInterval (2214727969 / 1000000000000) (2214728003 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1591291733550103 / 4000000000000) 0 (IntervalRat.scale (551 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (14624147431 / 1000000000000) (14624147614 / 1000000000000), orderedInterval (-37252697019 / 1000000000000) (-37252696836 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1405954505628163 / 4000000000000) 0 (IntervalRat.scale (551 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (17170436620 / 1000000000000) (17170436621 / 1000000000000), orderedInterval (38916395293 / 1000000000000) (38916395294 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (407500415440137 / 800000000000) 0 (IntervalRat.scale (551 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (33231795045 / 1000000000000) (33231795048 / 1000000000000), orderedInterval (12027717783 / 1000000000000) (12027717787 / 1000000000000)))) (orderedInterval (37133003 / 1000000000000) (37133033 / 1000000000000))) = true
  rfl'

theorem compactCertificate404_chunkChecks0_2 :
    compactCertificate404.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1127167594679339 / 4000000000000) 0 (IntervalRat.scale (551 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-7876693942 / 1000000000000) (-7876693921 / 1000000000000), orderedInterval (46887690808 / 1000000000000) (46887690829 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (955512453048979 / 4000000000000) 0 (IntervalRat.scale (551 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (40500831232 / 1000000000000) (40500831233 / 1000000000000), orderedInterval (31926498991 / 1000000000000) (31926498992 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (597915327252337 / 4000000000000) 0 (IntervalRat.scale (551 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-33163040916 / 1000000000000) (-33163035587 / 1000000000000), orderedInterval (56317273947 / 1000000000000) (56317279276 / 1000000000000)))) (orderedInterval (-2112553259 / 1000000000000) (-2112553012 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (321560851572879 / 4000000000000) 0 (IntervalRat.scale (551 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-43236451784 / 1000000000000) (-43236445954 / 1000000000000), orderedInterval (78049431552 / 1000000000000) (78049437383 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (873100264515637 / 4000000000000) 0 (IntervalRat.scale (551 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-40630025551 / 1000000000000) (-40629948101 / 1000000000000), orderedInterval (35671073065 / 1000000000000) (35671150515 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1192143767558549 / 4000000000000) 0 (IntervalRat.scale (551 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-16696484469 / 1000000000000) (-16696484468 / 1000000000000), orderedInterval (-43068160269 / 1000000000000) (-43068160268 / 1000000000000)))) (orderedInterval (2999731745 / 1000000000000) (2999733643 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (504084672747663 / 4000000000000) 0 (IntervalRat.scale (551 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (64636426730 / 1000000000000) (64636426731 / 1000000000000), orderedInterval (29303585851 / 1000000000000) (29303585852 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2049076208775023 / 4000000000000) 0 (IntervalRat.scale (551 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-29170786490 / 1000000000000) (-29170786489 / 1000000000000), orderedInterval (-19765717358 / 1000000000000) (-19765717357 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1368687944943457 / 4000000000000) 0 (IntervalRat.scale (551 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-21560209995 / 1000000000000) (-21560209994 / 1000000000000), orderedInterval (-37327349955 / 1000000000000) (-37327349954 / 1000000000000)))) (orderedInterval (6809470722 / 1000000000000) (6809470799 / 1000000000000))) = true
  rfl'

theorem compactCertificate404_chunkChecks0 :
    compactCertificate404.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate404.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate404_chunkChecks0_0
    compactCertificate404_chunkChecks0_1 compactCertificate404_chunkChecks0_2

theorem compactCertificate404_chunkChecks1_0 :
    compactCertificate404.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (551 / 2) 1 (IntervalRat.scale (551 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-8379366724 / 1000000000000) (-8379366699 / 1000000000000), orderedInterval (47349860353 / 1000000000000) (47349860378 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (811728212293451 / 4000000000000) 1 (IntervalRat.scale (551 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (26195803844 / 1000000000000) (26195806262 / 1000000000000), orderedInterval (-49571040376 / 1000000000000) (-49571037958 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (262496225847083 / 800000000000) 1 (IntervalRat.scale (551 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (36132119990 / 1000000000000) (36132224317 / 1000000000000), orderedInterval (-25247721343 / 1000000000000) (-25247617016 / 1000000000000)))) (orderedInterval (16663046411 / 1000000000000) (16663053751 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (236860267868257 / 4000000000000) 1 (IntervalRat.scale (551 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-31441771565 / 1000000000000) (-31441771564 / 1000000000000), orderedInterval (-98540926425 / 1000000000000) (-98540926424 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (636239996646829 / 4000000000000) 1 (IntervalRat.scale (551 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (23266937932 / 1000000000000) (23266938807 / 1000000000000), orderedInterval (-58903841676 / 1000000000000) (-58903840802 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1727515357201593 / 4000000000000) 1 (IntervalRat.scale (551 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29489401126 / 1000000000000) (-29489363970 / 1000000000000), orderedInterval (24619613657 / 1000000000000) (24619650812 / 1000000000000)))) (orderedInterval (-3755557122 / 1000000000000) (-3755552925 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1272479993294209 / 4000000000000) 1 (IntervalRat.scale (551 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-44709803302 / 1000000000000) (-44709803054 / 1000000000000), orderedInterval (1561863354 / 1000000000000) (1561863602 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2180416157236357 / 4000000000000) 1 (IntervalRat.scale (551 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-23242343011 / 1000000000000) (-23242336795 / 1000000000000), orderedInterval (25074866559 / 1000000000000) (25074872775 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1606084672747663 / 4000000000000) 1 (IntervalRat.scale (551 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (7222520680 / 1000000000000) (7222520681 / 1000000000000), orderedInterval (39149098059 / 1000000000000) (39149098060 / 1000000000000)))) (orderedInterval (-151313051 / 1000000000000) (-151312644 / 1000000000000))) = true
  rfl'

theorem compactCertificate404_chunkChecks1_1 :
    compactCertificate404.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2464146911204449 / 4000000000000) 1 (IntervalRat.scale (551 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (28195460775 / 1000000000000) (28195460777 / 1000000000000), orderedInterval (15418224531 / 1000000000000) (15418224533 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1422675882506521 / 4000000000000) 1 (IntervalRat.scale (551 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-42019446706 / 1000000000000) (-42019446667 / 1000000000000), orderedInterval (-4869066719 / 1000000000000) (-4869066680 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2524563319084589 / 4000000000000) 1 (IntervalRat.scale (551 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-14267516559 / 1000000000000) (-14267516558 / 1000000000000), orderedInterval (-28363319063 / 1000000000000) (-28363319062 / 1000000000000)))) (orderedInterval (-15828647917 / 1000000000000) (-15828647685 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2358774530429441 / 4000000000000) 1 (IntervalRat.scale (551 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-4604479031 / 1000000000000) (-4604479030 / 1000000000000), orderedInterval (32536599948 / 1000000000000) (32536599950 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1683332805279953 / 4000000000000) 1 (IntervalRat.scale (551 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (23379619763 / 1000000000000) (23379619764 / 1000000000000), orderedInterval (31055240224 / 1000000000000) (31055240225 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1908719989940487 / 4000000000000) 1 (IntervalRat.scale (551 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (15658478543 / 1000000000000) (15658478544 / 1000000000000), orderedInterval (32982709689 / 1000000000000) (32982709690 / 1000000000000)))) (orderedInterval (2939472417 / 1000000000000) (2939472471 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1591291733550103 / 4000000000000) 1 (IntervalRat.scale (551 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (14624147431 / 1000000000000) (14624147614 / 1000000000000), orderedInterval (-37252697019 / 1000000000000) (-37252696836 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1405954505628163 / 4000000000000) 1 (IntervalRat.scale (551 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (17170436620 / 1000000000000) (17170436621 / 1000000000000), orderedInterval (38916395293 / 1000000000000) (38916395294 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (407500415440137 / 800000000000) 1 (IntervalRat.scale (551 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (33231795045 / 1000000000000) (33231795048 / 1000000000000), orderedInterval (12027717783 / 1000000000000) (12027717787 / 1000000000000)))) (orderedInterval (-2893122541 / 1000000000000) (-2893122499 / 1000000000000))) = true
  rfl'

theorem compactCertificate404_chunkChecks1_2 :
    compactCertificate404.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1127167594679339 / 4000000000000) 1 (IntervalRat.scale (551 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-7876693942 / 1000000000000) (-7876693921 / 1000000000000), orderedInterval (46887690808 / 1000000000000) (46887690829 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (955512453048979 / 4000000000000) 1 (IntervalRat.scale (551 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (40500831232 / 1000000000000) (40500831233 / 1000000000000), orderedInterval (31926498991 / 1000000000000) (31926498992 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (597915327252337 / 4000000000000) 1 (IntervalRat.scale (551 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-33163040916 / 1000000000000) (-33163035587 / 1000000000000), orderedInterval (56317273947 / 1000000000000) (56317279276 / 1000000000000)))) (orderedInterval (-8240269171 / 1000000000000) (-8240269009 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (321560851572879 / 4000000000000) 1 (IntervalRat.scale (551 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-43236451784 / 1000000000000) (-43236445954 / 1000000000000), orderedInterval (78049431552 / 1000000000000) (78049437383 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (873100264515637 / 4000000000000) 1 (IntervalRat.scale (551 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-40630025551 / 1000000000000) (-40629948101 / 1000000000000), orderedInterval (35671073065 / 1000000000000) (35671150515 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1192143767558549 / 4000000000000) 1 (IntervalRat.scale (551 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-16696484469 / 1000000000000) (-16696484468 / 1000000000000), orderedInterval (-43068160269 / 1000000000000) (-43068160268 / 1000000000000)))) (orderedInterval (2508984960 / 1000000000000) (2508986413 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (504084672747663 / 4000000000000) 1 (IntervalRat.scale (551 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (64636426730 / 1000000000000) (64636426731 / 1000000000000), orderedInterval (29303585851 / 1000000000000) (29303585852 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2049076208775023 / 4000000000000) 1 (IntervalRat.scale (551 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-29170786490 / 1000000000000) (-29170786489 / 1000000000000), orderedInterval (-19765717358 / 1000000000000) (-19765717357 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1368687944943457 / 4000000000000) 1 (IntervalRat.scale (551 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-21560209995 / 1000000000000) (-21560209994 / 1000000000000), orderedInterval (-37327349955 / 1000000000000) (-37327349954 / 1000000000000)))) (orderedInterval (11771036784 / 1000000000000) (11771036892 / 1000000000000))) = true
  rfl'

theorem compactCertificate404_chunkChecks1 :
    compactCertificate404.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate404.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate404_chunkChecks1_0
    compactCertificate404_chunkChecks1_1 compactCertificate404_chunkChecks1_2

theorem compactCertificate404_chunkChecks2_0 :
    compactCertificate404.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (551 / 2) 2 (IntervalRat.scale (551 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-8379366724 / 1000000000000) (-8379366699 / 1000000000000), orderedInterval (47349860353 / 1000000000000) (47349860378 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (811728212293451 / 4000000000000) 2 (IntervalRat.scale (551 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (26195803844 / 1000000000000) (26195806262 / 1000000000000), orderedInterval (-49571040376 / 1000000000000) (-49571037958 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (262496225847083 / 800000000000) 2 (IntervalRat.scale (551 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (36132119990 / 1000000000000) (36132224317 / 1000000000000), orderedInterval (-25247721343 / 1000000000000) (-25247617016 / 1000000000000)))) (orderedInterval (120792753 / 1000000000000) (120801511 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (236860267868257 / 4000000000000) 2 (IntervalRat.scale (551 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-31441771565 / 1000000000000) (-31441771564 / 1000000000000), orderedInterval (-98540926425 / 1000000000000) (-98540926424 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (636239996646829 / 4000000000000) 2 (IntervalRat.scale (551 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (23266937932 / 1000000000000) (23266938807 / 1000000000000), orderedInterval (-58903841676 / 1000000000000) (-58903840802 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1727515357201593 / 4000000000000) 2 (IntervalRat.scale (551 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29489401126 / 1000000000000) (-29489363970 / 1000000000000), orderedInterval (24619613657 / 1000000000000) (24619650812 / 1000000000000)))) (orderedInterval (-5437027399 / 1000000000000) (-5437020830 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1272479993294209 / 4000000000000) 2 (IntervalRat.scale (551 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-44709803302 / 1000000000000) (-44709803054 / 1000000000000), orderedInterval (1561863354 / 1000000000000) (1561863602 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2180416157236357 / 4000000000000) 2 (IntervalRat.scale (551 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-23242343011 / 1000000000000) (-23242336795 / 1000000000000), orderedInterval (25074866559 / 1000000000000) (25074872775 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1606084672747663 / 4000000000000) 2 (IntervalRat.scale (551 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (7222520680 / 1000000000000) (7222520681 / 1000000000000), orderedInterval (39149098059 / 1000000000000) (39149098060 / 1000000000000)))) (orderedInterval (-3176727530 / 1000000000000) (-3176726729 / 1000000000000))) = true
  rfl'

theorem compactCertificate404_chunkChecks2_1 :
    compactCertificate404.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2464146911204449 / 4000000000000) 2 (IntervalRat.scale (551 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (28195460775 / 1000000000000) (28195460777 / 1000000000000), orderedInterval (15418224531 / 1000000000000) (15418224533 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1422675882506521 / 4000000000000) 2 (IntervalRat.scale (551 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-42019446706 / 1000000000000) (-42019446667 / 1000000000000), orderedInterval (-4869066719 / 1000000000000) (-4869066680 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2524563319084589 / 4000000000000) 2 (IntervalRat.scale (551 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-14267516559 / 1000000000000) (-14267516558 / 1000000000000), orderedInterval (-28363319063 / 1000000000000) (-28363319062 / 1000000000000)))) (orderedInterval (40940678686 / 1000000000000) (40940679178 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2358774530429441 / 4000000000000) 2 (IntervalRat.scale (551 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-4604479031 / 1000000000000) (-4604479030 / 1000000000000), orderedInterval (32536599948 / 1000000000000) (32536599950 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1683332805279953 / 4000000000000) 2 (IntervalRat.scale (551 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (23379619763 / 1000000000000) (23379619764 / 1000000000000), orderedInterval (31055240224 / 1000000000000) (31055240225 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1908719989940487 / 4000000000000) 2 (IntervalRat.scale (551 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (15658478543 / 1000000000000) (15658478544 / 1000000000000), orderedInterval (32982709689 / 1000000000000) (32982709690 / 1000000000000)))) (orderedInterval (-5312421705 / 1000000000000) (-5312421616 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1591291733550103 / 4000000000000) 2 (IntervalRat.scale (551 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (14624147431 / 1000000000000) (14624147614 / 1000000000000), orderedInterval (-37252697019 / 1000000000000) (-37252696836 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1405954505628163 / 4000000000000) 2 (IntervalRat.scale (551 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (17170436620 / 1000000000000) (17170436621 / 1000000000000), orderedInterval (38916395293 / 1000000000000) (38916395294 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (407500415440137 / 800000000000) 2 (IntervalRat.scale (551 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (33231795045 / 1000000000000) (33231795048 / 1000000000000), orderedInterval (12027717783 / 1000000000000) (12027717787 / 1000000000000)))) (orderedInterval (-1650884485 / 1000000000000) (-1650884423 / 1000000000000))) = true
  rfl'

theorem compactCertificate404_chunkChecks2_2 :
    compactCertificate404.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1127167594679339 / 4000000000000) 2 (IntervalRat.scale (551 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-7876693942 / 1000000000000) (-7876693921 / 1000000000000), orderedInterval (46887690808 / 1000000000000) (46887690829 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (955512453048979 / 4000000000000) 2 (IntervalRat.scale (551 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (40500831232 / 1000000000000) (40500831233 / 1000000000000), orderedInterval (31926498991 / 1000000000000) (31926498992 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (597915327252337 / 4000000000000) 2 (IntervalRat.scale (551 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-33163040916 / 1000000000000) (-33163035587 / 1000000000000), orderedInterval (56317273947 / 1000000000000) (56317279276 / 1000000000000)))) (orderedInterval (753545205 / 1000000000000) (753545321 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (321560851572879 / 4000000000000) 2 (IntervalRat.scale (551 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-43236451784 / 1000000000000) (-43236445954 / 1000000000000), orderedInterval (78049431552 / 1000000000000) (78049437383 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (873100264515637 / 4000000000000) 2 (IntervalRat.scale (551 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-40630025551 / 1000000000000) (-40629948101 / 1000000000000), orderedInterval (35671073065 / 1000000000000) (35671150515 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1192143767558549 / 4000000000000) 2 (IntervalRat.scale (551 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-16696484469 / 1000000000000) (-16696484468 / 1000000000000), orderedInterval (-43068160269 / 1000000000000) (-43068160268 / 1000000000000)))) (orderedInterval (-2153200152 / 1000000000000) (-2153199004 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (504084672747663 / 4000000000000) 2 (IntervalRat.scale (551 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (64636426730 / 1000000000000) (64636426731 / 1000000000000), orderedInterval (29303585851 / 1000000000000) (29303585852 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2049076208775023 / 4000000000000) 2 (IntervalRat.scale (551 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-29170786490 / 1000000000000) (-29170786489 / 1000000000000), orderedInterval (-19765717358 / 1000000000000) (-19765717357 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1368687944943457 / 4000000000000) 2 (IntervalRat.scale (551 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-21560209995 / 1000000000000) (-21560209994 / 1000000000000), orderedInterval (-37327349955 / 1000000000000) (-37327349954 / 1000000000000)))) (orderedInterval (-14574222860 / 1000000000000) (-14574222700 / 1000000000000))) = true
  rfl'

theorem compactCertificate404_chunkChecks2 :
    compactCertificate404.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate404.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate404_chunkChecks2_0
    compactCertificate404_chunkChecks2_1 compactCertificate404_chunkChecks2_2

theorem compactCertificate404_chunkChecks3_0 :
    compactCertificate404.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (551 / 2) 3 (IntervalRat.scale (551 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-8379366724 / 1000000000000) (-8379366699 / 1000000000000), orderedInterval (47349860353 / 1000000000000) (47349860378 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (811728212293451 / 4000000000000) 3 (IntervalRat.scale (551 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (26195803844 / 1000000000000) (26195806262 / 1000000000000), orderedInterval (-49571040376 / 1000000000000) (-49571037958 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (262496225847083 / 800000000000) 3 (IntervalRat.scale (551 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (36132119990 / 1000000000000) (36132224317 / 1000000000000), orderedInterval (-25247721343 / 1000000000000) (-25247617016 / 1000000000000)))) (orderedInterval (-16080485415 / 1000000000000) (-16080474992 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (236860267868257 / 4000000000000) 3 (IntervalRat.scale (551 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-31441771565 / 1000000000000) (-31441771564 / 1000000000000), orderedInterval (-98540926425 / 1000000000000) (-98540926424 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (636239996646829 / 4000000000000) 3 (IntervalRat.scale (551 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (23266937932 / 1000000000000) (23266938807 / 1000000000000), orderedInterval (-58903841676 / 1000000000000) (-58903840802 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1727515357201593 / 4000000000000) 3 (IntervalRat.scale (551 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29489401126 / 1000000000000) (-29489363970 / 1000000000000), orderedInterval (24619613657 / 1000000000000) (24619650812 / 1000000000000)))) (orderedInterval (7165275781 / 1000000000000) (7165286064 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1272479993294209 / 4000000000000) 3 (IntervalRat.scale (551 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-44709803302 / 1000000000000) (-44709803054 / 1000000000000), orderedInterval (1561863354 / 1000000000000) (1561863602 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2180416157236357 / 4000000000000) 3 (IntervalRat.scale (551 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-23242343011 / 1000000000000) (-23242336795 / 1000000000000), orderedInterval (25074866559 / 1000000000000) (25074872775 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1606084672747663 / 4000000000000) 3 (IntervalRat.scale (551 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (7222520680 / 1000000000000) (7222520681 / 1000000000000), orderedInterval (39149098059 / 1000000000000) (39149098060 / 1000000000000)))) (orderedInterval (3073272130 / 1000000000000) (3073273705 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate404_chunkChecks3_1 :
    compactCertificate404.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2464146911204449 / 4000000000000) 3 (IntervalRat.scale (551 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (28195460775 / 1000000000000) (28195460777 / 1000000000000), orderedInterval (15418224531 / 1000000000000) (15418224533 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1422675882506521 / 4000000000000) 3 (IntervalRat.scale (551 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-42019446706 / 1000000000000) (-42019446667 / 1000000000000), orderedInterval (-4869066719 / 1000000000000) (-4869066680 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2524563319084589 / 4000000000000) 3 (IntervalRat.scale (551 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-14267516559 / 1000000000000) (-14267516558 / 1000000000000), orderedInterval (-28363319063 / 1000000000000) (-28363319062 / 1000000000000)))) (orderedInterval (79734456035 / 1000000000000) (79734457110 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2358774530429441 / 4000000000000) 3 (IntervalRat.scale (551 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-4604479031 / 1000000000000) (-4604479030 / 1000000000000), orderedInterval (32536599948 / 1000000000000) (32536599950 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1683332805279953 / 4000000000000) 3 (IntervalRat.scale (551 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (23379619763 / 1000000000000) (23379619764 / 1000000000000), orderedInterval (31055240224 / 1000000000000) (31055240225 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1908719989940487 / 4000000000000) 3 (IntervalRat.scale (551 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (15658478543 / 1000000000000) (15658478544 / 1000000000000), orderedInterval (32982709689 / 1000000000000) (32982709690 / 1000000000000)))) (orderedInterval (-3820136623 / 1000000000000) (-3820136472 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1591291733550103 / 4000000000000) 3 (IntervalRat.scale (551 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (14624147431 / 1000000000000) (14624147614 / 1000000000000), orderedInterval (-37252697019 / 1000000000000) (-37252696836 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1405954505628163 / 4000000000000) 3 (IntervalRat.scale (551 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (17170436620 / 1000000000000) (17170436621 / 1000000000000), orderedInterval (38916395293 / 1000000000000) (38916395294 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (407500415440137 / 800000000000) 3 (IntervalRat.scale (551 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (33231795045 / 1000000000000) (33231795048 / 1000000000000), orderedInterval (12027717783 / 1000000000000) (12027717787 / 1000000000000)))) (orderedInterval (3979656495 / 1000000000000) (3979656590 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate404_chunkChecks3_2 :
    compactCertificate404.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1127167594679339 / 4000000000000) 3 (IntervalRat.scale (551 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-7876693942 / 1000000000000) (-7876693921 / 1000000000000), orderedInterval (46887690808 / 1000000000000) (46887690829 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (955512453048979 / 4000000000000) 3 (IntervalRat.scale (551 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (40500831232 / 1000000000000) (40500831233 / 1000000000000), orderedInterval (31926498991 / 1000000000000) (31926498992 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (597915327252337 / 4000000000000) 3 (IntervalRat.scale (551 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-33163040916 / 1000000000000) (-33163035587 / 1000000000000), orderedInterval (56317273947 / 1000000000000) (56317279276 / 1000000000000)))) (orderedInterval (8904733139 / 1000000000000) (8904733231 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (321560851572879 / 4000000000000) 3 (IntervalRat.scale (551 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-43236451784 / 1000000000000) (-43236445954 / 1000000000000), orderedInterval (78049431552 / 1000000000000) (78049437383 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (873100264515637 / 4000000000000) 3 (IntervalRat.scale (551 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-40630025551 / 1000000000000) (-40629948101 / 1000000000000), orderedInterval (35671073065 / 1000000000000) (35671150515 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1192143767558549 / 4000000000000) 3 (IntervalRat.scale (551 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-16696484469 / 1000000000000) (-16696484468 / 1000000000000), orderedInterval (-43068160269 / 1000000000000) (-43068160268 / 1000000000000)))) (orderedInterval (-3732621475 / 1000000000000) (-3732620563 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (504084672747663 / 4000000000000) 3 (IntervalRat.scale (551 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (64636426730 / 1000000000000) (64636426731 / 1000000000000), orderedInterval (29303585851 / 1000000000000) (29303585852 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2049076208775023 / 4000000000000) 3 (IntervalRat.scale (551 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-29170786490 / 1000000000000) (-29170786489 / 1000000000000), orderedInterval (-19765717358 / 1000000000000) (-19765717357 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1368687944943457 / 4000000000000) 3 (IntervalRat.scale (551 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-21560209995 / 1000000000000) (-21560209994 / 1000000000000), orderedInterval (-37327349955 / 1000000000000) (-37327349954 / 1000000000000)))) (orderedInterval (-23725620601 / 1000000000000) (-23725620356 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate404_chunkChecks3 :
    compactCertificate404.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate404.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate404_chunkChecks3_0
    compactCertificate404_chunkChecks3_1 compactCertificate404_chunkChecks3_2

theorem compactCertificate404_chunkChecks4_0 :
    compactCertificate404.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (551 / 2) 4 (IntervalRat.scale (551 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-8379366724 / 1000000000000) (-8379366699 / 1000000000000), orderedInterval (47349860353 / 1000000000000) (47349860378 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (811728212293451 / 4000000000000) 4 (IntervalRat.scale (551 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (26195803844 / 1000000000000) (26195806262 / 1000000000000), orderedInterval (-49571040376 / 1000000000000) (-49571037958 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (262496225847083 / 800000000000) 4 (IntervalRat.scale (551 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (36132119990 / 1000000000000) (36132224317 / 1000000000000), orderedInterval (-25247721343 / 1000000000000) (-25247617016 / 1000000000000)))) (orderedInterval (1133474793 / 1000000000000) (1133487237 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (236860267868257 / 4000000000000) 4 (IntervalRat.scale (551 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-31441771565 / 1000000000000) (-31441771564 / 1000000000000), orderedInterval (-98540926425 / 1000000000000) (-98540926424 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (636239996646829 / 4000000000000) 4 (IntervalRat.scale (551 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (23266937932 / 1000000000000) (23266938807 / 1000000000000), orderedInterval (-58903841676 / 1000000000000) (-58903840802 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1727515357201593 / 4000000000000) 4 (IntervalRat.scale (551 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29489401126 / 1000000000000) (-29489363970 / 1000000000000), orderedInterval (24619613657 / 1000000000000) (24619650812 / 1000000000000)))) (orderedInterval (12703010546 / 1000000000000) (12703026695 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1272479993294209 / 4000000000000) 4 (IntervalRat.scale (551 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-44709803302 / 1000000000000) (-44709803054 / 1000000000000), orderedInterval (1561863354 / 1000000000000) (1561863602 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2180416157236357 / 4000000000000) 4 (IntervalRat.scale (551 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-23242343011 / 1000000000000) (-23242336795 / 1000000000000), orderedInterval (25074866559 / 1000000000000) (25074872775 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1606084672747663 / 4000000000000) 4 (IntervalRat.scale (551 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (7222520680 / 1000000000000) (7222520681 / 1000000000000), orderedInterval (39149098059 / 1000000000000) (39149098060 / 1000000000000)))) (orderedInterval (11752260977 / 1000000000000) (11752264088 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate404_chunkChecks4_1 :
    compactCertificate404.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2464146911204449 / 4000000000000) 4 (IntervalRat.scale (551 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (28195460775 / 1000000000000) (28195460777 / 1000000000000), orderedInterval (15418224531 / 1000000000000) (15418224533 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1422675882506521 / 4000000000000) 4 (IntervalRat.scale (551 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-42019446706 / 1000000000000) (-42019446667 / 1000000000000), orderedInterval (-4869066719 / 1000000000000) (-4869066680 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2524563319084589 / 4000000000000) 4 (IntervalRat.scale (551 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-14267516559 / 1000000000000) (-14267516558 / 1000000000000), orderedInterval (-28363319063 / 1000000000000) (-28363319062 / 1000000000000)))) (orderedInterval (-190340150498 / 1000000000000) (-190340148117 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2358774530429441 / 4000000000000) 4 (IntervalRat.scale (551 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-4604479031 / 1000000000000) (-4604479030 / 1000000000000), orderedInterval (32536599948 / 1000000000000) (32536599950 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1683332805279953 / 4000000000000) 4 (IntervalRat.scale (551 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (23379619763 / 1000000000000) (23379619764 / 1000000000000), orderedInterval (31055240224 / 1000000000000) (31055240225 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1908719989940487 / 4000000000000) 4 (IntervalRat.scale (551 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (15658478543 / 1000000000000) (15658478544 / 1000000000000), orderedInterval (32982709689 / 1000000000000) (32982709690 / 1000000000000)))) (orderedInterval (13096133014 / 1000000000000) (13096133275 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1591291733550103 / 4000000000000) 4 (IntervalRat.scale (551 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (14624147431 / 1000000000000) (14624147614 / 1000000000000), orderedInterval (-37252697019 / 1000000000000) (-37252696836 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1405954505628163 / 4000000000000) 4 (IntervalRat.scale (551 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (17170436620 / 1000000000000) (17170436621 / 1000000000000), orderedInterval (38916395293 / 1000000000000) (38916395294 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (407500415440137 / 800000000000) 4 (IntervalRat.scale (551 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (33231795045 / 1000000000000) (33231795048 / 1000000000000), orderedInterval (12027717783 / 1000000000000) (12027717787 / 1000000000000)))) (orderedInterval (8045151962 / 1000000000000) (8045152112 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate404_chunkChecks4_2 :
    compactCertificate404.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1127167594679339 / 4000000000000) 4 (IntervalRat.scale (551 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-7876693942 / 1000000000000) (-7876693921 / 1000000000000), orderedInterval (46887690808 / 1000000000000) (46887690829 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (955512453048979 / 4000000000000) 4 (IntervalRat.scale (551 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (40500831232 / 1000000000000) (40500831233 / 1000000000000), orderedInterval (31926498991 / 1000000000000) (31926498992 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (597915327252337 / 4000000000000) 4 (IntervalRat.scale (551 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-33163040916 / 1000000000000) (-33163035587 / 1000000000000), orderedInterval (56317273947 / 1000000000000) (56317279276 / 1000000000000)))) (orderedInterval (-75404654 / 1000000000000) (-75404577 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (321560851572879 / 4000000000000) 4 (IntervalRat.scale (551 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-43236451784 / 1000000000000) (-43236445954 / 1000000000000), orderedInterval (78049431552 / 1000000000000) (78049437383 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (873100264515637 / 4000000000000) 4 (IntervalRat.scale (551 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-40630025551 / 1000000000000) (-40629948101 / 1000000000000), orderedInterval (35671073065 / 1000000000000) (35671150515 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1192143767558549 / 4000000000000) 4 (IntervalRat.scale (551 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-16696484469 / 1000000000000) (-16696484468 / 1000000000000), orderedInterval (-43068160269 / 1000000000000) (-43068160268 / 1000000000000)))) (orderedInterval (2148577879 / 1000000000000) (2148578611 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (504084672747663 / 4000000000000) 4 (IntervalRat.scale (551 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (64636426730 / 1000000000000) (64636426731 / 1000000000000), orderedInterval (29303585851 / 1000000000000) (29303585852 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2049076208775023 / 4000000000000) 4 (IntervalRat.scale (551 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-29170786490 / 1000000000000) (-29170786489 / 1000000000000), orderedInterval (-19765717358 / 1000000000000) (-19765717357 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1368687944943457 / 4000000000000) 4 (IntervalRat.scale (551 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-21560209995 / 1000000000000) (-21560209994 / 1000000000000), orderedInterval (-37327349955 / 1000000000000) (-37327349954 / 1000000000000)))) (orderedInterval (38199889999 / 1000000000000) (38199890393 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate404_chunkChecks4 :
    compactCertificate404.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate404.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate404_chunkChecks4_0
    compactCertificate404_chunkChecks4_1 compactCertificate404_chunkChecks4_2

theorem compactCertificate404_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate404.chunkCheck r b = true :=
  compactCertificate404.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate404_chunkChecks0
    · exact compactCertificate404_chunkChecks1
    · exact compactCertificate404_chunkChecks2
    · exact compactCertificate404_chunkChecks3
    · exact compactCertificate404_chunkChecks4)

theorem compactCertificate404_coefficient0 :
    compactCertificate404.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate404_coefficient1 :
    compactCertificate404.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate404_coefficient2 :
    compactCertificate404.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate404_coefficient3 :
    compactCertificate404.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate404_coefficient4 :
    compactCertificate404.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate404_coefficients : ∀ r : Fin 5,
    compactCertificate404.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate404_coefficient0
  · exact compactCertificate404_coefficient1
  · exact compactCertificate404_coefficient2
  · exact compactCertificate404_coefficient3
  · exact compactCertificate404_coefficient4

theorem compactCertificate404_lower : (1 : ℚ) ≤ compactCertificate404.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate404, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate404_proves {t : ℝ} (ht : t ∈ compactCertificate404.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate404.proves compactCertificate404_states compactCertificate404_chunks
    compactCertificate404_coefficients compactCertificate404_lower ht

end Erdos232
