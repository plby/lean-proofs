/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate551 : CompactCertificate where
  left := 422
  right := 423
  center := 845 / 2
  grid := fun i =>
    match i.val with
    | 0 => 135
    | 1 => 99
    | 2 => 160
    | 3 => 29
    | 4 => 78
    | 5 => 211
    | 6 => 155
    | 7 => 266
    | 8 => 196
    | 9 => 301
    | 10 => 174
    | 11 => 308
    | 12 => 288
    | 13 => 206
    | 14 => 233
    | 15 => 194
    | 16 => 172
    | 17 => 249
    | 18 => 138
    | 19 => 117
    | 20 => 73
    | 21 => 39
    | 22 => 107
    | 23 => 146
    | 24 => 62
    | 25 => 250
    | _ => 167
  point := fun i =>
    match i.val with
    | 0 => 845 / 2
    | 1 => 248969270195269 / 800000000000
    | 2 => 80511546584677 / 160000000000
    | 3 => 72648612104783 / 800000000000
    | 4 => 195144390986051 / 800000000000
    | 5 => 529854982517367 / 800000000000
    | 6 => 390288781972271 / 800000000000
    | 7 => 668766480168683 / 800000000000
    | 8 => 492610362421697 / 800000000000
    | 9 => 755790976394831 / 800000000000
    | 10 => 436356123672599 / 800000000000
    | 11 => 774321598775491 / 800000000000
    | 12 => 723471679932079 / 800000000000
    | 13 => 516303528298207 / 800000000000
    | 14 => 585433172958153 / 800000000000
    | 15 => 488073145136057 / 800000000000
    | 16 => 431227425501197 / 800000000000
    | 17 => 124986515806503 / 160000000000
    | 18 => 345719280400741 / 800000000000
    | 19 => 293070062731901 / 800000000000
    | 20 => 183389637578303 / 800000000000
    | 21 => 98627557016001 / 800000000000
    | 22 => 267793003091003 / 800000000000
    | 23 => 365648451392731 / 800000000000
    | 24 => 154610362421697 / 800000000000
    | 25 => 628482539533537 / 800000000000
    | _ => 419797209973583 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (28642106758 / 1000000000000) (28642132252 / 1000000000000), orderedInterval (-26233550302 / 1000000000000) (-26233524809 / 1000000000000))
    | 1 => (orderedInterval (-37534681930 / 1000000000000) (-37534681929 / 1000000000000), orderedInterval (-25173876070 / 1000000000000) (-25173876069 / 1000000000000))
    | 2 => (orderedInterval (34521325410 / 1000000000000) (34521325428 / 1000000000000), orderedInterval (8534670906 / 1000000000000) (8534670924 / 1000000000000))
    | 3 => (orderedInterval (-39300858310 / 1000000000000) (-39300858309 / 1000000000000), orderedInterval (-73715355172 / 1000000000000) (-73715355171 / 1000000000000))
    | 4 => (orderedInterval (-16498771428 / 1000000000000) (-16498771147 / 1000000000000), orderedInterval (48382921810 / 1000000000000) (48382922091 / 1000000000000))
    | 5 => (orderedInterval (-7004252022 / 1000000000000) (-7004252021 / 1000000000000), orderedInterval (-30196354770 / 1000000000000) (-30196354769 / 1000000000000))
    | 6 => (orderedInterval (-35826019966 / 1000000000000) (-35826017729 / 1000000000000), orderedInterval (4664477159 / 1000000000000) (4664479396 / 1000000000000))
    | 7 => (orderedInterval (24334734826 / 1000000000000) (24334734832 / 1000000000000), orderedInterval (12999501947 / 1000000000000) (12999501953 / 1000000000000))
    | 8 => (orderedInterval (22975712858 / 1000000000000) (22975712859 / 1000000000000), orderedInterval (22475523378 / 1000000000000) (22475523379 / 1000000000000))
    | 9 => (orderedInterval (2472773907 / 1000000000000) (2472773908 / 1000000000000), orderedInterval (-25842042272 / 1000000000000) (-25842042271 / 1000000000000))
    | 10 => (orderedInterval (-13517563754 / 1000000000000) (-13517563652 / 1000000000000), orderedInterval (31388053031 / 1000000000000) (31388053133 / 1000000000000))
    | 11 => (orderedInterval (22579288946 / 1000000000000) (22579288960 / 1000000000000), orderedInterval (12150050713 / 1000000000000) (12150050727 / 1000000000000))
    | 12 => (orderedInterval (9002470110 / 1000000000000) (9002470111 / 1000000000000), orderedInterval (24953319328 / 1000000000000) (24953319329 / 1000000000000))
    | 13 => (orderedInterval (-26487220261 / 1000000000000) (-26487176040 / 1000000000000), orderedInterval (16898155834 / 1000000000000) (16898200055 / 1000000000000))
    | 14 => (orderedInterval (-16301924048 / 1000000000000) (-16301924047 / 1000000000000), orderedInterval (-24569226290 / 1000000000000) (-24569226289 / 1000000000000))
    | 15 => (orderedInterval (31874027755 / 1000000000000) (31874027884 / 1000000000000), orderedInterval (5220646579 / 1000000000000) (5220646708 / 1000000000000))
    | 16 => (orderedInterval (-17506178886 / 1000000000000) (-17506178311 / 1000000000000), orderedInterval (29589394703 / 1000000000000) (29589395278 / 1000000000000))
    | 17 => (orderedInterval (8589202449 / 1000000000000) (8589202453 / 1000000000000), orderedInterval (-27230246705 / 1000000000000) (-27230246701 / 1000000000000))
    | 18 => (orderedInterval (-21848206221 / 1000000000000) (-21848203722 / 1000000000000), orderedInterval (31581650969 / 1000000000000) (31581653467 / 1000000000000))
    | 19 => (orderedInterval (17895696624 / 1000000000000) (17895697176 / 1000000000000), orderedInterval (-37674664302 / 1000000000000) (-37674663750 / 1000000000000))
    | 20 => (orderedInterval (-33366788000 / 1000000000000) (-33366787999 / 1000000000000), orderedInterval (-40716719395 / 1000000000000) (-40716719394 / 1000000000000))
    | 21 => (orderedInterval (-71838658686 / 1000000000000) (-71838658659 / 1000000000000), orderedInterval (-1438822174 / 1000000000000) (-1438822147 / 1000000000000))
    | 22 => (orderedInterval (25485447731 / 1000000000000) (25485452926 / 1000000000000), orderedInterval (-35426188535 / 1000000000000) (-35426183340 / 1000000000000))
    | 23 => (orderedInterval (-27460567029 / 1000000000000) (-27460545996 / 1000000000000), orderedInterval (25304013046 / 1000000000000) (25304034078 / 1000000000000))
    | 24 => (orderedInterval (-38318664153 / 1000000000000) (-38318634316 / 1000000000000), orderedInterval (42827825920 / 1000000000000) (42827855757 / 1000000000000))
    | 25 => (orderedInterval (23802875968 / 1000000000000) (23802875970 / 1000000000000), orderedInterval (15598337477 / 1000000000000) (15598337478 / 1000000000000))
    | _ => (orderedInterval (-26971603673 / 1000000000000) (-26971603672 / 1000000000000), orderedInterval (-22013523291 / 1000000000000) (-22013523290 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (13028728741 / 1000000000000) (13028738877 / 1000000000000)
      | 1 => orderedInterval (321917233 / 1000000000000) (321917294 / 1000000000000)
      | 2 => orderedInterval (-195302949 / 1000000000000) (-195302924 / 1000000000000)
      | 3 => orderedInterval (1768856572 / 1000000000000) (1768856749 / 1000000000000)
      | 4 => orderedInterval (-2584732727 / 1000000000000) (-2584728495 / 1000000000000)
      | 5 => orderedInterval (1589808655 / 1000000000000) (1589808731 / 1000000000000)
      | 6 => orderedInterval (1394202095 / 1000000000000) (1394202632 / 1000000000000)
      | 7 => orderedInterval (2852869473 / 1000000000000) (2852871254 / 1000000000000)
      | _ => orderedInterval (2891994388 / 1000000000000) (2891994686 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-9974364194 / 1000000000000) (-9974354055 / 1000000000000)
      | 1 => orderedInterval (4556937527 / 1000000000000) (4556937591 / 1000000000000)
      | 2 => orderedInterval (-1674017 / 1000000000000) (-1673975 / 1000000000000)
      | 3 => orderedInterval (17226783265 / 1000000000000) (17226783626 / 1000000000000)
      | 4 => orderedInterval (1692005388 / 1000000000000) (1692011857 / 1000000000000)
      | 5 => orderedInterval (-3362362847 / 1000000000000) (-3362362744 / 1000000000000)
      | 6 => orderedInterval (-4035267746 / 1000000000000) (-4035267212 / 1000000000000)
      | 7 => orderedInterval (-1453384779 / 1000000000000) (-1453382896 / 1000000000000)
      | _ => orderedInterval (2887011440 / 1000000000000) (2887011687 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-14012850643 / 1000000000000) (-14012840474 / 1000000000000)
      | 1 => orderedInterval (-1053310252 / 1000000000000) (-1053310168 / 1000000000000)
      | 2 => orderedInterval (1758955697 / 1000000000000) (1758955772 / 1000000000000)
      | 3 => orderedInterval (-13020151758 / 1000000000000) (-13020150991 / 1000000000000)
      | 4 => orderedInterval (6337411063 / 1000000000000) (6337420971 / 1000000000000)
      | 5 => orderedInterval (-3141988238 / 1000000000000) (-3141988093 / 1000000000000)
      | 6 => orderedInterval (-2563909834 / 1000000000000) (-2563909298 / 1000000000000)
      | 7 => orderedInterval (-2209502721 / 1000000000000) (-2209500710 / 1000000000000)
      | _ => orderedInterval (-1065727559 / 1000000000000) (-1065727277 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (9678813423 / 1000000000000) (9678823598 / 1000000000000)
      | 1 => orderedInterval (-8614943181 / 1000000000000) (-8614943059 / 1000000000000)
      | 2 => orderedInterval (1420060808 / 1000000000000) (1420060943 / 1000000000000)
      | 3 => orderedInterval (-77077267457 / 1000000000000) (-77077265785 / 1000000000000)
      | 4 => orderedInterval (-1938797360 / 1000000000000) (-1938782203 / 1000000000000)
      | 5 => orderedInterval (7748985395 / 1000000000000) (7748985603 / 1000000000000)
      | 6 => orderedInterval (4231324454 / 1000000000000) (4231324994 / 1000000000000)
      | 7 => orderedInterval (2060008949 / 1000000000000) (2060011100 / 1000000000000)
      | _ => orderedInterval (227472599 / 1000000000000) (227472991 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (15279850357 / 1000000000000) (15279860564 / 1000000000000)
      | 1 => orderedInterval (2981723468 / 1000000000000) (2981723654 / 1000000000000)
      | 2 => orderedInterval (-9004885740 / 1000000000000) (-9004885490 / 1000000000000)
      | 3 => orderedInterval (75006638619 / 1000000000000) (75006642319 / 1000000000000)
      | 4 => orderedInterval (-16296452240 / 1000000000000) (-16296429005 / 1000000000000)
      | 5 => orderedInterval (6787858019 / 1000000000000) (6787858327 / 1000000000000)
      | 6 => orderedInterval (3136895757 / 1000000000000) (3136896304 / 1000000000000)
      | 7 => orderedInterval (2654378369 / 1000000000000) (2654380682 / 1000000000000)
      | _ => orderedInterval (-11131013144 / 1000000000000) (-11131012533 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (21068341481 / 1000000000000) (21068358804 / 1000000000000)
    | 1 => orderedInterval (7535684037 / 1000000000000) (7535703879 / 1000000000000)
    | 2 => orderedInterval (-28971074245 / 1000000000000) (-28971050268 / 1000000000000)
    | 3 => orderedInterval (-62264342370 / 1000000000000) (-62264311818 / 1000000000000)
    | _ => orderedInterval (69414993465 / 1000000000000) (69415034822 / 1000000000000)

theorem compactCertificate551_stateChecks0 :
    compactCertificate551.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 135 12 (845 / 2)) (orderedInterval (28642106758 / 1000000000000) (28642132252 / 1000000000000), orderedInterval (-26233550302 / 1000000000000) (-26233524809 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 99 12 (248969270195269 / 800000000000)) (orderedInterval (-37534681930 / 1000000000000) (-37534681929 / 1000000000000), orderedInterval (-25173876070 / 1000000000000) (-25173876069 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 160 12 (80511546584677 / 160000000000)) (orderedInterval (34521325410 / 1000000000000) (34521325428 / 1000000000000), orderedInterval (8534670906 / 1000000000000) (8534670924 / 1000000000000))) = true
  rfl'

theorem compactCertificate551_stateChecks1 :
    compactCertificate551.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (72648612104783 / 800000000000)) (orderedInterval (-39300858310 / 1000000000000) (-39300858309 / 1000000000000), orderedInterval (-73715355172 / 1000000000000) (-73715355171 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (195144390986051 / 800000000000)) (orderedInterval (-16498771428 / 1000000000000) (-16498771147 / 1000000000000), orderedInterval (48382921810 / 1000000000000) (48382922091 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 211 12 (529854982517367 / 800000000000)) (orderedInterval (-7004252022 / 1000000000000) (-7004252021 / 1000000000000), orderedInterval (-30196354770 / 1000000000000) (-30196354769 / 1000000000000))) = true
  rfl'

theorem compactCertificate551_stateChecks2 :
    compactCertificate551.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 155 12 (390288781972271 / 800000000000)) (orderedInterval (-35826019966 / 1000000000000) (-35826017729 / 1000000000000), orderedInterval (4664477159 / 1000000000000) (4664479396 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 266 12 (668766480168683 / 800000000000)) (orderedInterval (24334734826 / 1000000000000) (24334734832 / 1000000000000), orderedInterval (12999501947 / 1000000000000) (12999501953 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 196 12 (492610362421697 / 800000000000)) (orderedInterval (22975712858 / 1000000000000) (22975712859 / 1000000000000), orderedInterval (22475523378 / 1000000000000) (22475523379 / 1000000000000))) = true
  rfl'

theorem compactCertificate551_stateChecks3 :
    compactCertificate551.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 301 12 (755790976394831 / 800000000000)) (orderedInterval (2472773907 / 1000000000000) (2472773908 / 1000000000000), orderedInterval (-25842042272 / 1000000000000) (-25842042271 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 174 12 (436356123672599 / 800000000000)) (orderedInterval (-13517563754 / 1000000000000) (-13517563652 / 1000000000000), orderedInterval (31388053031 / 1000000000000) (31388053133 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 308 12 (774321598775491 / 800000000000)) (orderedInterval (22579288946 / 1000000000000) (22579288960 / 1000000000000), orderedInterval (12150050713 / 1000000000000) (12150050727 / 1000000000000))) = true
  rfl'

theorem compactCertificate551_stateChecks4 :
    compactCertificate551.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 288 12 (723471679932079 / 800000000000)) (orderedInterval (9002470110 / 1000000000000) (9002470111 / 1000000000000), orderedInterval (24953319328 / 1000000000000) (24953319329 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 206 12 (516303528298207 / 800000000000)) (orderedInterval (-26487220261 / 1000000000000) (-26487176040 / 1000000000000), orderedInterval (16898155834 / 1000000000000) (16898200055 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 233 12 (585433172958153 / 800000000000)) (orderedInterval (-16301924048 / 1000000000000) (-16301924047 / 1000000000000), orderedInterval (-24569226290 / 1000000000000) (-24569226289 / 1000000000000))) = true
  rfl'

theorem compactCertificate551_stateChecks5 :
    compactCertificate551.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 194 12 (488073145136057 / 800000000000)) (orderedInterval (31874027755 / 1000000000000) (31874027884 / 1000000000000), orderedInterval (5220646579 / 1000000000000) (5220646708 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 172 12 (431227425501197 / 800000000000)) (orderedInterval (-17506178886 / 1000000000000) (-17506178311 / 1000000000000), orderedInterval (29589394703 / 1000000000000) (29589395278 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 249 12 (124986515806503 / 160000000000)) (orderedInterval (8589202449 / 1000000000000) (8589202453 / 1000000000000), orderedInterval (-27230246705 / 1000000000000) (-27230246701 / 1000000000000))) = true
  rfl'

theorem compactCertificate551_stateChecks6 :
    compactCertificate551.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 138 12 (345719280400741 / 800000000000)) (orderedInterval (-21848206221 / 1000000000000) (-21848203722 / 1000000000000), orderedInterval (31581650969 / 1000000000000) (31581653467 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 117 12 (293070062731901 / 800000000000)) (orderedInterval (17895696624 / 1000000000000) (17895697176 / 1000000000000), orderedInterval (-37674664302 / 1000000000000) (-37674663750 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (183389637578303 / 800000000000)) (orderedInterval (-33366788000 / 1000000000000) (-33366787999 / 1000000000000), orderedInterval (-40716719395 / 1000000000000) (-40716719394 / 1000000000000))) = true
  rfl'

theorem compactCertificate551_stateChecks7 :
    compactCertificate551.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (98627557016001 / 800000000000)) (orderedInterval (-71838658686 / 1000000000000) (-71838658659 / 1000000000000), orderedInterval (-1438822174 / 1000000000000) (-1438822147 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 107 12 (267793003091003 / 800000000000)) (orderedInterval (25485447731 / 1000000000000) (25485452926 / 1000000000000), orderedInterval (-35426188535 / 1000000000000) (-35426183340 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 146 12 (365648451392731 / 800000000000)) (orderedInterval (-27460567029 / 1000000000000) (-27460545996 / 1000000000000), orderedInterval (25304013046 / 1000000000000) (25304034078 / 1000000000000))) = true
  rfl'

theorem compactCertificate551_stateChecks8 :
    compactCertificate551.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (154610362421697 / 800000000000)) (orderedInterval (-38318664153 / 1000000000000) (-38318634316 / 1000000000000), orderedInterval (42827825920 / 1000000000000) (42827855757 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 250 12 (628482539533537 / 800000000000)) (orderedInterval (23802875968 / 1000000000000) (23802875970 / 1000000000000), orderedInterval (15598337477 / 1000000000000) (15598337478 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 167 12 (419797209973583 / 800000000000)) (orderedInterval (-26971603673 / 1000000000000) (-26971603672 / 1000000000000), orderedInterval (-22013523291 / 1000000000000) (-22013523290 / 1000000000000))) = true
  rfl'

theorem compactCertificate551_states : ∀ j,
    BesselStateValid (compactCertificate551.point j) (compactCertificate551.state j) :=
  compactCertificate551.statesValid_of_checks3 compactCertificate551_stateChecks0
    compactCertificate551_stateChecks1 compactCertificate551_stateChecks2
    compactCertificate551_stateChecks3 compactCertificate551_stateChecks4
    compactCertificate551_stateChecks5 compactCertificate551_stateChecks6
    compactCertificate551_stateChecks7 compactCertificate551_stateChecks8

theorem compactCertificate551_chunkChecks0_0 :
    compactCertificate551.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (845 / 2) 0 (IntervalRat.scale (845 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (28642106758 / 1000000000000) (28642132252 / 1000000000000), orderedInterval (-26233550302 / 1000000000000) (-26233524809 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (248969270195269 / 800000000000) 0 (IntervalRat.scale (845 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-37534681930 / 1000000000000) (-37534681929 / 1000000000000), orderedInterval (-25173876070 / 1000000000000) (-25173876069 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (80511546584677 / 160000000000) 0 (IntervalRat.scale (845 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (34521325410 / 1000000000000) (34521325428 / 1000000000000), orderedInterval (8534670906 / 1000000000000) (8534670924 / 1000000000000)))) (orderedInterval (13028728741 / 1000000000000) (13028738877 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (72648612104783 / 800000000000) 0 (IntervalRat.scale (845 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-39300858310 / 1000000000000) (-39300858309 / 1000000000000), orderedInterval (-73715355172 / 1000000000000) (-73715355171 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (195144390986051 / 800000000000) 0 (IntervalRat.scale (845 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-16498771428 / 1000000000000) (-16498771147 / 1000000000000), orderedInterval (48382921810 / 1000000000000) (48382922091 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (529854982517367 / 800000000000) 0 (IntervalRat.scale (845 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-7004252022 / 1000000000000) (-7004252021 / 1000000000000), orderedInterval (-30196354770 / 1000000000000) (-30196354769 / 1000000000000)))) (orderedInterval (321917233 / 1000000000000) (321917294 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (390288781972271 / 800000000000) 0 (IntervalRat.scale (845 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-35826019966 / 1000000000000) (-35826017729 / 1000000000000), orderedInterval (4664477159 / 1000000000000) (4664479396 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (668766480168683 / 800000000000) 0 (IntervalRat.scale (845 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (24334734826 / 1000000000000) (24334734832 / 1000000000000), orderedInterval (12999501947 / 1000000000000) (12999501953 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (492610362421697 / 800000000000) 0 (IntervalRat.scale (845 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (22975712858 / 1000000000000) (22975712859 / 1000000000000), orderedInterval (22475523378 / 1000000000000) (22475523379 / 1000000000000)))) (orderedInterval (-195302949 / 1000000000000) (-195302924 / 1000000000000))) = true
  rfl'

theorem compactCertificate551_chunkChecks0_1 :
    compactCertificate551.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (755790976394831 / 800000000000) 0 (IntervalRat.scale (845 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (2472773907 / 1000000000000) (2472773908 / 1000000000000), orderedInterval (-25842042272 / 1000000000000) (-25842042271 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (436356123672599 / 800000000000) 0 (IntervalRat.scale (845 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-13517563754 / 1000000000000) (-13517563652 / 1000000000000), orderedInterval (31388053031 / 1000000000000) (31388053133 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (774321598775491 / 800000000000) 0 (IntervalRat.scale (845 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (22579288946 / 1000000000000) (22579288960 / 1000000000000), orderedInterval (12150050713 / 1000000000000) (12150050727 / 1000000000000)))) (orderedInterval (1768856572 / 1000000000000) (1768856749 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (723471679932079 / 800000000000) 0 (IntervalRat.scale (845 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (9002470110 / 1000000000000) (9002470111 / 1000000000000), orderedInterval (24953319328 / 1000000000000) (24953319329 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (516303528298207 / 800000000000) 0 (IntervalRat.scale (845 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-26487220261 / 1000000000000) (-26487176040 / 1000000000000), orderedInterval (16898155834 / 1000000000000) (16898200055 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (585433172958153 / 800000000000) 0 (IntervalRat.scale (845 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-16301924048 / 1000000000000) (-16301924047 / 1000000000000), orderedInterval (-24569226290 / 1000000000000) (-24569226289 / 1000000000000)))) (orderedInterval (-2584732727 / 1000000000000) (-2584728495 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (488073145136057 / 800000000000) 0 (IntervalRat.scale (845 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (31874027755 / 1000000000000) (31874027884 / 1000000000000), orderedInterval (5220646579 / 1000000000000) (5220646708 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (431227425501197 / 800000000000) 0 (IntervalRat.scale (845 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-17506178886 / 1000000000000) (-17506178311 / 1000000000000), orderedInterval (29589394703 / 1000000000000) (29589395278 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (124986515806503 / 160000000000) 0 (IntervalRat.scale (845 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (8589202449 / 1000000000000) (8589202453 / 1000000000000), orderedInterval (-27230246705 / 1000000000000) (-27230246701 / 1000000000000)))) (orderedInterval (1589808655 / 1000000000000) (1589808731 / 1000000000000))) = true
  rfl'

theorem compactCertificate551_chunkChecks0_2 :
    compactCertificate551.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (345719280400741 / 800000000000) 0 (IntervalRat.scale (845 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-21848206221 / 1000000000000) (-21848203722 / 1000000000000), orderedInterval (31581650969 / 1000000000000) (31581653467 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (293070062731901 / 800000000000) 0 (IntervalRat.scale (845 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (17895696624 / 1000000000000) (17895697176 / 1000000000000), orderedInterval (-37674664302 / 1000000000000) (-37674663750 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (183389637578303 / 800000000000) 0 (IntervalRat.scale (845 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-33366788000 / 1000000000000) (-33366787999 / 1000000000000), orderedInterval (-40716719395 / 1000000000000) (-40716719394 / 1000000000000)))) (orderedInterval (1394202095 / 1000000000000) (1394202632 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (98627557016001 / 800000000000) 0 (IntervalRat.scale (845 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-71838658686 / 1000000000000) (-71838658659 / 1000000000000), orderedInterval (-1438822174 / 1000000000000) (-1438822147 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (267793003091003 / 800000000000) 0 (IntervalRat.scale (845 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (25485447731 / 1000000000000) (25485452926 / 1000000000000), orderedInterval (-35426188535 / 1000000000000) (-35426183340 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (365648451392731 / 800000000000) 0 (IntervalRat.scale (845 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-27460567029 / 1000000000000) (-27460545996 / 1000000000000), orderedInterval (25304013046 / 1000000000000) (25304034078 / 1000000000000)))) (orderedInterval (2852869473 / 1000000000000) (2852871254 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (154610362421697 / 800000000000) 0 (IntervalRat.scale (845 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-38318664153 / 1000000000000) (-38318634316 / 1000000000000), orderedInterval (42827825920 / 1000000000000) (42827855757 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (628482539533537 / 800000000000) 0 (IntervalRat.scale (845 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (23802875968 / 1000000000000) (23802875970 / 1000000000000), orderedInterval (15598337477 / 1000000000000) (15598337478 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (419797209973583 / 800000000000) 0 (IntervalRat.scale (845 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-26971603673 / 1000000000000) (-26971603672 / 1000000000000), orderedInterval (-22013523291 / 1000000000000) (-22013523290 / 1000000000000)))) (orderedInterval (2891994388 / 1000000000000) (2891994686 / 1000000000000))) = true
  rfl'

theorem compactCertificate551_chunkChecks0 :
    compactCertificate551.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate551.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate551_chunkChecks0_0
    compactCertificate551_chunkChecks0_1 compactCertificate551_chunkChecks0_2

theorem compactCertificate551_chunkChecks1_0 :
    compactCertificate551.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (845 / 2) 1 (IntervalRat.scale (845 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (28642106758 / 1000000000000) (28642132252 / 1000000000000), orderedInterval (-26233550302 / 1000000000000) (-26233524809 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (248969270195269 / 800000000000) 1 (IntervalRat.scale (845 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-37534681930 / 1000000000000) (-37534681929 / 1000000000000), orderedInterval (-25173876070 / 1000000000000) (-25173876069 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (80511546584677 / 160000000000) 1 (IntervalRat.scale (845 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (34521325410 / 1000000000000) (34521325428 / 1000000000000), orderedInterval (8534670906 / 1000000000000) (8534670924 / 1000000000000)))) (orderedInterval (-9974364194 / 1000000000000) (-9974354055 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (72648612104783 / 800000000000) 1 (IntervalRat.scale (845 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-39300858310 / 1000000000000) (-39300858309 / 1000000000000), orderedInterval (-73715355172 / 1000000000000) (-73715355171 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (195144390986051 / 800000000000) 1 (IntervalRat.scale (845 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-16498771428 / 1000000000000) (-16498771147 / 1000000000000), orderedInterval (48382921810 / 1000000000000) (48382922091 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (529854982517367 / 800000000000) 1 (IntervalRat.scale (845 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-7004252022 / 1000000000000) (-7004252021 / 1000000000000), orderedInterval (-30196354770 / 1000000000000) (-30196354769 / 1000000000000)))) (orderedInterval (4556937527 / 1000000000000) (4556937591 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (390288781972271 / 800000000000) 1 (IntervalRat.scale (845 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-35826019966 / 1000000000000) (-35826017729 / 1000000000000), orderedInterval (4664477159 / 1000000000000) (4664479396 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (668766480168683 / 800000000000) 1 (IntervalRat.scale (845 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (24334734826 / 1000000000000) (24334734832 / 1000000000000), orderedInterval (12999501947 / 1000000000000) (12999501953 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (492610362421697 / 800000000000) 1 (IntervalRat.scale (845 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (22975712858 / 1000000000000) (22975712859 / 1000000000000), orderedInterval (22475523378 / 1000000000000) (22475523379 / 1000000000000)))) (orderedInterval (-1674017 / 1000000000000) (-1673975 / 1000000000000))) = true
  rfl'

theorem compactCertificate551_chunkChecks1_1 :
    compactCertificate551.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (755790976394831 / 800000000000) 1 (IntervalRat.scale (845 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (2472773907 / 1000000000000) (2472773908 / 1000000000000), orderedInterval (-25842042272 / 1000000000000) (-25842042271 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (436356123672599 / 800000000000) 1 (IntervalRat.scale (845 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-13517563754 / 1000000000000) (-13517563652 / 1000000000000), orderedInterval (31388053031 / 1000000000000) (31388053133 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (774321598775491 / 800000000000) 1 (IntervalRat.scale (845 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (22579288946 / 1000000000000) (22579288960 / 1000000000000), orderedInterval (12150050713 / 1000000000000) (12150050727 / 1000000000000)))) (orderedInterval (17226783265 / 1000000000000) (17226783626 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (723471679932079 / 800000000000) 1 (IntervalRat.scale (845 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (9002470110 / 1000000000000) (9002470111 / 1000000000000), orderedInterval (24953319328 / 1000000000000) (24953319329 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (516303528298207 / 800000000000) 1 (IntervalRat.scale (845 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-26487220261 / 1000000000000) (-26487176040 / 1000000000000), orderedInterval (16898155834 / 1000000000000) (16898200055 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (585433172958153 / 800000000000) 1 (IntervalRat.scale (845 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-16301924048 / 1000000000000) (-16301924047 / 1000000000000), orderedInterval (-24569226290 / 1000000000000) (-24569226289 / 1000000000000)))) (orderedInterval (1692005388 / 1000000000000) (1692011857 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (488073145136057 / 800000000000) 1 (IntervalRat.scale (845 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (31874027755 / 1000000000000) (31874027884 / 1000000000000), orderedInterval (5220646579 / 1000000000000) (5220646708 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (431227425501197 / 800000000000) 1 (IntervalRat.scale (845 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-17506178886 / 1000000000000) (-17506178311 / 1000000000000), orderedInterval (29589394703 / 1000000000000) (29589395278 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (124986515806503 / 160000000000) 1 (IntervalRat.scale (845 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (8589202449 / 1000000000000) (8589202453 / 1000000000000), orderedInterval (-27230246705 / 1000000000000) (-27230246701 / 1000000000000)))) (orderedInterval (-3362362847 / 1000000000000) (-3362362744 / 1000000000000))) = true
  rfl'

theorem compactCertificate551_chunkChecks1_2 :
    compactCertificate551.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (345719280400741 / 800000000000) 1 (IntervalRat.scale (845 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-21848206221 / 1000000000000) (-21848203722 / 1000000000000), orderedInterval (31581650969 / 1000000000000) (31581653467 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (293070062731901 / 800000000000) 1 (IntervalRat.scale (845 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (17895696624 / 1000000000000) (17895697176 / 1000000000000), orderedInterval (-37674664302 / 1000000000000) (-37674663750 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (183389637578303 / 800000000000) 1 (IntervalRat.scale (845 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-33366788000 / 1000000000000) (-33366787999 / 1000000000000), orderedInterval (-40716719395 / 1000000000000) (-40716719394 / 1000000000000)))) (orderedInterval (-4035267746 / 1000000000000) (-4035267212 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (98627557016001 / 800000000000) 1 (IntervalRat.scale (845 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-71838658686 / 1000000000000) (-71838658659 / 1000000000000), orderedInterval (-1438822174 / 1000000000000) (-1438822147 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (267793003091003 / 800000000000) 1 (IntervalRat.scale (845 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (25485447731 / 1000000000000) (25485452926 / 1000000000000), orderedInterval (-35426188535 / 1000000000000) (-35426183340 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (365648451392731 / 800000000000) 1 (IntervalRat.scale (845 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-27460567029 / 1000000000000) (-27460545996 / 1000000000000), orderedInterval (25304013046 / 1000000000000) (25304034078 / 1000000000000)))) (orderedInterval (-1453384779 / 1000000000000) (-1453382896 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (154610362421697 / 800000000000) 1 (IntervalRat.scale (845 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-38318664153 / 1000000000000) (-38318634316 / 1000000000000), orderedInterval (42827825920 / 1000000000000) (42827855757 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (628482539533537 / 800000000000) 1 (IntervalRat.scale (845 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (23802875968 / 1000000000000) (23802875970 / 1000000000000), orderedInterval (15598337477 / 1000000000000) (15598337478 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (419797209973583 / 800000000000) 1 (IntervalRat.scale (845 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-26971603673 / 1000000000000) (-26971603672 / 1000000000000), orderedInterval (-22013523291 / 1000000000000) (-22013523290 / 1000000000000)))) (orderedInterval (2887011440 / 1000000000000) (2887011687 / 1000000000000))) = true
  rfl'

theorem compactCertificate551_chunkChecks1 :
    compactCertificate551.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate551.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate551_chunkChecks1_0
    compactCertificate551_chunkChecks1_1 compactCertificate551_chunkChecks1_2

theorem compactCertificate551_chunkChecks2_0 :
    compactCertificate551.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (845 / 2) 2 (IntervalRat.scale (845 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (28642106758 / 1000000000000) (28642132252 / 1000000000000), orderedInterval (-26233550302 / 1000000000000) (-26233524809 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (248969270195269 / 800000000000) 2 (IntervalRat.scale (845 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-37534681930 / 1000000000000) (-37534681929 / 1000000000000), orderedInterval (-25173876070 / 1000000000000) (-25173876069 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (80511546584677 / 160000000000) 2 (IntervalRat.scale (845 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (34521325410 / 1000000000000) (34521325428 / 1000000000000), orderedInterval (8534670906 / 1000000000000) (8534670924 / 1000000000000)))) (orderedInterval (-14012850643 / 1000000000000) (-14012840474 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (72648612104783 / 800000000000) 2 (IntervalRat.scale (845 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-39300858310 / 1000000000000) (-39300858309 / 1000000000000), orderedInterval (-73715355172 / 1000000000000) (-73715355171 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (195144390986051 / 800000000000) 2 (IntervalRat.scale (845 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-16498771428 / 1000000000000) (-16498771147 / 1000000000000), orderedInterval (48382921810 / 1000000000000) (48382922091 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (529854982517367 / 800000000000) 2 (IntervalRat.scale (845 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-7004252022 / 1000000000000) (-7004252021 / 1000000000000), orderedInterval (-30196354770 / 1000000000000) (-30196354769 / 1000000000000)))) (orderedInterval (-1053310252 / 1000000000000) (-1053310168 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (390288781972271 / 800000000000) 2 (IntervalRat.scale (845 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-35826019966 / 1000000000000) (-35826017729 / 1000000000000), orderedInterval (4664477159 / 1000000000000) (4664479396 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (668766480168683 / 800000000000) 2 (IntervalRat.scale (845 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (24334734826 / 1000000000000) (24334734832 / 1000000000000), orderedInterval (12999501947 / 1000000000000) (12999501953 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (492610362421697 / 800000000000) 2 (IntervalRat.scale (845 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (22975712858 / 1000000000000) (22975712859 / 1000000000000), orderedInterval (22475523378 / 1000000000000) (22475523379 / 1000000000000)))) (orderedInterval (1758955697 / 1000000000000) (1758955772 / 1000000000000))) = true
  rfl'

theorem compactCertificate551_chunkChecks2_1 :
    compactCertificate551.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (755790976394831 / 800000000000) 2 (IntervalRat.scale (845 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (2472773907 / 1000000000000) (2472773908 / 1000000000000), orderedInterval (-25842042272 / 1000000000000) (-25842042271 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (436356123672599 / 800000000000) 2 (IntervalRat.scale (845 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-13517563754 / 1000000000000) (-13517563652 / 1000000000000), orderedInterval (31388053031 / 1000000000000) (31388053133 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (774321598775491 / 800000000000) 2 (IntervalRat.scale (845 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (22579288946 / 1000000000000) (22579288960 / 1000000000000), orderedInterval (12150050713 / 1000000000000) (12150050727 / 1000000000000)))) (orderedInterval (-13020151758 / 1000000000000) (-13020150991 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (723471679932079 / 800000000000) 2 (IntervalRat.scale (845 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (9002470110 / 1000000000000) (9002470111 / 1000000000000), orderedInterval (24953319328 / 1000000000000) (24953319329 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (516303528298207 / 800000000000) 2 (IntervalRat.scale (845 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-26487220261 / 1000000000000) (-26487176040 / 1000000000000), orderedInterval (16898155834 / 1000000000000) (16898200055 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (585433172958153 / 800000000000) 2 (IntervalRat.scale (845 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-16301924048 / 1000000000000) (-16301924047 / 1000000000000), orderedInterval (-24569226290 / 1000000000000) (-24569226289 / 1000000000000)))) (orderedInterval (6337411063 / 1000000000000) (6337420971 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (488073145136057 / 800000000000) 2 (IntervalRat.scale (845 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (31874027755 / 1000000000000) (31874027884 / 1000000000000), orderedInterval (5220646579 / 1000000000000) (5220646708 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (431227425501197 / 800000000000) 2 (IntervalRat.scale (845 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-17506178886 / 1000000000000) (-17506178311 / 1000000000000), orderedInterval (29589394703 / 1000000000000) (29589395278 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (124986515806503 / 160000000000) 2 (IntervalRat.scale (845 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (8589202449 / 1000000000000) (8589202453 / 1000000000000), orderedInterval (-27230246705 / 1000000000000) (-27230246701 / 1000000000000)))) (orderedInterval (-3141988238 / 1000000000000) (-3141988093 / 1000000000000))) = true
  rfl'

theorem compactCertificate551_chunkChecks2_2 :
    compactCertificate551.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (345719280400741 / 800000000000) 2 (IntervalRat.scale (845 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-21848206221 / 1000000000000) (-21848203722 / 1000000000000), orderedInterval (31581650969 / 1000000000000) (31581653467 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (293070062731901 / 800000000000) 2 (IntervalRat.scale (845 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (17895696624 / 1000000000000) (17895697176 / 1000000000000), orderedInterval (-37674664302 / 1000000000000) (-37674663750 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (183389637578303 / 800000000000) 2 (IntervalRat.scale (845 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-33366788000 / 1000000000000) (-33366787999 / 1000000000000), orderedInterval (-40716719395 / 1000000000000) (-40716719394 / 1000000000000)))) (orderedInterval (-2563909834 / 1000000000000) (-2563909298 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (98627557016001 / 800000000000) 2 (IntervalRat.scale (845 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-71838658686 / 1000000000000) (-71838658659 / 1000000000000), orderedInterval (-1438822174 / 1000000000000) (-1438822147 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (267793003091003 / 800000000000) 2 (IntervalRat.scale (845 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (25485447731 / 1000000000000) (25485452926 / 1000000000000), orderedInterval (-35426188535 / 1000000000000) (-35426183340 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (365648451392731 / 800000000000) 2 (IntervalRat.scale (845 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-27460567029 / 1000000000000) (-27460545996 / 1000000000000), orderedInterval (25304013046 / 1000000000000) (25304034078 / 1000000000000)))) (orderedInterval (-2209502721 / 1000000000000) (-2209500710 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (154610362421697 / 800000000000) 2 (IntervalRat.scale (845 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-38318664153 / 1000000000000) (-38318634316 / 1000000000000), orderedInterval (42827825920 / 1000000000000) (42827855757 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (628482539533537 / 800000000000) 2 (IntervalRat.scale (845 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (23802875968 / 1000000000000) (23802875970 / 1000000000000), orderedInterval (15598337477 / 1000000000000) (15598337478 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (419797209973583 / 800000000000) 2 (IntervalRat.scale (845 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-26971603673 / 1000000000000) (-26971603672 / 1000000000000), orderedInterval (-22013523291 / 1000000000000) (-22013523290 / 1000000000000)))) (orderedInterval (-1065727559 / 1000000000000) (-1065727277 / 1000000000000))) = true
  rfl'

theorem compactCertificate551_chunkChecks2 :
    compactCertificate551.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate551.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate551_chunkChecks2_0
    compactCertificate551_chunkChecks2_1 compactCertificate551_chunkChecks2_2

theorem compactCertificate551_chunkChecks3_0 :
    compactCertificate551.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (845 / 2) 3 (IntervalRat.scale (845 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (28642106758 / 1000000000000) (28642132252 / 1000000000000), orderedInterval (-26233550302 / 1000000000000) (-26233524809 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (248969270195269 / 800000000000) 3 (IntervalRat.scale (845 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-37534681930 / 1000000000000) (-37534681929 / 1000000000000), orderedInterval (-25173876070 / 1000000000000) (-25173876069 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (80511546584677 / 160000000000) 3 (IntervalRat.scale (845 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (34521325410 / 1000000000000) (34521325428 / 1000000000000), orderedInterval (8534670906 / 1000000000000) (8534670924 / 1000000000000)))) (orderedInterval (9678813423 / 1000000000000) (9678823598 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (72648612104783 / 800000000000) 3 (IntervalRat.scale (845 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-39300858310 / 1000000000000) (-39300858309 / 1000000000000), orderedInterval (-73715355172 / 1000000000000) (-73715355171 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (195144390986051 / 800000000000) 3 (IntervalRat.scale (845 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-16498771428 / 1000000000000) (-16498771147 / 1000000000000), orderedInterval (48382921810 / 1000000000000) (48382922091 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (529854982517367 / 800000000000) 3 (IntervalRat.scale (845 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-7004252022 / 1000000000000) (-7004252021 / 1000000000000), orderedInterval (-30196354770 / 1000000000000) (-30196354769 / 1000000000000)))) (orderedInterval (-8614943181 / 1000000000000) (-8614943059 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (390288781972271 / 800000000000) 3 (IntervalRat.scale (845 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-35826019966 / 1000000000000) (-35826017729 / 1000000000000), orderedInterval (4664477159 / 1000000000000) (4664479396 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (668766480168683 / 800000000000) 3 (IntervalRat.scale (845 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (24334734826 / 1000000000000) (24334734832 / 1000000000000), orderedInterval (12999501947 / 1000000000000) (12999501953 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (492610362421697 / 800000000000) 3 (IntervalRat.scale (845 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (22975712858 / 1000000000000) (22975712859 / 1000000000000), orderedInterval (22475523378 / 1000000000000) (22475523379 / 1000000000000)))) (orderedInterval (1420060808 / 1000000000000) (1420060943 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate551_chunkChecks3_1 :
    compactCertificate551.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (755790976394831 / 800000000000) 3 (IntervalRat.scale (845 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (2472773907 / 1000000000000) (2472773908 / 1000000000000), orderedInterval (-25842042272 / 1000000000000) (-25842042271 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (436356123672599 / 800000000000) 3 (IntervalRat.scale (845 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-13517563754 / 1000000000000) (-13517563652 / 1000000000000), orderedInterval (31388053031 / 1000000000000) (31388053133 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (774321598775491 / 800000000000) 3 (IntervalRat.scale (845 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (22579288946 / 1000000000000) (22579288960 / 1000000000000), orderedInterval (12150050713 / 1000000000000) (12150050727 / 1000000000000)))) (orderedInterval (-77077267457 / 1000000000000) (-77077265785 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (723471679932079 / 800000000000) 3 (IntervalRat.scale (845 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (9002470110 / 1000000000000) (9002470111 / 1000000000000), orderedInterval (24953319328 / 1000000000000) (24953319329 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (516303528298207 / 800000000000) 3 (IntervalRat.scale (845 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-26487220261 / 1000000000000) (-26487176040 / 1000000000000), orderedInterval (16898155834 / 1000000000000) (16898200055 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (585433172958153 / 800000000000) 3 (IntervalRat.scale (845 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-16301924048 / 1000000000000) (-16301924047 / 1000000000000), orderedInterval (-24569226290 / 1000000000000) (-24569226289 / 1000000000000)))) (orderedInterval (-1938797360 / 1000000000000) (-1938782203 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (488073145136057 / 800000000000) 3 (IntervalRat.scale (845 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (31874027755 / 1000000000000) (31874027884 / 1000000000000), orderedInterval (5220646579 / 1000000000000) (5220646708 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (431227425501197 / 800000000000) 3 (IntervalRat.scale (845 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-17506178886 / 1000000000000) (-17506178311 / 1000000000000), orderedInterval (29589394703 / 1000000000000) (29589395278 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (124986515806503 / 160000000000) 3 (IntervalRat.scale (845 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (8589202449 / 1000000000000) (8589202453 / 1000000000000), orderedInterval (-27230246705 / 1000000000000) (-27230246701 / 1000000000000)))) (orderedInterval (7748985395 / 1000000000000) (7748985603 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate551_chunkChecks3_2 :
    compactCertificate551.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (345719280400741 / 800000000000) 3 (IntervalRat.scale (845 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-21848206221 / 1000000000000) (-21848203722 / 1000000000000), orderedInterval (31581650969 / 1000000000000) (31581653467 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (293070062731901 / 800000000000) 3 (IntervalRat.scale (845 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (17895696624 / 1000000000000) (17895697176 / 1000000000000), orderedInterval (-37674664302 / 1000000000000) (-37674663750 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (183389637578303 / 800000000000) 3 (IntervalRat.scale (845 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-33366788000 / 1000000000000) (-33366787999 / 1000000000000), orderedInterval (-40716719395 / 1000000000000) (-40716719394 / 1000000000000)))) (orderedInterval (4231324454 / 1000000000000) (4231324994 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (98627557016001 / 800000000000) 3 (IntervalRat.scale (845 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-71838658686 / 1000000000000) (-71838658659 / 1000000000000), orderedInterval (-1438822174 / 1000000000000) (-1438822147 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (267793003091003 / 800000000000) 3 (IntervalRat.scale (845 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (25485447731 / 1000000000000) (25485452926 / 1000000000000), orderedInterval (-35426188535 / 1000000000000) (-35426183340 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (365648451392731 / 800000000000) 3 (IntervalRat.scale (845 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-27460567029 / 1000000000000) (-27460545996 / 1000000000000), orderedInterval (25304013046 / 1000000000000) (25304034078 / 1000000000000)))) (orderedInterval (2060008949 / 1000000000000) (2060011100 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (154610362421697 / 800000000000) 3 (IntervalRat.scale (845 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-38318664153 / 1000000000000) (-38318634316 / 1000000000000), orderedInterval (42827825920 / 1000000000000) (42827855757 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (628482539533537 / 800000000000) 3 (IntervalRat.scale (845 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (23802875968 / 1000000000000) (23802875970 / 1000000000000), orderedInterval (15598337477 / 1000000000000) (15598337478 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (419797209973583 / 800000000000) 3 (IntervalRat.scale (845 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-26971603673 / 1000000000000) (-26971603672 / 1000000000000), orderedInterval (-22013523291 / 1000000000000) (-22013523290 / 1000000000000)))) (orderedInterval (227472599 / 1000000000000) (227472991 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate551_chunkChecks3 :
    compactCertificate551.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate551.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate551_chunkChecks3_0
    compactCertificate551_chunkChecks3_1 compactCertificate551_chunkChecks3_2

theorem compactCertificate551_chunkChecks4_0 :
    compactCertificate551.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (845 / 2) 4 (IntervalRat.scale (845 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (28642106758 / 1000000000000) (28642132252 / 1000000000000), orderedInterval (-26233550302 / 1000000000000) (-26233524809 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (248969270195269 / 800000000000) 4 (IntervalRat.scale (845 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-37534681930 / 1000000000000) (-37534681929 / 1000000000000), orderedInterval (-25173876070 / 1000000000000) (-25173876069 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (80511546584677 / 160000000000) 4 (IntervalRat.scale (845 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (34521325410 / 1000000000000) (34521325428 / 1000000000000), orderedInterval (8534670906 / 1000000000000) (8534670924 / 1000000000000)))) (orderedInterval (15279850357 / 1000000000000) (15279860564 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (72648612104783 / 800000000000) 4 (IntervalRat.scale (845 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-39300858310 / 1000000000000) (-39300858309 / 1000000000000), orderedInterval (-73715355172 / 1000000000000) (-73715355171 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (195144390986051 / 800000000000) 4 (IntervalRat.scale (845 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-16498771428 / 1000000000000) (-16498771147 / 1000000000000), orderedInterval (48382921810 / 1000000000000) (48382922091 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (529854982517367 / 800000000000) 4 (IntervalRat.scale (845 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-7004252022 / 1000000000000) (-7004252021 / 1000000000000), orderedInterval (-30196354770 / 1000000000000) (-30196354769 / 1000000000000)))) (orderedInterval (2981723468 / 1000000000000) (2981723654 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (390288781972271 / 800000000000) 4 (IntervalRat.scale (845 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-35826019966 / 1000000000000) (-35826017729 / 1000000000000), orderedInterval (4664477159 / 1000000000000) (4664479396 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (668766480168683 / 800000000000) 4 (IntervalRat.scale (845 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (24334734826 / 1000000000000) (24334734832 / 1000000000000), orderedInterval (12999501947 / 1000000000000) (12999501953 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (492610362421697 / 800000000000) 4 (IntervalRat.scale (845 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (22975712858 / 1000000000000) (22975712859 / 1000000000000), orderedInterval (22475523378 / 1000000000000) (22475523379 / 1000000000000)))) (orderedInterval (-9004885740 / 1000000000000) (-9004885490 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate551_chunkChecks4_1 :
    compactCertificate551.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (755790976394831 / 800000000000) 4 (IntervalRat.scale (845 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (2472773907 / 1000000000000) (2472773908 / 1000000000000), orderedInterval (-25842042272 / 1000000000000) (-25842042271 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (436356123672599 / 800000000000) 4 (IntervalRat.scale (845 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-13517563754 / 1000000000000) (-13517563652 / 1000000000000), orderedInterval (31388053031 / 1000000000000) (31388053133 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (774321598775491 / 800000000000) 4 (IntervalRat.scale (845 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (22579288946 / 1000000000000) (22579288960 / 1000000000000), orderedInterval (12150050713 / 1000000000000) (12150050727 / 1000000000000)))) (orderedInterval (75006638619 / 1000000000000) (75006642319 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (723471679932079 / 800000000000) 4 (IntervalRat.scale (845 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (9002470110 / 1000000000000) (9002470111 / 1000000000000), orderedInterval (24953319328 / 1000000000000) (24953319329 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (516303528298207 / 800000000000) 4 (IntervalRat.scale (845 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-26487220261 / 1000000000000) (-26487176040 / 1000000000000), orderedInterval (16898155834 / 1000000000000) (16898200055 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (585433172958153 / 800000000000) 4 (IntervalRat.scale (845 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-16301924048 / 1000000000000) (-16301924047 / 1000000000000), orderedInterval (-24569226290 / 1000000000000) (-24569226289 / 1000000000000)))) (orderedInterval (-16296452240 / 1000000000000) (-16296429005 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (488073145136057 / 800000000000) 4 (IntervalRat.scale (845 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (31874027755 / 1000000000000) (31874027884 / 1000000000000), orderedInterval (5220646579 / 1000000000000) (5220646708 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (431227425501197 / 800000000000) 4 (IntervalRat.scale (845 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-17506178886 / 1000000000000) (-17506178311 / 1000000000000), orderedInterval (29589394703 / 1000000000000) (29589395278 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (124986515806503 / 160000000000) 4 (IntervalRat.scale (845 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (8589202449 / 1000000000000) (8589202453 / 1000000000000), orderedInterval (-27230246705 / 1000000000000) (-27230246701 / 1000000000000)))) (orderedInterval (6787858019 / 1000000000000) (6787858327 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate551_chunkChecks4_2 :
    compactCertificate551.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (345719280400741 / 800000000000) 4 (IntervalRat.scale (845 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-21848206221 / 1000000000000) (-21848203722 / 1000000000000), orderedInterval (31581650969 / 1000000000000) (31581653467 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (293070062731901 / 800000000000) 4 (IntervalRat.scale (845 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (17895696624 / 1000000000000) (17895697176 / 1000000000000), orderedInterval (-37674664302 / 1000000000000) (-37674663750 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (183389637578303 / 800000000000) 4 (IntervalRat.scale (845 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-33366788000 / 1000000000000) (-33366787999 / 1000000000000), orderedInterval (-40716719395 / 1000000000000) (-40716719394 / 1000000000000)))) (orderedInterval (3136895757 / 1000000000000) (3136896304 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (98627557016001 / 800000000000) 4 (IntervalRat.scale (845 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-71838658686 / 1000000000000) (-71838658659 / 1000000000000), orderedInterval (-1438822174 / 1000000000000) (-1438822147 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (267793003091003 / 800000000000) 4 (IntervalRat.scale (845 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (25485447731 / 1000000000000) (25485452926 / 1000000000000), orderedInterval (-35426188535 / 1000000000000) (-35426183340 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (365648451392731 / 800000000000) 4 (IntervalRat.scale (845 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-27460567029 / 1000000000000) (-27460545996 / 1000000000000), orderedInterval (25304013046 / 1000000000000) (25304034078 / 1000000000000)))) (orderedInterval (2654378369 / 1000000000000) (2654380682 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (154610362421697 / 800000000000) 4 (IntervalRat.scale (845 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-38318664153 / 1000000000000) (-38318634316 / 1000000000000), orderedInterval (42827825920 / 1000000000000) (42827855757 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (628482539533537 / 800000000000) 4 (IntervalRat.scale (845 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (23802875968 / 1000000000000) (23802875970 / 1000000000000), orderedInterval (15598337477 / 1000000000000) (15598337478 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (419797209973583 / 800000000000) 4 (IntervalRat.scale (845 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-26971603673 / 1000000000000) (-26971603672 / 1000000000000), orderedInterval (-22013523291 / 1000000000000) (-22013523290 / 1000000000000)))) (orderedInterval (-11131013144 / 1000000000000) (-11131012533 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate551_chunkChecks4 :
    compactCertificate551.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate551.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate551_chunkChecks4_0
    compactCertificate551_chunkChecks4_1 compactCertificate551_chunkChecks4_2

theorem compactCertificate551_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate551.chunkCheck r b = true :=
  compactCertificate551.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate551_chunkChecks0
    · exact compactCertificate551_chunkChecks1
    · exact compactCertificate551_chunkChecks2
    · exact compactCertificate551_chunkChecks3
    · exact compactCertificate551_chunkChecks4)

theorem compactCertificate551_coefficient0 :
    compactCertificate551.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate551_coefficient1 :
    compactCertificate551.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate551_coefficient2 :
    compactCertificate551.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate551_coefficient3 :
    compactCertificate551.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate551_coefficient4 :
    compactCertificate551.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate551_coefficients : ∀ r : Fin 5,
    compactCertificate551.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate551_coefficient0
  · exact compactCertificate551_coefficient1
  · exact compactCertificate551_coefficient2
  · exact compactCertificate551_coefficient3
  · exact compactCertificate551_coefficient4

theorem compactCertificate551_lower : (1 : ℚ) ≤ compactCertificate551.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate551, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate551_proves {t : ℝ} (ht : t ∈ compactCertificate551.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate551.proves compactCertificate551_states compactCertificate551_chunks
    compactCertificate551_coefficients compactCertificate551_lower ht

end Erdos232
